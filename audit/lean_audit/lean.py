"""The only place in this package that talks to Lean.

Design constraints that shaped this module:

1. **No re-implementation of the kernel.** The audit asks Lean questions and
   records the answers. It never decides on its own that something is proved.
2. **Version-stable surface only.** The commands used are `#print axioms`,
   `#check`, and plain compilation — stable across Lean 4 releases. Nothing
   here depends on `#print` internals that have churned between versions.
3. **Every run is evidence.** Each invocation records argv, exit status, stdout,
   stderr, duration, and the sha256 of the exact input text, so a third party
   can replay the audit byte for byte.
4. **Probes preserve the environment.** A probe file is the client's source
   followed by the probe commands, so it compiles under exactly the same
   imports, options, and namespaces as the code under audit.
"""

from __future__ import annotations

import os
import re
import shutil
import signal
import subprocess
import tempfile
import time
from dataclasses import dataclass, field
from pathlib import Path

from .model import Evidence, SourceSpan

DIAG_RE = re.compile(
    r"^(?P<file>[^\s:][^:]*):(?P<line>\d+):(?P<col>\d+):\s+"
    r"(?P<severity>error|warning|information|info|trace)(?:\((?P<code>[^)]*)\))?:\s*"
    r"(?P<message>.*)$"
)
BARE_DIAG_RE = re.compile(r"^(?P<severity>error|warning)(?:\((?P<code>[^)]*)\))?:\s*(?P<message>.*)$")


class ToolchainMissing(RuntimeError):
    """No usable Lean toolchain was found."""


@dataclass
class Diagnostic:
    severity: str
    message: str
    file: str | None = None
    line: int | None = None
    col: int | None = None
    code: str | None = None
    continuation: list[str] = field(default_factory=list)

    @property
    def is_error(self) -> bool:
        return self.severity == "error"

    @property
    def full_message(self) -> str:
        return "\n".join([self.message, *self.continuation]).strip()

    def span(self) -> SourceSpan | None:
        if self.file is None or self.line is None:
            return None
        return SourceSpan(self.file, self.line, self.col or 1, self.line, self.col or 1)

    def to_dict(self) -> dict:
        d = {"severity": self.severity, "message": self.full_message}
        if self.file:
            d["file"] = self.file
        if self.line is not None:
            d["line"] = self.line
        if self.col is not None:
            d["col"] = self.col
        if self.code:
            d["code"] = self.code
        return d

    def signature(self) -> str:
        """Identity of a diagnostic, for delta-debugging reproducibility."""
        msg = re.sub(r"\s+", " ", self.full_message)[:200]
        return f"{self.code or ''}|{msg}"


@dataclass
class RunResult:
    command: list[str]
    stdout: str
    stderr: str
    exit_code: int | None
    duration_ms: int
    timed_out: bool
    input_text: str
    input_path: str

    @property
    def ok(self) -> bool:
        return self.exit_code == 0 and not self.timed_out

    @property
    def combined(self) -> str:
        return self.stdout + ("\n" if self.stdout and self.stderr else "") + self.stderr

    def diagnostics(self) -> list[Diagnostic]:
        return parse_diagnostics(self.stderr + "\n" + self.stdout)

    @property
    def errors(self) -> list[Diagnostic]:
        return [d for d in self.diagnostics() if d.is_error]

    def evidence(self, summary: str, location: SourceSpan | None = None) -> Evidence:
        return Evidence(
            kind="lean_run",
            summary=summary,
            command=self.command,
            stdout=self.stdout,
            stderr=self.stderr,
            exit_code=self.exit_code,
            exit_status="timeout" if self.timed_out else ("ok" if self.ok else "error"),
            duration_ms=self.duration_ms,
            location=location,
            input_text=self.input_text,
        )


def parse_diagnostics(text: str) -> list[Diagnostic]:
    out: list[Diagnostic] = []
    current: Diagnostic | None = None
    for line in text.splitlines():
        if not line.strip():
            continue
        m = DIAG_RE.match(line)
        if m:
            current = Diagnostic(
                severity=_norm_sev(m.group("severity")),
                message=m.group("message").strip(),
                file=m.group("file"),
                line=int(m.group("line")),
                col=int(m.group("col")),
                code=m.group("code"),
            )
            out.append(current)
            continue
        m = BARE_DIAG_RE.match(line)
        if m and not line.startswith(" "):
            current = Diagnostic(
                severity=_norm_sev(m.group("severity")),
                message=m.group("message").strip(),
                code=m.group("code"),
            )
            out.append(current)
            continue
        if current is not None:
            current.continuation.append(line.rstrip())
    return out


def _norm_sev(sev: str) -> str:
    return "info" if sev in ("information", "info") else sev


def _version_key(version: str) -> tuple[int, ...]:
    m = re.search(r"(\d+)\.(\d+)\.(\d+)", version)
    if not m:
        return (0, 0, 0)
    return tuple(int(g) for g in m.groups())


@dataclass
class Toolchain:
    lean: str
    version: str
    lake: str | None = None
    is_lake_project: bool = False

    @property
    def version_key(self) -> tuple[int, ...]:
        return _version_key(self.version)

    def command_for(self, source_path: str, extra_flags: list[str] | None = None) -> list[str]:
        flags = list(extra_flags or [])
        if self.lake and self.is_lake_project:
            return [self.lake, "env", "lean", *flags, source_path]
        return [self.lean, *flags, source_path]

    def to_dict(self) -> dict:
        return {
            "lean": self.lean,
            "version": self.version,
            "lake": self.lake,
            "is_lake_project": self.is_lake_project,
        }


def discover(project_dir: str | None = None) -> Toolchain:
    """Find a Lean toolchain. Raises ToolchainMissing with a helpful message."""
    candidates: list[str] = []
    env_lean = os.environ.get("LEAN_AUDIT_LEAN")
    if env_lean:
        candidates.append(env_lean)
    on_path = shutil.which("lean")
    if on_path:
        candidates.append(on_path)
    elan_bin = Path.home() / ".elan" / "bin" / "lean"
    if elan_bin.exists():
        candidates.append(str(elan_bin))

    errors: list[str] = []
    for cand in candidates:
        try:
            proc = subprocess.run(
                [cand, "--version"], capture_output=True, text=True, timeout=120
            )
        except (OSError, subprocess.SubprocessError) as exc:
            errors.append(f"{cand}: {exc}")
            continue
        if proc.returncode == 0 and "Lean" in (proc.stdout + proc.stderr):
            lake = shutil.which("lake") or (
                str(Path(cand).parent / "lake") if (Path(cand).parent / "lake").exists() else None
            )
            is_project = bool(
                project_dir
                and (
                    (Path(project_dir) / "lakefile.lean").exists()
                    or (Path(project_dir) / "lakefile.toml").exists()
                )
            )
            version = (proc.stdout or proc.stderr).strip()
            return Toolchain(lean=cand, version=version, lake=lake, is_lake_project=is_project)

    detail = "; ".join(errors) if errors else "no `lean` executable on PATH, in ~/.elan/bin, or in $LEAN_AUDIT_LEAN"
    raise ToolchainMissing(
        "No Lean toolchain found — " + detail + ".\n"
        "Install with:  curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh\n"
        "or set LEAN_AUDIT_LEAN=/path/to/lean. Notes: GitHub release downloads can be blocked on hosts that only "
        "allow git/npm/pypi egress, in which case run the audit where a toolchain is already installed."
    )


class LeanRunner:
    """Runs Lean on generated sources inside a scratch directory."""

    def __init__(
        self,
        toolchain: Toolchain,
        workdir: str,
        project_dir: str | None = None,
        timeout: float = 300.0,
        env: dict[str, str] | None = None,
    ) -> None:
        self.toolchain = toolchain
        self.workdir = Path(workdir)
        self.workdir.mkdir(parents=True, exist_ok=True)
        self.project_dir = Path(project_dir).resolve() if project_dir else None
        self.timeout = timeout
        self.env = dict(os.environ if env is None else env)
        self.run_count = 0
        self.total_duration_ms = 0

    # -- low level -------------------------------------------------------
    def run_source(self, source: str, name: str = "Probe.lean", extra_flags: list[str] | None = None) -> RunResult:
        path = self.workdir / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(source, encoding="utf-8")
        return self.run_path(str(path), extra_flags=extra_flags)

    def run_path(self, path: str, extra_flags: list[str] | None = None) -> RunResult:
        cmd = self.toolchain.command_for(path, extra_flags)
        cwd = str(self.project_dir) if (self.project_dir and self.toolchain.is_lake_project) else str(Path(path).parent)
        started = time.monotonic()
        timed_out = False
        proc: subprocess.CompletedProcess[str] | None = None
        try:
            proc = subprocess.run(
                cmd,
                cwd=cwd,
                capture_output=True,
                text=True,
                timeout=self.timeout,
                env=self.env,
                start_new_session=True,
            )
        except subprocess.TimeoutExpired as exc:
            timed_out = True
            proc = subprocess.CompletedProcess(
                cmd,
                returncode=None,
                stdout=_as_text(exc.stdout),
                stderr=_as_text(exc.stderr) + f"\n[audit] timed out after {self.timeout}s",
            )
        duration = int((time.monotonic() - started) * 1000)
        self.run_count += 1
        self.total_duration_ms += duration
        return RunResult(
            command=cmd,
            stdout=proc.stdout or "",
            stderr=proc.stderr or "",
            exit_code=proc.returncode,
            duration_ms=duration,
            timed_out=timed_out,
            input_text=Path(path).read_text(encoding="utf-8"),
            input_path=str(path),
        )

    def compile_in_place(self, path: str) -> RunResult:
        """Compile a client file without leaving build artifacts in their tree."""
        out = self.workdir / "audit-out.olean"
        return self.run_path(path, extra_flags=["-o", str(out)])

    # -- probes ----------------------------------------------------------
    def probe(self, source: str, commands: list[str], name: str = "Probe.lean") -> tuple[RunResult, list[str]]:
        """Append `commands` to `source` and run it.

        Returns the run plus the command block as written, so the exact probe can
        be quoted in the report.
        """
        block = "\n\n-- ==== lean-audit probes (generated; nothing above this line was modified) ====\n"
        block += "\n".join(commands) + "\n"
        result = self.run_source(source.rstrip("\n") + "\n" + block, name=name)
        return result, commands


def _as_text(value: bytes | str | None) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return value


def doctor(project_dir: str | None = None) -> dict:
    """Environment report for `lean-audit doctor`."""
    info: dict = {
        "project_dir": str(Path(project_dir).resolve()) if project_dir else None,
        "lean_version": None,
        "lean_path": None,
        "lake_path": None,
        "lake_project": False,
        "mathlib_present": False,
        "probe": None,
    }
    try:
        tc = discover(project_dir)
    except ToolchainMissing as exc:
        info["error"] = str(exc)
        return info
    info.update(tc.to_dict())
    info["lean_version"] = tc.version
    info["lean_path"] = tc.lean
    info["lake_path"] = tc.lake

    if project_dir:
        lake_dir = Path(project_dir) / ".lake" / "packages"
        info["mathlib_present"] = (lake_dir / "mathlib").exists() or (lake_dir / "Mathlib").exists()

    with tempfile.TemporaryDirectory() as tmp:
        runner = LeanRunner(tc, tmp, project_dir=project_dir, timeout=180)
        # A self-contained probe: no imports, so it works even without Mathlib.
        run = runner.run_source(
            "theorem _audit_probe (n : Nat) : n = n := rfl\n"
            "#print axioms _audit_probe\n"
            "set_option pp.all true in\n"
            "#check @_audit_probe\n"
        )
        info["probe"] = {
            "ok": run.ok,
            "exit_code": run.exit_code,
            "stdout": run.stdout.strip()[:2000],
            "stderr": run.stderr.strip()[:2000],
        }
    return info
