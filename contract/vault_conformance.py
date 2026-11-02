#!/usr/bin/env python3
"""Conformance probes: the handshake between this auditor and a Lean "vault".

A vault is any repository that owns a real Lean 4 toolchain, a built Lake
project, and (optionally) a corpus. This auditor cannot assume anything about it:
Lean output formats vary between versions, and a wrong assumption silently
degrades a verdict from "verified" to "verified nothing".

So instead of a promise, both sides run the same probes and compare the answers.
The auditor's engine imports this module; the vault side runs this file directly
(it has no imports from the auditor and needs nothing beyond a Lean install).
A test in `tests/test_audit.py` fails if the two copies ever diverge.

Every probe answers one question: "does this specific Lean command produce the
shape of output the auditor parses?" A failed probe maps to an explicit
capability, and the engine degrades named checks rather than guessing.

Contract version: lean-audit-vault/1
"""

from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

CONTRACT_VERSION = "lean-audit-vault/1"

# ---------------------------------------------------------------------------
# Probe definitions. The IDs are part of the contract: changing one is a
# contract version bump.
# ---------------------------------------------------------------------------

CLEAN_SOURCE = "theorem conformance_clean (n : Nat) : n = n := rfl\n"
AXIOM_SOURCE = (
    "axiom conformance_assumption : False\n"
    "theorem conformance_uses_axiom : False := conformance_assumption\n"
)
SORRY_SOURCE = "theorem conformance_sorry : 1 = 1 := by\n  sorry\n"
DECIDE_SOURCE = "example : ¬ (1 > 2) := by decide\n"
BADNAME_SOURCE = "#check this_identifier_does_not_exist\n"
TYPEERROR_SOURCE = "theorem conformance_bad : (1 : Nat) = 2 := rfl\n"

# (id, capability it gates, required, human description)
PROBES = [
    ("version", "toolchain", True, "`lean --version` identifies the toolchain"),
    ("print_axioms_clean", "axiom_query", True, "`#print axioms` reports an empty axiom set"),
    ("print_axioms_list", "axiom_query", True, "`#print axioms` reports a non-empty axiom set"),
    ("print_axioms_sorry", "axiom_query", True, "`#print axioms` exposes `sorryAx`"),
    ("sorry_warning", "sorry_warning", True, "compiling a `sorry` emits the `declaration uses 'sorry'` warning"),
    ("diagnostic_format", "diagnostics", True, "errors are printed as `file:line:col: error: message`"),
    ("olean_out", "olean_out", True, "`-o <path>` keeps build artifacts out of the client's tree"),
    ("pp_all_inline", "pp_all", True, "`set_option pp.all true in #check @f` prints a fully elaborated type"),
    ("pp_all_global", "pp_all", False, "a file-wide `set_option pp.all true` also works (fallback)"),
    ("decide_refutation", "decide_refutation", False, "`by decide` can refute a closed hypothesis"),
    ("lake_env", "lake_env", False, "`lake env lean` runs inside the project"),
    ("mathlib_import", "mathlib", False, "`import Mathlib` resolves in this project"),
]

REQUIRED_IDS = {pid for pid, _cap, required, _d in PROBES if required}


class ProbeRunner:
    def __init__(self, lean_path: str, project: str | None, timeout: float = 180.0, lake_path: str | None = None):
        self.lean_path = lean_path
        self.lake_path = lake_path
        self.project = Path(project).resolve() if project else None
        self.timeout = timeout
        self.tmp = Path(tempfile.mkdtemp(prefix="vault-conformance-"))

    def close(self) -> None:
        shutil.rmtree(self.tmp, ignore_errors=True)

    # -- process helpers -------------------------------------------------
    def run(self, argv: list[str], cwd: str | None = None, timeout: float | None = None):
        try:
            proc = subprocess.run(
                argv,
                cwd=cwd or str(self.tmp),
                capture_output=True,
                text=True,
                timeout=timeout or self.timeout,
                start_new_session=True,
            )
            return proc.returncode, proc.stdout or "", proc.stderr or "", False
        except subprocess.TimeoutExpired as exc:
            return None, _text(exc.stdout), _text(exc.stderr) + "\n[timeout]", True
        except OSError as exc:
            return None, "", f"[oserror] {exc}", True

    def compile(self, source: str, name: str, extra_flags: list[str] | None = None):
        path = self.tmp / name
        path.write_text(source, encoding="utf-8")
        argv = [self.lean_path, *(extra_flags or []), str(path)]
        return self.run(argv), path

    # -- capability detection -------------------------------------------
    def detect_lake(self) -> str | None:
        if self.lake_path and Path(self.lake_path).exists():
            return self.lake_path
        sibling = Path(self.lean_path).parent / "lake"
        if sibling.exists():
            return str(sibling)
        return shutil.which("lake")

    def has_lakefile(self) -> bool:
        if not self.project:
            return False
        return any((self.project / name).exists() for name in ("lakefile.lean", "lakefile.toml"))


def _text(value) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", "replace")
    return value


# ---------------------------------------------------------------------------
# Individual probes
# ---------------------------------------------------------------------------
def _ok(probe_id: str, observed: str, detail: str = "") -> dict:
    return {"id": probe_id, "status": "ok", "observed": _clip(observed), "detail": detail}


def _fail(probe_id: str, observed: str, detail: str) -> dict:
    return {"id": probe_id, "status": "fail", "observed": _clip(observed), "detail": detail}


def _skip(probe_id: str, detail: str) -> dict:
    return {"id": probe_id, "status": "skipped", "observed": "", "detail": detail}


def _clip(text: str, limit: int = 600) -> str:
    text = (text or "").strip()
    return text if len(text) <= limit else text[: limit - 1] + "…"


def probe_version(runner: ProbeRunner) -> dict:
    code, out, err, _ = runner.run([runner.lean_path, "--version"], timeout=120)
    blob = (out or "") + (err or "")
    match = re.search(r"Lean \(version (\d+)\.(\d+)\.(\d+)", blob)
    if code == 0 and match:
        return _ok("version", blob, f"parsed version {'.'.join(match.groups())}")
    return _fail("version", blob, "could not parse `Lean (version X.Y.Z` from --version output")


def probe_print_axioms(runner: ProbeRunner, probe_id: str, source: str, needle: str) -> dict:
    (code, out, err, _), _path = runner.compile(source, f"{probe_id}.lean")
    blob = (out or "") + (err or "")
    pattern = re.compile(
        r"^@?'?(?P<name>[^'\n]+?)'?\s+"
        r"(?:depends on axioms:\s*\[(?P<list>[^\]]*)\]|does not depend on any axioms)",
        re.M,
    )
    matches = list(pattern.finditer(blob))
    if not matches:
        return _fail(probe_id, blob, "no `#print axioms` line matched the expected format")
    if needle == "":
        empty = [m for m in matches if m.group("list") is None]
        if empty:
            return _ok(probe_id, blob, "matched the 'does not depend on any axioms' form")
        return _fail(probe_id, blob, "expected a line reporting no axioms")
    lists = [m.group("list") or "" for m in matches]
    if any(needle in entry for entry in lists):
        return _ok(probe_id, blob, f"found `{needle}` in the reported axiom list")
    return _fail(probe_id, blob, f"`{needle}` not present in any reported axiom list")


def probe_sorry_warning(runner: ProbeRunner) -> dict:
    (code, out, err, _), _path = runner.compile(SORRY_SOURCE, "sorry_warning.lean")
    blob = (out or "") + (err or "")
    if re.search(r"declaration uses 'sorry'", blob):
        return _ok("sorry_warning", blob, "Lean emits the standard sorry warning")
    return _fail("sorry_warning", blob, "expected `declaration uses 'sorry'` in the compiler output")


def probe_diagnostic_format(runner: ProbeRunner) -> dict:
    """Errors must carry a file:line:col the auditor can attribute to a declaration.

    A type error is tried first because it also has continuation lines the parser
    must survive; an unknown identifier is the fallback, since its position is
    reported identically across Lean versions.
    """
    pattern = re.compile(r"^(?P<file>.+?):(?P<line>\d+):(?P<col>\d+):\s+error:", re.M)
    (code, out, err, _), _path = runner.compile(TYPEERROR_SOURCE, "diagnostic_format.lean")
    blob = (out or "") + (err or "")
    match = pattern.search(blob)
    if match:
        return _ok("diagnostic_format", blob, f"type error at {match.group('line')}:{match.group('col')}")

    (code, out, err, _), _path = runner.compile(BADNAME_SOURCE, "diagnostic_format_name.lean")
    blob2 = (out or "") + (err or "")
    match = pattern.search(blob2)
    if match:
        return _ok(
            "diagnostic_format",
            blob2,
            f"unknown-identifier error at {match.group('line')}:{match.group('col')} (type-error probe produced no match)",
        )
    return _fail("diagnostic_format", (blob + "\n---\n" + blob2), "no `file:line:col: error:` diagnostic from either probe")


def probe_olean_out(runner: ProbeRunner) -> dict:
    source = CLEAN_SOURCE
    path = runner.tmp / "olean_out.lean"
    path.write_text(source, encoding="utf-8")
    out_flag = runner.tmp / "audit-out.olean"
    code, out, err, _ = runner.run([runner.lean_path, "-o", str(out_flag), str(path)])
    beside = path.with_suffix(".olean")
    blob = (out or "") + (err or "")
    if code != 0:
        return _fail("olean_out", blob, "`lean -o <path> <file>` did not succeed")
    if beside.exists():
        return _fail("olean_out", blob, "compiling with `-o` still wrote an .olean next to the source")
    return _ok("olean_out", "compiled with -o into a scratch directory", "no artifact left in the client tree")


def probe_pp_all(runner: ProbeRunner, inline: bool) -> dict:
    probe_id = "pp_all_inline" if inline else "pp_all_global"
    if inline:
        source = CLEAN_SOURCE + "set_option pp.all true in\n#check @conformance_clean\n"
        name = "pp_all_inline.lean"
    else:
        source = "set_option pp.all true\n" + CLEAN_SOURCE + "#check @conformance_clean\n"
        name = "pp_all_global.lean"
    (code, out, err, _), _path = runner.compile(source, name)
    blob = (out or "") + (err or "")
    line = next((l for l in (out or "").splitlines() if l.strip().startswith("@") and " : " in l), None)
    if line:
        return _ok(probe_id, line, "`#check` printed a fully qualified, @-prefixed type")
    return _fail(probe_id, blob, "`#check` did not print an `@name : type` line under pp.all")


def probe_decide(runner: ProbeRunner) -> dict:
    (code, out, err, _), _path = runner.compile(DECIDE_SOURCE, "decide_refutation.lean")
    blob = (out or "") + (err or "")
    if code == 0:
        return _ok("decide_refutation", "`by decide` closed a negated decidable goal", "")
    return _fail(
        "decide_refutation",
        blob,
        "`by decide` is unavailable; the vacuity-by-refutation probe cannot run on this toolchain",
    )


def probe_lake_env(runner: ProbeRunner) -> dict:
    lake = runner.detect_lake()
    if not lake or not runner.has_lakefile():
        return _skip("lake_env", "no lakefile in the project, or `lake` is not installed")
    source = runner.tmp / "lake_env.lean"
    source.write_text(CLEAN_SOURCE, encoding="utf-8")
    code, out, err, _ = runner.run([lake, "env", "lean", str(source)], cwd=str(runner.project))
    blob = (out or "") + (err or "")
    if code == 0:
        return _ok("lake_env", "`lake env lean` compiled a probe file", "")
    return _fail("lake_env", blob, "`lake env lean` failed; audits must run with a built project")


def probe_mathlib(runner: ProbeRunner) -> dict:
    source = "import Mathlib\ntheorem conformance_mathlib : (1 : Nat) = 1 := rfl\n"
    (code, out, err, _), _path = runner.compile(source, "mathlib_import.lean")
    blob = (out or "") + (err or "")
    if code == 0:
        return _ok("mathlib_import", "`import Mathlib` resolved", "")
    if re.search(r"unknown module prefix|object file .* does not exist|could not resolve import", blob):
        return _skip("mathlib_import", "Mathlib is not built in this project (not a failure of the toolchain)")
    return _fail("mathlib_import", blob, "importing Mathlib failed unexpectedly")


PROBE_FUNCS = {
    "version": lambda r: probe_version(r),
    "print_axioms_clean": lambda r: probe_print_axioms(r, "print_axioms_clean", CLEAN_SOURCE + "#print axioms conformance_clean\n", ""),
    "print_axioms_list": lambda r: probe_print_axioms(r, "print_axioms_list", AXIOM_SOURCE + "#print axioms conformance_uses_axiom\n", "conformance_assumption"),
    "print_axioms_sorry": lambda r: probe_print_axioms(r, "print_axioms_sorry", SORRY_SOURCE + "#print axioms conformance_sorry\n", "sorryAx"),
    "sorry_warning": lambda r: probe_sorry_warning(r),
    "diagnostic_format": lambda r: probe_diagnostic_format(r),
    "olean_out": lambda r: probe_olean_out(r),
    "pp_all_inline": lambda r: probe_pp_all(r, inline=True),
    "pp_all_global": lambda r: probe_pp_all(r, inline=False),
    "decide_refutation": lambda r: probe_decide(r),
    "lake_env": lambda r: probe_lake_env(r),
    "mathlib_import": lambda r: probe_mathlib(r),
}


# ---------------------------------------------------------------------------
def discover_lean(explicit: str | None = None) -> str | None:
    for candidate in (explicit, os.environ.get("LEAN_AUDIT_LEAN"), shutil.which("lean")):
        if candidate and Path(candidate).exists():
            return candidate
    elan = Path.home() / ".elan" / "bin" / "lean"
    return str(elan) if elan.exists() else None


def run_conformance(project: str | None = None, lean: str | None = None, timeout: float = 180.0) -> dict:
    result = {
        "contract_version": CONTRACT_VERSION,
        "generated_at": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "project": str(Path(project).resolve()) if project else None,
        "lean": {"path": None, "version": None},
        "probes": [],
        "capabilities": {},
        "summary": {},
        "compatible": False,
    }

    lean_path = discover_lean(lean)
    if lean_path is None:
        result["error"] = (
            "No Lean toolchain found. Install with: "
            "curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh"
        )
        result["summary"] = {"ok": 0, "failed": 0, "skipped": 0, "required_failed": []}
        return result

    runner = ProbeRunner(lean_path, project, timeout=timeout)
    try:
        results = []
        for probe_id, capability, required, description in PROBES:
            try:
                outcome = PROBE_FUNCS[probe_id](runner)
            except Exception as exc:  # a crashing probe is a failed probe, never a pass
                outcome = _fail(probe_id, "", f"probe crashed: {type(exc).__name__}: {exc}")
            outcome["capability"] = capability
            outcome["required"] = required
            outcome["description"] = description
            results.append(outcome)
        result["probes"] = results

        version_probe = next((p for p in results if p["id"] == "version"), None)
        if version_probe and version_probe["status"] == "ok":
            match = re.search(r"Lean \(version [^)]+\)", version_probe["observed"])
            result["lean"] = {
                "path": lean_path,
                "version": match.group(0) if match else version_probe["observed"][:120],
            }

        capabilities: dict[str, bool] = {}
        for probe in results:
            cap = probe["capability"]
            capabilities[cap] = capabilities.get(cap, False) or probe["status"] == "ok"
        # pp_all is satisfied if either form works.
        result["capabilities"] = capabilities
    finally:
        runner.close()

    required_failed = [
        p["id"] for p in result["probes"] if p["required"] and p["status"] != "ok"
    ]
    ok = sum(1 for p in result["probes"] if p["status"] == "ok")
    failed = sum(1 for p in result["probes"] if p["status"] == "fail")
    skipped = sum(1 for p in result["probes"] if p["status"] == "skipped")
    result["summary"] = {
        "ok": ok,
        "failed": failed,
        "skipped": skipped,
        "required_failed": required_failed,
    }
    result["compatible"] = not required_failed
    return result


def render_text(result: dict) -> str:
    lines = []
    lean = result.get("lean") or {}
    lines.append(f"vault conformance — {result['contract_version']}")
    lines.append(f"  project: {result.get('project') or '(none)'}")
    lines.append(f"  lean:    {lean.get('version') or 'NOT FOUND'}")
    if lean.get("path"):
        lines.append(f"  path:    {lean['path']}")
    lines.append("")
    symbols = {"ok": "✓", "fail": "✗", "skipped": "·"}
    for probe in result["probes"]:
        required = "" if probe["required"] else " (optional)"
        lines.append(f"  {symbols[probe['status']]} {probe['id']:<20}{required}")
        if probe["status"] != "ok" and probe["detail"]:
            lines.append(f"      {probe['detail']}")
    summary = result.get("summary", {})
    lines.append("")
    lines.append(
        f"  {summary.get('ok', 0)} ok · {summary.get('failed', 0)} failed · "
        f"{summary.get('skipped', 0)} skipped"
    )
    if result.get("compatible"):
        lines.append("  COMPATIBLE — this vault can back a full audit")
    else:
        failed = ", ".join(summary.get("required_failed", []))
        lines.append(f"  INCOMPATIBLE — required probes failed: {failed}")
    if result.get("error"):
        lines.append("")
        lines.append(result["error"])
    return "\n".join(lines)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        prog="vault_conformance",
        description="Check that a Lean toolchain produces the output shapes the auditor parses.",
    )
    parser.add_argument("--project", help="Lake project root to test against (enables lake_env / mathlib probes)")
    parser.add_argument("--lean", help="path to the `lean` executable")
    parser.add_argument("--timeout", type=float, default=180.0)
    parser.add_argument("--out", help="write the JSON result here")
    parser.add_argument("--json", dest="json_out", action="store_true", help="print JSON instead of text")
    args = parser.parse_args(argv)

    result = run_conformance(args.project, args.lean, args.timeout)
    payload = json.dumps(result, indent=2)
    if args.out:
        Path(args.out).write_text(payload + "\n", encoding="utf-8")
    if args.json_out:
        print(payload)
    else:
        print(render_text(result))

    if result.get("lean", {}).get("path") is None:
        return 2
    return 0 if result.get("compatible") else 1


if __name__ == "__main__":
    sys.exit(main())
