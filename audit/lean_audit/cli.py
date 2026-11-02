"""Command line interface.

Exit codes are part of the contract, because the marketplace worker dispatches on
them: 0 PASS, 1 WARN, 2 FAIL, 3 INCONCLUSIVE / environment problem.
"""

from __future__ import annotations

import argparse
import datetime as _dt
import json
import shutil
import sys
import tempfile
from pathlib import Path

from . import SCHEMA_VERSION, __version__, expr, stmtparse
from .checks import REGISTRY, AuditContext, run_all
from .conformance_probe import render_text as render_conformance
from .conformance_probe import run_conformance
from .config import Config
from .lean import LeanRunner, ToolchainMissing, discover, doctor
from .model import Verdict, now_ms
from .report import build_report, render_markdown, sha256_text, to_json
from .source import index_source
from .vault import VaultError, load_conformance, load_vault

EXIT_CODES = {
    Verdict.PASS: 0,
    Verdict.WARN: 1,
    Verdict.FAIL: 2,
    Verdict.INCONCLUSIVE: 3,
    Verdict.SKIPPED: 3,
}


def main(argv: list[str] | None = None) -> int:
    parser = _build_parser()
    args = parser.parse_args(argv)
    if not getattr(args, "command", None):
        parser.print_help()
        return 3
    return {
        "audit": cmd_audit,
        "doctor": cmd_doctor,
        "selfcheck": cmd_selfcheck,
        "checks": cmd_checks,
        "init-claim": cmd_init_claim,
        "conform": cmd_conform,
        "vault": cmd_vault,
    }[args.command](args)


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog="lean-audit",
        description="Evidence-carrying audits for Lean 4: kernel acceptance, axiom surface, statement honesty, and proof dependence.",
    )
    p.add_argument("--version", action="version", version=f"lean-audit {__version__} ({SCHEMA_VERSION})")
    sub = p.add_subparsers(dest="command")

    audit = sub.add_parser("audit", help="audit one Lean file")
    audit.add_argument("target", help="path to the .lean file under audit")
    audit.add_argument("--project", help="Lake project root (enables `lake env lean` and Mathlib imports)")
    audit.add_argument("--vault", help="directory containing vault.manifest.json; supplies the toolchain, project, and provenance")
    audit.add_argument("--json", dest="json_out", help="write the JSON report here ('-' for stdout)")
    audit.add_argument("--markdown", dest="markdown_out", help="write a human-readable report here")
    audit.add_argument("--claim", dest="claim", help="JSON file describing the intended claim")
    audit.add_argument("--timeout", type=float, default=300.0, help="per-invocation timeout in seconds")
    audit.add_argument("--checks", help=f"comma-separated subset of: {', '.join(n for n, _ in REGISTRY)}")
    audit.add_argument("--max-mutants", type=int, default=40, help="cap on mutation experiments (each costs one Lean run)")
    audit.add_argument("--allow-axiom", action="append", default=None, help="additional axiom to treat as acceptable")
    audit.add_argument("--allow-compiler-trust", action="store_true", help="do not flag native_decide-style trust")
    audit.add_argument("--strict", action="store_true", help="treat medium findings as failures")
    audit.add_argument("--keep-workdir", action="store_true", help="keep probe/mutant files for inspection")
    audit.add_argument("--quiet", action="store_true", help="suppress the terminal summary")

    doc = sub.add_parser("doctor", help="check that the Lean environment is usable")
    doc.add_argument("--project", help="Lake project root")
    doc.add_argument("--json", dest="json_out", help="write the environment report here ('-' for stdout)")

    self_check = sub.add_parser("selfcheck", help="audit the bundled corpus and verify the auditor catches what it should")
    self_check.add_argument("--corpus", default=str(Path(__file__).parent.parent / "corpus"))
    self_check.add_argument("--verbose", action="store_true")

    sub.add_parser("checks", help="list the available checks")

    conform = sub.add_parser(
        "conform",
        help="bootstrap the auditor/vault handshake: does this toolchain emit the output shapes the audit parses?",
    )
    conform.add_argument("--vault", help="vault directory (reads project root from its manifest)")
    conform.add_argument("--project", help="Lake project root, if not using a manifest")
    conform.add_argument("--lean", help="path to the `lean` executable")
    conform.add_argument("--timeout", type=float, default=180.0)
    conform.add_argument("--json", dest="json_out", help="write the conformance result here ('-' for stdout)")
    conform.add_argument("--write-manifest", metavar="DIR", help="also write a starter vault.manifest.json into DIR")

    vault = sub.add_parser("vault", help="show a vault's identity, capabilities, and corpus inventory")
    vault.add_argument("directory", help="vault directory")
    vault.add_argument("--json", dest="json_out", help="write the summary here ('-' for stdout)")

    claim = sub.add_parser("init-claim", help="generate a claim template from a declaration's elaborated statement")
    claim.add_argument("target")
    claim.add_argument("--declaration", help="declaration name (default: the first theorem)")
    claim.add_argument("--pick", type=int, default=0, help="which theorem to use when several exist")
    claim.add_argument("--project")
    claim.add_argument("--out", help="write here instead of stdout")
    return p


# ---------------------------------------------------------------------------
def cmd_audit(args) -> int:
    target = Path(args.target).expanduser().resolve()
    if not target.exists():
        print(f"lean-audit: no such file: {target}", file=sys.stderr)
        return 3
    if target.suffix != ".lean":
        print(f"lean-audit: warning: {target.name} does not end in .lean", file=sys.stderr)

    vault = None
    if getattr(args, "vault", None):
        try:
            vault = load_vault(args.vault)
        except VaultError as exc:
            print(f"lean-audit: {exc}", file=sys.stderr)
            return 3

    project = Path(args.project).expanduser().resolve() if args.project else None
    if vault is not None and project is None:
        project = vault.project_dir
    if project is None:
        project = _guess_project(target)
    source = target.read_text(encoding="utf-8")
    index = index_source(str(target), source)

    config = Config(
        timeout=args.timeout,
        max_mutants=max_mutants(args),
        enabled_checks=tuple(c.strip() for c in args.checks.split(",")) if args.checks else None,
        claim_path=str(Path(args.claim).expanduser().resolve()) if args.claim else None,
        strict=args.strict,
        keep_workdir=args.keep_workdir,
        allow_compiler_trust=args.allow_compiler_trust,
        allow_axioms=tuple(sorted(set(config_default_axioms()) | set(args.allow_axiom or ()))),
    )

    started = _dt.datetime.now()
    started_ms = now_ms()
    workdir = Path(tempfile.mkdtemp(prefix="lean-audit-"))
    try:
        toolchain = discover(str(project) if project else None)
    except ToolchainMissing as exc:
        report = _no_toolchain_report(target, source, str(exc), config, started, started_ms)
        _emit(report, args)
        return 3

    runner = LeanRunner(toolchain, str(workdir), project_dir=str(project) if project else None, timeout=config.timeout)
    capabilities: dict = {}
    if vault is not None:
        conformance = load_conformance(vault)
        if conformance is not None:
            capabilities = dict(conformance.get("capabilities") or {})
        declared = (vault.raw.get("capabilities") or {})
        for key, value in declared.items():
            capabilities.setdefault(key, bool(value))
    ctx = AuditContext(
        target=target,
        source=source,
        index=index,
        toolchain=toolchain,
        runner=runner,
        config=config,
        project_dir=project,
        vault=vault,
        capabilities=capabilities,
    )
    results = run_all(ctx)

    if args.strict:
        results = [_strictify(r) for r in results]

    toolchain_info = toolchain.to_dict()
    if vault is not None:
        toolchain_info["vault"] = vault.identity()
        toolchain_info["capabilities"] = capabilities
    report = build_report(
        target=str(target),
        results=results,
        toolchain=toolchain_info,
        config=config.to_dict(),
        notes=ctx.notes,
        runner_stats={"lean_runs": runner.run_count, "lean_time_ms": runner.total_duration_ms},
        started_at=started,
        duration_ms=now_ms() - started_ms,
        target_sha256=sha256_text(source),
    )
    _emit(report, args)
    overall = report["verdict"]["overall"]
    if not args.keep_workdir:
        shutil.rmtree(workdir, ignore_errors=True)
    else:
        print(f"lean-audit: workdir kept at {workdir}", file=sys.stderr)
    return EXIT_CODES.get(Verdict(overall), 3)


def max_mutants(args) -> int:
    return max(0, args.max_mutants)


def config_default_axioms():
    from .config import STANDARD_AXIOMS

    return STANDARD_AXIOMS


def _strictify(result):
    from .model import Severity

    if any(f.severity.rank >= Severity.MEDIUM.rank for f in result.findings) and result.verdict in (
        Verdict.PASS,
        Verdict.WARN,
    ):
        result.verdict = Verdict.WARN if result.verdict is Verdict.PASS else result.verdict
    return result


def _guess_project(target: Path) -> Path | None:
    for parent in [target.parent, *target.parent.parents]:
        if (parent / "lakefile.lean").exists() or (parent / "lakefile.toml").exists():
            return parent
    return None


def _no_toolchain_report(target, source, error, config, started, started_ms) -> dict:
    from .model import Category, CheckResult, Confidence, Finding, Severity

    finding = Finding(
        check="build",
        code="no_toolchain",
        severity=Severity.CRITICAL,
        category=Category.REPRODUCIBILITY,
        confidence=Confidence.PROVEN,
        title="No Lean toolchain available: nothing was verified",
        detail=(
            "This audit could not find a usable Lean installation, so no proof was checked. "
            "The absence of a verdict is not a verdict of correctness — this report states "
            "explicitly that no evidence was gathered."
        ),
        remediation=error,
    )
    results = [
        CheckResult(
            name="build",
            verdict=Verdict.INCONCLUSIVE,
            summary="no Lean toolchain",
            skip_reason=error,
            findings=[finding],
            duration_ms=now_ms() - started_ms,
        )
    ]
    return build_report(
        target=str(target),
        results=results,
        toolchain={"error": error},
        config=config.to_dict(),
        notes=["No Lean toolchain was found; every check was skipped."],
        runner_stats={"lean_runs": 0, "lean_time_ms": 0},
        started_at=started,
        duration_ms=now_ms() - started_ms,
        target_sha256=sha256_text(source),
    )


def _emit(report: dict, args) -> None:
    payload = to_json(report)
    if args.json_out == "-":
        print(payload)
    elif args.json_out:
        Path(args.json_out).expanduser().write_text(payload + "\n", encoding="utf-8")
    if args.markdown_out:
        Path(args.markdown_out).expanduser().write_text(render_markdown(report) + "\n", encoding="utf-8")
    if not getattr(args, "quiet", False):
        print(render_terminal(report), file=sys.stdout if args.json_out != "-" else sys.stderr)


def render_terminal(report: dict) -> str:
    v = report["verdict"]
    symbols = {"pass": "✓", "warn": "!", "fail": "✗", "inconclusive": "?", "skipped": "·"}
    lines = []
    lines.append(f"audit report — {report['target']['path']}")
    lines.append(f"sha256 {report['target']['sha256'][:32]}…  lean {report['environment'].get('version', 'unknown')}")
    lines.append("")
    for check in report["checks"]:
        if check["verdict"] == "skipped":
            continue
        lines.append(f"  {symbols.get(check['verdict'], '?')} {check['name']:<12} {check['summary']}")
    lines.append("")
    counts = v["counts"]
    lines.append(
        f"  verdict: {v['overall'].upper()}  "
        f"({counts['critical']} critical, {counts['high']} high, {counts['medium']} medium)"
    )
    lines.append(f"  {v['reason']}")
    severe = [f for f in report["findings"] if f["severity"] in ("critical", "high")]
    if severe:
        lines.append("")
        lines.append("  top findings:")
        for f in severe[:8]:
            where = f["declaration"] or (f["location"]["file"].split("/")[-1] if f.get("location") else "")
            lines.append(f"    [{f['severity']}] {f['code']}: {f['title'][:96]}  {where}")
    return "\n".join(lines)


# ---------------------------------------------------------------------------
def cmd_doctor(args) -> int:
    info = doctor(args.project)
    if args.json_out:
        payload = json.dumps(info, indent=2)
        if args.json_out == "-":
            print(payload)
        else:
            Path(args.json_out).expanduser().write_text(payload + "\n", encoding="utf-8")
    else:
        print(f"project:     {info.get('project_dir') or '(none)'}")
        print(f"lean:        {info.get('lean_path') or 'NOT FOUND'}")
        print(f"version:     {info.get('lean_version') or '—'}")
        print(f"lake:        {info.get('lake_path') or '—'}")
        print(f"lake project:{'yes' if info.get('lake_project') else 'no'}")
        print(f"mathlib:     {'present' if info.get('mathlib_present') else 'not found in .lake/packages'}")
        probe = info.get("probe") or {}
        if probe:
            print(f"probe:       {'ok' if probe.get('ok') else 'FAILED'} (exit {probe.get('exit_code')})")
            if probe.get("stdout"):
                for line in probe["stdout"].splitlines():
                    print(f"  | {line}")
            if probe.get("stderr"):
                for line in probe["stderr"].splitlines()[:12]:
                    print(f"  ! {line}")
        if info.get("error"):
            print("")
            print(info["error"])
    return 0 if info.get("lean_path") else 3


def cmd_conform(args) -> int:
    project = args.project
    if args.vault and not project:
        try:
            project = str(load_vault(args.vault).project_dir)
        except VaultError as exc:
            print(f"lean-audit: {exc}", file=sys.stderr)
            return 3
    result = run_conformance(project, args.lean, args.timeout)

    if args.json_out == "-":
        print(json.dumps(result, indent=2))
    elif args.json_out:
        Path(args.json_out).expanduser().write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    if args.json_out != "-":
        print(render_conformance(result))

    if args.write_manifest:
        from .vault import CONTRACT_VERSION

        lean = result.get("lean") or {}
        manifest = {
            "contract_version": CONTRACT_VERSION,
            "name": Path(args.write_manifest).resolve().name,
            "repo": "<vault repo url>",
            "commit": "<git rev-parse HEAD>",
            "generated_at": result.get("generated_at"),
            "lean": {"path": lean.get("path"), "version": lean.get("version")},
            "project": {"root": ".", "build_command": "lake build", "has_mathlib": False, "packages": []},
            "corpus": [],
            "capabilities": result.get("capabilities") or {},
            "conformance": "conformance.json",
        }
        out = Path(args.write_manifest).expanduser() / "vault.manifest.json"
        out.write_text(json.dumps(manifest, indent=2) + "\n", encoding="utf-8")
        print(f"\nlean-audit: wrote starter manifest {out} — fill in repo, commit, and corpus.", file=sys.stderr)

    if (result.get("lean") or {}).get("path") is None:
        return 2
    return 0 if result.get("compatible") else 1


def cmd_vault(args) -> int:
    try:
        vault = load_vault(args.directory)
    except VaultError as exc:
        print(f"lean-audit: {exc}", file=sys.stderr)
        return 3
    conformance = load_conformance(vault)
    summary = {
        "vault": vault.identity(),
        "project": {"root": str(vault.project_dir), "build_command": vault.build_command, "has_mathlib": vault.has_mathlib},
        "capabilities": (conformance or {}).get("capabilities") or vault.raw.get("capabilities") or {},
        "conformance": {
            "published": conformance is not None,
            "compatible": (conformance or {}).get("compatible"),
            "required_failed": ((conformance or {}).get("summary") or {}).get("required_failed", []),
        },
        "corpus": [
            {"id": e.id, "path": e.path, "claim": e.claim, "expect": e.expect}
            for e in vault.corpus
        ],
    }
    if args.json_out == "-":
        print(json.dumps(summary, indent=2))
        return 0
    if args.json_out:
        Path(args.json_out).expanduser().write_text(json.dumps(summary, indent=2) + "\n", encoding="utf-8")

    print(f"vault:       {vault.name}")
    print(f"repo:        {vault.repo or '(not recorded)'}")
    print(f"commit:      {vault.commit or '(not recorded)'}")
    print(f"contract:    {vault.contract_version}")
    print(f"lean:        {vault.lean_version or '(unknown)'}")
    print(f"project:     {vault.project_dir}")
    print(f"mathlib:     {'declared' if vault.has_mathlib else 'not declared'}")
    conf = summary["conformance"]
    if conf["published"]:
        state = "COMPATIBLE" if conf["compatible"] else f"INCOMPATIBLE ({', '.join(conf['required_failed'])})"
        print(f"conformance: {state}")
    else:
        print("conformance: no conformance.json published — capabilities are unverified")
    caps = summary["capabilities"]
    if caps:
        print("capabilities:")
        for key in sorted(caps):
            print(f"  {'yes' if caps[key] else 'no ':<4} {key}")
    print(f"corpus:      {len(vault.corpus)} file(s)")
    for entry in vault.corpus[:40]:
        print(f"  {entry.id:<32} {entry.path}")
    return 0


def cmd_checks(args) -> int:
    print(f"lean-audit {__version__} — checks\n")
    for name, desc in REGISTRY:
        print(f"  {name:<12} {desc}")
    print("\nexit codes: 0 pass · 1 warn · 2 fail · 3 inconclusive/environment")
    return 0


def cmd_init_claim(args) -> int:
    target = Path(args.target).expanduser().resolve()
    source = target.read_text(encoding="utf-8")
    index = index_source(str(target), source)
    theorems = [d for d in index.named_theorems()]
    if not theorems:
        print("lean-audit: no named theorems in this file", file=sys.stderr)
        return 3
    if args.declaration:
        matches = [d for d in theorems if d.name == args.declaration or d.qualified_name == args.declaration]
        if not matches:
            print(f"lean-audit: no declaration named {args.declaration}", file=sys.stderr)
            return 3
        decl = matches[0]
    else:
        decl = theorems[min(args.pick, len(theorems) - 1)]

    vault = None
    if getattr(args, "vault", None):
        try:
            vault = load_vault(args.vault)
        except VaultError as exc:
            print(f"lean-audit: {exc}", file=sys.stderr)
            return 3

    project = Path(args.project).expanduser().resolve() if args.project else None
    if vault is not None and project is None:
        project = vault.project_dir
    if project is None:
        project = _guess_project(target)
    try:
        toolchain = discover(str(project) if project else None)
    except ToolchainMissing as exc:
        print(str(exc), file=sys.stderr)
        return 3

    with tempfile.TemporaryDirectory() as tmp:
        runner = LeanRunner(toolchain, tmp, project_dir=str(project) if project else None)
        run_result, _ = runner.probe(
            source,
            [f"set_option pp.all true in\n#check @{decl.qualified_name}"],
            name="ProbeClaim.lean",
        )
    parsed = stmtparse.parse_check_output(run_result.stdout, decl.qualified_name or "")
    if parsed is None:
        print("lean-audit: could not elaborate the declaration's type", file=sys.stderr)
        return 3

    claim = {
        "declaration": decl.qualified_name,
        "prose": "<write the claim in plain language here; prose alone cannot be machine-compared>",
        "quantifiers": [
            {"name": b.name, "type": b.type_text} for b in parsed.binders if b.kind != "instance"
        ],
        "hypotheses": [b.type_text for b in parsed.binders if b.kind == "explicit"],
        "conclusion": parsed.conclusion,
        "_generated_by": f"lean-audit {__version__} init-claim",
        "_note": (
            "This template is the ELABORATED statement. Correct it to describe what you actually "
            "intended to prove, then run `lean-audit audit <file> --claim <this file>`. If you "
            "leave it as generated, the claim check can only confirm the formal statement matches "
            "itself."
        ),
    }
    payload = json.dumps(claim, indent=2)
    if args.out:
        Path(args.out).expanduser().write_text(payload + "\n", encoding="utf-8")
        print(f"wrote {args.out}")
    else:
        print(payload)
    return 0


def cmd_selfcheck(args) -> int:
    corpus = Path(args.corpus).expanduser().resolve()
    if not corpus.exists():
        print(f"lean-audit: no corpus at {corpus}", file=sys.stderr)
        return 3
    cases = sorted(corpus.glob("*.lean"))
    if not cases:
        print(f"lean-audit: corpus is empty: {corpus}", file=sys.stderr)
        return 3

    failures = 0
    for case in cases:
        expect_path = case.with_suffix(".expect.json")
        if not expect_path.exists():
            print(f"  ? {case.name}: no expectation file, skipped")
            continue
        expected = json.loads(expect_path.read_text(encoding="utf-8"))
        argv = ["audit", str(case), "--json", "-", "--quiet"]
        if expected.get("claim"):
            argv += ["--claim", str(case.with_suffix(".claim.json"))]
        code, report = _run_capture(argv)
        got_codes = {f["code"] for f in (report or {}).get("findings", [])}
        missing = [c for c in expected.get("must_flag", []) if c not in got_codes]
        forbidden = [c for c in expected.get("must_not_flag", []) if c in got_codes]
        want_verdict = expected.get("verdict")
        got_verdict = ((report or {}).get("verdict") or {}).get("overall")
        ok = not missing and not forbidden and (want_verdict is None or want_verdict == got_verdict)
        if ok:
            print(f"  ✓ {case.name}")
        else:
            failures += 1
            print(f"  ✗ {case.name}")
            if missing:
                print(f"      expected these findings, did not get them: {missing}")
            if forbidden:
                print(f"      findings that should not appear: {forbidden}")
            if want_verdict and want_verdict != got_verdict:
                print(f"      verdict: expected {want_verdict}, got {got_verdict}")
        if args.verbose and report:
            for f in report.get("findings", []):
                print(f"      - {f['severity']:<8} {f['code']}")
    print("")
    print(f"selfcheck: {len(cases) - failures}/{len(cases)} cases behaved as specified")
    return 0 if failures == 0 else 2


def _run_capture(argv: list[str]) -> tuple[int, dict | None]:
    import io
    from contextlib import redirect_stdout

    buffer = io.StringIO()
    with redirect_stdout(buffer):
        code = main(argv)
    text = buffer.getvalue()
    try:
        return code, json.loads(text) if text.strip().startswith("{") else None
    except json.JSONDecodeError:
        return code, None


if __name__ == "__main__":
    sys.exit(main())
