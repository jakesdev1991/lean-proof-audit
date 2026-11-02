"""`build`: does Lean's kernel accept this file, and does it accept it cleanly?

This is the only check whose failure is unambiguously fatal: if the file does not
compile, nothing else in the audit can be trusted, and every later check reports
`inconclusive` rather than inventing a result.
"""

from __future__ import annotations

import re

from ..model import (
    Category,
    CheckResult,
    Confidence,
    Finding,
    Severity,
    Verdict,
    now_ms,
)
from . import AuditContext

# Diagnostics that mean "the auditor's environment is incomplete", not
# "the client's proof is wrong". Conflating these would be the single most
# damaging mistake this tool could make, so they are separated explicitly.
ENVIRONMENT_ERROR_PATTERNS = (
    r"unknown module prefix",
    r"object file .* does not exist",
    r"failed to open file '.*\.olean'",
    r"could not resolve import",
    r"unknown package",
)

SORRY_PATTERNS = (
    r"declaration uses 'sorry'",
    r"declaration uses 'admit'",
    r"uses 'sorry'",
)


def run(ctx: AuditContext) -> CheckResult:
    started = now_ms()
    run_result = ctx.runner.compile_in_place(str(ctx.target))
    ctx.cache["build"] = run_result
    findings: list[Finding] = []
    diags = run_result.diagnostics()

    if run_result.timed_out:
        return CheckResult(
            name="build",
            verdict=Verdict.INCONCLUSIVE,
            summary=f"compilation exceeded the {ctx.config.timeout:g}s timeout",
            duration_ms=now_ms() - started,
            skip_reason="timeout",
            findings=[
                Finding(
                    check="build",
                    code="build_timeout",
                    severity=Severity.MEDIUM,
                    category=Category.REPRODUCIBILITY,
                    confidence=Confidence.PROVEN,
                    title="Compilation timed out",
                    detail=(
                        "The audit could not finish compiling this file within the configured "
                        "timeout. No soundness conclusion can be drawn. Re-run with a larger "
                        "`--timeout`, or the file may loop nonterminating at elaboration time."
                    ),
                    remediation="Re-run with `--timeout 1800`.",
                    evidence=[run_result.evidence("timed out compilation")],
                )
            ],
        )

    env_errors = []
    errors = []
    for d in diags:
        if d.is_error:
            if any(re.search(p, d.full_message) for p in ENVIRONMENT_ERROR_PATTERNS):
                env_errors.append(d)
            else:
                errors.append(d)

    for d in errors:
        findings.append(
            Finding(
                check="build",
                code="build_error",
                severity=Severity.CRITICAL,
                category=Category.SOUNDNESS,
                confidence=Confidence.PROVEN,
                title="Kernel rejects the file",
                detail=(
                    "Lean reported an error, so there is no accepted proof term for at least one "
                    "declaration in this file. Everything downstream of that declaration is "
                    "unverified. Exact compiler output is attached."
                ),
                location=d.span(),
                evidence=[
                    _diag_evidence(run_result, d),
                ],
            )
        )

    for d in env_errors:
        findings.append(
            Finding(
                check="build",
                code="build_environment_incomplete",
                severity=Severity.HIGH,
                category=Category.REPRODUCIBILITY,
                confidence=Confidence.PROVEN,
                title="Dependencies are not built in the audit environment",
                detail=(
                    "Lean could not load an imported module. This is a property of the "
                    "environment the audit ran in, not a defect in the code under audit — but it "
                    "does mean the code has not been checked. Build the project first "
                    "(`lake build`) and re-run."
                ),
                location=d.span(),
                remediation="Run `lake build` in the project, then re-run the audit.",
                evidence=[_diag_evidence(run_result, d)],
            )
        )

    for d in diags:
        if d.is_error:
            continue
        msg = d.full_message
        if any(re.search(p, msg) for p in SORRY_PATTERNS):
            findings.append(
                Finding(
                    check="build",
                    code="placeholder_proof",
                    severity=Severity.CRITICAL,
                    category=Category.SOUNDNESS,
                    confidence=Confidence.PROVEN,
                    title="Declaration is closed by `sorry`/`admit`",
                    detail=(
                        "Lean compiled the declaration only because the goal was discharged with "
                        "`sorryAx`. The declaration is therefore *not proved*, regardless of the "
                        "file compiling without errors. Note that `sorry` is only a warning by "
                        "default; a green build is not evidence of completeness."
                    ),
                    location=d.span(),
                    remediation="Replace the placeholder with a real proof, or mark the declaration as a conjecture.",
                    evidence=[_diag_evidence(run_result, d)],
                )
            )
            continue
        if d.severity == "warning":
            findings.append(
                Finding(
                    check="build",
                    code="build_warning",
                    severity=Severity.LOW,
                    category=Category.REPRODUCIBILITY,
                    confidence=Confidence.PROVEN,
                    title="Compiler warning",
                    detail=(
                        "Not a soundness defect, but warnings often indicate a statement that does "
                        "not mean what it appears to: unused hypotheses, deprecated lemmas, or "
                        "declarations whose type changed. Listed so the client sees them."
                    ),
                    location=d.span(),
                    evidence=[_diag_evidence(run_result, d)],
                )
            )

    if run_result.exit_code == 0 and not errors:
        verdict = Verdict.WARN if any(f.severity.rank >= Severity.LOW.rank for f in findings) else Verdict.PASS
        if any(f.severity is Severity.CRITICAL for f in findings):
            verdict = Verdict.FAIL
        summary = "compiles clean" if verdict is Verdict.PASS else "compiles with findings"
    elif errors:
        verdict = Verdict.FAIL
        summary = f"{len(errors)} error(s) — file does not compile"
    else:
        verdict = Verdict.INCONCLUSIVE
        summary = "compilation status could not be established"

    return CheckResult(
        name="build",
        verdict=verdict,
        summary=summary,
        findings=findings,
        duration_ms=now_ms() - started,
        data={
            "exit_code": run_result.exit_code,
            "error_count": len(errors),
            "environment_error_count": len(env_errors),
            "warning_count": sum(1 for d in diags if d.severity == "warning"),
            "command": run_result.command,
            "duration_ms": run_result.duration_ms,
        },
    )


def _diag_evidence(run_result, diag) -> "object":
    from ..model import Evidence

    return Evidence(
        kind="lean_run",
        summary=f"{diag.severity}: {diag.message[:120]}",
        command=run_result.command,
        stdout=run_result.stdout,
        stderr=run_result.stderr,
        exit_code=run_result.exit_code,
        exit_status="ok" if run_result.ok else "error",
        duration_ms=run_result.duration_ms,
        location=diag.span(),
        input_text=None,
    )
