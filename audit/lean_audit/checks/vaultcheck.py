"""`vault`: is the environment that produced this verdict the one it claims?

An audit is only reproducible if the environment is pinned. When the audit runs
against a vault, this check compares what the vault declares with what was
actually found at runtime, and reports any disagreement as a reproducibility
finding rather than letting the report quietly imply provenance it does not have.
"""

from __future__ import annotations

from ..model import (
    Category,
    CheckResult,
    Confidence,
    Evidence,
    Finding,
    Severity,
    Verdict,
    now_ms,
)
from ..vault import version_matches
from . import AuditContext


def run(ctx: AuditContext) -> CheckResult:
    started = now_ms()
    vault = getattr(ctx, "vault", None)
    if vault is None:
        return CheckResult(
            name="vault",
            verdict=Verdict.SKIPPED,
            summary="no vault supplied; the environment is whatever this machine has",
            skip_reason="no --vault",
            duration_ms=now_ms() - started,
        )

    findings: list[Finding] = []
    discovered = ctx.toolchain.version
    matches = version_matches(vault.lean_version, discovered)

    if matches is False:
        findings.append(
            Finding(
                check="vault",
                code="vault_lean_version_mismatch",
                severity=Severity.HIGH,
                category=Category.REPRODUCIBILITY,
                confidence=Confidence.PROVEN,
                title="The Lean version in use is not the version the vault declares",
                detail=(
                    f"The vault declares `{vault.lean_version}`; this run used `{discovered}`. "
                    "Statement elaboration and axiom output can differ between Lean versions, so "
                    "this report is not byte-reproducible against the vault's published result. "
                    "It is still a real audit of the code, but it is not the audit the vault's "
                    "pinned environment would produce."
                ),
                evidence=[
                    Evidence(kind="provenance", summary=f"declared: {vault.lean_version}"),
                    Evidence(kind="provenance", summary=f"discovered: {discovered}"),
                ],
            )
        )
    elif matches is None:
        findings.append(
            Finding(
                check="vault",
                code="vault_lean_version_unknown",
                severity=Severity.MEDIUM,
                category=Category.REPRODUCIBILITY,
                confidence=Confidence.PROVEN,
                title="Could not compare the declared and discovered Lean versions",
                detail=(
                    "One side did not report a parseable version. The audit still ran, but the "
                    "environment is only partially pinned."
                ),
            )
        )

    if not vault.lean_path:
        findings.append(
            Finding(
                check="vault",
                code="vault_lean_path_unpinned",
                severity=Severity.LOW,
                category=Category.REPRODUCIBILITY,
                confidence=Confidence.PROVEN,
                title="The vault does not pin an absolute path to its Lean executable",
                detail=(
                    "Without a pinned path, a different Lean on PATH silently changes the "
                    "environment between runs. `elan` provides one for free; a manifest that omits "
                    "it makes the report harder to reproduce on another machine."
                ),
                remediation="Set `lean.path` in vault.manifest.json to the output of `which lean`.",
            )
        )

    if not vault.commit:
        findings.append(
            Finding(
                check="vault",
                code="vault_commit_unrecorded",
                severity=Severity.LOW,
                category=Category.REPRODUCIBILITY,
                confidence=Confidence.PROVEN,
                title="The vault does not record its own commit",
                detail=(
                    "Recording the vault commit ties a report to an exact state of the corpus and "
                    "toolchain. Without it, 'the vault at the time' is not a reproducible reference."
                ),
                remediation="Add `commit: $(git rev-parse HEAD)` to vault.manifest.json.",
            )
        )

    high = [f for f in findings if f.severity.rank >= Severity.HIGH.rank]
    verdict = Verdict.FAIL if high else (Verdict.WARN if findings else Verdict.PASS)
    summary = (
        "environment matches the vault manifest"
        if not findings
        else f"{len(findings)} provenance issue(s) between the vault manifest and this run"
    )
    return CheckResult(
        name="vault",
        verdict=verdict,
        summary=summary,
        findings=findings,
        duration_ms=now_ms() - started,
        data={
            "vault": vault.identity(),
            "discovered_lean_version": discovered,
            "version_matches": matches,
        },
    )
