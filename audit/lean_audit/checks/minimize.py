"""`minimize`: when the file does not compile, find the smallest thing that fails.

A raw Lean error in a 900-line file is not an audit finding; it is a starting
point. This check removes declarations one at a time, recompiling after each
removal, and keeps a removal only when the *same* diagnostic still appears. The
result is a fragment the client can paste into a scratch file, plus a
classification of what kind of failure it is — which is what determines the fix.
"""

from __future__ import annotations

import re

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
from . import AuditContext

MAX_RUNS = 30

FAILURE_KINDS = (
    (r"unknown identifier|unknown constant|unknown namespace", "unknown identifier", "a name is misspelled, not imported, or shadowed"),
    (r"unknown module|object file .* does not exist", "missing dependency", "the imported module is not built in this environment"),
    (r"type mismatch|application type mismatch|has type|but is expected to have type", "type mismatch", "a term's type does not match what the declaration requires"),
    (r"failed to synthesize", "missing instance", "no instance of the required typeclass is in scope"),
    (r"unresolved goals|unsolved goals", "unsolved goals", "the tactic proof did not close the goal"),
    (r"unsolved goals|tactic .* failed|`simp` made no progress", "tactic failure", "a tactic could not apply to the goal"),
    (r"maximum recursion depth|deep recursion", "elaboration depth", "the expression is too deeply nested to elaborate"),
    (r"deterministic timeout|heartbeats exceeded|maximum heartbeats", "timeout", "elaboration exceeded the heartbeat budget"),
    (r"fail to show termination|termination", "termination", "recursion could not be shown terminating"),
    (r"declaration uses 'sorry'", "placeholder", "a goal was closed with `sorry`"),
)


def run(ctx: AuditContext) -> CheckResult:
    started = now_ms()
    build = ctx.cache.get("build")
    if build is None:
        return CheckResult(
            name="minimize",
            verdict=Verdict.INCONCLUSIVE,
            summary="skipped: no build result available",
            skip_reason="build did not run",
            duration_ms=now_ms() - started,
        )
    if build.ok and not build.errors:
        return CheckResult(
            name="minimize",
            verdict=Verdict.SKIPPED,
            summary="nothing to minimize: the file compiles",
            skip_reason="no errors",
            duration_ms=now_ms() - started,
        )

    errors = build.errors
    if not errors:
        return CheckResult(
            name="minimize",
            verdict=Verdict.INCONCLUSIVE,
            summary="the build failed without an attributable diagnostic",
            skip_reason="no diagnostic",
            duration_ms=now_ms() - started,
        )

    target = errors[0]
    signature = target.signature()
    kind, explanation = _classify(target.full_message)
    evidence: list[Evidence] = []

    decls = ctx.index.decls
    if len(decls) < 2:
        return CheckResult(
            name="minimize",
            verdict=Verdict.WARN,
            summary=f"{kind}: {explanation}",
            findings=[_finding(target, kind, explanation, ctx, evidence, kept=None)],
            duration_ms=now_ms() - started,
            data={"error_signature": signature, "kept_declarations": []},
        )

    kept = list(decls)
    removed: list[str] = []
    runs = 0
    current_source = ctx.source
    while runs < MAX_RUNS and len(kept) > 1:
        progressed = False
        for decl in list(kept):
            if runs >= MAX_RUNS or len(kept) <= 1:
                break
            candidate_decls = [d for d in kept if d is not decl]
            candidate_source = _remove_decls(ctx.source, kept, candidate_decls)
            run_result = ctx.runner.run_source(candidate_source, name="Minimize.lean")
            runs += 1
            still_failing = any(d.signature() == signature for d in run_result.errors)
            if still_failing:
                kept = candidate_decls
                removed.append(decl.qualified_name or decl.name or decl.kw)
                current_source = candidate_source
                progressed = True
        if not progressed:
            break

    minimal_run = ctx.runner.run_source(current_source, name="MinimalFragment.lean")
    runs += 1
    evidence.append(
        minimal_run.evidence(
            f"minimal fragment reproducing the error after {len(removed)} declaration removal(s)"
        )
    )

    kind, explanation = _classify(target.full_message)
    data = {
        "error_signature": signature,
        "error_kind": kind,
        "kept_declarations": [d.qualified_name or d.name or d.kw for d in kept],
        "removed_declarations": removed,
        "runs": runs,
        "minimal_source": current_source,
    }
    return CheckResult(
        name="minimize",
        verdict=Verdict.WARN,
        summary=(
            f"{kind}: {explanation}"
            + (f" (reduced to {len(kept)} declaration(s))" if removed else "")
        ),
        findings=[_finding(target, kind, explanation, ctx, evidence, kept=kept)],
        duration_ms=now_ms() - started,
        data=data,
    )


def _finding(target, kind, explanation, ctx, evidence, kept) -> Finding:
    detail = (
        f"First failing diagnostic, classified as **{kind}**: {explanation}.\n\n"
        f"Lean said:\n\n    {target.full_message.splitlines()[0][:400]}"
    )
    if kept is not None:
        detail += (
            f"\n\nThe file was reduced to {len(kept)} declaration(s) while reproducing the same "
            "diagnostic; that fragment is attached as the minimal reproducing case."
        )
    return Finding(
        check="minimize",
        code=f"failure_{kind.replace(' ', '_')}",
        severity=Severity.HIGH if kind not in ("placeholder",) else Severity.CRITICAL,
        category=Category.SOUNDNESS,
        confidence=Confidence.PROVEN,
        title=f"Failure classified as: {kind}",
        detail=detail,
        location=target.span(),
        evidence=evidence,
    )


def _classify(message: str) -> tuple[str, str]:
    for pattern, kind, explanation in FAILURE_KINDS:
        if re.search(pattern, message):
            return kind, explanation
    return "other", "the diagnostic did not match a known failure class; read it verbatim"


def _remove_decls(original: str, kept: list, candidate: list) -> str:
    """Blank out the declarations that are not in `candidate`."""
    removed_spans = [d for d in kept if d not in candidate]
    text = original
    for decl in sorted(removed_spans, key=lambda d: d.start, reverse=True):
        text = text[: decl.start] + _blank(original[decl.start : decl.end]) + text[decl.end :]
    return text


def _blank(segment: str) -> str:
    return "".join("\n" if ch == "\n" else " " for ch in segment)
