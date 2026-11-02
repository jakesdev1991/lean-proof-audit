"""`claim`: does the formal statement match the claim the client says it proved?

This is the most expensive bug in formalisation, and the one no kernel can catch:
a correct proof of the wrong statement. The check is deliberately *structural*
rather than an LLM opinion:

  * the claim is supplied as data (JSON), not prose, so both sides are explicit;
  * the formal side is the kernel's own `pp.all` elaboration;
  * the comparison reports quantifier count, dropped hypotheses, added
    hypotheses, and conclusion agreement, each as a separate finding.

A prose-only claim cannot be verified structurally, and this check says so
instead of pretending otherwise.
"""

from __future__ import annotations

import json
from pathlib import Path

from .. import expr
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


def run(ctx: AuditContext) -> CheckResult:
    started = now_ms()
    if not ctx.config.claim_path:
        return CheckResult(
            name="claim",
            verdict=Verdict.SKIPPED,
            summary="no claim supplied — correspondence to the intended claim is unverified",
            skip_reason="no --claim file",
            duration_ms=now_ms() - started,
            data={
                "note": (
                    "The formal statement can be vacuous or can differ from the intended claim "
                    "without this being detectable from the code alone. Supply a claim file to "
                    "check the quantifier and hypothesis structure against it."
                )
            },
        )

    path = Path(ctx.config.claim_path)
    try:
        claim = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return CheckResult(
            name="claim",
            verdict=Verdict.INCONCLUSIVE,
            summary=f"claim file could not be read: {exc}",
            skip_reason=str(exc),
            duration_ms=now_ms() - started,
        )

    profiles = ctx.cache.get("statement_profiles") or {}
    decl_name = claim.get("declaration")
    if not decl_name:
        return CheckResult(
            name="claim",
            verdict=Verdict.INCONCLUSIVE,
            summary="claim file does not name a declaration",
            skip_reason="missing `declaration` key",
            duration_ms=now_ms() - started,
        )

    formal = profiles.get(decl_name)
    if formal is None:
        matches = [k for k in profiles if k.endswith("." + decl_name) or k == decl_name]
        formal = profiles[matches[0]] if len(matches) == 1 else None
    if formal is None:
        return CheckResult(
            name="claim",
            verdict=Verdict.INCONCLUSIVE,
            summary=f"declaration `{decl_name}` was not found in the audited file",
            skip_reason="declaration not found",
            duration_ms=now_ms() - started,
            findings=[
                Finding(
                    check="claim",
                    code="claim_declaration_missing",
                    severity=Severity.HIGH,
                    category=Category.STATEMENT,
                    confidence=Confidence.PROVEN,
                    title=f"The claim names `{decl_name}`, which is not in the file",
                    detail=(
                        "A claim that does not point at a declaration in the audited file cannot be "
                        "verified. Either the name is wrong or the declaration was renamed or "
                        "removed — in which case the claim is unproven, not merely unchecked."
                    ),
                )
            ],
        )

    findings: list[Finding] = []
    profile = formal
    formal_binders = profile["binders"]
    formal_conclusion = profile["conclusion"]

    if not claim.get("conclusion") and not claim.get("hypotheses"):
        return CheckResult(
            name="claim",
            verdict=Verdict.INCONCLUSIVE,
            summary="claim contains prose only; structural comparison is not possible",
            skip_reason="prose-only claim",
            duration_ms=now_ms() - started,
            findings=[
                Finding(
                    check="claim",
                    code="claim_prose_only",
                    severity=Severity.MEDIUM,
                    category=Category.STATEMENT,
                    confidence=Confidence.PROVEN,
                    title="The claim is prose, so correspondence cannot be machine-checked",
                    detail=(
                        "Structural verification compares an explicit claim (quantifiers, "
                        "hypotheses, conclusion) against the elaborated statement. A prose claim "
                        "cannot be compared this way, and no heuristic is offered in its place. "
                        "The elaborated statement is included in the report for human review."
                    ),
                    evidence=[Evidence(kind="statement", summary=json.dumps(profile, indent=2)[:4000])],
                )
            ],
        )

    declared_quantifiers = claim.get("quantifiers") or []
    declared_hypotheses = claim.get("hypotheses") or []
    formal_explicit = [b for b in formal_binders if b["kind"] == "explicit"]
    formal_variables = [b for b in formal_binders if not _looks_like_hypothesis(b["type"])]

    # -- quantifier structure ------------------------------------------
    if declared_quantifiers and len(declared_quantifiers) != len(formal_variables):
        findings.append(
            Finding(
                check="claim",
                code="claim_quantifier_arity_mismatch",
                severity=Severity.HIGH,
                category=Category.STATEMENT,
                confidence=Confidence.PROVEN,
                title=(
                    f"The claim declares {len(declared_quantifiers)} quantifier(s); the formal "
                    f"statement binds {len(formal_variables)} variable(s)"
                ),
                detail=(
                    "The elaborated formal statement binds a different number of variables than "
                    "the claim intends. Either the claim is under-specified or the formalisation "
                    "quantifies over something the claim does not mention."
                ),
                evidence=[Evidence(kind="statement", summary=json.dumps(formal_binders, indent=2)[:3000])],
            )
        )
    for quant in declared_quantifiers:
        qname = quant.get("name")
        if qname and not any(b["name"] == qname for b in formal_binders):
            findings.append(
                Finding(
                    check="claim",
                    code="claim_quantifier_missing",
                    severity=Severity.MEDIUM,
                    category=Category.STATEMENT,
                    confidence=Confidence.HEURISTIC,
                    title=f"Quantifier `{qname}` from the claim is not a binder in the formal statement",
                    detail=(
                        "Binder names do not have to agree for a theorem to be correct, but a "
                        "mismatch usually means the structural comparison below is comparing "
                        "different things. Review the telescope side by side."
                    ),
                    evidence=[Evidence(kind="statement", summary=json.dumps(formal_binders, indent=2)[:3000])],
                )
            )

    # -- hypotheses -----------------------------------------------------
    formal_hyp_text = " || ".join(b["type"] for b in formal_binders) + " || " + formal_conclusion
    formal_all_text = formal_hyp_text
    for hypothesis in declared_hypotheses:
        if not _claim_element_present(hypothesis, formal_all_text):
            findings.append(
                Finding(
                    check="claim",
                    code="claim_hypothesis_dropped",
                    severity=Severity.CRITICAL,
                    category=Category.STATEMENT,
                    confidence=Confidence.HEURISTIC,
                    title=f"The claim assumes `{_short(hypothesis)}`, which the formal statement does not",
                    detail=(
                        "A hypothesis in the intended claim is absent from the formal statement. "
                        "The formal theorem is therefore STRONGER than intended — and if the "
                        "claim needed that hypothesis, the formal statement is likely false or "
                        "only true for a different reason. This is the exact failure mode of "
                        "\"proved the wrong thing\"."
                    ),
                    remediation="Add the missing hypothesis to the formal statement, or weaken the claim.",
                    evidence=[Evidence(kind="statement", summary=json.dumps(profile, indent=2)[:4000])],
                )
            )

    for binder in formal_explicit:
        btype = binder["type"]
        if _looks_like_hypothesis(btype) and not any(
            _claim_element_present(h, btype) for h in declared_hypotheses
        ):
            findings.append(
                Finding(
                    check="claim",
                    code="claim_extra_hypothesis",
                    severity=Severity.MEDIUM,
                    category=Category.STATEMENT,
                    confidence=Confidence.HEURISTIC,
                    title=f"The formal statement assumes `{binder['name'] or '_'} : {_short(btype)}`, which the claim does not mention",
                    detail=(
                        "The formal theorem assumes more than the claim states, so the result is "
                        "weaker than what was promised to the reader. Either the claim is missing "
                        "a hypothesis, or the formalisation is over-general."
                    ),
                    evidence=[Evidence(kind="statement", summary=f"( {binder['name']} : {btype} )")],
                )
            )

    # -- conclusion -----------------------------------------------------
    claimed_conclusion = claim.get("conclusion")
    if claimed_conclusion:
        shared = expr.local_vars(claimed_conclusion) & expr.local_vars(formal_conclusion)
        if not shared and not _claim_element_present(claimed_conclusion, formal_conclusion):
            findings.append(
                Finding(
                    check="claim",
                    code="claim_conclusion_mismatch",
                    severity=Severity.HIGH,
                    category=Category.STATEMENT,
                    confidence=Confidence.HEURISTIC,
                    title="The formal conclusion does not share any term with the claimed conclusion",
                    detail=(
                        "No identifier in common between the claim's conclusion and the elaborated "
                        "formal conclusion. That does not prove a mismatch, but it is strong "
                        "evidence the two are about different propositions. Compare them in the "
                        "report before accepting either."
                    ),
                    evidence=[
                        Evidence(kind="statement", summary=f"claimed:   {claimed_conclusion[:1000]}"),
                        Evidence(kind="statement", summary=f"formal:    {formal_conclusion[:1000]}"),
                    ],
                )
            )

    hard = [f for f in findings if f.severity.rank >= Severity.HIGH.rank]
    if hard:
        verdict = Verdict.FAIL
        summary = f"{len(hard)} structural mismatch(es) between the claim and the formal statement"
    elif findings:
        verdict = Verdict.WARN
        summary = "the claim and the formal statement differ in detail; review the side-by-side"
    else:
        verdict = Verdict.PASS
        summary = "the formal statement is structurally consistent with the supplied claim"

    return CheckResult(
        name="claim",
        verdict=verdict,
        summary=summary,
        findings=findings,
        duration_ms=now_ms() - started,
        data={
            "claim": claim,
            "declaration": decl_name,
            "formal_telescope": profile.get("telescope"),
            "formal_fingerprint": profile.get("fingerprint"),
        },
    )


def _claim_element_present(element: str, haystack: str) -> bool:
    """Is `element` structurally contained in `haystack`?

    Two tests, both required:
      * every locally-bound name of the element occurs in the haystack;
      * every *distinctive* token (a global constant such as `Even`, or an
        operator such as `≤`) also occurs there.

    The second test is the one that matters: `Even n` and `Odd n` share their
    only local variable, so a comparison based on variable names alone would
    call them equal. `Even` vs `Odd` is precisely the error this check exists to
    catch.
    """
    wanted = expr.local_vars(element)
    if wanted and not wanted <= expr.local_vars(haystack):
        return False
    distinctive = _distinctive_tokens(element)
    if distinctive:
        return distinctive <= _distinctive_tokens(haystack)
    return expr.normalize(element) in expr.normalize(haystack)


def _distinctive_tokens(text: str) -> set[str]:
    """Globals and operators: the part of a claim that carries its meaning."""
    locals_ = expr.local_vars(text)
    tokens: set[str] = set()
    for ident in expr.identifiers(text):
        if ident in locals_ or ident.startswith("_uniq."):
            continue
        tokens.add(ident.split(".")[-1] if ident[:1].islower() else ident)
    masked = expr.blank_comments_and_strings(text)
    for op in ("≤", "≥", "<", ">", "≠", "=", "∧", "∨", "¬", "∣", "∈", "→", "↔"):
        if expr.has_top_level(masked, op):
            tokens.add(op)
    return tokens


def _looks_like_hypothesis(type_text: str) -> bool:
    """A binder is treated as a hypothesis if it is a proposition."""
    return bool(
        expr.has_top_level(type_text, "=")
        or expr.has_top_level(type_text, "≤")
        or expr.has_top_level(type_text, "≥")
        or expr.has_top_level(type_text, "<")
        or expr.has_top_level(type_text, ">")
        or expr.has_top_level(type_text, "≠")
        or expr.has_top_level(type_text, "∣")
        or expr.has_top_level(type_text, "∈")
        or type_text.strip().startswith(("¬", "@Not", "Not", "∀", "∃"))
    )


def _short(text: str, limit: int = 90) -> str:
    flat = " ".join(text.split())
    return flat if len(flat) <= limit else flat[: limit - 1] + "…"
