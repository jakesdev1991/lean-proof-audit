"""`dependence`: does the proof actually use the statement it claims to prove?

Static statement analysis can only say "this hypothesis looks unused". This
check settles it empirically, using the oldest technique for measuring whether a
proof depends on something: delete it and see whether the proof still compiles.

Two mutations are applied to each theorem's *statement* (the proof is never
edited):

  drop_hypothesis   delete one hypothesis from the statement.
                    * compiles  -> the proof term never references it (inert)
                    * fails     -> the proof genuinely uses it
  conclusion_true   replace the conclusion with `True`.
                    * compiles  -> the proof is goal-agnostic automation, so
                                   dependence evidence for this theorem is weak
                    * fails     -> the proof is specific to the stated conclusion

Interpretation rules that this module deliberately does NOT make:

  * A surviving mutation is never reported as "the theorem is false". A theorem
    whose proof ignores a hypothesis is still true; what is established is that
    the hypothesis does not constrain the proof.
  * A killed mutation is never reported as "proved". Compilation is not
    soundness; the `trust` check is what queries the axiom set.

Every mutant is re-parsed before it is compiled, and a mutant whose parse does
not match the intended edit exactly is discarded as `invalid` rather than being
counted as evidence.
"""

from __future__ import annotations

from dataclasses import dataclass

from .. import stmtparse
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

SURVIVED = "survived"
KILLED = "killed"
INCONCLUSIVE = "inconclusive"
INVALID = "invalid"
SKIPPED = "skipped"


@dataclass
class Mutant:
    decl: str
    kind: str           # drop_hypothesis | conclusion_true
    target: str         # hypothesis name, or "conclusion"
    mutated_type: str
    source: str
    status: str = SKIPPED
    detail: str = ""
    evidence: Evidence | None = None
    failed_lines: list[int] | None = None


def run(ctx: AuditContext) -> CheckResult:
    started = now_ms()
    build = ctx.cache.get("build")
    if build is None or not build.ok:
        return CheckResult(
            name="dependence",
            verdict=Verdict.INCONCLUSIVE,
            summary="skipped: the file must compile before mutations can be tested",
            skip_reason="build failed",
            duration_ms=now_ms() - started,
        )

    budget = ctx.config.max_mutants
    findings: list[Finding] = []
    mutants: list[Mutant] = []
    dependence_map: dict[str, dict] = {}

    for decl in ctx.theorems:
        if not decl.name or "private" in decl.modifiers:
            continue
        stmt, notes = _statement_source(ctx, decl)
        if stmt is None or notes:
            dependence_map[decl.qualified_name or decl.name] = {
                "status": "statement_not_parsed",
                "notes": notes,
            }
            continue

        candidates = _generate_mutants(ctx, decl, budget - len(mutants))
        mutants.extend(candidates)
        if len(mutants) >= budget:
            break

    for mutant in mutants:
        _run_mutant(ctx, mutant)

    dependence_map.update(_summarise(ctx, mutants, findings))

    invalid = [m for m in mutants if m.status == INVALID]
    if invalid:
        ctx.notes.append(
            f"dependence: {len(invalid)} mutation(s) were discarded because the mutated "
            "statement did not re-parse to the intended edit"
        )

    if any(f.severity.rank >= Severity.HIGH.rank for f in findings):
        verdict = Verdict.FAIL
    elif findings:
        verdict = Verdict.WARN
    elif mutants:
        verdict = Verdict.PASS
    else:
        verdict = Verdict.INCONCLUSIVE
    summary = (
        f"{sum(1 for m in mutants if m.status == KILLED)} killed / "
        f"{sum(1 for m in mutants if m.status == SURVIVED)} survived of {len(mutants)} mutants"
    )
    if not mutants:
        summary = "no statements could be mutated"

    return CheckResult(
        name="dependence",
        verdict=verdict,
        summary=summary,
        findings=findings,
        duration_ms=now_ms() - started,
        data={
            "dependence": dependence_map,
            "mutants": [
                {
                    "declaration": m.decl,
                    "kind": m.kind,
                    "target": m.target,
                    "status": m.status,
                    "detail": m.detail,
                    "mutated_type": " ".join(m.mutated_type.split()),
                }
                for m in mutants
            ],
            "budget": budget,
        },
    )


# ---------------------------------------------------------------------------
# Statement source model
#
# Lean splits a statement across the `:`: `theorem foo (n : Nat) (h : P) : Q`.
# The two halves are edited separately, because rewriting the whole statement as
# `(n : Nat) → (h : P) → Q` after the declaration name is not valid syntax.
# ---------------------------------------------------------------------------
@dataclass
class StatementSource:
    decl: object
    binders_text: str
    type_text: str
    binders_span: tuple[int, int]
    type_span: tuple[int, int]
    pre_binders: list
    inner: stmtparse.ParsedStatement

    def rebuild(self, source: str, new_binders: str | None = None, new_type: str | None = None) -> str:
        b = self.binders_text if new_binders is None else new_binders
        t = self.type_text if new_type is None else new_type
        return (
            source[: self.binders_span[0]]
            + b
            + source[self.binders_span[1] : self.type_span[0]]
            + t
            + source[self.type_span[1] :]
        )


def _statement_source(ctx: AuditContext, decl) -> tuple[StatementSource | None, list[str]]:
    notes: list[str] = []
    parts = decl.statement_parts(ctx.source)
    if parts is None:
        return None, ["declaration has no type span (no `:` and `:=` found)"]
    binders_span, type_span = parts
    binders_text = ctx.source[binders_span[0] : binders_span[1]]
    type_text = ctx.source[type_span[0] : type_span[1]]
    pre_binders, notes = stmtparse.parse_binders_segment(binders_text, binders_span[0])
    inner = stmtparse.parse_telescope(type_text)
    notes = notes + inner.notes
    return (
        StatementSource(
            decl=decl,
            binders_text=binders_text,
            type_text=type_text,
            binders_span=binders_span,
            type_span=type_span,
            pre_binders=pre_binders,
            inner=inner,
        ),
        notes,
    )


def _generate_mutants(ctx: AuditContext, decl, remaining: int) -> list[Mutant]:
    out: list[Mutant] = []
    if remaining <= 0:
        return out
    name = decl.qualified_name or decl.name or "?"
    stmt, notes = _statement_source(ctx, decl)
    if stmt is None:
        return out

    total_pre = len(stmt.pre_binders)
    total_inner = len(stmt.inner.binders)

    for binder in stmt.pre_binders:
        if len(out) >= remaining:
            break
        rel_start = binder.span[0] - stmt.binders_span[0]
        rel_end = binder.span[1] - stmt.binders_span[0]
        new_binders = stmt.binders_text[:rel_start] + stmt.binders_text[rel_end:]
        reparse, reparse_notes = stmtparse.parse_binders_segment(new_binders, 0)
        if reparse_notes or len(reparse) != total_pre - 1:
            out.append(
                Mutant(
                    decl=name,
                    kind="drop_hypothesis",
                    target=binder.name or "anonymous",
                    mutated_type="",
                    source="",
                    status=INVALID,
                    detail="mutated telescope did not re-parse to one fewer binder",
                )
            )
            continue
        out.append(
            Mutant(
                decl=name,
                kind="drop_hypothesis",
                target=binder.name or "anonymous",
                mutated_type=" ".join(new_binders.split()) + " : " + " ".join(stmt.type_text.split()),
                source=stmt.rebuild(ctx.source, new_binders=new_binders),
            )
        )

    for binder in stmt.inner.binders:
        if len(out) >= remaining:
            break
        if binder.span is None or binder.kind == "instance":
            continue
        new_type = _drop_binder(stmt.type_text, binder.span, binder.kind)
        if new_type is None:
            out.append(
                Mutant(
                    decl=name,
                    kind="drop_hypothesis",
                    target=binder.name or "anonymous",
                    mutated_type="",
                    source="",
                    status=INVALID,
                    detail="could not remove this binder without breaking the syntax",
                )
            )
            continue
        check = stmtparse.parse_telescope(new_type)
        if not check.parse_ok or len(check.binders) != total_inner - 1:
            out.append(
                Mutant(
                    decl=name,
                    kind="drop_hypothesis",
                    target=binder.name or "anonymous",
                    mutated_type=new_type,
                    source="",
                    status=INVALID,
                    detail="mutated statement did not re-parse to a telescope with one fewer binder",
                )
            )
            continue
        out.append(
            Mutant(
                decl=name,
                kind="drop_hypothesis",
                target=binder.name or "anonymous",
                mutated_type=new_type,
                source=stmt.rebuild(ctx.source, new_type=new_type),
            )
        )

    if len(out) < remaining and stmt.inner.conclusion_span is not None and stmt.inner.conclusion:
        new_type = _replace_conclusion(stmt.type_text, stmt.inner.conclusion_span, "True")
        check = stmtparse.parse_telescope(new_type)
        if check.parse_ok and len(check.binders) == total_inner and check.conclusion.strip() == "True":
            out.append(
                Mutant(
                    decl=name,
                    kind="conclusion_true",
                    target="conclusion",
                    mutated_type=new_type,
                    source=stmt.rebuild(ctx.source, new_type=new_type),
                )
            )
    return out


def _drop_binder(type_text: str, span: tuple[int, int], kind: str) -> str | None:
    """Remove one binder from a type, keeping the result syntactically valid.

    Returns None when no safe edit exists. Every returned string is re-parsed by
    the caller before it is compiled, so a bad edit becomes an `invalid` mutant
    rather than a false finding.
    """
    start, end = span
    after = type_text[end:]
    stripped_after = after.lstrip()
    before = type_text[:start]

    if stripped_after.startswith("→"):
        return (before + stripped_after[1:]).strip()
    if stripped_after.startswith("->"):
        return (before + stripped_after[2:]).strip()
    if stripped_after.startswith(","):
        # Last binder of a `∀`/`∃` list: the comma closes the list.
        prefix = before.rstrip()
        rest = stripped_after[1:].lstrip()
        if not rest:
            return None
        if prefix.endswith(("∀", "forall")):
            # This was the only binder: drop the quantifier with it.
            return rest
        if prefix.endswith((")", "}", "]", "⦄")):
            # Other binders remain; the comma must stay to close the list.
            return f"{prefix}, {rest}".strip()
        return None
    if stripped_after.startswith(("(", "{", "[")):
        # Another binder group follows: this one is in the middle of a list.
        return (before + stripped_after).strip()
    return None


def _replace_conclusion(type_text: str, span: tuple[int, int], new: str) -> str:
    start, end = span
    return f"{type_text[:start]}{new}{type_text[end:]}".strip()


def _run_mutant(ctx: AuditContext, mutant: Mutant) -> None:
    if mutant.status == INVALID:
        return
    run_result = ctx.runner.run_source(mutant.source, name=f"Mutant_{abs(hash((mutant.decl, mutant.kind, mutant.target))) % 10**8}.lean")
    mutant.evidence = run_result.evidence(
        f"mutant {mutant.kind} on {mutant.decl} ({mutant.target})"
    )

    if run_result.timed_out:
        mutant.status = INCONCLUSIVE
        mutant.detail = "mutant compilation timed out"
        return

    errors = run_result.errors
    if run_result.exit_code == 0 and not errors:
        mutant.status = SURVIVED
        mutant.detail = "compiled unchanged with the mutated statement"
        return

    # Attribute failures to the mutated declaration. An error elsewhere in the
    # file means the mutant told us nothing about this theorem.
    target_lines = _decl_line_range(ctx, mutant.decl)
    attributed = [
        d
        for d in errors
        if d.line is not None and target_lines[0] <= d.line <= target_lines[1]
    ]
    if attributed:
        mutant.status = KILLED
        mutant.detail = attributed[0].full_message.splitlines()[0][:300]
        mutant.failed_lines = [d.line for d in attributed if d.line]
        return

    mutant.status = INCONCLUSIVE
    mutant.detail = (
        "compilation failed, but not inside the mutated declaration: "
        + (errors[0].full_message.splitlines()[0][:200] if errors else "no diagnostic could be attributed")
    )


def _decl_line_range(ctx: AuditContext, decl_name: str) -> tuple[int, int]:
    for decl in ctx.index.decls:
        if (decl.qualified_name or decl.name) == decl_name:
            start = ctx.index.line_of(decl.start)
            end = ctx.index.line_of(max(decl.start, decl.end - 1))
            # Mutants replace the type, which shifts the proof down by one line at
            # most; widen the window to keep attribution stable.
            return (start, end + 2)
    return (1, 10**6)


def _summarise(ctx, mutants: list[Mutant], findings: list[Finding]) -> dict[str, dict]:
    per_decl: dict[str, dict] = {}
    for mutant in mutants:
        entry = per_decl.setdefault(
            mutant.decl,
            {"hypotheses": {}, "conclusion_sensitivity": "unknown", "evidence_strength": "unknown"},
        )
        if mutant.kind == "drop_hypothesis":
            entry["hypotheses"][mutant.target] = {
                "drop_hypothesis": mutant.status,
                "meaning": _hypothesis_meaning(mutant.status),
            }
        elif mutant.kind == "conclusion_true":
            if mutant.status == KILLED:
                entry["conclusion_sensitivity"] = "specific"
                entry["evidence_strength"] = "strong"
            elif mutant.status == SURVIVED:
                entry["conclusion_sensitivity"] = "agnostic"
                entry["evidence_strength"] = "weak"

    for decl_name, entry in per_decl.items():
        for hyp, result in entry["hypotheses"].items():
            if result["drop_hypothesis"] == SURVIVED:
                findings.append(
                    Finding(
                        check="dependence",
                        code="inert_hypothesis",
                        severity=Severity.MEDIUM,
                        category=Category.DEPENDENCE,
                        confidence=Confidence.HEURISTIC_CONFIRMED,
                        title=f"`{decl_name}` does not use its hypothesis `{hyp}`",
                        detail=(
                            "The hypothesis was deleted from the statement, the proof was left "
                            "untouched, and Lean still accepted the declaration. The proof term "
                            "therefore does not depend on it. The theorem remains true, but it is "
                            "weaker than it looks: a reader will assume that hypothesis is doing "
                            "work. Either drop it, or the conclusion is meant to be stronger."
                        ),
                        declaration=decl_name,
                        remediation="Remove the unused hypothesis, or strengthen the conclusion so the hypothesis is needed.",
                        evidence=[_mutant_evidence(h) for h in mutants if h.decl == decl_name and h.target == hyp],
                    )
                )
        if entry["conclusion_sensitivity"] == "agnostic":
            findings.append(
                Finding(
                    check="dependence",
                    code="goal_agnostic_proof",
                    severity=Severity.MEDIUM,
                    category=Category.DEPENDENCE,
                    confidence=Confidence.HEURISTIC_CONFIRMED,
                    title=f"`{decl_name}` compiles even when its conclusion is replaced by `True`",
                    detail=(
                        "The proof closes the goal regardless of what the goal is, which is what "
                        "automation-driven proofs (`simp`, `trivial`, `decide`-style) do. This does "
                        "not make the theorem false. It does mean that for this declaration the "
                        "proof carries no information about the conclusion, so the statement is "
                        "doing all the work and deserves the closest reading."
                    ),
                    declaration=decl_name,
                    evidence=[
                        _mutant_evidence(h)
                        for h in mutants
                        if h.decl == decl_name and h.kind == "conclusion_true"
                    ],
                )
            )
    return per_decl


def _hypothesis_meaning(status: str) -> str:
    return {
        KILLED: "the proof depends on this hypothesis",
        SURVIVED: "the proof does not depend on this hypothesis",
        INCONCLUSIVE: "dependence could not be established",
        INVALID: "mutation could not be constructed safely",
        SKIPPED: "not tested",
    }.get(status, "unknown")


def _mutant_evidence(mutant: Mutant) -> Evidence:
    if mutant.evidence is not None:
        ev = mutant.evidence
        ev.summary = f"{mutant.kind} -> {mutant.status}: {mutant.detail}"
        return ev
    return Evidence(kind="probe", summary=f"{mutant.kind} -> {mutant.status}: {mutant.detail}")
