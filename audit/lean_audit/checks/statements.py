"""`statements`: does the theorem say what the client thinks it says?

A kernel pass certifies the step from hypotheses to conclusion. It says nothing
about whether that step is interesting. The classic failures it cannot see:

  * a hypothesis that makes the statement vacuous (prove `False` from it and
    everything follows);
  * a quantifier over an empty type;
  * a conclusion that is true by reflexivity or by definition;
  * a hypothesis nothing else mentions, which makes the statement *look* like it
    assumes something it never uses;
  * notation whose meaning is resolved by an instance, so the elaborated claim
    differs from what a reader sees.

Two of these are checked the hard way: where a hypothesis is closed (mentions no
bound variables) the audit asks Lean to *prove its negation* with `decide`. If
Lean proves `¬ h`, the theorem is vacuous as stated, and that is a kernel fact
rather than a heuristic.
"""

from __future__ import annotations

import hashlib
import re

from .. import expr, stmtparse
from ..model import (
    Category,
    CheckResult,
    Confidence,
    Evidence,
    Finding,
    Severity,
    SourceSpan,
    Verdict,
    now_ms,
)
from . import AuditContext

EMPTY_TYPE_RE = re.compile(r"^(?:@?\s*)?(Empty|PEmpty|False|Fin 0|Fin\s+0)\b")
MAX_REFUTATIONS = 12


def run(ctx: AuditContext) -> CheckResult:
    started = now_ms()
    findings: list[Finding] = []
    build = ctx.cache.get("build")
    if build is None or not build.ok:
        return CheckResult(
            name="statements",
            verdict=Verdict.INCONCLUSIVE,
            summary="skipped: the file must compile before statements can be elaborated",
            skip_reason="build failed",
            duration_ms=now_ms() - started,
        )

    decls = [d for d in ctx.theorems if d.name and "private" not in d.modifiers]
    if not decls:
        return CheckResult(
            name="statements",
            verdict=Verdict.SKIPPED,
            summary="no named public theorems in this file",
            skip_reason="no declarations",
            duration_ms=now_ms() - started,
        )

    profiles, probe = _elaborate_statements(ctx, decls)
    # Cached so the `claim` check compares against exactly these elaborations.
    ctx.cache["statement_profiles"] = {k: _profile(v) for k, v in profiles.items()}
    ctx.cache["statement_probe"] = probe
    findings.extend(_auto_implicit_findings(ctx))

    refutable, refute_evidence = _refutable_hypotheses(ctx, profiles)
    data_profiles: dict[str, dict] = {}

    for decl in decls:
        parsed = profiles.get(decl.qualified_name or "")
        loc = ctx.index.span(decl.start, decl.start + 1)
        if parsed is None:
            findings.append(
                Finding(
                    check="statements",
                    code="statement_unparsed",
                    severity=Severity.MEDIUM,
                    category=Category.REPRODUCIBILITY,
                    confidence=Confidence.PROVEN,
                    title=f"Could not recover the elaborated type of `{decl.name}`",
                    detail=(
                        "`#check` produced no usable output for this declaration, so its "
                        "statement-level properties are unverified. Reported as unverified rather "
                        "than passed."
                    ),
                    declaration=decl.qualified_name,
                    location=loc,
                    evidence=[probe.evidence("pp.all statement probe")],
                )
            )
            continue

        data_profiles[decl.qualified_name or decl.name or "?"] = _profile(parsed)
        findings.extend(
            _analyze(
                ctx,
                decl,
                parsed,
                loc,
                refutable.get(decl.qualified_name or "", []),
                refute_evidence,
            )
        )

    if any(f.severity.rank >= Severity.CRITICAL.rank for f in findings):
        verdict = Verdict.FAIL
        summary = "at least one statement is vacuous or trivially true as stated"
    elif any(f.severity.rank >= Severity.HIGH.rank for f in findings):
        verdict = Verdict.FAIL
        summary = "statement-level defects found that a kernel pass cannot see"
    elif findings:
        verdict = Verdict.WARN
        summary = "statements are structurally sound; review the observations"
    else:
        verdict = Verdict.PASS
        summary = f"{len(data_profiles)} statement(s) show no vacuity or triviality"

    return CheckResult(
        name="statements",
        verdict=verdict,
        summary=summary,
        findings=findings,
        duration_ms=now_ms() - started,
        data={"statements": data_profiles, "probe_input_sha256": probe.evidence("probe").to_dict().get("input_sha256")},
    )


# ---------------------------------------------------------------------------
# pp.all probe
# ---------------------------------------------------------------------------
def _elaborate_statements(ctx: AuditContext, decls) -> tuple[dict[str, stmtparse.ParsedStatement], object]:
    inline = [f"set_option pp.all true in\n#check @{d.qualified_name}" for d in decls]
    run_inline, _ = ctx.runner.probe(ctx.source, inline, name="ProbeStatements.lean")
    profiles: dict[str, stmtparse.ParsedStatement] = {}
    for decl in decls:
        parsed = stmtparse.parse_check_output(run_inline.stdout, decl.qualified_name or "")
        if parsed is not None:
            profiles[decl.qualified_name or ""] = parsed

    if len(profiles) == len(decls):
        return profiles, run_inline

    # Fallback: some Lean versions do not accept `set_option ... in` before a
    # command. Set the option globally, after the imports (which must come first).
    forced = _with_global_pp_all(ctx.source)
    run_forced, _ = ctx.runner.probe(forced, [f"#check @{d.qualified_name}" for d in decls], name="ProbeStatementsForced.lean")
    for decl in decls:
        if decl.qualified_name in profiles:
            continue
        parsed = stmtparse.parse_check_output(run_forced.stdout, decl.qualified_name or "")
        if parsed is not None:
            profiles[decl.qualified_name or ""] = parsed
    if len(profiles) > len([d for d in decls if stmtparse.parse_check_output(run_inline.stdout, d.qualified_name or "")]):
        return profiles, run_forced
    return profiles, run_inline


def _with_global_pp_all(source: str) -> str:
    lines = source.splitlines()
    last_import = -1
    for i, line in enumerate(lines):
        if line.strip().startswith("import "):
            last_import = i
    insert_at = last_import + 1 if last_import >= 0 else 0
    return "\n".join(lines[:insert_at] + ["set_option pp.all true"] + lines[insert_at:])


# ---------------------------------------------------------------------------
# per-statement analysis
# ---------------------------------------------------------------------------
def _analyze(ctx, decl, parsed: stmtparse.ParsedStatement, loc, refuted: list[tuple[str, str]], refute_evidence=None) -> list[Finding]:
    findings: list[Finding] = []
    name = decl.qualified_name or decl.name or "<anonymous>"

    if not parsed.parse_ok:
        findings.append(
            Finding(
                check="statements",
                code="statement_parse_incomplete",
                severity=Severity.LOW,
                category=Category.REPRODUCIBILITY,
                confidence=Confidence.PROVEN,
                title=f"Telescope of `{name}` could not be fully classified",
                detail=(
                    "Part of this declaration's type used syntax this auditor does not model, so "
                    "the statement-level analysis is partial. The details are recorded; nothing "
                    "was concluded from the unparsed part."
                ),
                declaration=name,
                location=loc,
                evidence=[
                    Evidence(kind="statement", summary="; ".join(parsed.notes)[:1000]),
                    Evidence(kind="statement", summary=f"raw type: {parsed.raw[:2000]}"),
                ],
            )
        )

    # -- explicitly refuted hypotheses (kernel fact) --------------------
    for hyp_name, hyp_type in refuted:
        findings.append(
            Finding(
                check="statements",
                code="refutable_hypothesis",
                severity=Severity.CRITICAL,
                category=Category.STATEMENT,
                confidence=Confidence.PROVEN,
                title=f"`{name}` is vacuous: its hypothesis `{hyp_name}` is refutable",
                detail=(
                    f"Lean proved `¬ ({hyp_type})` by computation. A hypothesis that cannot hold "
                    "makes the theorem vacuously true: it constrains nothing, and every theorem "
                    "with that hypothesis is equally provable. This is the statement-level defect "
                    "a kernel check cannot detect."
                ),
                declaration=name,
                location=loc,
                remediation="Correct the hypothesis, or state the theorem with a satisfiable one.",
                evidence=[
                    refute_evidence.evidence(f"Lean proved ¬ ({hyp_type}) by decide")
                ]
                if refute_evidence is not None
                else [],
            )
        )

    # -- hypothesis-level ----------------------------------------------
    conclusion_vars = expr.local_vars(parsed.conclusion)
    for binder in parsed.binders:
        btype = binder.type_text
        bname = binder.name or "<anonymous hypothesis>"
        bvars = expr.local_vars(btype)
        others = set(conclusion_vars)
        for other in parsed.binders:
            if other is not binder:
                others |= expr.local_vars(other.type_text)

        if _is_false(btype):
            findings.append(
                Finding(
                    check="statements",
                    code="false_hypothesis",
                    severity=Severity.CRITICAL,
                    category=Category.STATEMENT,
                    confidence=Confidence.PROVEN,
                    title=f"`{name}` assumes `False`",
                    detail=(
                        f"The hypothesis `{bname}` has type `False`. The theorem is therefore "
                        "vacuously true and proves nothing about the conclusion."
                    ),
                    declaration=name,
                    location=loc,
                    evidence=[Evidence(kind="statement", summary=f"( {bname} : {btype} )")],
                )
            )
        elif EMPTY_TYPE_RE.match(_strip_at(btype)):
            findings.append(
                Finding(
                    check="statements",
                    code="empty_domain",
                    severity=Severity.HIGH,
                    category=Category.STATEMENT,
                    confidence=Confidence.HEURISTIC,
                    title=f"`{name}` quantifies over an empty type",
                    detail=(
                        f"`{bname} : {btype}` is an empty type, so the quantified statement has no "
                        "instances. Such a theorem is true but carries no content."
                    ),
                    declaration=name,
                    location=loc,
                    evidence=[Evidence(kind="statement", summary=f"( {bname} : {btype} )")],
                )
            )
        elif bvars and not (bvars & others):
            findings.append(
                Finding(
                    check="statements",
                    code="decorative_hypothesis",
                    severity=Severity.MEDIUM,
                    category=Category.STATEMENT,
                    confidence=Confidence.HEURISTIC,
                    title=f"`{name}` has a hypothesis nothing else mentions: `{bname}`",
                    detail=(
                        f"`{bname} : {btype}` mentions no identifier that appears in the "
                        "conclusion or in any other hypothesis. Either the statement assumes "
                        "something it never uses (which overstates what it claims to need), or "
                        "the conclusion is weaker than intended. The `dependence` check tests "
                        "this directly by deleting the hypothesis and re-running the proof."
                    ),
                    declaration=name,
                    location=loc,
                    remediation="Remove the hypothesis if it is unused, or strengthen the conclusion.",
                    evidence=[
                        Evidence(
                            kind="statement",
                            summary=(
                                f"hypothesis variables: {sorted(bvars)}; "
                                f"variables elsewhere: {sorted(others)}; intersection: empty"
                            ),
                        )
                    ],
                )
            )

    # -- conclusion-level ----------------------------------------------
    conc = parsed.conclusion
    if _is_true(conc):
        findings.append(
            Finding(
                check="statements",
                code="trivial_conclusion",
                severity=Severity.HIGH,
                category=Category.STATEMENT,
                confidence=Confidence.PROVEN,
                title=f"`{name}` concludes `True`",
                detail=(
                    "The conclusion is `True`, so the theorem is true no matter what the "
                    "hypotheses say. Be aware that its axioms can still be kernel-clean: this is "
                    "not a soundness failure, it is a statement failure."
                ),
                declaration=name,
                location=loc,
                evidence=[Evidence(kind="statement", summary=f"⊢ {conc}")],
            )
        )
    else:
        reflexive = _reflexive_pair(conc)
        if reflexive is not None:
            findings.append(
                Finding(
                    check="statements",
                    code="reflexive_conclusion",
                    severity=Severity.HIGH,
                    category=Category.STATEMENT,
                    confidence=Confidence.HEURISTIC,
                    title=f"`{name}` concludes an identity: `{reflexive}`",
                    detail=(
                        "Both sides of the conclusion are the same expression, so the statement "
                        "holds by `rfl` and carries no mathematical content. Usually a sign that a "
                        "definition was meant to differ between the two sides."
                    ),
                    declaration=name,
                    location=loc,
                    evidence=[Evidence(kind="statement", summary=f"⊢ {conc}")],
                )
            )
        for note in expr.notation_notes(conc):
            findings.append(
                Finding(
                    check="statements",
                    code="elaborated_core",
                    severity=Severity.INFO,
                    category=Category.STATEMENT,
                    confidence=Confidence.PROVEN,
                    title=f"`{name}`: `{note.symbol}` is {note.meaning}",
                    detail=(
                        "Shown so the elaborated claim can be compared against the intended one. "
                        "`pp.all` output is what the kernel sees; the surface syntax is not."
                    ),
                    declaration=name,
                    location=loc,
                    evidence=[Evidence(kind="statement", summary=f"⊢ {conc[:1500]}")],
                )
            )

    if not parsed.binders and not _is_true(conc):
        findings.append(
            Finding(
                check="statements",
                code="closed_statement",
                severity=Severity.INFO,
                category=Category.STATEMENT,
                confidence=Confidence.PROVEN,
                title=f"`{name}` is a closed proposition (no parameters)",
                detail=(
                    "The statement has no hypotheses or quantifiers. That is fine for a concrete "
                    "computed fact, and worth a second look if it was meant to be a general theorem."
                ),
                declaration=name,
                location=loc,
            )
        )
    return findings


def _auto_implicit_findings(ctx: AuditContext) -> list[Finding]:
    setting = ctx.index.set_option("autoImplicit")
    relaxed = ctx.index.set_option("relaxedAutoImplicit")
    if relaxed is not None:
        return [
            Finding(
                check="statements",
                code="relaxed_auto_implicit",
                severity=Severity.HIGH,
                category=Category.STATEMENT,
                confidence=Confidence.PROVEN,
                title="`relaxedAutoImplicit` is enabled",
                detail=(
                    "With autoImplicit, any identifier a declaration mentions but never binds is "
                    "silently turned into an implicitly universally quantified hypothesis. A typo "
                    "in a variable name then changes the theorem instead of causing an error — the "
                    "statement quietly becomes a different (usually weaker) claim."
                ),
                evidence=[Evidence(kind="source", summary=f"set_option relaxedAutoImplicit {relaxed}")],
            )
        ]
    if setting is None:
        return [
            Finding(
                check="statements",
                code="auto_implicit_not_disabled",
                severity=Severity.INFO,
                category=Category.STATEMENT,
                confidence=Confidence.HEURISTIC,
                title="`autoImplicit` is not explicitly disabled in this file",
                detail=(
                    "Lean's default for autoImplicit depends on the toolchain version and on the "
                    "project's `lakefile`. When it is on, an unbound identifier silently becomes a "
                    "new hypothesis. Adding `set_option autoImplicit false` makes the file's "
                    "statements stable across toolchain upgrades."
                ),
                remediation="Add `set_option autoImplicit false` near the top of the file.",
            )
        ]
    if setting.strip().lower() == "true":
        return [
            Finding(
                check="statements",
                code="auto_implicit_enabled",
                severity=Severity.MEDIUM,
                category=Category.STATEMENT,
                confidence=Confidence.PROVEN,
                title="`autoImplicit` is enabled in this file",
                detail=(
                    "Any identifier used without being bound is silently generalized into an "
                    "implicit hypothesis. That turns a misspelled variable into a different, "
                    "usually vacuous, theorem rather than into a compile error."
                ),
                evidence=[Evidence(kind="source", summary="set_option autoImplicit true")],
            )
        ]
    return []


# ---------------------------------------------------------------------------
# kernel-backed refutation of closed hypotheses
# ---------------------------------------------------------------------------
def _refutable_hypotheses(ctx: AuditContext, profiles) -> tuple[dict[str, list[tuple[str, str]]], object | None]:
    """Ask Lean to prove `¬ h` for closed hypotheses. Only proofs are reported.

    Attribution is by explicit marker (`-- audit-hyp N` on the probe line itself),
    never by arithmetic on line numbers, and the function *fails closed*: any
    error the probe cannot attribute, or a run in which every single hypothesis
    "failed", is treated as "the probe did not work" and produces no findings at
    all. A missed vacuity is a gap; an invented one destroys the report's value.
    """
    candidates: list[tuple[str, str, str]] = []  # (declaration, hypothesis name, type)
    for decl_name, parsed in profiles.items():
        count = 0
        for binder in parsed.binders:
            if binder.kind == "instance":
                continue
            btype = binder.type_text.strip()
            if not btype or expr.local_vars(btype):
                continue  # depends on other variables: not a closed claim
            if _is_true(btype) or _is_false(btype):
                continue
            candidates.append((decl_name, binder.name or "anonymous", btype))
            count += 1
            if count >= MAX_REFUTATIONS:
                break

    if not candidates:
        return {}, None

    commands = [
        f"example : ¬ ({btype}) := by decide  -- audit-hyp {idx}"
        for idx, (_decl, _hyp, btype) in enumerate(candidates)
    ]
    run_result, _ = ctx.runner.probe(ctx.source, commands, name="ProbeRefute.lean")

    if run_result.timed_out:
        return {}, run_result
    diagnostics = run_result.diagnostics()
    if not diagnostics and not run_result.ok:
        return {}, run_result
    # An error we cannot pin to a probe line means the whole probe file may have
    # failed before reaching the examples. Do not draw conclusions from it.
    if any(d.is_error and d.line is None for d in diagnostics):
        return {}, run_result

    input_lines = run_result.input_text.splitlines()
    failed_ids: set[int] = set()
    attributed = 0
    for diag in diagnostics:
        if not diag.is_error or diag.line is None:
            continue
        idx = _hypothesis_marker(input_lines, diag.line)
        if idx is None:
            continue
        failed_ids.add(idx)
        attributed += 1
    if attributed == 0:
        return {}, run_result

    survived = [i for i in range(len(candidates)) if i not in failed_ids]
    if not survived:
        # Every refutation attempt failed: almost certainly the probe could not
        # run (no `Decidable` instance, missing tactic). Report nothing.
        return {}, run_result

    refuted: dict[str, list[tuple[str, str]]] = {}
    for idx in survived:
        decl_name, hyp_name, btype = candidates[idx]
        refuted.setdefault(decl_name, []).append((hyp_name, btype))
    return refuted, run_result


def _hypothesis_marker(lines: list[str], line_number: int) -> int | None:
    """Find `-- audit-hyp N` on (or just before) the reported line."""
    window = range(max(0, line_number - 3), min(len(lines), line_number))
    for index in sorted(window, reverse=True):
        match = re.search(r"--\s*audit-hyp\s+(\d+)", lines[index])
        if match:
            return int(match.group(1))
    return None


# ---------------------------------------------------------------------------
# helpers
# ---------------------------------------------------------------------------
def _profile(parsed: stmtparse.ParsedStatement) -> dict:
    fingerprint = hashlib.sha256(
        expr.normalize(parsed.raw).encode("utf-8")
    ).hexdigest()
    return {
        "fingerprint": f"sha256:{fingerprint}",
        "binders": [
            {"name": b.name, "kind": b.kind, "type": " ".join(b.type_text.split())}
            for b in parsed.binders
        ],
        "conclusion": " ".join(parsed.conclusion.split()),
        "conclusion_locals": sorted(expr.local_vars(parsed.conclusion)),
        "telescope": parsed.render_telescope(max_width=200),
        "parse_ok": parsed.parse_ok,
        "parse_notes": parsed.notes,
    }


def _strip_at(text: str) -> str:
    return text.strip().lstrip("@").strip()


def _is_true(text: str) -> bool:
    return _strip_at(text).strip() in ("True",)


def _is_false(text: str) -> bool:
    return _strip_at(text).strip() in ("False", "@False")


def _reflexive_pair(conclusion: str) -> str | None:
    """Detect `@Eq α x x` / `@Iff p p` / `x = x` style conclusions."""
    t = _strip_at(conclusion)
    for head in ("@Eq ", "Eq ", "@Iff ", "Iff "):
        if t.startswith(head):
            rest = t[len(head) :].strip()
            parts = _split_top_level_args(rest)
            if len(parts) >= 2:
                for i in range(len(parts) - 1):
                    for j in range(i + 1, len(parts)):
                        if parts[i] and expr.is_trivially_equal(parts[i], parts[j]):
                            return parts[i]
            return None
    # infix forms, as they appear in source-level type text
    for op in ("!=", "≤", "≥", "="):
        idx = expr.top_level_index(t, op)
        if idx > 0:
            left, right = t[:idx], t[idx + len(op) :]
            if expr.is_trivially_equal(left, right):
                return left.strip()
    # `p → p`
    arrow = expr.top_level_index(t, "→")
    if arrow > 0:
        left, right = t[:arrow], t[arrow + 1 :]
        if expr.is_trivially_equal(left, right):
            return left.strip()
    return None


def _split_top_level_args(text: str) -> list[str]:
    """Split `a b (c d) e` into its depth-0 tokens/groups."""
    parts: list[str] = []
    current: list[str] = []
    depth = 0
    masked = expr.blank_comments_and_strings(text)
    for i, ch in enumerate(masked):
        if ch in "([{⦃":
            depth += 1
        elif ch in ")]}⦄":
            depth = max(0, depth - 1)
        if depth == 0 and ch.isspace():
            if current:
                parts.append(text[len("".join(parts)) : len("".join(parts)) + 0] or "".join(current))
                current = []
            continue
        current.append(text[i])
    if current:
        parts.append("".join(current))
    return [p.strip() for p in parts if p.strip()]
