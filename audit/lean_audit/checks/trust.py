"""`trust`: what is each theorem actually standing on?

A Lean proof is only as trustworthy as the axioms its proof term transitively
depends on. `#print axioms` is the kernel's own answer to that question, so this
check asks it directly and classifies the answer:

  * standard axioms     — propext / Classical.choice / Quot.sound (Mathlib's floor)
  * `sorryAx`           — a hole; the theorem is not proved
  * compiler-trust      — `native_decide` proves by running code, not by reduction
  * anything else       — an assumption the client may not know they are making

The source is also scanned for constructs that can hide an assumption from a
reader (`unsafe`, `partial`, `@[implemented_by]`, `@[extern]`) even when the
kernel-checked statement looks innocent.
"""

from __future__ import annotations

import re

from ..config import COMPILER_TRUST_AXIOMS, HOLE_AXIOMS
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

AXIOM_LINE_RE = re.compile(
    r"^@?'?(?P<name>[^'\n]+?)'?\s+"
    r"(?:depends on axioms:\s*\[(?P<list>[^\]]*)\]|does not depend on any axioms)",
    re.M,
)


def run(ctx: AuditContext) -> CheckResult:
    started = now_ms()
    build = ctx.cache.get("build")
    findings: list[Finding] = []

    if build is None or not build.ok:
        return CheckResult(
            name="trust",
            verdict=Verdict.INCONCLUSIVE,
            summary="skipped: the file must compile before axioms can be queried",
            skip_reason="build failed",
            duration_ms=now_ms() - started,
        )

    decls = [d for d in ctx.theorems if d.name]
    private = [d for d in decls if "private" in d.modifiers]
    public = [d for d in decls if "private" not in d.modifiers]
    if not public:
        return CheckResult(
            name="trust",
            verdict=Verdict.INCONCLUSIVE,
            summary="no named public theorems to query",
            skip_reason="no probeable declarations",
            duration_ms=now_ms() - started,
        )

    commands = [f"#print axioms {d.qualified_name}" for d in public]
    probe_run, _ = ctx.runner.probe(ctx.source, commands, name="ProbeAxioms.lean")
    results = _parse_axiom_output(probe_run.stdout)

    by_name: dict[str, list[str]] = {}
    for raw_name, axioms in results:
        by_name[_clean_name(raw_name)] = axioms

    per_decl: dict[str, list[str]] = {}
    allowed = set(ctx.config.allow_axioms)

    for decl in public:
        axioms = None
        for candidate in (decl.qualified_name, decl.name):
            if candidate and _clean_name(candidate) in by_name:
                axioms = by_name[_clean_name(candidate)]
                break
        if axioms is None:
            findings.append(
                Finding(
                    check="trust",
                    code="axioms_unknown",
                    severity=Severity.MEDIUM,
                    category=Category.SOUNDNESS,
                    confidence=Confidence.PROVEN,
                    title=f"Could not query the axiom set of `{decl.name}`",
                    detail=(
                        "`#print axioms` produced no result for this declaration, so its "
                        "dependency surface is unverified. This happens when the declaration is "
                        "not in scope by name at the end of the file (e.g. it is `private`, or "
                        "declared inside a `where`/`section` that closes with a different name). "
                        "Treated as unverified, never as clean."
                    ),
                    declaration=decl.qualified_name,
                    location=ctx.index.span(decl.start, decl.start + 1),
                    remediation="Make the declaration public, or audit it in a file where it is in scope.",
                    evidence=[probe_run.evidence("axiom probe produced no output for this declaration")],
                )
            )
            continue
        per_decl[decl.qualified_name or decl.name or "?"] = axioms
        findings.extend(_classify(ctx, decl, axioms, allowed, probe_run))

    findings.extend(_source_construct_findings(ctx))

    for decl in private:
        findings.append(
            Finding(
                check="trust",
                code="private_declaration_unprobeable",
                severity=Severity.MEDIUM,
                category=Category.SOUNDNESS,
                confidence=Confidence.HEURISTIC,
                title=f"`{decl.name}` is private, so its axioms cannot be queried by name",
                detail=(
                    "Private declarations are renamed (`_private.<Module>.N.<name>`) at "
                    "elaboration time, so the axiom set of this theorem cannot be queried from "
                    "outside its module. The build check still catches `sorry` warnings, but the "
                    "axiom surface of this specific theorem is unverified."
                ),
                declaration=decl.name,
                location=ctx.index.span(decl.start, decl.start + 1),
                remediation="Make audited theorems public so their axiom sets are independently checkable.",
            )
        )

    hard = [f for f in findings if f.severity.rank >= Severity.HIGH.rank]
    if hard:
        verdict = Verdict.FAIL
        summary = f"{len(hard)} declaration(s) rest on assumptions the kernel does not grant"
    elif findings:
        verdict = Verdict.WARN
        summary = "all queried theorems are kernel-clean; secondary observations below"
    else:
        verdict = Verdict.PASS
        summary = f"{len(per_decl)} theorem(s) depend only on standard axioms"

    return CheckResult(
        name="trust",
        verdict=verdict,
        summary=summary,
        findings=findings,
        duration_ms=now_ms() - started,
        data={
            "axioms_by_declaration": per_decl,
            "probe_commands": commands,
            "probe_duration_ms": probe_run.duration_ms,
            "allowed_axioms": sorted(allowed),
        },
    )


def _parse_axiom_output(stdout: str) -> list[tuple[str, list[str]]]:
    out: list[tuple[str, list[str]]] = []
    for m in AXIOM_LINE_RE.finditer(stdout):
        raw = m.group("list")
        axioms = [a.strip() for a in raw.split(",")] if raw else []
        out.append((m.group("name"), [a for a in axioms if a]))
    return out


def _clean_name(name: str) -> str:
    return name.strip().strip("'").lstrip("@")


def _classify(ctx: AuditContext, decl, axioms: list[str], allowed: set[str], probe_run) -> list[Finding]:
    findings: list[Finding] = []
    decl_name = decl.qualified_name or decl.name or "<anonymous>"
    loc = ctx.index.span(decl.start, decl.start + 1)

    for axiom in axioms:
        clean = _clean_name(axiom)
        if clean in allowed:
            continue
        if clean in HOLE_AXIOMS:
            findings.append(
                Finding(
                    check="trust",
                    code="depends_on_sorry",
                    severity=Severity.CRITICAL,
                    category=Category.SOUNDNESS,
                    confidence=Confidence.PROVEN,
                    title=f"`{decl_name}` depends on `sorryAx`",
                    detail=(
                        "The kernel accepted this declaration, but its proof term contains a "
                        "hole: it depends transitively on `sorryAx`. A `sorry` in a helper lemma "
                        "three files away puts the headline theorem in exactly this state, and "
                        "the file still compiles without error. This declaration is not proved."
                    ),
                    declaration=decl_name,
                    location=loc,
                    remediation="Prove the placeholder, or state the result as a conjecture instead of a theorem.",
                    evidence=[probe_run.evidence(f"#print axioms {decl.qualified_name}: sorryAx present")],
                )
            )
        elif clean in COMPILER_TRUST_AXIOMS:
            findings.append(
                Finding(
                    check="trust",
                    code="compiler_trust",
                    severity=Severity.HIGH if not ctx.config.allow_compiler_trust else Severity.INFO,
                    category=Category.SOUNDNESS,
                    confidence=Confidence.PROVEN,
                    title=f"`{decl_name}` trusts the compiler via `{clean}`",
                    detail=(
                        "This proof uses `native_decide` (or equivalent), which discharges the "
                        "goal by compiling and running a decision procedure. The result is only as "
                        "sound as the Lean-to-C compilation chain and the hardware it ran on, not "
                        "as the kernel's reduction. Many projects accept this; the audit's job is "
                        "to make the choice visible."
                    ),
                    declaration=decl_name,
                    location=loc,
                    remediation="Replace `native_decide` with `decide` where the goal reduces in the kernel.",
                    evidence=[probe_run.evidence(f"#print axioms {decl.qualified_name}: {clean}")],
                )
            )
        else:
            findings.append(
                Finding(
                    check="trust",
                    code="unverified_axiom",
                    severity=Severity.CRITICAL,
                    category=Category.SOUNDNESS,
                    confidence=Confidence.PROVEN,
                    title=f"`{decl_name}` depends on the non-standard axiom `{clean}`",
                    detail=(
                        f"`{clean}` is not one of the axioms Lean's logic grants "
                        f"({', '.join(ctx.config.allow_axioms)}). Any theorem depending on it is "
                        "only as true as that assumption. This is the most common way a "
                        "\"kernel-verified\" claim turns out to be conditional."
                    ),
                    declaration=decl_name,
                    location=loc,
                    evidence=[probe_run.evidence(f"#print axioms {decl.qualified_name}: {clean}")],
                )
            )
    return findings


def _source_construct_findings(ctx: AuditContext) -> list[Finding]:
    findings: list[Finding] = []
    for hit in ctx.index.trust_tokens:
        if hit.token in ("sorry", "admit"):
            severity = Severity.CRITICAL
            code = "source_placeholder"
            title = f"`{hit.token}` appears in the source"
            detail = (
                f"`{hit.token}` at line {hit.line} discharges a goal without a proof. Even if it "
                "sits in a `def` or an auxiliary lemma, anything downstream inherits the hole."
            )
        elif hit.token == "native_decide":
            severity = Severity.HIGH
            code = "source_native_decide"
            title = "`native_decide` appears in the source"
            detail = (
                "`native_decide` proves a goal by executing compiled code. It is accepted by "
                "Lean, but the trust boundary moves from the kernel to the compiler and the "
                "machine that ran it."
            )
        else:
            severity = Severity.LOW
            code = "source_trust_construct"
            title = f"`{hit.token}` appears in the source"
            detail = (
                f"`{hit.token}`: a construct that separates logical content from runtime "
                "behaviour. It does not by itself weaken a proved statement, and it is listed so "
                "the trust surface is explicit rather than implicit."
            )
        findings.append(
            Finding(
                check="trust",
                code=code,
                severity=severity,
                category=Category.SOUNDNESS,
                confidence=Confidence.HEURISTIC,
                title=title,
                detail=detail,
                location=_line_span(ctx, hit.line, hit.col),
                evidence=[
                    Evidence(
                        kind="source",
                        summary=f"line {hit.line}: {hit.context}",
                        location=_line_span(ctx, hit.line, hit.col),
                    )
                ],
            )
        )
    return findings


def _line_span(ctx: AuditContext, line: int, col: int):
    from ..model import SourceSpan

    text = ctx.source
    line_text = text.splitlines()[line - 1] if line - 1 < len(text.splitlines()) else ""
    return SourceSpan(str(ctx.target), line, col, line, max(col, len(line_text)))
