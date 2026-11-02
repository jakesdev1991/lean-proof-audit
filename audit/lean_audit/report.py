"""Aggregate check results into one verdict, and render it.

The JSON report is the contract: stable schema, every finding carrying its own
evidence, and per-declaration statement fingerprints so a later re-audit can
prove the statement under audit has not changed.
"""

from __future__ import annotations

import datetime as _dt
import hashlib
import json
from typing import Any

from . import SCHEMA_VERSION, __version__
from .model import Category, CheckResult, Severity, Verdict, worst_verdict

SEVERITY_ORDER = [Severity.CRITICAL, Severity.HIGH, Severity.MEDIUM, Severity.LOW, Severity.INFO]


def build_report(
    *,
    target: str,
    results: list[CheckResult],
    toolchain: dict,
    config: dict,
    notes: list[str],
    runner_stats: dict,
    started_at: _dt.datetime,
    duration_ms: int,
    target_sha256: str,
) -> dict[str, Any]:
    findings = [f for r in results for f in r.findings]
    counts = {s.value: sum(1 for f in findings if f.severity is s) for s in SEVERITY_ORDER}

    overall = worst_verdict([r.verdict for r in results])
    if overall is Verdict.SKIPPED:
        overall = Verdict.INCONCLUSIVE

    sound_failures = [
        f
        for f in findings
        if f.category is Category.SOUNDNESS and f.severity.rank >= Severity.HIGH.rank
    ]
    statement_failures = [
        f
        for f in findings
        if f.category is Category.STATEMENT and f.severity.rank >= Severity.HIGH.rank
    ]
    dependence_failures = [
        f
        for f in findings
        if f.category is Category.DEPENDENCE and f.severity.rank >= Severity.HIGH.rank
    ]
    incomplete = [r.name for r in results if r.verdict is Verdict.INCONCLUSIVE]

    declarations = _declarations(results)
    reason = _reason(overall, counts, sound_failures, statement_failures, incomplete)

    return {
        "schema": SCHEMA_VERSION,
        "auditor": {"name": "lean-audit", "version": __version__},
        "generated_at": started_at.astimezone(_dt.timezone.utc).isoformat(),
        "target": {"path": target, "sha256": target_sha256},
        "environment": toolchain,
        "config": config,
        "verdict": {
            "overall": overall.value,
            "reason": reason,
            "sound": not sound_failures,
            "statements_honest": not statement_failures,
            "dependence_checked": bool(dependence_failures) or any(
                r.name == "dependence" and r.verdict is not Verdict.SKIPPED for r in results
            ),
            "incomplete_checks": incomplete,
            "counts": counts,
        },
        "checks": [r.to_dict() for r in results],
        "findings": [f.to_dict() for f in findings],
        "declarations": declarations,
        "notes": notes,
        "stats": {
            "duration_ms": duration_ms,
            **runner_stats,
        },
    }


def _declarations(results: list[CheckResult]) -> list[dict]:
    by_decl: dict[str, dict] = {}
    for result in results:
        statements = (result.data or {}).get("statements") or {}
        for name, profile in statements.items():
            entry = by_decl.setdefault(name, {"declaration": name})
            entry["fingerprint"] = profile.get("fingerprint")
            entry["telescope"] = profile.get("telescope")
            entry["conclusion"] = profile.get("conclusion")
            entry["binders"] = len(profile.get("binders") or [])
        axioms = (result.data or {}).get("axioms_by_declaration") or {}
        for name, ax in axioms.items():
            entry = by_decl.setdefault(name, {"declaration": name})
            entry["axioms"] = ax
        dependence = (result.data or {}).get("dependence") or {}
        for name, dep in dependence.items():
            entry = by_decl.setdefault(name, {"declaration": name})
            entry["dependence"] = dep
    for name, entry in by_decl.items():
        entry["findings"] = sum(
            1
            for result in results
            for f in result.findings
            if f.declaration == name
        )
        if "axioms" in entry:
            entry["axiom_status"] = "clean" if not entry["axioms"] else "depends on axioms"
    return sorted(by_decl.values(), key=lambda e: e["declaration"])


def _reason(overall, counts, sound_failures, statement_failures, incomplete) -> str:
    if overall is Verdict.FAIL:
        parts = []
        if sound_failures:
            parts.append(f"{len(sound_failures)} soundness defect(s)")
        if statement_failures:
            parts.append(f"{len(statement_failures)} statement-level defect(s)")
        return "FAIL: " + ", ".join(parts) if parts else "FAIL: at least one check rejected the code"
    if overall is Verdict.WARN:
        return f"WARN: {counts['medium']} medium and {counts['low']} low finding(s); nothing unsound established"
    if overall is Verdict.INCONCLUSIVE:
        return "INCONCLUSIVE: " + (", ".join(incomplete) + " could not complete" if incomplete else "insufficient evidence")
    return "PASS: compiles, axiom-clean, no vacuous or trivially-true statements found"


def to_json(report: dict) -> str:
    return json.dumps(report, indent=2, sort_keys=False, ensure_ascii=False)


# ---------------------------------------------------------------------------
# human-readable render
# ---------------------------------------------------------------------------
BADGE = {
    "pass": "PASS",
    "warn": "WARN",
    "fail": "FAIL",
    "inconclusive": "INCONCLUSIVE",
    "skipped": "skipped",
}
SEV_ICON = {
    Severity.CRITICAL: "CRIT",
    Severity.HIGH: "HIGH",
    Severity.MEDIUM: "MED ",
    Severity.LOW: "LOW ",
    Severity.INFO: "info",
}


def render_markdown(report: dict) -> str:
    out: list[str] = []
    v = report["verdict"]
    out.append(f"# Lean Proof Audit — {badge(v['overall'])}")
    out.append("")
    out.append(f"**Target** `{report['target']['path']}`  ")
    out.append(f"**SHA-256** `{report['target']['sha256']}`  ")
    out.append(f"**Generated** {report['generated_at']}  ")
    env = report["environment"]
    out.append(f"**Lean** {env.get('version') or 'not found'}  ")
    out.append(f"**Auditor** {report['auditor']['name']} {report['auditor']['version']} (schema {report['schema']})")
    out.append("")
    out.append("## Verdict")
    out.append("")
    out.append(f"> {v['reason']}")
    out.append("")
    out.append("| Question | Answer |")
    out.append("| --- | --- |")
    out.append(f"| Is every theorem sound (kernel + axioms)? | {'yes' if v['sound'] else '**no**'} |")
    out.append(f"| Do the statements say what they appear to say? | {'yes' if v['statements_honest'] else '**no**'} |")
    out.append(f"| Is proof dependence established? | {'yes' if v['dependence_checked'] else 'not established'} |")
    if v["incomplete_checks"]:
        out.append(f"| Incomplete checks | {', '.join(v['incomplete_checks'])} |")
    out.append("")
    c = v["counts"]
    out.append(
        f"{c['critical']} critical · {c['high']} high · {c['medium']} medium · "
        f"{c['low']} low · {c['info']} informational"
    )
    out.append("")

    out.append("## Checks")
    out.append("")
    out.append("| Check | Result | Summary |")
    out.append("| --- | --- | --- |")
    for check in report["checks"]:
        out.append(f"| `{check['name']}` | {badge(check['verdict'])} | {_esc(check['summary'])} |")
    out.append("")

    findings = report["findings"]
    if findings:
        out.append("## Findings")
        out.append("")
        for sev in SEVERITY_ORDER:
            group = [f for f in findings if f["severity"] == sev.value]
            if not group:
                continue
            out.append(f"### {sev.value.capitalize()} severity — {len(group)} finding(s)")
            out.append("")
            for f in group:
                out.append(f"#### `{f['code']}` — {_esc(f['title'])}")
                out.append("")
                meta = [f"check `{f['check']}`", f"category `{f['category']}`", f"confidence `{f['confidence']}`"]
                if f.get("declaration"):
                    meta.insert(0, f"declaration `{f['declaration']}`")
                if f.get("location"):
                    loc = f["location"]
                    meta.append(f"at `{loc['file']}:{loc['start']['line']}:{loc['start']['col']}`")
                out.append(" · ".join(meta))
                out.append("")
                out.append(f["detail"])
                out.append("")
                if f.get("remediation"):
                    out.append(f"**Fix:** {f['remediation']}")
                    out.append("")
                for ev in f.get("evidence", []):
                    out.append(f"<details><summary>evidence: {_esc(ev['summary'][:120])}</summary>")
                    out.append("")
                    wrote = False
                    if ev.get("command"):
                        out.append("```")
                        out.append("$ " + " ".join(ev["command"]))
                        out.append("```")
                        wrote = True
                    body = (ev.get("stdout") or "") + (ev.get("stderr") or "")
                    if body.strip():
                        out.append("```")
                        out.append(body.strip()[:1800])
                        out.append("```")
                        wrote = True
                    if ev.get("input_sha256"):
                        out.append(f"probe input sha256: `{ev['input_sha256']}`")
                        wrote = True
                    if not wrote:
                        out.append("_recorded observation (see JSON report for full detail)_")
                    out.append("")
                    out.append("</details>")
                    out.append("")

    decls = report.get("declarations") or []
    if decls:
        out.append("## Declarations")
        out.append("")
        out.append("| Declaration | Axioms | Hypotheses | Conclusion | Fingerprint |")
        out.append("| --- | --- | --- | --- | --- |")
        for d in decls:
            axioms = ", ".join(d.get("axioms") or []) or "none"
            concl = _esc((d.get("conclusion") or "—")[:80])
            fp = (d.get("fingerprint") or "—").replace("sha256:", "")[:16]
            out.append(
                f"| `{d['declaration']}` | {_esc(axioms)[:60]} | {d.get('binders', '—')} | {concl} | `{fp}` |"
            )
        out.append("")
        out.append(
            "Fingerprints are SHA-256 of the *elaborated* statement (`pp.all`). A re-audit that "
            "produces the same fingerprint proves the statement has not changed since this report."
        )
        out.append("")

    if report.get("notes"):
        out.append("## Notes")
        out.append("")
        for note in report["notes"]:
            out.append(f"- {_esc(note)}")
        out.append("")

    out.append("## Reproduce")
    out.append("")
    out.append("```bash")
    out.append("pip install -e audit/")
    out.append(f"lean-audit audit {report['target']['path']}   # schema {report['schema']}")
    out.append("```")
    out.append("")
    out.append(
        "Every finding records the exact Lean invocation, its exit status, and a sha256 of the "
        "probe input, so any claim in this report can be re-derived rather than trusted."
    )
    out.append("")
    return "\n".join(out)


def badge(verdict: str) -> str:
    return f"**{BADGE.get(verdict, verdict.upper())}**"


def _esc(text: str) -> str:
    return str(text).replace("|", "\\|").replace("\n", " ")


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()
