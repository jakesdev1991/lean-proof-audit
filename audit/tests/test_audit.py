"""Test suite for the auditor.

Two layers:

  * unit tests for the pieces that decide what a finding means (parsing,
    mutation construction, claim matching, verdict aggregation). These run with
    no Lean installation.
  * end-to-end tests that drive the real CLI against the corpus, using the
    simulated toolchain in `tests/fakelean/`. They verify the *pipeline*:
    probing, attribution, aggregation, exit codes.

What neither layer proves: that the audit's verdicts match real Lean on a real
project. That requires a toolchain and is what `lean-audit selfcheck` is for —
run it on a machine with Lean before trusting a verdict in production.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
sys.path.insert(0, str(ROOT))

from lean_audit import expr, stmtparse  # noqa: E402
from lean_audit.checks import claim as claim_check  # noqa: E402
from lean_audit.checks import dependence  # noqa: E402
from lean_audit.checks import minimize, statements, trust  # noqa: E402
from lean_audit.checks.build import ENVIRONMENT_ERROR_PATTERNS  # noqa: E402
from lean_audit.lean import parse_diagnostics  # noqa: E402
from lean_audit.model import (  # noqa: E402
    CheckResult,
    Category,
    Confidence,
    Finding,
    Severity,
    Verdict,
    worst_verdict,
)
from lean_audit.report import build_report, render_markdown, to_json  # noqa: E402
from lean_audit.source import index_source  # noqa: E402


class TestTelescopeParsing(unittest.TestCase):
    """`pp.all` output is the audit's view of the kernel's own elaboration."""

    def test_implicit_and_instance_binders(self):
        parsed = stmtparse.parse_telescope(
            "{α : Type u_1} → [inst : @Add α] → (n : α) → @Eq α n n"
        )
        self.assertTrue(parsed.parse_ok, parsed.notes)
        self.assertEqual([(b.kind, b.name) for b in parsed.binders],
                         [("implicit", "α"), ("instance", "inst"), ("explicit", "n")])
        self.assertEqual(parsed.conclusion, "@Eq α n n")

    def test_anonymous_arrows_become_hypotheses(self):
        parsed = stmtparse.parse_telescope("@And p q → @Or r s → True")
        self.assertEqual(len(parsed.binders), 2)
        self.assertEqual(parsed.conclusion, "True")
        self.assertTrue(all(b.anonymous for b in parsed.binders))

    def test_forall_list(self):
        parsed = stmtparse.parse_telescope("∀ (α : Type) (f : α → α), @Function.Injective α α f")
        self.assertEqual([b.name for b in parsed.binders], ["α", "f"])
        self.assertEqual(parsed.conclusion, "@Function.Injective α α f")

    def test_arrows_inside_parens_do_not_split(self):
        parsed = stmtparse.parse_telescope("@Eq (@Nat → Nat) f g")
        self.assertEqual(parsed.binders, [])
        self.assertEqual(parsed.conclusion, "@Eq (@Nat → Nat) f g")

    def test_unnamed_bracketed_hypothesis(self):
        parsed = stmtparse.parse_telescope("{α : Type} → [inst : @Add α] → (@Add α) → α → α")
        self.assertEqual(len(parsed.binders), 4)
        self.assertFalse(any("→" in b.type_text for b in parsed.binders[-1:]))

    def test_unparseable_input_is_reported_not_guessed(self):
        parsed = stmtparse.parse_telescope("∀ , garbage")
        self.assertFalse(parsed.parse_ok)
        self.assertTrue(parsed.notes)

    def test_check_output_extraction(self):
        parsed = stmtparse.parse_check_output(
            "  @Foo.bar : {α : Type u_1} → α → α\nsome other output\n", "Foo.bar"
        )
        self.assertIsNotNone(parsed)
        self.assertEqual(parsed.conclusion, "α")


class TestExpressionAnalysis(unittest.TestCase):
    def test_local_vars_ignore_globals_and_universes(self):
        text = "@LE.le Nat instLENat (@OfNat.ofNat Nat (OfNat.mk Nat 0)) n"
        self.assertEqual(expr.local_vars(text), {"n", "instLENat"})

    def test_notation_notes_detect_hidden_core(self):
        notes = expr.notation_notes("@LE.le Nat instLENat 0 n")
        self.assertIn("LE.le", [n.symbol for n in notes])

    def test_multiset_comment_masking_preserves_offsets(self):
        text = "a -- trailing\n/- block /- nested -/ still -/\nb \"string\""
        masked = expr.blank_comments_and_strings(text)
        self.assertEqual(len(masked), len(text))
        self.assertEqual(masked.count("\n"), text.count("\n"))
        self.assertNotIn("trailing", masked)

    def test_depth_aware_search(self):
        self.assertFalse(expr.has_top_level("(@And (p → q) q)", "→"))
        self.assertTrue(expr.has_top_level("p → q", "→"))


class TestSourceIndex(unittest.TestCase):
    SOURCE = '''import Mathlib

set_option autoImplicit false

namespace Outer
namespace Inner
@[simp]
theorem a (n : Nat) (h : n > 5) : n = n ∨ n = 0 := by
  exact Or.inr rfl
end Inner
theorem b : True := trivial
end Outer

theorem c (n : Nat) : n = n := by
  sorry

axiom spooky : False
'''

    def setUp(self):
        self.index = index_source("Demo.lean", self.SOURCE)

    def test_declarations_and_qualification(self):
        names = [(d.kw, d.qualified_name) for d in self.index.decls]
        self.assertIn(("theorem", "Outer.Inner.a"), names)
        self.assertIn(("theorem", "Outer.b"), names)
        self.assertIn(("theorem", "c"), names)

    def test_statement_span_splits_at_the_colon(self):
        decl = next(d for d in self.index.decls if d.name == "a")
        (bstart, bend), (tstart, tend) = decl.statement_parts(self.SOURCE)
        self.assertEqual(self.SOURCE[bstart:bend].strip(), "(n : Nat) (h : n > 5)")
        self.assertEqual(self.SOURCE[tstart:tend].strip(), "n = n ∨ n = 0")

    def test_pre_colon_binders_parse(self):
        decl = next(d for d in self.index.decls if d.name == "a")
        (bstart, bend), _ = decl.statement_parts(self.SOURCE)
        binders, notes = stmtparse.parse_binders_segment(self.SOURCE[bstart:bend], bstart)
        self.assertEqual(notes, [])
        self.assertEqual([(b.name, b.type_text) for b in binders],
                         [("n", "Nat"), ("h", "n > 5")])

    def test_attributes_and_options(self):
        decl = next(d for d in self.index.decls if d.name == "a")
        self.assertEqual(decl.attributes, ["simp"])
        self.assertEqual(self.index.set_option("autoImplicit"), "false")
        self.assertEqual(self.index.imports, ["Mathlib"])

    def test_trust_tokens_are_located(self):
        tokens = {hit.token for hit in self.index.trust_tokens}
        self.assertIn("sorry", tokens)

    def test_axiom_declaration_recorded(self):
        self.assertTrue(any(d.kw == "axiom" and d.name == "spooky" for d in self.index.decls))


class TestMutationConstruction(unittest.TestCase):
    """Every mutant must be syntactically valid before it is compiled."""

    def test_drop_binder_shapes(self):
        cases = [
            "∀ (n : Nat) (m : Nat), n = m",
            "∀ (n : Nat), n = n",
            "(n : Nat) → (h : n > 0) → n ≥ 0",
            "(n : Nat) → n = n",
        ]
        for text in cases:
            parsed = stmtparse.parse_telescope(text)
            for binder in parsed.binders:
                mutated = dependence._drop_binder(text, binder.span, binder.kind)
                if mutated is None:
                    continue
                reparsed = stmtparse.parse_telescope(mutated)
                self.assertTrue(reparsed.parse_ok, f"{text!r} -> {mutated!r}: {reparsed.notes}")
                self.assertEqual(len(reparsed.binders), len(parsed.binders) - 1,
                                 f"{text!r} -> {mutated!r}")

    def test_unsafe_drop_returns_none_rather_than_broken_syntax(self):
        self.assertIsNone(dependence._drop_binder("(n : Nat)", (0, 10), "explicit"))

    def test_conclusion_replacement(self):
        text = "(n : Nat) → (h : n > 0) → n ≥ 0"
        parsed = stmtparse.parse_telescope(text)
        mutated = dependence._replace_conclusion(text, parsed.conclusion_span, "True")
        self.assertTrue(mutated.endswith("True"))
        self.assertEqual(len(stmtparse.parse_telescope(mutated).binders), 2)


class TestStatementHeuristics(unittest.TestCase):
    def test_reflexive_conclusions(self):
        for text in ("@Eq Nat n n", "Eq Nat n n", "@Iff p p", "p → p", "n = n"):
            self.assertIsNotNone(statements._reflexive_pair(text), text)
        for text in ("@Eq Nat n m", "@Eq Nat n (@HAdd.hAdd n 1)", "n = m"):
            self.assertIsNone(statements._reflexive_pair(text), text)

    def test_trivial_propositions(self):
        self.assertTrue(statements._is_true("True"))
        self.assertTrue(statements._is_false("False"))
        self.assertFalse(statements._is_true("1 = 1"))


class TestClaimMatching(unittest.TestCase):
    """`Even n` and `Odd n` share every variable name and mean different things."""

    def test_distinctive_tokens_catch_predicate_substitution(self):
        haystack = "n > 0 || n > 0 ∨ n = 0"
        self.assertTrue(claim_check._claim_element_present("n > 0", haystack))
        self.assertFalse(claim_check._claim_element_present("Even n", haystack))
        self.assertFalse(claim_check._claim_element_present("Odd n", haystack))

    def test_operator_substitution_is_caught(self):
        self.assertFalse(claim_check._claim_element_present("n < 0", "n > 0"))

    def test_hypotheses_are_not_counted_as_quantifiers(self):
        self.assertTrue(claim_check._looks_like_hypothesis("n > 0"))
        self.assertTrue(claim_check._looks_like_hypothesis("n ≤ m"))
        self.assertFalse(claim_check._looks_like_hypothesis("Nat"))


class TestTrustParsing(unittest.TestCase):
    def test_axiom_lines(self):
        output = (
            "'A.b' depends on axioms: [propext, Classical.choice, Quot.sound]\n"
            "'A.c' depends on axioms: [sorryAx]\n"
            "'A.d' does not depend on any axioms\n"
            "@'A.e' depends on axioms: [Lean.ofReduceBool]\n"
        )
        parsed = dict(trust._parse_axiom_output(output))
        self.assertEqual(parsed["A.b"], ["propext", "Classical.choice", "Quot.sound"])
        self.assertEqual(parsed["A.c"], ["sorryAx"])
        self.assertEqual(parsed["A.d"], [])
        self.assertEqual(parsed["A.e"], ["Lean.ofReduceBool"])


class TestDiagnostics(unittest.TestCase):
    def test_multiline_error_continuations(self):
        text = (
            "Demo.lean:13:24: error: application type mismatch\n"
            "  h\n"
            "argument\n"
            "  n\n"
            "has type\n"
            "  Nat : Type\n"
        )
        diags = parse_diagnostics(text)
        self.assertEqual(len(diags), 1)
        self.assertEqual(diags[0].line, 13)
        self.assertIn("has type", diags[0].full_message)

    def test_environment_errors_are_distinguishable(self):
        import re

        env_message = "unknown module prefix 'Mathlib'"
        client_message = "application type mismatch"
        self.assertTrue(any(re.search(p, env_message) for p in ENVIRONMENT_ERROR_PATTERNS))
        self.assertFalse(any(re.search(p, client_message) for p in ENVIRONMENT_ERROR_PATTERNS))

    def test_failure_classification(self):
        for message, expected in (
            ("application type mismatch", "type mismatch"),
            ("failed to synthesize instance", "missing instance"),
            ("declaration uses 'sorry'", "placeholder"),
            ("maximum heartbeats exceeded", "timeout"),
        ):
            self.assertEqual(minimize._classify(message)[0], expected)


class TestReportAggregation(unittest.TestCase):
    def _finding(self, category, severity, code="x", decl="T"):
        return Finding(
            check="test", code=code, severity=severity, category=category,
            confidence=Confidence.PROVEN, title="t", detail="d", declaration=decl,
        )

    def _report(self, findings, verdict=Verdict.FAIL):
        result = CheckResult(name="test", verdict=verdict, summary="s", findings=findings)
        return build_report(
            target="X.lean", results=[result], toolchain={}, config={}, notes=[],
            runner_stats={"lean_runs": 1, "lean_time_ms": 1},
            started_at=__import__("datetime").datetime.now(),
            duration_ms=1, target_sha256="0" * 64,
        )

    def test_soundness_failure_clears_sound_flag(self):
        report = self._report([self._finding(Category.SOUNDNESS, Severity.CRITICAL)])
        self.assertFalse(report["verdict"]["sound"])

    def test_statement_failure_does_not_clear_sound_flag(self):
        report = self._report([self._finding(Category.STATEMENT, Severity.HIGH)])
        self.assertTrue(report["verdict"]["sound"])
        self.assertFalse(report["verdict"]["statements_honest"])

    def test_low_severity_findings_keep_sound_and_honest(self):
        report = self._report([self._finding(Category.STATEMENT, Severity.LOW)])
        self.assertTrue(report["verdict"]["sound"])
        self.assertTrue(report["verdict"]["statements_honest"])

    def test_report_is_json_serialisable_and_renders(self):
        report = self._report([self._finding(Category.SOUNDNESS, Severity.HIGH)])
        json.loads(to_json(report))
        markdown = render_markdown(report)
        self.assertIn("Lean Proof Audit", markdown)
        self.assertIn("high", markdown.lower())

    def test_worst_verdict_ignores_skipped(self):
        self.assertIs(worst_verdict([Verdict.PASS, Verdict.SKIPPED]), Verdict.PASS)
        self.assertIs(worst_verdict([Verdict.PASS, Verdict.FAIL]), Verdict.FAIL)


class TestEndToEnd(unittest.TestCase):
    """Drive the real CLI against the corpus with the simulated toolchain."""

    @classmethod
    def setUpClass(cls):
        cls.env = dict(os.environ)
        cls.env["PATH"] = str(HERE / "fakelean") + os.pathsep + cls.env["PATH"]

    def run_audit(self, name: str, extra: list[str] | None = None):
        case = ROOT / "corpus" / f"{name}.lean"
        proc = subprocess.run(
            [sys.executable, "-m", "lean_audit.cli", "audit", str(case), "--json", "-", "--quiet"]
            + (extra or []),
            cwd=ROOT, env=self.env, capture_output=True, text=True, timeout=300,
        )
        return proc.returncode, json.loads(proc.stdout)

    def test_corpus_matches_expectations(self):
        failures = []
        for expect_path in sorted((ROOT / "corpus").glob("*.expect.json")):
            name = expect_path.name.replace(".expect.json", "")
            expected = json.loads(expect_path.read_text())
            extra = ["--claim", str(ROOT / "corpus" / f"{name}.claim.json")] if expected.get("claim") else []
            code, report = self.run_audit(name, extra)
            codes = {f["code"] for f in report["findings"]}
            missing = [c for c in expected.get("must_flag", []) if c not in codes]
            forbidden = [c for c in expected.get("must_not_flag", []) if c in codes]
            verdict = report["verdict"]["overall"]
            if missing or forbidden or verdict != expected["verdict"]:
                failures.append(f"{name}: missing={missing} forbidden={forbidden} verdict={verdict}")
        self.assertEqual(failures, [], "\n".join(failures))

    def test_clean_case_is_a_true_pass(self):
        code, report = self.run_audit("clean")
        self.assertEqual(code, 0)
        self.assertEqual(report["verdict"]["overall"], "pass")
        self.assertEqual(report["findings"], [])

    def test_sorry_case_is_not_a_pass(self):
        code, report = self.run_audit("hole")
        self.assertNotEqual(code, 0)
        self.assertFalse(report["verdict"]["sound"])

    def test_every_finding_carries_evidence_or_is_a_known_heuristic(self):
        for name in ("hole", "vacuous", "axiom_abuse"):
            _code, report = self.run_audit(name)
            for finding in report["findings"]:
                if finding["severity"] in ("critical", "high"):
                    self.assertTrue(
                        finding["evidence"],
                        f"{name}: {finding['code']} is high/critical with no evidence",
                    )

    def test_report_records_environment_and_fingerprints(self):
        _code, report = self.run_audit("vacuous")
        self.assertIn("version", report["environment"])
        self.assertTrue(report["declarations"])
        self.assertTrue(all(d.get("fingerprint") for d in report["declarations"]))

    def test_missing_toolchain_is_inconclusive_not_pass(self):
        env = dict(self.env)
        env["PATH"] = "/nonexistent"
        env["LEAN_AUDIT_LEAN"] = ""
        proc = subprocess.run(
            [sys.executable, "-m", "lean_audit.cli", "audit", str(ROOT / "corpus" / "clean.lean"),
             "--json", "-", "--quiet"],
            cwd=ROOT, env=env, capture_output=True, text=True, timeout=120,
        )
        self.assertEqual(proc.returncode, 3)
        report = json.loads(proc.stdout)
        self.assertEqual(report["verdict"]["overall"], "inconclusive")


if __name__ == "__main__":
    unittest.main(verbosity=2)
