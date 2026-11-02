# Lean Proof Audit — **FAIL**

**Target** `/home/user/lean-proof-audit/audit/corpus/vacuous.lean`  
**SHA-256** `1da8d11f71a4df355baee3ecfa36581eb6f59475a9d1545996545220b27bea44`  
**Generated** 2026-11-02T06:42:51.580766+00:00  
**Lean** Lean (version 4.999.0, fake-toolchain-for-tests, Release)  
**Auditor** lean-audit 2.0.0 (schema lean-audit/2)

## Verdict

> FAIL: 1 statement-level defect(s)

| Question | Answer |
| --- | --- |
| Is every theorem sound (kernel + axioms)? | yes |
| Do the statements say what they appear to say? | **no** |
| Is proof dependence established? | yes |

0 critical · 1 high · 3 medium · 0 low · 0 informational

## Checks

| Check | Result | Summary |
| --- | --- | --- |
| `build` | **PASS** | compiles clean |
| `trust` | **PASS** | 1 theorem(s) depend only on standard axioms |
| `statements` | **FAIL** | statement-level defects found that a kernel pass cannot see |
| `dependence` | **WARN** | 1 killed / 2 survived of 3 mutants |
| `minimize` | **skipped** | nothing to minimize: the file compiles |
| `claim` | **skipped** | no claim supplied — correspondence to the intended claim is unverified |

## Findings

### High severity — 1 finding(s)

#### `trivial_conclusion` — `vacuous` concludes `True`

declaration `vacuous` · check `statements` · category `statement` · confidence `proven` · at `/home/user/lean-proof-audit/audit/corpus/vacuous.lean:11:1`

The conclusion is `True`, so the theorem is true no matter what the hypotheses say. Be aware that its axioms can still be kernel-clean: this is not a soundness failure, it is a statement failure.

<details><summary>evidence: ⊢ True</summary>

_recorded observation (see JSON report for full detail)_

</details>

### Medium severity — 3 finding(s)

#### `decorative_hypothesis` — `vacuous` has a hypothesis nothing else mentions: `h`

declaration `vacuous` · check `statements` · category `statement` · confidence `heuristic` · at `/home/user/lean-proof-audit/audit/corpus/vacuous.lean:11:1`

`h : n > 5` mentions no identifier that appears in the conclusion or in any other hypothesis. Either the statement assumes something it never uses (which overstates what it claims to need), or the conclusion is weaker than intended. The `dependence` check tests this directly by deleting the hypothesis and re-running the proof.

**Fix:** Remove the hypothesis if it is unused, or strengthen the conclusion.

<details><summary>evidence: hypothesis variables: ['n']; variables elsewhere: []; intersection: empty</summary>

_recorded observation (see JSON report for full detail)_

</details>

#### `inert_hypothesis` — `vacuous` does not use its hypothesis `h`

declaration `vacuous` · check `dependence` · category `dependence` · confidence `heuristic_confirmed`

The hypothesis was deleted from the statement, the proof was left untouched, and Lean still accepted the declaration. The proof term therefore does not depend on it. The theorem remains true, but it is weaker than it looks: a reader will assume that hypothesis is doing work. Either drop it, or the conclusion is meant to be stronger.

**Fix:** Remove the unused hypothesis, or strengthen the conclusion so the hypothesis is needed.

<details><summary>evidence: drop_hypothesis -> survived: compiled unchanged with the mutated statement</summary>

```
$ /home/user/lean-proof-audit/audit/tests/fakelean/lean /tmp/lean-audit-vz1_ofh1/Mutant_41195433.lean
```
probe input sha256: `075fdc61ae4f4fc9cf4405a0cbc7593c00ec9a700a56c8c806e108835c0911ab`

</details>

#### `goal_agnostic_proof` — `vacuous` compiles even when its conclusion is replaced by `True`

declaration `vacuous` · check `dependence` · category `dependence` · confidence `heuristic_confirmed`

The proof closes the goal regardless of what the goal is, which is what automation-driven proofs (`simp`, `trivial`, `decide`-style) do. This does not make the theorem false. It does mean that for this declaration the proof carries no information about the conclusion, so the statement is doing all the work and deserves the closest reading.

<details><summary>evidence: conclusion_true -> survived: compiled unchanged with the mutated statement</summary>

```
$ /home/user/lean-proof-audit/audit/tests/fakelean/lean /tmp/lean-audit-vz1_ofh1/Mutant_65141623.lean
```
probe input sha256: `8fe1cfb207d711eadd01e46233386dfd9c1ca0a4331265abb4f98105cac1bba2`

</details>

## Declarations

| Declaration | Axioms | Hypotheses | Conclusion | Fingerprint |
| --- | --- | --- | --- | --- |
| `vacuous` | none | 2 | True | `49da7ece4860f999` |

Fingerprints are SHA-256 of the *elaborated* statement (`pp.all`). A re-audit that produces the same fingerprint proves the statement has not changed since this report.

## Reproduce

```bash
pip install -e audit/
lean-audit audit /home/user/lean-proof-audit/audit/corpus/vacuous.lean   # schema lean-audit/2
```

Every finding records the exact Lean invocation, its exit status, and a sha256 of the probe input, so any claim in this report can be re-derived rather than trusted.

