# What this audit actually establishes

A Lean proof can fail in four independent ways. Most audits check one of them,
and a green build checks none of them completely:

| Failure | Kernel catches it? |
| --- | --- |
| The proof does not typecheck | **yes** |
| The proof typechecks but rests on `sorryAx`, a custom axiom, or `native_decide` | no — the file compiles |
| The statement is vacuously true, quantifies over nothing, or concludes `True` | no — it is a true theorem |
| The statement is not the claim that was meant | no — that is not a mathematical property |
| The proof never uses the hypotheses the statement advertises | no — the theorem is still true |

This tool separates those questions and answers each with evidence. The design
rule throughout: **never re-implement the kernel, never let a check coerce an
unknown into a pass.**

---

## The checks

### `build` — is there an accepted proof term?

Runs the real compiler on the file. Distinguishes two kinds of failure that are
easy to conflate and dangerous to conflate:

* **the client's code is wrong** — a genuine diagnostic;
* **the auditor's environment is incomplete** — `unknown module prefix
  'Mathlib'`, missing `.olean` files. This is reported as
  `build_environment_incomplete`, never as a defect in the code, because an
  unbuilt project would otherwise look like a broken proof.

`sorry` is a *warning* in Lean, so a clean exit code is not evidence that a
theorem is proved. That case is caught by `trust`, not here — but the warning is
also surfaced directly as `placeholder_proof`, because it is the single most
common way a "verified" file is not verified.

### `trust` — what is the proof standing on?

`#print axioms` for every named theorem, with the results classified:

| Axioms | Meaning | Severity |
| --- | --- | --- |
| `propext`, `Classical.choice`, `Quot.sound` | Lean's own logic and Mathlib's floor | accepted |
| `sorryAx` | a hole; the theorem is **not proved** | critical |
| `Lean.ofReduceBool`, `Lean.trustCompiler` | compiler-trust (`native_decide`) | high |
| anything else | an assumption the client is making | critical |

The source is also scanned for `unsafe`, `partial`, `@[implemented_by]`,
`@[extern]`, and `native_decide`, so the trust surface is listed explicitly even
where the kernel-checked statement looks innocent.

A theorem that is `private` cannot be queried by name from outside its module.
That is reported as `private_declaration_unprobeable` with medium severity — the
audit does not claim to have verified it.

### `statements` — does the statement say what it appears to say?

The statement is taken from `set_option pp.all true; #check @name`, which is the
kernel's own elaboration — implicit arguments, instance binders, and notation
fully expanded. From that telescope:

* `trivial_conclusion` — the conclusion is `True`; the theorem asserts nothing.
* `reflexive_conclusion` — both sides of the conclusion are the same expression
  (`n = n`, `@Iff p p`), so it holds by `rfl`.
* `false_hypothesis` / `empty_domain` — the statement assumes `False` or
  quantifies over an empty type.
* `decorative_hypothesis` — a hypothesis mentions no variable that appears in the
  conclusion or in any other hypothesis. **Heuristic**, and always escalated only
  after `dependence` confirms it.
* `refutable_hypothesis` — **the hard one.** For every *closed* hypothesis (one
  that mentions no bound variable) the audit asks Lean to prove `¬ h` by
  `decide`. If Lean proves the negation, the hypothesis cannot hold, the theorem
  is vacuously true, and that is a kernel fact rather than a heuristic.
* `auto_implicit_*` — with autoImplicit on, a misspelled variable silently
  becomes an implicit hypothesis instead of a compile error, which changes the
  theorem without changing the source's meaning.
* `elaborated_core` — informational: where notation hides meaning
  (`OfNat.ofNat`, `LE.le`, `Membership.mem`), the elaborated form is quoted so
  the reader can compare it against what they intended.

Every statement gets a **fingerprint**: SHA-256 of the normalised `pp.all`
elaboration. Re-auditing a file and getting the same fingerprint proves the
statement has not changed since the earlier report.

### `dependence` — does the proof use what the statement claims?

Mutation testing on the *statement*, never on the proof:

* delete one hypothesis and recompile. If Lean still accepts the declaration,
  the proof term does not depend on that hypothesis → `inert_hypothesis`.
* replace the conclusion with `True` and recompile. If that compiles, the proof
  is goal-agnostic (`simp`-style automation), so dependence evidence for that
  declaration is weak — reported as `goal_agnostic_proof`.

Two rules keep this honest:

1. Every mutant is **re-parsed** before it is compiled. An edit that does not
   produce the intended telescope is discarded as `invalid`, not counted.
2. Surviving a mutation is *never* reported as "the theorem is false". It is
   reported as what it is: the proof does not use that part of the statement.

### `minimize` — when it fails, what is the smallest failure?

Delta-debugging over declarations: remove one at a time, keep the removal only
if the *same* diagnostic signature still appears. The result is a fragment small
enough to paste into a scratch file, plus a classification — `type mismatch`,
`missing instance`, `unknown identifier`, `unsolved goals`, `timeout`,
`termination`, `placeholder` — which is what determines the kind of fix.

### `claim` — is the formal statement the claim?

This is the expensive bug: a correct proof of the wrong statement. The claim is
supplied as **data**, not prose, so both sides are explicit:

```json
{
  "declaration": "parity",
  "quantifiers": [{ "name": "n", "type": "Nat" }],
  "hypotheses": ["n > 0", "Even n"],
  "conclusion": "n > 0 ∨ n = 0"
}
```

`lean-audit init-claim <file>` generates this template from the elaborated
statement so the client can correct it rather than write it from scratch.

Reported mismatches:

* `claim_hypothesis_dropped` — **critical**. The formal statement omits a
  hypothesis the claim needs, so the formal theorem is *stronger* than intended.
* `claim_extra_hypothesis` — the formalisation assumes more than the claim, so
  the result is weaker than promised.
* `claim_quantifier_arity_mismatch`, `claim_conclusion_mismatch`.

Matching uses **distinctive tokens**, not just variable names: `Even n` and
`Odd n` share their only variable and mean different things, so a name-only
comparison would call them equal.

A prose-only claim is reported as `claim_prose_only`. No heuristic is offered in
its place, because a confident-sounding guess about mathematical intent is worse
than an admitted gap.

---

## What this audit does not do

Stated plainly, because a report that overstates its reach is worse than a
smaller truthful one.

* **It does not check mathematical truth.** Lean's kernel does, conditional on
  the axioms. This tool reports what the kernel accepted and what it rested on.
* **It does not read prose.** Without a structured claim file, correspondence
  between the intended claim and the formal statement is unverified.
* **It is not a proof-repair tool.** It reports the smallest failing fragment and
  the failure class; it does not fix anything.
* **It does not decide termination, consistency, or whether the axioms you
  allowed are themselves consistent.**
* **Mutation testing is syntactic.** It measures whether the proof term depends
  on a piece of the statement, not whether the resulting theorem is interesting.
* **Static statement heuristics can miss.** A hypothesis that is decorative in a
  way the token analysis cannot see is not reported; the mutation check is the
  backstop, and it is bounded by `--max-mutants`.

## Failure modes of the auditor itself

* If no Lean toolchain is found, the verdict is `INCONCLUSIVE` and exit code 3.
  Never `PASS`.
* A check that raises is recorded as `INCONCLUSIVE` with a traceback, not
  dropped.
* If `#check` produces nothing for a declaration, that is
  `statement_unparsed` — unverified, not clean.
* If the refutation probe cannot attribute its errors, it reports nothing rather
  than guessing. Failing closed is the designed behaviour.
* If every refutation attempt in a run fails, the probe is assumed broken and no
  vacuity findings are produced.

## Reproducing a verdict

Every finding records the command, its exit status, and the SHA-256 of the exact
input text, so any verdict can be re-derived rather than trusted. `report.json`
carries the target's SHA-256, the toolchain version, and the policy
(`allowed_axioms`, `allow_compiler_trust`, mutation budget) in force.
