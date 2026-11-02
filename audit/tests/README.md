# Tests

```bash
python3 -m unittest tests.test_audit -v   # from audit/
```

## `fakelean/` is a simulator, not Lean

`tests/fakelean/lean` is a small Python program that imitates the *observable
behaviour* of `lean file.lean`, `#print axioms`, and `#check` with deterministic
rules, so the audit pipeline can be tested on a machine with no toolchain:

* `--!error: …` in a source file produces a compile error;
* `sorry` produces Lean's warning and puts `sorryAx` in the axiom set;
* a name used in a statement or proof that is not bound is
  `unknown identifier` — which is exactly what happens when mutation testing
  deletes a hypothesis;
* a `True` conclusion with a non-automated proof is a type mismatch.

It exists to prove the *pipeline* is correct: probe construction, diagnostic
attribution, mutation semantics, verdict aggregation, exit codes.

It must never be presented as Lean, and it cannot establish anything about Lean
itself. Verdicts that matter must come from a real toolchain:

```bash
lean-audit doctor
lean-audit selfcheck
```

The end-to-end tests assert both halves of what matters: that planted defects are
caught, and that `corpus/clean.lean` produces no findings at all.
