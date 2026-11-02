# Example report

`report.md` and `report.json` here were produced by running the auditor on
`corpus/vacuous.lean`, a file that **compiles cleanly, is axiom-clean, and
proves nothing**.

> **Read this before quoting the output.** The Lean version printed in these
> files is `4.999.0, fake-toolchain-for-tests`. They were generated with the
> *simulated* toolchain in `tests/fakelean/` so that the report format can be
> reviewed on a machine without Lean installed. The verdicts reflect the
> auditor's real logic, but the compiler output is simulated. Re-generate with a
> real toolchain before showing the report to a client:

```bash
lean-audit audit corpus/vacuous.lean --markdown out.md --json out.json
```

What to look at:

| Part of the report | Why it is there |
| --- | --- |
| Verdict table | Separates "is it sound?" from "does the statement mean anything?" — two questions a green build collapses into one |
| `trivial_conclusion` | A kernel pass cannot see this |
| `decorative_hypothesis` (heuristic) vs `inert_hypothesis` (confirmed) | The static suspicion and the Lean-backed confirmation are reported separately, with different confidence levels |
| Declarations table | Statement fingerprints, so a re-audit can prove the statement has not changed |
| Evidence blocks | The command, its exact input (by sha256), and its output for every finding |
