# Lean Proof Audit

Machine-checked verdicts for Lean 4 proofs — with the evidence attached.

| Path | What it is |
| --- | --- |
| [`audit/`](audit/) | The audit engine: six checks, a JSON/Markdown report, exit codes a worker can dispatch on |
| [`audit/docs/AUDIT.md`](audit/docs/AUDIT.md) | Methodology. What each check establishes, and what it explicitly does not |
| [`audit/corpus/`](audit/corpus/) | Planted defects the engine must catch, plus one clean theorem it must not flag |
| [`index.html`](index.html) | The service landing page |

## Why the engine is the product

A green `lake build` certifies one thing: Lean's kernel accepted a proof term for
the statement as written. It says nothing about whether the proof rests on
`sorryAx` hidden three lemmas deep, whether the statement is vacuously true,
whether the proof ignores the hypotheses the statement advertises, or whether the
statement is the claim that was meant. Those are four different questions, and
the engine answers them separately rather than averaging them into a score.

```bash
cd audit && pip install -e . && lean-audit doctor
lean-audit audit YourFile.lean --project . --markdown report.md --json report.json
```

## Design commitments

* **The kernel is never re-implemented.** Every claim about a Lean file comes
  from a real `lean` invocation whose command and output are attached to the
  finding.
* **Unknown is not pass.** No toolchain, an incomplete environment, an
  unparseable statement, or a crashed check all yield `INCONCLUSIVE` (exit 3),
  never `PASS`.
* **Heuristics are labelled and confirmed.** A static suspicion is reported at
  `confidence: heuristic`; it is escalated only after a Lean run confirms it.
* **Probes fail closed.** If a probe cannot attribute its results, it reports
  nothing instead of guessing.
