# Lean Proof Audit

Machine-checked verdicts for Lean 4 proofs — with the evidence attached.

| Path | What it is |
| --- | --- |
| [`audit/`](audit/) | The audit engine: six checks, a JSON/Markdown report, exit codes a worker can dispatch on |
| [`audit/docs/AUDIT.md`](audit/docs/AUDIT.md) | Methodology. What each check establishes, and what it explicitly does not |
| [`audit/corpus/`](audit/corpus/) | Planted defects the engine must catch, plus one clean theorem it must not flag |
| [`contract/`](contract/) | The interface to [`audit-vault`](https://github.com/jakesdev1991/audit-vault): versioned manifest, conformance probes, and instructions for the agent that runs the real toolchain |
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

## Two repos, two agents, one toolchain

`audit-vault` owns the real Lean 4 install; this repo owns the auditor. The
auditor cannot inspect the vault (it is private), so the interface is a contract
both sides *execute* rather than a document either side trusts:

```bash
# vault side, once
python3 contract/vault_conformance.py --project . --out conformance.json

# auditor side, per audit
lean-audit conform --vault ../audit-vault
lean-audit audit ../audit-vault/Corpus/X.lean --vault ../audit-vault
```

The conformance result is 12 probes, each answering "does this Lean emit the
output shape my parser depends on?". Its `capabilities` map then gates what the
audit is allowed to claim: if `decide_refutation` is unavailable, the report says
vacuity was **not tested** rather than finding none. A capability the environment
lacks becomes a gap in the report, never a silent pass.

Start here: [`contract/FOR-THE-VAULT-AGENT.md`](contract/FOR-THE-VAULT-AGENT.md).

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
