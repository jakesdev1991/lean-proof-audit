# lean-audit

An audit engine for Lean 4 code. It answers four separate questions and keeps
them separate, because a green build collapses all of them into one:

| Question | Check | Exit-code impact |
| --- | --- | --- |
| Is there an accepted proof term? | `build` | fail on error |
| Is the proof standing on anything it shouldn't? | `trust` | fail on `sorryAx`, custom axioms, compiler trust |
| Does the statement say what it appears to say? | `statements` | fail on vacuity, `True`, empty domains |
| Does the proof use what the statement advertises? | `dependence` | warn, with Lean-backed confirmation |
| When it fails, what is the smallest failure? | `minimize` | — |
| Is the formal statement the claim that was meant? | `claim` | fail on dropped hypotheses |
| Is this the environment the verdict claims? | `vault` | fail on a Lean version mismatch |

Full methodology, including an explicit list of what this audit does *not*
establish: [`docs/AUDIT.md`](docs/AUDIT.md).

## Using a vault (a repo that owns a real toolchain)

A *vault* is any repository that pins a Lean 4 toolchain, a built Lake project,
and a corpus. The interface is versioned and machine-validated — see
[`../contract/CONTRACT.md`](../contract/CONTRACT.md).

```bash
lean-audit conform --vault ../audit-vault                 # does this toolchain
                                                          # emit the shapes the
                                                          # audit parses?
lean-audit vault ../audit-vault                           # identity + corpus inventory
lean-audit audit ../audit-vault/Corpus/X.lean --vault ../audit-vault
```

The conformance run is not a formality: its `capabilities` map decides what the
audit may claim. With `decide_refutation: false`, the statements check emits
`refutation_probe_unavailable` — "vacuity was not tested" — instead of implying
it found no vacuous theorems. A capability the environment lacks is a gap in the
report, never a silent pass.

Reports produced through a vault carry its name, repo, commit, and declared Lean
version under `environment.vault`, and a `vault_lean_version_mismatch` finding if
the Lean that actually ran disagrees with the manifest.

## Install

```bash
pip install -e .
lean-audit doctor            # is there a usable Lean toolchain?
```

`doctor` prints the Lean version it found and runs a three-command probe
(`#print axioms`, `pp.all`, `#check`) so you know the toolchain can answer the
questions the audit asks before you trust a verdict from it.

## Use

```bash
lean-audit audit Splitting.lean --project . --markdown report.md --json report.json
```

```text
audit report — Splitting.lean
  ✓ build        compiles clean
  ✗ trust        depends on sorryAx
  ✗ statements   statement-level defects found that a kernel pass cannot see
  ! dependence   3 killed / 1 survived of 4 mutants

  verdict: FAIL  (1 critical, 1 high, 2 medium)
```

Exit codes: `0` pass · `1` warn · `2` fail · `3` inconclusive or environment
problem. A run with no usable toolchain exits `3` and says so in the report — it
never reports `PASS`.

Useful flags:

| Flag | Purpose |
| --- | --- |
| `--claim claim.json` | verify the formal statement against an explicit claim |
| `--max-mutants N` | mutation budget (each mutant costs one Lean run) |
| `--allow-axiom NAME` | treat an additional axiom as acceptable, and record it in the report |
| `--allow-compiler-trust` | stop flagging `native_decide`, while still listing it |
| `--checks build,trust` | run a subset |
| `--strict` | treat medium findings as failures |

## Generate a claim file

```bash
lean-audit init-claim Splitting.lean --out claim.json
```

This emits the **elaborated** statement as a template. Correct it to describe
what you actually intended to prove; if you leave it as generated, the claim
check can only confirm the statement matches itself.

## Verify the auditor

```bash
make test              # unit + end-to-end suite (no Lean required)
make selfcheck         # audit the corpus and check it catches what it should (needs Lean)
make publish-contract  # republish contract/vault_conformance.py after editing probes
```

The corpus in `corpus/` contains planted defects — a `sorry`, a custom axiom, a
vacuous statement, a decorative hypothesis, a non-compiling file, a dropped
claim hypothesis — plus one genuinely clean theorem that must produce **zero**
findings. That last case is the point: an auditor that flags everything is
worthless.

## Layout

```
lean_audit/
  source.py       structural map of a Lean file (declarations, statement spans)
  stmtparse.py    telescope parser: type -> binders + conclusion
  expr.py         token-level analysis of elaborated (pp.all) expressions
  lean.py         the only module that talks to Lean; every run is evidence
  model.py        findings, severities, evidence
  report.py       verdict aggregation, JSON + Markdown rendering
  conformance_probe.py  the vault handshake probes (copied to contract/, verbatim)
  vault.py        vault manifest loading and validation
  checks/         build, trust, statements, dependence, minimize, claim, vault
schema/           JSON Schema for the report
docs/AUDIT.md     what each check establishes, and what it does not
docs/example-report/  a rendered report, with a note on how it was produced
corpus/           planted defects and their expectations
tests/            unit tests, end-to-end tests, simulated toolchain, vault fixture
../contract/      the auditor/vault interface: docs, schemas, published probe script
```
