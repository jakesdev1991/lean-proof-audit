# lean-audit ⟷ vault contract `lean-audit-vault/1`

Two repositories, two agents, one real Lean 4 toolchain.

* **`lean-proof-audit`** (this repo) — the auditor. Parses Lean output, so it is
  sensitive to output format.
* **`audit-vault`** — the vault. Owns the real Lean toolchain, the built Lake
  project, and the corpus.

The auditor cannot see inside the vault, and must not assume what Lean prints.
So the two sides agree on **four artifacts** and the auditor validates all of
them mechanically. A document nobody executes is a wish; a probe that fails is a
finding.

---

## The four artifacts

### 1. `vault.manifest.json` (the vault publishes, the auditor reads)

Declares identity and layout. Validated on load; a wrong
`contract_version` is refused outright rather than half-honoured.

```json
{
  "contract_version": "lean-audit-vault/1",
  "name": "audit-vault",
  "repo": "https://github.com/jakesdev1991/audit-vault",
  "commit": "<git rev-parse HEAD>",
  "lean": { "path": "/home/user/.elan/bin/lean", "version": "Lean (version 4.36.0, …)" },
  "project": { "root": ".", "build_command": "lake build", "has_mathlib": true, "packages": ["mathlib"] },
  "corpus": [
    { "id": "splitting", "path": "Corpus/Splitting.lean", "claim": "Corpus/Splitting.claim.json", "expect": "fail" }
  ],
  "capabilities": { "decide_refutation": true },
  "conformance": "conformance.json"
}
```

| Field | Why the auditor needs it |
| --- | --- |
| `lean.path`, `lean.version` | A version that disagrees with the toolchain actually discovered becomes a `vault_lean_version_mismatch` **high** reproducibility finding. Without a pinned version the report is not reproducible. |
| `project.root` | Audits run under `lake env lean`, so the client's imports resolve. An unbuilt project otherwise looks like a broken proof. |
| `corpus[].path` | Named targets, so "audit corpus item X" is a stable reference rather than a path plus a memory. |
| `corpus[].claim` | Points at the claim file, so correspondence to the intended claim can be checked. |
| `corpus[].expect` | Enables the vault to assert the *expected verdict*, turning a re-audit into a regression test. |
| `capabilities` | Lets the auditor say "this environment cannot test vacuity" instead of implying it found none. |

### 2. `conformance.json` (the vault publishes, the auditor reads)

Output of `vault_conformance.py`. Its `capabilities` map controls whether the
auditor may claim a result at all:

| capability | Gates | If false, the auditor reports |
| --- | --- | --- |
| `axiom_query` | `#print axioms` parsing | `trust` is inconclusive, never "clean" |
| `diagnostics` | `file:line:col: error:` parsing | findings cannot be attributed to declarations |
| `pp_all` | `set_option pp.all true` + `#check` | `statements` cannot recover the elaborated type |
| `decide_refutation` | `by decide` on a negated goal | `refutation_probe_unavailable` — vacuity is *untested*, not clean |
| `olean_out` | `lean -o <path>` | artifacts would land in the client's tree |
| `lake_env` | `lake env lean` | project imports unverified |
| `mathlib` | `import Mathlib` | Mathlib-dependent files cannot be audited |

### 3. The audit report (the auditor publishes, the vault can consume)

Produced by `lean-audit audit … --json`. Schema:
[`lean-proof-audit/audit/schema/audit-report.schema.json`](https://github.com/jakesdev1991/lean-proof-audit/blob/main/audit/schema/audit-report.schema.json).
It echoes the vault's identity under `environment.vault`, so a verdict always
names the environment that produced it.

### 4. `vault_conformance.py` (shared, byte-identical)

The probe script. It lives at `audit/lean_audit/conformance_probe.py` in the
auditor and is copied verbatim to `contract/vault_conformance.py` by
`make publish-contract`. A test fails if the copies diverge. It imports nothing
from the auditor and needs nothing but Python 3 and Lean.

---

## Who runs what

**Vault side, once, and again whenever Lean or the corpus changes:**

```bash
python3 conformance_probe.py --project . --out conformance.json
git rev-parse HEAD   # put it in vault.manifest.json
git add vault.manifest.json conformance.json corpus/ && git commit -m "vault: bump conformance"
```

**Auditor side, per audit:**

```bash
lean-audit vault ../audit-vault              # identity + capabilities + corpus
lean-audit audit ../audit-vault/Corpus/Splitting.lean --vault ../audit-vault \
    --markdown report.md --json report.json
```

**Both sides, when something breaks:**

```bash
python3 conformance_probe.py --project . --json   # which probe fails, and what it observed
```

---

## Rules

1. **Never downgrade a failure to a skip.** A probe that cannot run is
   `skipped`, and a skipped *required* probe makes the vault incompatible.
2. **`required` is the auditor's call.** The vault may not mark a probe optional
   to make itself compatible.
3. **Changing a probe ID or an expected output shape is a contract version bump**
   (`lean-audit-vault/2`). The auditor refuses unknown versions by design.
4. **Provenance is not optional.** A report with an unpinned Lean version is a
   reproduction hazard, and is reported as one.
5. **The simulator in `audit/tests/fakelean/` is never evidence.** It validates
   the pipeline; it establishes nothing about Lean. Any capability claim that
   matters must come from `conformance.json` produced against real Lean.

---

## Current status

| Side | State |
| --- | --- |
| `lean-proof-audit` | Contract implemented: `lean-audit conform`, `lean-audit vault`, `--vault`, `vault` check, capability-driven degradation. Tested against the simulated toolchain only. |
| `audit-vault` | **Unknown to this agent** — the repository is private and this agent's GitHub token cannot read it (403). Nothing in this contract has been validated against the vault's actual contents; the probes exist precisely because the author could not inspect it. |

The first real interaction will be the vault agent publishing
`vault.manifest.json` + `conformance.json`. If any probe fails there, that is
the auditor discovering an assumption it got wrong — which is the point of the
handshake rather than a flaw in it.
