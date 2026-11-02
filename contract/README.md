# Contract artifacts

| File | Role | Editable by hand? |
| --- | --- | --- |
| [`CONTRACT.md`](CONTRACT.md) | The interface: artifacts, obligations, rules | yes |
| [`FOR-THE-VAULT-AGENT.md`](FOR-THE-VAULT-AGENT.md) | Copy-paste instructions for the agent that runs `audit-vault` | yes |
| [`vault_conformance.py`](vault_conformance.py) | The probe script both sides run | **no — generated** |
| [`vault.schema.json`](vault.schema.json) | JSON Schema for `vault.manifest.json` | yes |
| [`conformance.schema.json`](conformance.schema.json) | JSON Schema for `conformance.json` | yes |

`vault_conformance.py` is a verbatim copy of
`audit/lean_audit/conformance_probe.py`. Regenerate it with:

```bash
cd audit && make publish-contract
```

`make test` fails if the copy drifts from the source, so the two agents can
never end up running different probes under the same contract version.
