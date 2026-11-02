"""Vault manifests: how this auditor consumes a repository that owns a real
Lean 4 toolchain.

A vault publishes one JSON file (`vault.manifest.json`) describing where its
Lean lives, how its project is built, what its corpus contains, and where its
conformance result sits. The auditor reads that file instead of guessing, and
records the vault's identity in every report it produces — so a verdict always
names the environment that produced it.

Nothing here trusts the manifest. Fields are validated, and a manifest that
disagrees with the toolchain actually discovered at runtime produces a
`vault_mismatch` reproducibility finding rather than a quiet downgrade.
"""

from __future__ import annotations

import json
from dataclasses import dataclass, field
from pathlib import Path

CONTRACT_VERSION = "lean-audit-vault/1"


class VaultError(RuntimeError):
    """The vault manifest is missing, unreadable, or not this contract version."""


@dataclass
class VaultCorpusEntry:
    id: str
    path: str
    claim: str | None = None
    expect: str | None = None
    note: str | None = None


@dataclass
class Vault:
    root: Path
    contract_version: str
    name: str = "unnamed-vault"
    repo: str | None = None
    commit: str | None = None
    generated_at: str | None = None
    lean_path: str | None = None
    lean_version: str | None = None
    project_root: str = "."
    build_command: str | None = None
    has_mathlib: bool = False
    packages: list[str] = field(default_factory=list)
    corpus: list[VaultCorpusEntry] = field(default_factory=list)
    conformance_path: str | None = None
    raw: dict = field(default_factory=dict)

    # -- resolution ------------------------------------------------------
    @property
    def project_dir(self) -> Path:
        return (self.root / self.project_root).resolve()

    def corpus_entry(self, corpus_id: str) -> VaultCorpusEntry | None:
        for entry in self.corpus:
            if entry.id == corpus_id:
                return entry
        return None

    def resolve(self, relative: str) -> Path:
        return (self.root / relative).resolve()

    def identity(self) -> dict:
        return {
            "name": self.name,
            "repo": self.repo,
            "commit": self.commit,
            "root": str(self.root),
            "contract_version": self.contract_version,
            "lean_version": self.lean_version,
            "has_mathlib": self.has_mathlib,
            "generated_at": self.generated_at,
        }


MANIFEST_NAMES = ("vault.manifest.json", "vault.json")


def find_manifest(path: str | Path) -> Path:
    root = Path(path).expanduser().resolve()
    if root.is_file():
        return root
    if not root.exists():
        raise VaultError(f"no such vault directory: {root}")
    for name in MANIFEST_NAMES:
        candidate = root / name
        if candidate.exists():
            return candidate
    raise VaultError(
        f"{root} does not look like a vault: expected one of {', '.join(MANIFEST_NAMES)}.\n"
        "Generate one with `python3 contract/vault_conformance.py --project . --out conformance.json` "
        "and publish `vault.manifest.json` (see contract/CONTRACT.md)."
    )


def load_vault(path: str | Path) -> Vault:
    manifest_path = find_manifest(path)
    try:
        raw = json.loads(manifest_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise VaultError(f"could not read {manifest_path}: {exc}") from exc
    if not isinstance(raw, dict):
        raise VaultError(f"{manifest_path}: manifest must be a JSON object")

    version = raw.get("contract_version")
    if version != CONTRACT_VERSION:
        raise VaultError(
            f"{manifest_path}: contract_version is {version!r}, this auditor speaks {CONTRACT_VERSION!r}. "
            "Refusing to audit against a vault whose output shapes are not the ones it validates."
        )

    lean = raw.get("lean") or {}
    project = raw.get("project") or {}
    corpus_raw = raw.get("corpus") or []
    if not isinstance(corpus_raw, list):
        raise VaultError(f"{manifest_path}: `corpus` must be a list")

    corpus: list[VaultCorpusEntry] = []
    for index, entry in enumerate(corpus_raw):
        if not isinstance(entry, dict) or "path" not in entry:
            raise VaultError(f"{manifest_path}: corpus[{index}] needs at least a `path`")
        corpus.append(
            VaultCorpusEntry(
                id=str(entry.get("id") or entry["path"]),
                path=str(entry["path"]),
                claim=entry.get("claim"),
                expect=entry.get("expect"),
                note=entry.get("note"),
            )
        )

    return Vault(
        root=manifest_path.parent,
        contract_version=version,
        name=str(raw.get("name") or manifest_path.parent.name),
        repo=raw.get("repo"),
        commit=raw.get("commit"),
        generated_at=raw.get("generated_at"),
        lean_path=lean.get("path"),
        lean_version=lean.get("version"),
        project_root=str(project.get("root") or "."),
        build_command=project.get("build_command"),
        has_mathlib=bool(project.get("has_mathlib")),
        packages=list(project.get("packages") or []),
        corpus=corpus,
        conformance_path=raw.get("conformance"),
        raw=raw,
    )


def load_conformance(vault: Vault) -> dict | None:
    """Read the vault's published conformance result, if it shipped one."""
    rel = vault.conformance_path or "conformance.json"
    path = vault.resolve(rel)
    if not path.exists():
        return None
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return None


def version_matches(declared: str | None, discovered: str | None) -> bool | None:
    """Compare the manifest's Lean version with the one actually discovered.

    Returns None when either side is unknown, so callers can distinguish
    "agrees" from "cannot tell".
    """
    import re

    if not declared or not discovered:
        return None

    def key(text: str) -> tuple[int, ...] | None:
        match = re.search(r"(\d+)\.(\d+)\.(\d+)", text)
        return tuple(int(g) for g in match.groups()) if match else None

    left, right = key(declared), key(discovered)
    if left is None or right is None:
        return None
    return left == right
