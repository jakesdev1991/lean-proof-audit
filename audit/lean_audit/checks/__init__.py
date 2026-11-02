"""Check registry.

A check is a function `run(ctx) -> CheckResult`. Checks must never raise: a
crashing check means the audit is incomplete, and an incomplete audit must
surface as `inconclusive` rather than as a clean bill of health.
"""

from __future__ import annotations

import traceback
from dataclasses import dataclass, field
from pathlib import Path

from ..config import Config
from ..lean import LeanRunner, Toolchain
from ..model import CheckResult, Verdict
from ..source import SourceIndex


@dataclass
class AuditContext:
    target: Path
    source: str
    index: SourceIndex
    toolchain: Toolchain
    runner: LeanRunner
    config: Config
    project_dir: Path | None = None
    cache: dict = field(default_factory=dict)
    notes: list[str] = field(default_factory=list)
    # Set when the audit runs against a vault (a repo owning a real toolchain).
    vault: object | None = None
    # Capabilities declared by the vault's conformance run. An explicit False
    # means "this environment cannot answer that question", which a check must
    # report rather than interpret as a negative result.
    capabilities: dict = field(default_factory=dict)

    @property
    def theorems(self):
        return self.index.named_theorems()


REGISTRY: list[tuple[str, str]] = [
    ("build", "kernel compilation of the file under audit"),
    ("trust", "axiom and trust surface of every theorem"),
    ("statements", "statement-level honesty: vacuity, empty domains, autoImplicit"),
    ("dependence", "mutation testing: which hypotheses the proof actually uses"),
    ("minimize", "minimal failing fragment when the build fails"),
    ("claim", "formal statement vs. the claim the client supplied"),
    ("vault", "environment provenance: does this run match the vault it claims?"),
]


def load_checks():
    from . import build, claim, dependence, minimize, statements, trust, vaultcheck

    return {
        "build": build.run,
        "trust": trust.run,
        "statements": statements.run,
        "dependence": dependence.run,
        "minimize": minimize.run,
        "claim": claim.run,
        "vault": vaultcheck.run,
    }


def run_all(ctx: AuditContext) -> list[CheckResult]:
    funcs = load_checks()
    selected = ctx.config.enabled_checks or tuple(funcs)
    results: list[CheckResult] = []
    for name, _desc in REGISTRY:
        if name not in selected:
            results.append(
                CheckResult(
                    name=name,
                    verdict=Verdict.SKIPPED,
                    summary="check not selected",
                    skip_reason="not in --checks",
                )
            )
            continue
        fn = funcs[name]
        try:
            results.append(fn(ctx))
        except Exception as exc:  # noqa: BLE001 - a crashing check must not fail the audit
            results.append(
                CheckResult(
                    name=name,
                    verdict=Verdict.INCONCLUSIVE,
                    summary=f"check crashed: {type(exc).__name__}: {exc}",
                    skip_reason=traceback.format_exc(limit=6),
                )
            )
    return results
