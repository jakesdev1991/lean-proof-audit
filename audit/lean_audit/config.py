"""Audit policy. Anything a client might reasonably disagree with is configurable
and is echoed into the report so the verdict is self-describing."""

from __future__ import annotations

from dataclasses import dataclass, field

# Axioms that Lean's own logic and Mathlib rely on. A proof depending on these
# is as sound as Lean itself; depending on anything else is an assumption the
# client is making, whether or not they know it.
STANDARD_AXIOMS = ("propext", "Classical.choice", "Quot.sound")

# Axioms introduced by trusting the compiler rather than the kernel.
COMPILER_TRUST_AXIOMS = ("Lean.ofReduceBool", "Lean.trustCompiler", "Lean.trustLevel")

# The axiom every `sorry`/`admit` elaborates to.
HOLE_AXIOMS = ("sorryAx",)


@dataclass
class Config:
    timeout: float = 300.0
    allow_axioms: tuple[str, ...] = STANDARD_AXIOMS
    allow_compiler_trust: bool = False
    max_mutants: int = 40
    mutant_timeout: float = 120.0
    enabled_checks: tuple[str, ...] | None = None
    claim_path: str | None = None
    strict: bool = False
    keep_workdir: bool = False

    def to_dict(self) -> dict:
        return {
            "timeout_seconds": self.timeout,
            "allowed_axioms": list(self.allow_axioms),
            "allow_compiler_trust": self.allow_compiler_trust,
            "max_mutants": self.max_mutants,
            "mutant_timeout_seconds": self.mutant_timeout,
            "checks": list(self.enabled_checks) if self.enabled_checks else "all",
            "strict": self.strict,
        }
