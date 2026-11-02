"""Core data model shared by every check.

Findings carry their own evidence so that a report can be defended line by line
after the fact. A finding without evidence is a bug in the check.
"""

from __future__ import annotations

import dataclasses
import enum
import hashlib
import json
import time
from dataclasses import dataclass, field
from typing import Any


class Severity(str, enum.Enum):
    INFO = "info"
    LOW = "low"
    MEDIUM = "medium"
    HIGH = "high"
    CRITICAL = "critical"

    @property
    def rank(self) -> int:
        return _SEV_RANK[self]


_SEV_RANK = {
    Severity.INFO: 0,
    Severity.LOW: 1,
    Severity.MEDIUM: 2,
    Severity.HIGH: 3,
    Severity.CRITICAL: 4,
}


class Verdict(str, enum.Enum):
    PASS = "pass"
    WARN = "warn"
    FAIL = "fail"
    INCONCLUSIVE = "inconclusive"
    SKIPPED = "skipped"

    @property
    def rank(self) -> int:
        return _VERDICT_RANK[self]


_VERDICT_RANK = {
    Verdict.SKIPPED: -1,
    Verdict.PASS: 0,
    Verdict.INCONCLUSIVE: 1,
    Verdict.WARN: 2,
    Verdict.FAIL: 3,
}


class Category(str, enum.Enum):
    """Which of the three questions a finding bears on.

    SOUNDNESS  - is there a real proof of the statement as written?
    STATEMENT  - does the statement say what the claimant thinks it says?
    DEPENDENCE - does the proof actually use the stated hypotheses/conclusion?
    REPRODUCIBILITY - can this verdict be re-derived from the recorded evidence?
    """

    SOUNDNESS = "soundness"
    STATEMENT = "statement"
    DEPENDENCE = "dependence"
    REPRODUCIBILITY = "reproducibility"


class Confidence(str, enum.Enum):
    PROVEN = "proven"        # backed by a Lean run recorded in evidence
    HEURISTIC = "heuristic"  # static analysis only; needs confirmation
    HEURISTIC_CONFIRMED = "heuristic_confirmed"  # static proposal + Lean run


@dataclass
class SourceSpan:
    file: str
    start_line: int
    start_col: int
    end_line: int
    end_col: int

    def to_dict(self) -> dict[str, Any]:
        return {
            "file": self.file,
            "start": {"line": self.start_line, "col": self.start_col},
            "end": {"line": self.end_line, "col": self.end_col},
        }

    def render(self) -> str:
        if self.start_line == self.end_line:
            return f"{self.file}:{self.start_line}:{self.start_col}"
        return f"{self.file}:{self.start_line}-{self.end_line}"


@dataclass
class Evidence:
    """A single, re-checkable observation supporting a finding."""

    kind: str  # lean_run | source | probe | statement
    summary: str
    command: list[str] | None = None
    stdout: str | None = None
    stderr: str | None = None
    exit_code: int | None = None
    exit_status: str | None = None  # ok | timeout | error | crashed
    duration_ms: int | None = None
    location: SourceSpan | None = None
    # The exact source fed to Lean, so a third party can replay it byte for byte.
    input_text: str | None = None
    digest: str | None = None

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {"kind": self.kind, "summary": self.summary}
        for key in ("command", "exit_code", "exit_status", "duration_ms"):
            val = getattr(self, key)
            if val is not None:
                d[key] = val
        for key in ("stdout", "stderr"):
            val = getattr(self, key)
            if val is not None:
                d[key] = _trim(val)
        if self.location is not None:
            d["location"] = self.location.to_dict()
        if self.input_text is not None:
            d["input_sha256"] = hashlib.sha256(
                self.input_text.encode("utf-8")
            ).hexdigest()
            d["input"] = _trim(self.input_text)
        if self.digest:
            d["digest"] = self.digest
        return d


@dataclass
class Finding:
    check: str
    code: str
    severity: Severity
    category: Category
    confidence: Confidence
    title: str
    detail: str
    declaration: str | None = None
    location: SourceSpan | None = None
    remediation: str | None = None
    evidence: list[Evidence] = field(default_factory=list)

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "check": self.check,
            "code": self.code,
            "severity": self.severity.value,
            "category": self.category.value,
            "confidence": self.confidence.value,
            "title": self.title,
            "detail": self.detail,
        }
        if self.declaration:
            d["declaration"] = self.declaration
        if self.location is not None:
            d["location"] = self.location.to_dict()
        if self.remediation:
            d["remediation"] = self.remediation
        d["evidence"] = [e.to_dict() for e in self.evidence]
        return d

    def key(self) -> str:
        return f"{self.code}:{self.declaration or ''}:{self.location.render() if self.location else ''}"


@dataclass
class CheckResult:
    name: str
    verdict: Verdict
    summary: str
    findings: list[Finding] = field(default_factory=list)
    data: dict[str, Any] = field(default_factory=dict)
    duration_ms: int = 0
    skip_reason: str | None = None

    def to_dict(self) -> dict[str, Any]:
        d: dict[str, Any] = {
            "name": self.name,
            "verdict": self.verdict.value,
            "summary": self.summary,
            "duration_ms": self.duration_ms,
            "findings": [f.to_dict() for f in self.findings],
        }
        if self.data:
            d["data"] = self.data
        if self.skip_reason:
            d["skip_reason"] = self.skip_reason
        return d

    @property
    def worst_severity(self) -> Severity | None:
        if not self.findings:
            return None
        return max((f.severity for f in self.findings), key=lambda s: s.rank)


def _trim(text: str, limit: int = 20000) -> str:
    if len(text) <= limit:
        return text
    return text[:limit] + f"\n… [truncated {len(text) - limit} chars]"


def worst_verdict(verdicts: list[Verdict]) -> Verdict:
    live = [v for v in verdicts if v is not Verdict.SKIPPED]
    if not live:
        return Verdict.SKIPPED
    return max(live, key=lambda v: v.rank)


def now_ms() -> int:
    return int(time.time() * 1000)
