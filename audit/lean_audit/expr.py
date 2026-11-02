"""Textual analysis of elaborated (`pp.all`) Lean expressions.

Why textual and not a real parser: the audit must work against whatever Lean
version the client's project pins, without shipping a matched `.olean`-aware
frontend. `pp.all` output is unusually regular (fully explicit `@`-application,
binder annotations on every binder, no notation sugar), which makes a careful
token-level analysis both robust and auditable.

Every function here is deliberately conservative: when the text is ambiguous the
analysis returns "unknown" and the caller is expected to fall back to
`inconclusive` rather than guess.
"""

from __future__ import annotations

import re
from dataclasses import dataclass

# Identifiers: «quoted», dotted global names, plain names, and Lean's internal
# `_uniq.N` renaming for shadowed/hygienic names.
_IDENT_RE = re.compile(r"«[^»]*»|[A-Za-z_][A-Za-z0-9_'!?]*(?:\.[A-Za-z0-9_'!?«»]+)*|_uniq\.\d+")

_UNIVERSE_RE = re.compile(r"^u(_\d+)?$|^v(_\d+)?$|^w(_\d+)?$")

KEYWORDS = {
    "fun", "let", "in", "do", "have", "show", "by", "at", "from",
    "Prop", "Type", "Sort", "forall", "match", "with", "if", "then", "else",
    "trivial", "rfl", "exact", "apply",
}

# Elaborated spellings of notation that hides meaning from a human reader.
# Presence of these in `pp.all` output is not a defect; it is the audit's
# opportunity to show the client what the statement really asserts.
NOTATION_CORE = {
    "HAdd.hAdd": "addition (via the HAdd typeclass)",
    "HMul.hMul": "multiplication (via the HMul typeclass)",
    "HSub.hSub": "subtraction (via the HSub typeclass)",
    "HDiv.hDiv": "division (via the HDiv typeclass)",
    "HMod.hMod": "modulo (via the HMod typeclass)",
    "HPow.hPow": "exponentiation (via the HPow typeclass)",
    "HNeg.hNeg": "negation (via the HNeg typeclass)",
    "OfNat.ofNat": "a numeric literal (via OfNat — note: not necessarily ℕ)",
    "OfScientific.ofScientific": "a decimal literal",
    "Neg.neg": "negation",
    "LE.le": "≤ (via the LE typeclass — resolved by instance, not syntax)",
    "LT.lt": "< (via the LT typeclass — resolved by instance, not syntax)",
    "Dvd.dvd": "∣ divisibility (via Dvd)",
    "Eq": "equality",
    "Ne": "≠ (definitionally ¬ Eq)",
    "Membership.mem": "∈ membership (via Membership — the carrier type is an instance)",
    "Set.MapsTo": "MapsTo",
    "Filter.Tendsto": "Tendsto",
    "MeasureTheory.Measure": "a measure",
}

OPERATOR_TOKENS = ("≤", "≥", "<", ">", "=", "≠", "∧", "∨", "¬", "↔", "→", "∣", "∈", "+", "-", "*", "/", "^")


@dataclass(frozen=True)
class LocalVar:
    name: str


def blank_comments_and_strings(text: str) -> str:
    """Return `text` with comments and string/char literals blanked.

    Length is preserved exactly, so character offsets still address the
    original text. Newlines inside block comments are preserved so line/column
    arithmetic stays valid.
    """
    out = list(text)
    i, n = 0, len(text)
    while i < n:
        c = text[i]
        if c == "-" and text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if c == "/" and text.startswith("/-", i):
            depth = 0
            while i < n:
                if text.startswith("/-", i):
                    depth += 1
                    out[i] = out[i + 1] = " "
                    i += 2
                    continue
                if text.startswith("-/", i):
                    depth -= 1
                    out[i] = out[i + 1] = " "
                    i += 2
                    if depth == 0:
                        break
                    continue
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        if c == '"':
            out[i] = " "
            i += 1
            while i < n:
                if text[i] == "\\":
                    out[i] = " "
                    if i + 1 < n and text[i + 1] != "\n":
                        out[i + 1] = " "
                    i += 2
                    continue
                if text[i] == '"':
                    out[i] = " "
                    i += 1
                    break
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            continue
        if c == "'" and i + 2 < n and text[i + 2] == "'":
            # character literal
            for k in range(3):
                if text[i + k] != "\n":
                    out[i + k] = " "
            i += 3
            continue
        i += 1
    return "".join(out)


def identifiers(text: str) -> list[str]:
    masked = blank_comments_and_strings(text)
    return [m.group(0) for m in _IDENT_RE.finditer(masked)]


def local_vars(text: str) -> set[str]:
    """Best-effort set of locally bound variable names in an expression.

    In `pp.all`, global constants appear either dotted (`Nat.succ`) or
    capitalized (`Nat`, `True`), while locally bound variables print as bare
    lowercase names. Universes print as `u_1`. So: bare lowercase, not a
    keyword, not a universe, not `_uniq.N`.

    Known failure modes (documented, and why mutation confirms before a finding
    is raised): a local variable shadowing a bare lowercase global (e.g. `and`),
    or a local named with a capital. Both are rare and both make this function
    *under*- or *over*-report overlap, never invent a proof.
    """
    out: set[str] = set()
    for name in identifiers(text):
        if name.startswith("_uniq."):
            continue
        if "." in name:
            continue
        if not name or not (name[0].islower() or name[0] == "_"):
            continue
        if name in KEYWORDS or _UNIVERSE_RE.match(name):
            continue
        if name in {"_", "this"}:
            continue
        out.add(name)
    return out


def normalize(text: str) -> str:
    """Canonicalise an expression for equality comparison and fingerprinting."""
    t = blank_comments_and_strings(text)
    t = t.replace("->", "→").replace("=>", "⇒")
    t = re.sub(r"\s+", " ", t).strip()
    # pp.all prefixes applications with '@'; it carries no information for
    # comparison purposes, so drop it to make source-level and pp.all forms
    # comparable.
    t = re.sub(r"(?<![\w.])@(?=[\w«])", "", t)
    return t


def normalize_tokens(text: str) -> tuple[str, ...]:
    return tuple(re.findall(r"«[^»]*»|[A-Za-z_][A-Za-z0-9_'!?.]*|\d+|[^\s\w]", normalize(text)))


def is_trivially_equal(left: str, right: str) -> bool:
    """True when two expression texts are equal up to `pp.all` noise."""
    return normalize_tokens(left) == normalize_tokens(right)


def has_top_level(text: str, needle: str) -> bool:
    """True when `needle` occurs at bracket depth 0 (ignoring (), [], {})."""
    masked = blank_comments_and_strings(text)
    depth = 0
    i = 0
    n = len(masked)
    while i < n:
        c = masked[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and masked.startswith(needle, i):
            return True
        i += 1
    return False


def top_level_index(text: str, needle: str) -> int:
    """Index of the first depth-0 occurrence of `needle`, or -1."""
    masked = blank_comments_and_strings(text)
    depth = 0
    i, n = 0, len(masked)
    while i < n:
        c = masked[i]
        if c in "([{":
            depth += 1
        elif c in ")]}":
            depth = max(0, depth - 1)
        elif depth == 0 and masked.startswith(needle, i):
            return i
        i += 1
    return -1


def match_close(text: str, start: int) -> int:
    """Index of the bracket matching the one at `start`, or -1."""
    masked = blank_comments_and_strings(text)
    pairs = {"(": ")", "[": "]", "{": "}", "⦃": "⦄"}
    opener = masked[start]
    if opener not in pairs:
        return -1
    closer = pairs[opener]
    depth = 0
    for i in range(start, len(masked)):
        c = masked[i]
        if c == opener:
            depth += 1
        elif c == closer:
            depth -= 1
            if depth == 0:
                return i
    return -1


@dataclass
class NotationNote:
    symbol: str
    meaning: str


def notation_notes(text: str) -> list[NotationNote]:
    """Which notation-hidden constants appear in this elaborated expression."""
    seen: list[NotationNote] = []
    idents = set(identifiers(text))
    for const, meaning in NOTATION_CORE.items():
        if const in idents or any(i.endswith("." + const) for i in idents):
            seen.append(NotationNote(const, meaning))
    return seen


def describe_locals(text: str) -> str:
    vars_ = sorted(local_vars(text))
    return ", ".join(vars_) if vars_ else "(closed — no free local variables)"
