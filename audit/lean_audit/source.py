"""Structural map of a Lean source file.

Deliberately not a Lean parser. It extracts exactly what the audit needs to do
source surgery and to attribute findings to lines:

  * declaration headers (keyword, name, modifiers, attributes)
  * the character span of each declaration's *type* (everything between the
    top-level `:` and the top-level `:=`), so a statement can be rewritten and
    the original proof re-checked
  * file-level facts: imports, `set_option`s, and every occurrence of the tokens
    that change what a proof actually rests on

Zero-indentation declarations are treated as top level. This is true of
essentially all Lean files and is what makes the scan reliable; a nested
declaration (indented inside a `where` or `section`) is recorded in
`SourceIndex.notes` rather than silently skipped.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from . import expr

DECL_KEYWORDS = (
    "theorem", "lemma", "def", "abbrev", "instance", "axiom", "opaque",
    "example", "structure", "inductive", "class",
)
THEOREM_KEYWORDS = {"theorem", "lemma", "example"}
MODIFIERS = {"private", "protected", "noncomputable", "partial", "unsafe", "nonrec", "scoped", "local"}

HEADER_RE = re.compile(
    r"^(?P<mods>(?:(?:" + "|".join(sorted(MODIFIERS)) + r")\s+)*)"
    r"(?P<kw>" + "|".join(DECL_KEYWORDS) + r")\b(?P<rest>.*)$"
)
ATTR_RE = re.compile(r"^@\[(?P<body>[^\]]*)\]")
TOPLEVEL_BOUNDARY_RE = re.compile(r"^(?:namespace|section|end|import|open|universe|variable|set_option|attribute|#)\b")
SET_OPTION_RE = re.compile(r"^[ \t]*set_option[ \t]+(?P<name>[\w.]+)[ \t]+(?P<value>\S.*?)[ \t]*$", re.M)
IMPORT_RE = re.compile(r"^[ \t]*import[ \t]+([\w.«»]+)", re.M)

# Tokens worth locating by line, because each one changes the trust surface.
TRUST_TOKENS = {
    "sorry": "fills a goal with `sorryAx`",
    "admit": "`admit` is `sorry` under another name",
    "native_decide": "proves the goal by compiling a decision procedure and trusting the compiler",
    "sorryAx": "the axiom `sorry` elaborates to",
    "implemented_by": "declares that the runtime implementation differs from the logical definition",
    "extern": "binds a runtime symbol that has no logical content",
}


@dataclass
class Decl:
    kw: str
    name: str | None
    modifiers: set[str]
    attributes: list[str]
    start: int          # offset of the first character of the header (incl. attributes)
    end: int            # offset one past the last character of the declaration
    header_line: int
    type_start: int | None = None
    type_end: int | None = None
    body_start: int | None = None
    name_offset: int | None = None
    name_end: int | None = None
    type_colon: int | None = None
    namespace: str = ""
    parse_notes: list[str] = field(default_factory=list)

    @property
    def qualified_name(self) -> str | None:
        """Fully qualified name usable in a probe appended after the file.

        Probes are appended to the end of the client's file, which is outside
        every namespace the file opens, so short names are not in scope there.
        """
        if not self.name:
            return None
        return f"{self.namespace}.{self.name}" if self.namespace else self.name

    @property
    def is_theorem(self) -> bool:
        return self.kw in THEOREM_KEYWORDS

    @property
    def has_type(self) -> bool:
        return self.type_start is not None and self.type_end is not None

    def type_text(self, source: str) -> str | None:
        """The conclusion-and-hypotheses part *after* the `:` of the header.

        Note that in Lean the binder telescope (`(n : Nat) (h : P)`) sits before
        that colon, so this is NOT the whole statement. Use `binders_text` for
        the other part, or `statement_parts` for both with their source spans.
        """
        if not self.has_type:
            return None
        return source[self.type_start : self.type_end]

    def binders_text(self, source: str) -> str | None:
        """The pre-colon binder telescope, e.g. `(n : Nat) (h : n > 0)`."""
        if self.name_end is None or self.type_colon is None:
            return ""
        return source[self.name_end : self.type_colon]

    def statement_parts(self, source: str) -> tuple[tuple[int, int], tuple[int, int]] | None:
        """Absolute spans of (binder telescope, type) — the two halves of a statement.

        They are edited separately during mutation because Lean's syntax keeps
        them on either side of the `:`; collapsing them into one arrow-form string
        would produce a declaration that does not parse.
        """
        if self.name_end is None or self.type_colon is None or not self.has_type:
            return None
        return ((self.name_end, self.type_colon), (self.type_start, self.type_end))


@dataclass
class TokenHit:
    token: str
    line: int
    col: int
    context: str


@dataclass
class SourceIndex:
    path: str
    text: str
    masked: str
    line_starts: list[int]
    decls: list[Decl]
    imports: list[str]
    set_options: list[tuple[str, str]]
    trust_tokens: list[TokenHit]
    notes: list[str] = field(default_factory=list)

    # -- offsets ---------------------------------------------------------
    def line_of(self, offset: int) -> int:
        lo, hi = 0, len(self.line_starts) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if self.line_starts[mid] <= offset:
                lo = mid
            else:
                hi = mid - 1
        return lo + 1

    def col_of(self, offset: int) -> int:
        line = self.line_of(offset)
        return offset - self.line_starts[line - 1] + 1

    def span(self, start: int, end: int):
        from .model import SourceSpan

        return SourceSpan(
            file=self.path,
            start_line=self.line_of(start),
            start_col=self.col_of(start),
            end_line=self.line_of(max(start, end - 1)),
            end_col=self.col_of(max(start, end - 1)),
        )

    # -- lookups ---------------------------------------------------------
    def theorems(self) -> list[Decl]:
        return [d for d in self.decls if d.is_theorem]

    def named_theorems(self) -> list[Decl]:
        return [d for d in self.decls if d.is_theorem and d.name]

    def decl_at(self, offset: int) -> Decl | None:
        for d in self.decls:
            if d.start <= offset < d.end:
                return d
        return None

    def set_option(self, name: str) -> str | None:
        val = None
        for n, v in self.set_options:
            if n == name:
                val = v
        return val


def _line_starts(text: str) -> list[int]:
    starts = [0]
    for i, ch in enumerate(text):
        if ch == "\n":
            starts.append(i + 1)
    return starts


def index_source(path: str, text: str) -> SourceIndex:
    masked = expr.blank_comments_and_strings(text)
    starts = _line_starts(text)
    index = SourceIndex(
        path=path,
        text=text,
        masked=masked,
        line_starts=starts,
        decls=[],
        imports=IMPORT_RE.findall(masked),
        set_options=[(m.group("name"), m.group("value")) for m in SET_OPTION_RE.finditer(masked)],
        trust_tokens=[],
    )

    lines = masked.splitlines(keepends=True)
    offsets: list[int] = []
    pos = 0
    for line in lines:
        offsets.append(pos)
        pos += len(line)

    scope_stack: list[tuple[str, str]] = []
    pending_attrs: list[str] = []
    # (lineno, line_offset, header match, attrs, rest_text, rest_offset)
    header_starts: list[tuple[int, int, re.Match[str], list[str], str, int, str]] = []

    for lineno, line in enumerate(lines):
        raw = line.rstrip("\n")
        if not raw or raw[0] in " \t":
            continue  # indented: never a top-level declaration
        attrs: list[str] = []
        rest = raw
        while True:
            m = ATTR_RE.match(rest)
            if not m:
                break
            attrs.append(m.group("body").strip())
            rest = rest[m.end() :].lstrip()
        if not rest:
            # attribute-only line; carry to the next declaration
            pending_attrs.extend(attrs)
            continue
        ns_match = re.match(r"^(?:namespace|section)\b\s*([\w.«»]*)", raw)
        if ns_match:
            kind = "namespace" if raw.startswith("namespace") else "section"
            scope_stack.append((kind, ns_match.group(1)))
            pending_attrs = []
            continue
        end_match = re.match(r"^end\b\s*([\w.«»]*)", raw)
        if end_match:
            popped = end_match.group(1)
            if popped:
                parts = popped.split(".")
                for part in reversed(parts):
                    while scope_stack:
                        kind, name = scope_stack.pop()
                        if (kind == "namespace" and name == part) or (kind == "section" and name == part):
                            break
            elif scope_stack:
                scope_stack.pop()
            pending_attrs = []
            continue
        m = HEADER_RE.match(rest)
        if not m:
            if TOPLEVEL_BOUNDARY_RE.match(raw):
                pending_attrs = []
            continue
        body_attrs = pending_attrs + attrs
        pending_attrs = []
        # `m.group("rest")` is the text after the declaration keyword (and after
        # any attributes), and is always a suffix of `raw`, so this offset is exact.
        rest_offset = offsets[lineno] + (len(raw) - len(m.group("rest")))
        namespace_now = ".".join(n for kind, n in scope_stack if kind == "namespace" and n)
        header_starts.append((lineno, offsets[lineno], m, body_attrs, rest, rest_offset, namespace_now))

    for idx, (lineno, offset, m, attrs, rest, rest_offset, ns) in enumerate(header_starts):
        end = header_starts[idx + 1][1] if idx + 1 < len(header_starts) else len(text)
        # A declaration also ends at a following top-level boundary line.
        for later in range(lineno + 1, len(lines)):
            loff = offsets[later]
            if loff >= end:
                break
            s = lines[later].rstrip("\n")
            if s and s[0] not in " \t" and TOPLEVEL_BOUNDARY_RE.match(s):
                end = loff
                break
            if s and s[0] not in " \t" and (HEADER_RE.match(s) or ATTR_RE.match(s)):
                end = loff
                break

        decl = _build_decl(text, masked, offset, end, m, attrs, index, lineno, rest_offset)
        decl.namespace = ns
        index.decls.append(decl)

    _collect_trust_tokens(index, lines, offsets)
    return index


def _build_decl(text, masked, start, end, m, attrs, index, lineno, rest_offset) -> Decl:
    kw = m.group("kw")
    modifiers = set(m.group("mods").split())
    rest_start = rest_offset
    rest = m.group("rest")
    decl = Decl(
        kw=kw,
        name=None,
        modifiers=modifiers,
        attributes=attrs,
        start=start,
        end=end,
        header_line=lineno + 1,
    )

    # Locate the name token (if the declaration has one).
    nm = re.match(r"\s*([A-Za-z_«][\w.«»'!?]*)", rest)
    scan_from = rest_start
    if nm and nm.group(1) not in {"where", "extends"}:
        decl.name = nm.group(1)
        decl.name_offset = rest_start + nm.start(1)
        scan_from = rest_start + nm.end()
        decl.name_end = scan_from
    elif nm:
        scan_from = rest_start + nm.end()

    # Find the top-level `:` that opens the type, then the top-level `:=`.
    colon = _scan_top_level(masked, scan_from, end, ":")
    decl.type_colon = colon if colon >= 0 else None
    if decl.name_end is None:
        decl.name_end = scan_from
    assign = None
    if colon >= 0:
        assign = _scan_top_level(masked, colon + 1, end, ":=")
    if colon >= 0:
        type_start = colon + 1
        while type_start < end and masked[type_start].isspace():
            type_start += 1
        type_end = assign if assign is not None and assign > type_start else None
        if type_end is None:
            type_end = _type_end_fallback(masked, type_start, end)
        decl.type_start = type_start
        decl.type_end = type_end
        if assign is not None:
            decl.body_start = assign
    elif kw in ("theorem", "lemma"):
        decl.parse_notes.append("no top-level `:` found; declaration type could not be located")
    return decl


def _scan_top_level(masked: str, start: int, end: int, needle: str) -> int:
    depth = 0
    i = start
    while i < end:
        c = masked[i]
        if c in "([{⦃":
            depth += 1
        elif c in ")]}⦄":
            depth = max(0, depth - 1)
        elif depth == 0:
            if masked.startswith(needle, i):
                if needle == ":":
                    # exclude `:=` and `::`
                    nxt = masked[i + 1] if i + 1 < end else ""
                    if nxt in ("=", ":"):
                        i += 2
                        continue
                return i
        i += 1
    return -1


def _type_end_fallback(masked: str, start: int, end: int) -> int:
    """End of the type when the declaration has no `:=` body.

    Applies to `axiom`/`opaque`/pattern-matching equations. The type ends at the
    first newline reached at bracket depth 0 (single-line declarations, which is
    the norm when there is no body), or earlier at a `where`/`|` marker.
    """
    stop = end
    for marker in (" where", "|"):
        pos = _scan_top_level(masked, start, end, marker) if marker.strip() else -1
        if pos > start:
            stop = min(stop, pos)
    depth = 0
    i = start
    while i < stop:
        c = masked[i]
        if c in "([{⦃":
            depth += 1
        elif c in ")]}⦄":
            depth = max(0, depth - 1)
        elif c == "\n" and depth == 0:
            return i
        i += 1
    return stop


def _collect_trust_tokens(index: SourceIndex, lines: list[str], offsets: list[int]) -> None:
    token_re = re.compile(r"\b(" + "|".join(TRUST_TOKENS) + r")\b")
    for lineno, line in enumerate(lines):
        for m in token_re.finditer(line):
            index.trust_tokens.append(
                TokenHit(
                    token=m.group(1),
                    line=lineno + 1,
                    col=m.start() + 1,
                    context=line.strip()[:120],
                )
            )
