"""Split a Lean type into an ordered binder telescope plus a conclusion.

Input is either

  * a fully elaborated type from `set_option pp.all true; #check @name`
    (authoritative: implicit binders, instance binders, notation expanded), or
  * the type as written in the source file
    (needed for source surgery, i.e. mutation testing).

The grammar actually needed is small, because `pp.all` fully parenthesises:

    type      ::= binder* body
    binder    ::= '∀' group+ ','
                | group ('→' | ',')?
                | body '→'            (anonymous binder, e.g. `P → Q`)
    group     ::= '(' name ':' type ')' | '{' ... '}' | '[' ... ']'

Precondition: the type being parsed is a **theorem statement**, i.e. Prop-valued
(all uses in this package are on `theorem`/`lemma` declarations). Under that
precondition every depth-0 arrow is a hypothesis rather than a function-returning-
function, which is what licenses the anonymous-binder rule below. Do not reuse
this parser on the type of a general `def`.

Anything this module cannot classify raises no exception and invents no binder:
it is recorded in `notes` and the affected statement is marked `parse_ok =
False`, which downstream checks must treat as "cannot conclude", never as
"nothing wrong found".
"""

from __future__ import annotations

from dataclasses import dataclass, field

from . import expr

BINDER_OPENERS = {"(": "explicit", "{": "implicit", "[": "instance", "⦃": "strict_implicit"}


@dataclass
class Binder:
    name: str | None
    kind: str  # explicit | implicit | instance | strict_implicit
    type_text: str
    raw: str
    span: tuple[int, int] | None = None

    @property
    def anonymous(self) -> bool:
        return self.name is None


@dataclass
class ParsedStatement:
    raw: str
    binders: list[Binder] = field(default_factory=list)
    conclusion: str = ""
    conclusion_span: tuple[int, int] | None = None
    notes: list[str] = field(default_factory=list)

    @property
    def parse_ok(self) -> bool:
        return not self.notes

    @property
    def explicit_binders(self) -> list[Binder]:
        return [b for b in self.binders if b.kind == "explicit"]

    def binder(self, name: str) -> Binder | None:
        for b in self.binders:
            if b.name == name:
                return b
        return None

    def render_telescope(self, max_width: int | None = None) -> list[str]:
        lines = []
        for b in self.binders:
            prefix = {"explicit": "", "implicit": "implicit ", "instance": "instance ", "strict_implicit": "implicit "}[b.kind]
            nm = b.name if b.name else "_"
            lines.append(f"{prefix}({nm} : {_short(b.type_text, max_width)})")
        if self.conclusion:
            lines.append(f"⊢ {_short(self.conclusion, max_width)}")
        return lines


def _short(text: str, width: int | None) -> str:
    flat = " ".join(text.split())
    if width is None or len(flat) <= width:
        return flat
    return flat[: width - 1] + "…"


def parse_telescope(text: str) -> ParsedStatement:
    s = text
    n = len(s)
    masked = expr.blank_comments_and_strings(s)
    stmt = ParsedStatement(raw=s)
    i = 0

    def skip_ws(pos: int) -> int:
        while pos < n and masked[pos].isspace():
            pos += 1
        return pos

    def finish(pos: int) -> ParsedStatement:
        start = skip_ws(pos)
        body = s[start:].strip()
        end = start + len(s[start:].rstrip())
        stmt.conclusion = body
        stmt.conclusion_span = (start, end) if body else None
        return stmt

    while True:
        i = skip_ws(i)
        if i >= n:
            return finish(i)
        c = masked[i]

        # ---- ∀ (x : T) (y : U), body ----
        if c == "∀" or masked.startswith("forall", i):
            i += 1 if c == "∀" else len("forall")
            binders_before = len(stmt.binders)
            while True:
                i = skip_ws(i)
                if i >= n:
                    stmt.notes.append("forall without body")
                    return finish(i)
                if masked[i] == ",":
                    if len(stmt.binders) == binders_before:
                        stmt.notes.append("quantifier with an empty binder list")
                        return finish(i)
                    i += 1
                    break
                if masked[i] in BINDER_OPENERS:
                    close = expr.match_close(s, i)
                    if close < 0:
                        stmt.notes.append(f"unbalanced bracket at offset {i}")
                        return finish(i)
                    binder = _parse_group(s, i, close)
                    if binder is None:
                        stmt.notes.append(f"forall binder is not `name : type`: {s[i:close + 1]!r}")
                        return finish(i)
                    stmt.binders.append(binder)
                    i = close + 1
                    continue
                stmt.notes.append(f"unexpected token in forall binder list at offset {i}")
                return finish(i)
            continue

        # ---- explicit / implicit / instance binder group ----
        if c in BINDER_OPENERS:
            close = expr.match_close(s, i)
            if close < 0:
                stmt.notes.append(f"unbalanced bracket at offset {i}")
                return finish(i)
            inner = s[i + 1 : close]
            after = skip_ws(close + 1)
            nxt = masked[after] if after < n else ""
            followed_by_arrow = nxt == "→" or masked.startswith("->", after)
            followed_by_more = followed_by_arrow or nxt in (",", "(", "{", "[", "⦃")
            if expr.top_level_index(inner, ":") >= 0 and followed_by_more:
                binder = _parse_group(s, i, close)
                if binder is None:
                    stmt.notes.append(f"malformed binder: {s[i:close + 1]!r}")
                    return finish(i)
                stmt.binders.append(binder)
                if nxt == "→":
                    i = after + 1
                elif masked.startswith("->", after):
                    i = after + 2
                elif nxt == ",":
                    i = after + 1
                else:
                    i = after
                continue
            if followed_by_arrow:
                # Unnamed hypothesis written as a bracketed type: `(P) → Q`.
                # In a theorem statement this is a hypothesis, not a function
                # return type (see module docstring).
                stmt.binders.append(
                    Binder(
                        name=None,
                        kind="explicit",
                        type_text=inner.strip(),
                        raw=s[i : close + 1],
                        span=(i, close + 1),
                    )
                )
                i = after + (1 if nxt == "→" else 2)
                continue
            # a parenthesised type that ends the telescope: it is the conclusion
            return finish(i)

        # ---- anonymous binder: `P → Q` ----
        if c == "→" or masked.startswith("->", i):
            # stray arrow (e.g. type started mid-expression); drop it
            i += 1 if c == "→" else 2
            continue

        arrow = _find_top_level_arrow(s, i)
        if arrow is not None:
            pos, alen = arrow
            left = s[i:pos].strip()
            if left:
                stmt.binders.append(
                    Binder(name=None, kind="explicit", type_text=left, raw=left, span=(i, pos))
                )
            i = pos + alen
            continue

        return finish(i)


def _find_top_level_arrow(s: str, start: int) -> tuple[int, int] | None:
    masked = expr.blank_comments_and_strings(s)
    depth = 0
    i = start
    n = len(masked)
    while i < n:
        c = masked[i]
        if c in "([{⦃":
            depth += 1
        elif c in ")]}⦄":
            depth = max(0, depth - 1)
        elif depth == 0:
            if c == "→":
                return (i, 1)
            if masked.startswith("->", i):
                return (i, 2)
        i += 1
    return None


def _parse_group(s: str, open_idx: int, close_idx: int) -> Binder | None:
    opener = s[open_idx]
    kind = BINDER_OPENERS.get(opener, "explicit")
    inner = s[open_idx + 1 : close_idx]
    colon = expr.top_level_index(inner, ":")
    if colon < 0:
        return None
    # guard against `:=`, `::`
    while colon >= 0 and colon + 1 < len(inner) and inner[colon + 1] in "=:":
        next_colon = expr.top_level_index(inner[colon + 2 :], ":")
        if next_colon < 0:
            return None
        colon = colon + 2 + next_colon
    name = inner[:colon].strip()
    type_text = inner[colon + 1 :].strip()
    if not type_text:
        return None
    if not name or name == "_":
        name = None
    return Binder(
        name=name,
        kind=kind,
        type_text=type_text,
        raw=s[open_idx : close_idx + 1],
        span=(open_idx, close_idx + 1),
    )


def parse_check_output(text: str, decl: str) -> ParsedStatement | None:
    """Extract the type from one `#check @decl` output line and parse it.

    `pp.all` prints:  `@Foo.bar : {α : Type u_1} → α → α`
    Returns None when the declaration is not visible in the output at all.
    """
    for line in text.splitlines():
        stripped = line.strip()
        if not stripped.startswith("@") and not stripped.startswith(decl):
            continue
        marker = " : "
        idx = stripped.find(marker)
        if idx < 0:
            continue
        head = stripped[:idx].strip()
        if head.lstrip("@") != decl and decl not in head:
            continue
        return parse_telescope(stripped[idx + len(marker) :])
    return None


def parse_binders_segment(segment: str, absolute_offset: int) -> tuple[list[Binder], list[str]]:
    """Parse a pre-colon telescope such as `(n : Nat) (h : n > 0)`.

    Returns the binders with spans made absolute by `absolute_offset`, plus any
    notes. Binders in this position are space-separated groups with no arrows
    between them (Lean's syntax for `theorem foo (n : Nat) : T`), so the parse is
    a simple left-to-right walk. Anything unexpected is reported, not guessed.
    """
    binders: list[Binder] = []
    notes: list[str] = []
    i = 0
    n = len(segment)
    masked = expr.blank_comments_and_strings(segment)
    while True:
        while i < n and masked[i].isspace():
            i += 1
        if i >= n:
            break
        if masked[i] not in BINDER_OPENERS:
            notes.append(f"unexpected token in binder telescope at offset {i}: {segment[i:i + 40]!r}")
            break
        close = expr.match_close(segment, i)
        if close < 0:
            notes.append(f"unbalanced bracket in binder telescope at offset {i}")
            break
        binder = _parse_group(segment, i, close)
        if binder is None:
            notes.append(f"group is not a binder: {segment[i:close + 1]!r}")
            break
        binder.span = (i + absolute_offset, close + 1 + absolute_offset)
        binders.append(binder)
        i = close + 1
    return binders, notes
