#!/usr/bin/env python3
"""Read the textual form of Dynamatic's `handshake` MLIR dialect into a graph.

This is deliberately NOT a general MLIR parser.  It knows the subset that
`dynamatic-opt` actually prints for `handshake.func`: a `module { ... }`
wrapper (optional), one or more `handshake.func` items, ops written one
statement per (logical) line with an optional attribute dictionary and an
optional trailing `: type` clause.

The one rule that matters more than any grammar detail: never swallow text
we do not understand.  A dropped node here becomes a missing gate in the
Verilog later, with nothing to point at.  Every place this module gives up,
it raises ParseError with a file:line and the exact text it choked on.

What is intentionally NOT modelled:
  - MLIR's generic op syntax, only handshake's custom formats.
  - the extra-signal / bundle / unbundle / spec_commit speculation surface
    (see channel type grammar below) -- it does not appear in anything
    dynamatic-opt actually emits for a plain HLS flow, only in the dialect's
    own hand-written verifier tests.
  - anything inside a `#dialect<...>` attribute (e.g. `#handshake<deps[...]>`,
    `#handshake<bufProps{...}>`).  These are captured verbatim as opaque text
    (see OpaqueAttr) rather than semantically parsed: their internal grammar
    is not `key = value` MLIR syntax, it is bespoke pretty-printing, and nothing
    downstream of this file needs to look inside them yet.
"""

import argparse
import re
import sys
from dataclasses import dataclass, field
from typing import Any, Dict, List, Optional, Tuple, Union


class ParseError(Exception):
    """Carries enough to point a human straight at the offending text."""

    def __init__(self, message, filename, line, col, text):
        self.message = message
        self.filename = filename
        self.line = line
        self.col = col
        self.text = text
        super().__init__(str(self))

    def __str__(self):
        loc = f"{self.filename}:{self.line}:{self.col}"
        return f"{loc}: {self.message}\n    {self.text}"


# ---------------------------------------------------------------------------
# Data model
#
# Kept plain: dataclasses, no behaviour beyond to_text().  Six fields on Node
# are what the spec for this reader asked for (op, operands, results, attrs,
# bracket_arg, src_line); `type_sig` is the one addition that turned out to
# be unavoidable -- see the note above Node below.

@dataclass
class Channel:
    """A function argument or result port.

    `raw` is the exact type spelling (`!handshake.channel<i32>`,
    `memref<64xi32>`, ...).  `width`/`is_control` are the useful, decoded
    form for the common case; they are 0/False when the type is not a plain
    handshake channel or control (e.g. a `memref<...>` argument), and `raw`
    is what carries the truth in that case.  This `raw` field is not in the
    task's original three-field sketch; it was added because round-tripping
    a `memref<64xi32>` argument is impossible without storing its spelling
    somewhere, and because it is the simplest way to keep to_text() honest.
    """

    name: str
    width: int
    is_control: bool
    raw: str = ""
    ssa_name: str = ""  # the %name used in the signature, for defined funcs only


@dataclass(frozen=True)
class ArgSource:
    """A value's producer is function argument number `index`.

    Spelled out instead of using None so "this value comes from outside the
    function body" is a real, matchable case rather than a sentinel scattered
    through calling code.
    """

    index: int


@dataclass(frozen=True)
class ResultSource:
    """A value's producer is result `result_index` of `node_index`."""

    node_index: int
    result_index: int


ProducerRef = Union[ArgSource, ResultSource]


@dataclass
class TypedLiteral:
    """An MLIR typed literal attribute value, e.g. `42 : i32` or `0 : ui32`."""

    value: Any  # int, float, or bool
    type: str


@dataclass
class OpaqueAttr:
    """A `#dialect<...>` attribute captured verbatim, not parsed.

    e.g. `#handshake<deps[{dstAccess : "store3", ...}]>` or
    `#handshake<bufProps{"0": [0,0], ...}>`.  Their inner grammar is not
    ordinary `key = value` MLIR attribute syntax (it uses `:` where MLIR
    dict attrs use `=`), so it is out of scope here; `raw` is the exact
    source text, reprinted verbatim by to_text().
    """

    raw: str


@dataclass
class BareWord:
    """An unquoted enum-like attribute value, e.g. `ONE_SLOT_BREAK_DV` in
    `bufferType = ONE_SLOT_BREAK_DV`. Distinct from a Python str, which is
    how a *quoted* MLIR string attribute is stored -- reprinting one as the
    other changes the attribute."""

    text: str


@dataclass
class OperandItem:
    """A single `%value` reference as it appears inside a bracket/paren
    operand group, or standing alone. `type_suffix` is the raw `: type`
    text that occasionally follows a value inside such a group (e.g. lsq's
    `[%arg0 : memref<64xi32>]`) -- the value's real type is already fully
    known from its producer, so this is kept only because the source
    spelled it and the printer must be able to reproduce it. Empty when
    absent (the overwhelmingly common case)."""

    value: str
    type_suffix: str = ""


@dataclass
class LiteralArg:
    """A single bare, non-value token used as an op argument: a predicate
    (`sgt` in `cmpi sgt, ...`), an enum-like word (`MC` in `lsq[MC]`), a
    bracketed count (`2` in `fork [2]`), or a callee reference (`@foo` in
    `instance @foo(...)`)."""

    text: str


@dataclass
class OperandSegment:
    """One maximal run of operand-ish material after an op's mnemonic, in
    source order. Replaces a single flat `operands` list plus a single
    `bracket_arg`: real op syntax is not "mnemonic, one optional bracket,
    then a flat comma list" -- `mux`'s bare select operand is followed by a
    bracketed `[true, false]` pair, `lsq`'s bracketed memref arg is followed
    by a parenthesized operand list, `mem_controller` alternates bare
    operands and parenthesized groups -- and flattening all of that loses
    the grouping needed to reprint valid MLIR.

    `wrap` is `""` (bare/unwrapped -- exactly one item), `"[]"`, or `"()"`.
    `items` holds OperandItem (a value) or LiteralArg (a bare token) entries,
    in source order within the group.

    `trailing_comma` records whether a ',' followed this segment in the
    source, before whatever came next. This is not cosmetic: each op's
    hand-written dynamatic-opt printer treats commas as fixed grammar
    tokens at fixed positions (e.g. `cmpi`'s `sgt, %lhs, %rhs` -- the first
    comma is part of cmpi's declared assembly format, not a separator
    inserted by pretty-printing), so dropping or adding one can make the
    reprint fail to parse even though every operand is still present.
    """

    wrap: str
    items: List[Union[OperandItem, LiteralArg]]
    trailing_comma: bool = False


@dataclass
class InlineAttr:
    """One `key = value` property spelled bare (no enclosing `{}`) among an
    op's operands, as in `buffer`'s `bufferType = ONE_SLOT_BREAK_DV,
    numSlots = 1, dvLatency = 1` (its assemblyFormat in HandshakeOps.td
    spells these as fixed positional tokens, not as part of the generic
    attribute dict). Also merged into Node.attrs for lookup by key, but kept
    here too, *in position* among the other operand segments, so the
    printer can put each one back exactly where -- and in what order --
    the source had it, instead of guessing which ops need this treatment."""

    key: str
    value: Any
    trailing_comma: bool = False


@dataclass
class Node:
    """One operation statement inside a handshake.func body.

    `type_sig` is the raw text of the trailing `: ...` type clause (without
    the leading colon; empty string if the op had none).  It is not in the
    task's original field list, but round-tripping is impossible without it:
    the same mnemonic's result types cannot always be inferred from operand
    count (e.g. `cond_br`'s two result types are both inferred from its data
    operand, and are not spelled out in the type clause at all), so the
    clause is kept as text rather than reverse-engineered per-op. Downstream
    code that needs actual widths per node will need to add real semantics
    per opcode; that is out of scope for a front door.

    `arg_items` is the ordered list of OperandSegment / InlineAttr entries
    that followed the mnemonic in source order -- see those classes for why
    a single flat list is not enough to reprint valid MLIR. `operands`
    below is a read-only *view* over it: the op-to-cell mapper this reader
    feeds wants a plain list of producer references and must not have to
    walk segments, so the flat accessor is kept even though it is no longer
    the field that stores the data.

    `attrs_before_operands` records whether the `{...}` attribute dictionary
    appeared before any operand segment (only `end` does this in the real
    corpus) or after (everything else). Not derivable from `attrs` alone,
    and getting it wrong makes the reprint fail to parse for ops whose
    hand-written printer puts it in a fixed position.
    """

    op: str
    arg_items: List[Union[OperandSegment, InlineAttr]]
    results: List[str]
    attrs: Dict[str, Any]
    attrs_before_operands: bool = False
    # Not part of structural equality: it is *where this text came from*,
    # which a reprint-and-reparse round-trip can never reproduce (the
    # reprint is different text, with different line numbers) and should
    # not be expected to. `field(compare=False)` keeps it out of __eq__
    # while still being ordinary, inspectable data.
    src_line: int = field(compare=False, default=0)
    type_sig: str = ""

    @property
    def operands(self) -> List[str]:
        """Flat, ordered list of every value reference among arg_items --
        the same shape the old flat `operands` field had. Kept as a
        property (not the storage) so parsing/printing can see the real
        segment structure while downstream consumers can still ignore it."""
        out: List[str] = []
        for item in self.arg_items:
            if isinstance(item, OperandSegment):
                for sub in item.items:
                    if isinstance(sub, OperandItem):
                        out.append(sub.value)
        return out


@dataclass
class Func:
    """One `handshake.func`.

    Additions beyond the task's four-field sketch, all needed for a lossless
    round-trip of things that are genuinely in the corpus:
      - is_private / is_declaration: `handshake.func private @foo(...)  ...`
        with no body is a real top-level item (see handshake-hw-inst.mlir's
        instantiated callee prototype).
      - has_ellipsis: whether the literal `...` (implicit clock/reset) token
        was present; always true in real output, but kept honest rather than
        assumed.
      - attrs: the function's own attribute dict verbatim (argNames/resNames
        are consumed into args/results below, but nothing stops a function
        from carrying other attributes too).
    """

    name: str
    args: List[Channel]
    results: List[Channel]
    nodes: List[Node]
    producer: Dict[str, ProducerRef]
    consumers: Dict[str, List[Tuple[int, int]]]
    attrs: Dict[str, Any] = field(default_factory=dict)
    is_private: bool = False
    is_declaration: bool = False
    has_ellipsis: bool = True
    # Which chain of `module { ... }` blocks this func sat inside, as the
    # index of each block at each level. `()` means it was at top level with
    # no wrapper at all. Real dynamatic-opt output for a kernel is a single
    # module, so every func in it is (0,) -- but a --split-input-file fixture
    # fed back through the tool becomes `module { module {...} module {...} }`,
    # and flattening that would make the reprint a different (if equivalent)
    # program. Kept so the oracle comparison can stay byte-exact instead of
    # being relaxed to paper over it.
    module_path: Tuple[int, ...] = ()
    src_line: int = field(compare=False, default=0)  # see Node.src_line


# ---------------------------------------------------------------------------
# Tokenizer

@dataclass
class Token:
    kind: str
    text: str
    start: int
    end: int
    line: int
    col: int


_TOKEN_SPEC = [
    ("COMMENT", r"//[^\n]*"),
    ("WS", r"[ \t\r\n]+"),
    ("STRING", r'"(?:[^"\\]|\\.)*"'),
    ("HEXNUM", r"0x[0-9a-fA-F]+"),
    ("FLOATNUM", r"-?[0-9]+\.[0-9]+(?:[eE][+-]?[0-9]+)?"),
    ("INTNUM", r"-?[0-9]+"),
    ("VALUE", r"%[A-Za-z0-9_$.]+"),
    ("SYMBOL", r"@[A-Za-z_$][A-Za-z0-9_$.]*"),
    ("BANGID", r"![A-Za-z_][A-Za-z0-9_.]*"),
    ("HASHID", r"#[A-Za-z_][A-Za-z0-9_.]*"),
    ("ARROW", r"->"),
    ("ELLIPSIS", r"\.\.\."),
    ("IDENT", r"[A-Za-z_][A-Za-z0-9_.]*"),
    ("PUNCT", r"[{}()\[\]<>,:=#]"),
]
_MASTER_RE = re.compile(
    "|".join(f"(?P<{name}>{pat})" for name, pat in _TOKEN_SPEC)
)


def tokenize(text, filename):
    """Turn `text` into a flat token stream, comments and whitespace dropped.

    Anything the master regex cannot classify raises ParseError immediately
    (the "fail loudly" default: an unrecognised character is far more likely
    to be a hole in this parser than junk in Dynamatic's output).
    """
    tokens = []
    pos = 0
    line = 1
    line_start = 0
    n = len(text)
    while pos < n:
        m = _MASTER_RE.match(text, pos)
        if not m:
            col = pos - line_start + 1
            bad_line = text[line_start:text.find("\n", line_start) if text.find("\n", line_start) != -1 else n]
            raise ParseError(
                f"unrecognised character {text[pos]!r}", filename, line, col, bad_line
            )
        kind = m.lastgroup
        tok_text = m.group()
        start, end = m.span()
        if kind in ("WS", "COMMENT"):
            newlines = tok_text.count("\n")
            if newlines:
                line += newlines
                line_start = start + tok_text.rfind("\n") + 1
        else:
            col = start - line_start + 1
            tokens.append(Token(kind, tok_text, start, end, line, col))
        pos = end
    return tokens


# ---------------------------------------------------------------------------
# Parser

_OPEN_CLOSE = {"(": ")", "[": "]", "{": "}", "<": ">"}
_CLOSE_OPEN = {v: k for k, v in _OPEN_CLOSE.items()}


class _Parser:
    def __init__(self, text, filename):
        self.text = text
        self.filename = filename
        self.toks = tokenize(text, filename)
        self.pos = 0

    # -- token stream helpers ------------------------------------------------

    def peek(self, ahead=0):
        i = self.pos + ahead
        return self.toks[i] if i < len(self.toks) else None

    def advance(self):
        tok = self.peek()
        if tok is None:
            self._error_eof("unexpected end of input")
        self.pos += 1
        return tok

    def at_end(self):
        return self.peek() is None

    def _line_text(self, line):
        lines = self.text.splitlines()
        return lines[line - 1] if 0 < line <= len(lines) else ""

    def error(self, message, tok=None):
        if tok is None:
            tok = self.peek()
        if tok is None:
            self._error_eof(message)
        raise ParseError(message, self.filename, tok.line, tok.col, self._line_text(tok.line))

    def _error_eof(self, message):
        line = self.toks[-1].line if self.toks else 1
        raise ParseError(message, self.filename, line, 1, self._line_text(line))

    def expect_punct(self, text):
        tok = self.peek()
        if tok is None or tok.text != text:
            self.error(f"expected {text!r}, found {tok.text if tok else 'end of input'!r}")
        return self.advance()

    def expect_kind(self, kind, what):
        tok = self.peek()
        if tok is None or tok.kind != kind:
            self.error(f"expected {what}, found {tok.text if tok else 'end of input'!r}")
        return self.advance()

    def slice(self, start_tok, end_tok):
        return self.text[start_tok.start:end_tok.end]

    # -- balanced-bracket consumption ----------------------------------------

    def consume_balanced(self, open_text):
        """Consume tokens from an opening bracket (not yet consumed) through
        its matching close, tracking all four bracket kinds so a genuine
        mismatch (malformed input) is caught rather than silently
        misparsed."""
        start_tok = self.advance()
        if start_tok.text != open_text:
            self.error(f"expected {open_text!r}", start_tok)
        stack = [open_text]
        end_tok = start_tok
        while stack:
            if self.at_end():
                self.error(f"unterminated {stack[-1]!r} opened here", start_tok)
            tok = self.advance()
            if tok.text in _OPEN_CLOSE:
                stack.append(tok.text)
            elif tok.text in _CLOSE_OPEN:
                if stack[-1] != _CLOSE_OPEN[tok.text]:
                    self.error(
                        f"mismatched bracket: found {tok.text!r}, expected "
                        f"{_OPEN_CLOSE[stack[-1]]!r}",
                        tok,
                    )
                stack.pop()
            end_tok = tok
        return start_tok, end_tok

    # -- module / func --------------------------------------------------------

    def parse_module(self):
        """Top level: zero or more `handshake.func`, each optionally wrapped
        in its own `module { ... }` (dynamatic-opt's `--split-input-file`
        output is a sequence of independent `module { ... }` blocks, one per
        lit-test case, with `// -----` between them -- and `// -----` is a
        comment, so by the time this sees the token stream it has already
        vanished; the blocks just sit back to back). Anything else at top
        level is refused."""
        funcs = []
        counter = [0]
        while not self.at_end():
            self._parse_top_item(funcs, (), counter)
        return funcs

    def _parse_top_item(self, funcs, path, counter):
        """One top-level item: a `module { ... }` or a bare `handshake.func`.

        Modules nest. Feeding a `--split-input-file` fixture (already a
        sequence of `module { ... }` blocks) back through dynamatic-opt wraps
        the whole sequence in one more module, so the real corpus contains
        `module { module { ... } }`. Recursing rather than handling exactly
        one level is what makes the oracle gate usable on those files."""
        tok = self.peek()
        if tok.kind == "IDENT" and tok.text == "module":
            self.advance()
            if self.peek() and self.peek().text == "attributes":
                self.advance()
                self.parse_attr_dict()
            self.expect_punct("{")
            here = path + (counter[0],)
            counter[0] += 1
            inner = [0]
            while not (self.peek() and self.peek().text == "}"):
                self._parse_top_item(funcs, here, inner)
            self.expect_punct("}")
        else:
            func = self.parse_func()
            func.module_path = path
            funcs.append(func)

    def parse_func(self):
        tok = self.peek()
        if tok is None or not (tok.kind == "IDENT" and tok.text == "handshake.func"):
            self.error("expected 'handshake.func'")
        start_line = tok.line
        self.advance()
        is_private = False
        if self.peek() and self.peek().text == "private":
            is_private = True
            self.advance()
        name_tok = self.expect_kind("SYMBOL", "function name (e.g. @foo)")
        name = name_tok.text[1:]

        value_defs: Dict[str, ProducerRef] = {}
        args = self._parse_arg_list(value_defs)
        has_ellipsis = self._consumed_ellipsis

        results: List[Channel] = []
        if self.peek() and self.peek().text == "->":
            self.advance()
            results = self._parse_result_types()

        attrs = {}
        if self.peek() and self.peek().kind == "IDENT" and self.peek().text == "attributes":
            self.advance()
            attrs = self.parse_attr_dict()

        arg_names = attrs.get("argNames")
        if isinstance(arg_names, list) and len(arg_names) == len(args):
            for ch, nm in zip(args, arg_names):
                ch.name = nm
        res_names = attrs.get("resNames")
        if isinstance(res_names, list) and len(res_names) == len(results):
            for ch, nm in zip(results, res_names):
                ch.name = nm

        is_declaration = not (self.peek() and self.peek().text == "{")
        nodes: List[Node] = []
        if not is_declaration:
            self.expect_punct("{")
            while not (self.peek() and self.peek().text == "}"):
                nodes.append(self._parse_op(value_defs, len(args)))
            self.expect_punct("}")

        producer, consumers = self._resolve(args, nodes, value_defs)

        return Func(
            name=name,
            args=args,
            results=results,
            nodes=nodes,
            producer=producer,
            consumers=consumers,
            attrs=attrs,
            is_private=is_private,
            is_declaration=is_declaration,
            has_ellipsis=has_ellipsis,
            src_line=start_line,
        )

    def _parse_arg_list(self, value_defs):
        """Parses `(%name: type, %name: type, ..., ...)` for a definition, or
        `(type, type, ...)` for a declaration (no SSA names to bind)."""
        self.expect_punct("(")
        args: List[Channel] = []
        self._consumed_ellipsis = False
        arg_index = 0
        while not (self.peek() and self.peek().text == ")"):
            tok = self.peek()
            if tok.kind == "ELLIPSIS":
                self.advance()
                self._consumed_ellipsis = True
            else:
                if tok.kind == "VALUE":
                    val_tok = self.advance()
                    self.expect_punct(":")
                    ch = self._parse_port_type()
                    ch.ssa_name = val_tok.text[1:]
                    value_defs[val_tok.text[1:]] = ArgSource(arg_index)
                    arg_index += 1
                else:
                    ch = self._parse_port_type()
                    arg_index += 1
                args.append(ch)
            if self.peek() and self.peek().text == ",":
                self.advance()
            elif not (self.peek() and self.peek().text == ")"):
                self.error("expected ',' or ')' in argument list")
        self.expect_punct(")")
        return args

    def _parse_result_types(self):
        if self.peek() and self.peek().text == "(":
            self.advance()
            results = []
            while not (self.peek() and self.peek().text == ")"):
                results.append(self._parse_port_type())
                if self.peek() and self.peek().text == ",":
                    self.advance()
                elif not (self.peek() and self.peek().text == ")"):
                    self.error("expected ',' or ')' in result type list")
            self.expect_punct(")")
            return results
        return [self._parse_port_type()]

    def _parse_port_type(self):
        """A single arg/result type: `!handshake.channel<...>`,
        `!handshake.control<...>`, or `memref<...>` (kept as raw text --
        function arguments can reference plain memories)."""
        tok = self.peek()
        if tok is None:
            self.error("expected a type")
        if tok.kind == "BANGID" and tok.text in ("!handshake.channel", "!handshake.control"):
            is_control = tok.text == "!handshake.control"
            self.advance()
            open_tok = self.expect_punct("<")
            width = 0
            if not is_control:
                dtype_tok = self.expect_kind("IDENT", "a data type (e.g. i32) inside channel<...>")
                width = self._width_from_type_word(dtype_tok)
            nxt = self.peek()
            if nxt and nxt.text != ">":
                self.error(
                    "extra signals ('!handshake.channel<T, [...]>') are not "
                    "supported by this reader -- they belong to the "
                    "speculation surface, which is out of scope for a plain "
                    "HLS backend",
                    nxt,
                )
            end_tok = self.expect_punct(">")
            raw = self.slice(tok, end_tok)
            return Channel(name="", width=width, is_control=is_control, raw=raw)
        if tok.kind == "IDENT" and tok.text == "memref":
            self.advance()
            _, end_tok = self.consume_balanced("<")
            raw = self.slice(tok, end_tok)
            return Channel(name="", width=0, is_control=False, raw=raw)
        self.error(f"unsupported port type spelled {tok.text!r}", tok)

    @staticmethod
    def _width_from_type_word(tok):
        m = re.fullmatch(r"[if](\d+)", tok.text)
        if not m:
            raise ParseError(
                f"unsupported channel data type {tok.text!r} (expected iN or fN)",
                "<type>", tok.line, tok.col, tok.text,
            )
        return int(m.group(1))

    # -- op statements ---------------------------------------------------------

    def _parse_op(self, value_defs, num_args):
        start_tok = self.peek()
        src_line = start_tok.line

        # LHS: `%r1, %r2 = ` or `%r:N = ` or nothing (no results).
        results: List[str] = []
        if start_tok.kind == "VALUE":
            names = [self._parse_lhs_name()]
            while self.peek() and self.peek().text == ",":
                self.advance()
                names.append(self._parse_lhs_name())
            self.expect_punct("=")
            for group in names:
                results.extend(group)

        mnem_tok = self.expect_kind("IDENT", "an operation mnemonic")
        op = mnem_tok.text
        if op.startswith("handshake."):
            op = op[len("handshake."):]

        arg_items: List[Union[OperandSegment, InlineAttr]] = []
        attrs: Dict[str, Any] = {}
        attrs_seen = False
        attrs_before_operands = False

        def push(seg):
            """Append a segment and record whether a ',' followed it."""
            arg_items.append(seg)
            seg.trailing_comma = self._eat_optional_comma()

        while True:
            tok = self.peek()
            if tok is None or tok.text in ("}", ":"):
                break
            if tok.text == "{":
                if attrs_seen:
                    self.error("duplicate attribute dictionary on one op", tok)
                # `end` puts its attribute dict before its operands; every
                # other op in the corpus puts it after. Which one it was is
                # not recoverable from the dict itself, and each op's printer
                # expects it in one fixed place.
                if not arg_items:
                    attrs_before_operands = True
                attrs.update(self.parse_attr_dict())
                attrs_seen = True
                continue
            if tok.kind == "IDENT" and self.peek(1) and self.peek(1).text == "=":
                # An inline `key = value` property with no braces, as in
                # `buffer %0, bufferType = ONE_SLOT_BREAK_DV, numSlots = 1,
                # dvLatency = 1 {handshake.name = ...} : <i16>`.  Folded into
                # the same attrs dict as the braced form; nothing downstream
                # needs to know which spelling was used, only the value.
                # Values here never carry a `: type` suffix of their own
                # (unlike braced attrs, e.g. `value = 42 : i32`) -- if they
                # did, a bare trailing number could not be told apart from
                # the op's own trailing type clause (`... dvLatency = 1 :
                # <i32>`), since both look like "NUMBER :".
                self.advance()
                self.expect_punct("=")
                value = self._parse_attr_value(allow_type_suffix=False)
                attrs[tok.text] = value
                item = InlineAttr(tok.text, value)
                arg_items.append(item)
                item.trailing_comma = self._eat_optional_comma()
                continue
            if tok.kind == "VALUE":
                name = self._parse_operand_ref()
                push(OperandSegment("", [OperandItem(name)]))
                continue
            if tok.text == "[":
                push(OperandSegment("[]", self._parse_bracket_group()))
                continue
            if tok.text == "(":
                self.advance()
                items = []
                while not (self.peek() and self.peek().text == ")"):
                    items.append(OperandItem(self._parse_operand_ref()))
                    if self.peek() and self.peek().text == ",":
                        self.advance()
                self.expect_punct(")")
                push(OperandSegment("()", items))
                continue
            if tok.kind in ("SYMBOL", "IDENT"):
                self.advance()
                push(OperandSegment("", [LiteralArg(tok.text)]))
                continue
            self.error(f"unexpected token {tok.text!r} while parsing operands of {op!r}", tok)

        type_sig = self._parse_type_clause()

        return Node(
            op=op,
            arg_items=arg_items,
            results=results,
            attrs=attrs,
            attrs_before_operands=attrs_before_operands,
            src_line=src_line,
            type_sig=type_sig,
        )

    def _parse_lhs_name(self):
        """Parses one binding on the LHS of `=`: `%name` (one result) or
        `%name:N` (N grouped results, later referenced as %name#0..#(N-1)).
        Returns the list of result names to register, in order."""
        val_tok = self.expect_kind("VALUE", "a result name (e.g. %0)")
        base = val_tok.text[1:]
        if self.peek() and self.peek().text == ":":
            self.advance()
            n_tok = self.expect_kind("INTNUM", "a result-group count after ':'")
            n = int(n_tok.text)
            return [f"{base}#{i}" for i in range(n)]
        return [base]

    def _parse_operand_ref(self):
        val_tok = self.expect_kind("VALUE", "an operand (e.g. %0)")
        name = val_tok.text[1:]
        if self.peek() and self.peek().text == "#":
            self.advance()
            idx_tok = self.expect_kind("INTNUM", "a result index after '#'")
            name = f"{name}#{idx_tok.text}"
        return name

    def _eat_optional_comma(self):
        """Returns whether a comma was actually consumed. The caller records
        it: for several ops the comma is a fixed token in the op's declared
        assembly format rather than a separator the pretty-printer chose
        (`cmpi sgt, %a, %b`), so putting it back in the right places is the
        difference between a reprint dynamatic-opt accepts and one it does
        not."""
        if self.peek() and self.peek().text == ",":
            self.advance()
            return True
        return False

    def _parse_bracket_group(self):
        """Parses the contents of `[ ... ]` after an op mnemonic or operand.
        Returns a list of OperandItem (for a %-value) and LiteralArg (for a
        bare integer or identifier, as in `fork [2]` or `lsq[MC]`) in source
        order.

        A `: memref<...>` / `: <type>` suffix on a value, as in
        `[%mem : memref<64xi32>]`, is kept as OperandItem.type_suffix rather
        than discarded. The value's type is already known from its producer,
        so this carries no information -- but the source spelled it and the
        printer has to spell it back or dynamatic-opt rejects the result."""
        self.advance()  # '['
        items = []
        while not (self.peek() and self.peek().text == "]"):
            tok = self.peek()
            if tok.kind == "VALUE":
                name = self._parse_operand_ref()
                suffix = ""
                if self.peek() and self.peek().text == ":":
                    self.advance()
                    suffix = self._capture_type_atom()
                items.append(OperandItem(name, suffix))
            elif tok.kind == "INTNUM":
                self.advance()
                items.append(LiteralArg(tok.text))
            elif tok.kind == "IDENT":
                self.advance()
                items.append(LiteralArg(tok.text))
            else:
                self.error(f"unexpected token {tok.text!r} inside '[...]'", tok)
            if self.peek() and self.peek().text == ",":
                self.advance()
            elif not (self.peek() and self.peek().text == "]"):
                self.error("expected ',' or ']'")
        self.expect_punct("]")
        return items

    def _skip_type_atom(self):
        if not self._try_type_atom():
            self.error("expected a type")

    def _capture_type_atom(self):
        """_skip_type_atom, but returns the source text it consumed. Used for
        the redundant per-value type suffix inside a bracket group, which is
        reprinted verbatim rather than reconstructed."""
        start_tok = self.peek()
        if start_tok is None or not self._try_type_atom():
            self.error("expected a type")
        return self.text[start_tok.start:self.toks[self.pos - 1].end].strip()

    # -- type clause (kept as raw text; see Node docstring) --------------------

    def _try_type_atom(self):
        tok = self.peek()
        if tok is None:
            return False
        if tok.text in ("<", "(", "["):
            self.consume_balanced(tok.text)
            return True
        if tok.kind == "BANGID":
            self.advance()
            if self.peek() and self.peek().text == "<":
                self.consume_balanced("<")
            return True
        if tok.kind == "IDENT" and self.peek(1) and self.peek(1).text == "<":
            self.advance()
            self.consume_balanced("<")
            return True
        if tok.kind == "IDENT" and tok.text == "_":
            self.advance()
            return True
        return False

    def _try_type_list(self):
        if not self._try_type_atom():
            return False
        while self.peek() and self.peek().text == ",":
            self.advance()
            if not self._try_type_atom():
                self.error("expected a type after ','")
        return True

    def _parse_type_clause(self):
        tok = self.peek()
        if tok is None or tok.text != ":":
            return ""
        colon_tok = self.advance()
        self._try_type_list()
        if self.peek() and self.peek().kind == "IDENT" and self.peek().text == "to":
            self.advance()
            self._try_type_list()
        if self.peek() and self.peek().text == "->":
            self.advance()
            self._try_type_list()
        last = self.toks[self.pos - 1]
        return self.text[colon_tok.end:last.end].strip()

    # -- attribute dictionaries --------------------------------------------------

    def parse_attr_dict(self):
        self.expect_punct("{")
        attrs = {}
        while not (self.peek() and self.peek().text == "}"):
            key_tok = self.peek()
            if key_tok.kind == "STRING":
                self.advance()
                key = _unescape_string(key_tok.text)
            elif key_tok.kind == "IDENT":
                self.advance()
                key = key_tok.text
            else:
                self.error("expected an attribute key", key_tok)
            self.expect_punct("=")
            attrs[key] = self._parse_attr_value()
            if self.peek() and self.peek().text == ",":
                self.advance()
            elif not (self.peek() and self.peek().text == "}"):
                self.error("expected ',' or '}' in attribute dictionary")
        self.expect_punct("}")
        return attrs

    def _parse_attr_value(self, allow_type_suffix=True):
        tok = self.peek()
        if tok is None:
            self.error("expected an attribute value")
        if tok.kind == "STRING":
            self.advance()
            return _unescape_string(tok.text)
        if tok.kind == "IDENT" and tok.text in ("true", "false"):
            self.advance()
            return tok.text == "true"
        if tok.kind == "IDENT":
            # A bare, unquoted word used as a value (e.g. `buffer`'s
            # `bufferType = ONE_SLOT_BREAK_DV`, an enum-like literal with no
            # quotes and no type suffix). It must NOT be kept as a plain
            # string: the printer would then quote it on the way out, and
            # `bufferType = "ONE_SLOT_BREAK_DV"` is a different attribute
            # from `bufferType = ONE_SLOT_BREAK_DV`.
            self.advance()
            return BareWord(tok.text)
        if tok.kind in ("INTNUM", "FLOATNUM", "HEXNUM"):
            self.advance()
            value = _parse_number(tok)
            if allow_type_suffix and self.peek() and self.peek().text == ":":
                self.advance()
                type_tok = self.expect_kind("IDENT", "a type after ':'")
                return TypedLiteral(value=value, type=type_tok.text)
            return value
        if tok.text == "[":
            self.advance()
            items = []
            while not (self.peek() and self.peek().text == "]"):
                items.append(self._parse_attr_value())
                if self.peek() and self.peek().text == ",":
                    self.advance()
                elif not (self.peek() and self.peek().text == "]"):
                    self.error("expected ',' or ']' in attribute array")
            self.expect_punct("]")
            return items
        if tok.text == "{":
            return self.parse_attr_dict()
        if tok.kind == "HASHID":
            start_tok = self.advance()
            end_tok = start_tok
            if self.peek() and self.peek().text in _OPEN_CLOSE:
                _, end_tok = self.consume_balanced(self.peek().text)
            return OpaqueAttr(raw=self.slice(start_tok, end_tok))
        if tok.kind == "SYMBOL":
            self.advance()
            return tok.text
        self.error(f"unrecognised attribute value starting with {tok.text!r}", tok)

    # -- producer/consumer resolution --------------------------------------------

    def _resolve(self, args, nodes, value_defs):
        """Two passes, deliberately: handshake IR is a dataflow graph, not
        sequential SSA, and memory-interface ops (`lsq`, `mem_controller`)
        routinely reference a value defined by a *later* statement (a load's
        address comes from an lsq that is itself fed by that same load's
        result -- a real feedback loop). Registering every producer before
        resolving any operand is what makes that legal instead of a parse
        error."""
        producer: Dict[str, ProducerRef] = dict(value_defs)
        for node_index, node in enumerate(nodes):
            for result_index, name in enumerate(node.results):
                producer[name] = ResultSource(node_index, result_index)

        # MLIR accepts `%v#0` even when `%v` was never declared as a group
        # (only single-valued): the reference just means "the whole value".
        # Seen in real, hand-written handshake.func bodies in this corpus
        # (e.g. `%start#0` where `%start` is a plain, ungrouped argument).
        # `#1` and above on an ungrouped value stays an error.
        for name in list(producer.keys()):
            if "#" not in name:
                producer.setdefault(f"{name}#0", producer[name])

        consumers: Dict[str, List[Tuple[int, int]]] = {}
        for node_index, node in enumerate(nodes):
            for operand_index, ref in enumerate(node.operands):
                if ref not in producer:
                    raise ParseError(
                        f"operand %{ref} of {node.op!r} has no producer "
                        f"(not a function argument and not the result of any "
                        f"op in this function)",
                        self.filename, node.src_line, 1, self._line_text(node.src_line),
                    )
                consumers.setdefault(ref, []).append((node_index, operand_index))
        return producer, consumers


def _unescape_string(tok_text):
    inner = tok_text[1:-1]
    return inner.replace('\\"', '"').replace("\\\\", "\\").replace("\\n", "\n")


def _parse_number(tok):
    if tok.kind == "HEXNUM":
        return int(tok.text, 16)
    if tok.kind == "FLOATNUM":
        return float(tok.text)
    return int(tok.text)


def parse_module(text, filename="<string>"):
    """Parse `text` (one file's worth of handshake dialect, optionally
    wrapped in `module { ... }`) into a list of Func, in source order."""
    return _Parser(text, filename).parse_module()


def parse_func(text, filename="<string>"):
    """Convenience: parse text containing exactly one handshake.func."""
    funcs = parse_module(text, filename)
    if len(funcs) != 1:
        raise ValueError(f"expected exactly one handshake.func, found {len(funcs)}")
    return funcs[0]


# ---------------------------------------------------------------------------
# to_text(): the inverse of parse_module(), used only to round-trip.
#
# The reprint does not aim to match Dynamatic's own pretty-printer byte for
# byte (spacing, operand-list bracket-vs-bare choice, and grouped-vs-ungrouped
# result binding are all normalised away). It only has to be valid handshake
# text that reparses to a structurally-identical Func.

def _format_attr_value(value):
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, str):
        return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'
    if isinstance(value, int):
        return str(value)
    if isinstance(value, float):
        return repr(value)
    if isinstance(value, TypedLiteral):
        v = value.value
        v_text = "true" if v is True else "false" if v is False else str(v)
        return f"{v_text} : {value.type}"
    if isinstance(value, OpaqueAttr):
        return value.raw
    if isinstance(value, BareWord):
        return value.text
    if isinstance(value, list):
        return "[" + ", ".join(_format_attr_value(v) for v in value) + "]"
    if isinstance(value, dict):
        return _format_attr_dict(value)
    raise TypeError(f"don't know how to reprint attribute value {value!r}")


def _format_attr_dict(attrs):
    if not attrs:
        return "{}"
    items = ", ".join(f"{k} = {_format_attr_value(v)}" for k, v in attrs.items())
    return "{" + items + "}"


def _format_port_type(ch: Channel):
    if ch.raw:
        return ch.raw
    if ch.is_control:
        return "!handshake.control<>"
    return f"!handshake.channel<i{ch.width}>"


def _format_lhs(results):
    """Reprint the LHS binding list. Each entry in `results` is either a
    plain name ('memEnd') or a grouped-result alias ('outputs#0'). A run of
    consecutive entries 'x#0', 'x#1', ..., 'x#(k-1)' for a common base 'x'
    is reprinted as the grouped `%x:k` binding form; anything else (a bare
    name, or a lone '#0' that never grows into a full run) is reprinted as
    itself. Real ops mix the two on one LHS, e.g. `mem_controller`'s
    `%outputs:3, %memEnd = ...`, so this cannot just be all-or-nothing
    across the whole list -- it has to regroup run by run."""
    if not results:
        return ""
    parts = []
    i, n = 0, len(results)
    while i < n:
        name = results[i]
        base, sep, idx = name.rpartition("#")
        if sep and idx == "0":
            j, k = i + 1, 1
            while j < n:
                b2, sep2, idx2 = results[j].rpartition("#")
                if not sep2 or b2 != base or not idx2.isdigit() or int(idx2) != k:
                    break
                k += 1
                j += 1
            if k >= 2:
                parts.append(f"%{base}:{k}")
                i = j
                continue
        parts.append(f"%{name}")
        i += 1
    return ", ".join(parts) + " = "


def _format_operand(ref):
    return f"%{ref}"


def _format_arg_item(item):
    if isinstance(item, InlineAttr):
        return f"{item.key} = {_format_attr_value(item.value)}"
    inner = []
    for sub in item.items:
        if isinstance(sub, OperandItem):
            inner.append(f"%{sub.value}" + (f" : {sub.type_suffix}" if sub.type_suffix else ""))
        else:
            inner.append(str(sub.text))
    body = ", ".join(inner)
    if item.wrap == "[]":
        return f"[{body}]"
    if item.wrap == "()":
        return f"({body})"
    return body


def node_to_text(node: Node, indent="    "):
    parts = [indent, _format_lhs(node.results), node.op]
    # Inline `key = value` properties live in arg_items *and* in attrs (the
    # latter so lookup by key works regardless of spelling). They must be
    # printed from one place only -- emitting both gives MLIR a duplicate
    # attribute and dynamatic-opt rejects it by name.
    inline_keys = {i.key for i in node.arg_items if isinstance(i, InlineAttr)}
    braced = {k: v for k, v in node.attrs.items() if k not in inline_keys}
    attrs_text = _format_attr_dict(braced) if braced else ""
    if attrs_text and node.attrs_before_operands:
        parts.append(" " + attrs_text)
    # Segments carry their own trailing commas because for several ops the
    # comma is a fixed token in the declared assembly format rather than a
    # separator (`cmpi sgt, %a, %b`), so it cannot be re-derived by joining.
    for item in node.arg_items:
        parts.append(" " + _format_arg_item(item))
        if item.trailing_comma:
            parts.append(",")
    if attrs_text and not node.attrs_before_operands:
        parts.append(" " + attrs_text)
    if node.type_sig:
        parts.append(" : " + node.type_sig)
    return "".join(parts)


def func_to_text(func: Func):
    lines = []
    head = "handshake.func "
    if func.is_private:
        head += "private "
    head += f"@{func.name}("
    arg_parts = []
    for ch in func.args:
        # Whether to reprint a `%name:` prefix follows whether one was
        # actually captured (ch.ssa_name), not is_declaration. Most
        # declarations omit argument names, but the hand-written verifier
        # corpus (dynamatic/test/Dialect/Handshake/types.mlir) has bodyless
        # `handshake.func @f(%arg0: !handshake.control<>) -> ...` -- a real,
        # legal form -- so a declaration can still carry names.
        if ch.ssa_name:
            arg_parts.append(f"%{ch.ssa_name}: {_format_port_type(ch)}")
        else:
            arg_parts.append(_format_port_type(ch))
    if func.has_ellipsis:
        arg_parts.append("...")
    head += ", ".join(arg_parts) + ")"
    if func.results:
        if len(func.results) == 1:
            head += " -> " + _format_port_type(func.results[0])
        else:
            head += " -> (" + ", ".join(_format_port_type(r) for r in func.results) + ")"

    # Only synthesize argNames/resNames if the source actually had them (any
    # channel with a non-empty name). A func with no `attributes {argNames =
    # ...}` clause at all parses with every Channel.name == "" -- reprinting
    # an argNames=["", ""] attribute in that case would not just be noise,
    # it would make attrs != {} on reparse, breaking round-trip equality.
    attrs = dict(func.attrs)
    if any(ch.name for ch in func.args) or any(ch.name for ch in func.results):
        attrs["argNames"] = [ch.name for ch in func.args]
        attrs["resNames"] = [ch.name for ch in func.results]
    if attrs:
        head += " attributes " + _format_attr_dict(attrs)

    if func.is_declaration:
        lines.append(head)
        return "\n".join(lines)

    lines.append(head + " {")
    for node in func.nodes:
        lines.append(node_to_text(node))
    lines.append("}")
    return "\n".join(lines)


def _indent_block(text, by="  "):
    return "\n".join((by + ln if ln.strip() else ln) for ln in text.split("\n"))


def _emit_level(funcs, depth):
    """Reprint `funcs` at nesting `depth`, re-opening a `module { ... }`
    wherever module_path says one was. Funcs are emitted in source order and
    consecutive funcs sharing a path share a module, which is exactly how
    they were read."""
    out = []
    i = 0
    while i < len(funcs):
        path = funcs[i].module_path
        if len(path) <= depth:
            out.append(func_to_text(funcs[i]))
            i += 1
            continue
        j = i
        while j < len(funcs) and funcs[j].module_path[:depth + 1] == path[:depth + 1]:
            j += 1
        out.append("module {\n" + _indent_block(_emit_level(funcs[i:j], depth + 1)) + "\n}")
        i = j
    return "\n".join(out)


def module_to_text(funcs: List[Func], wrap=None):
    """Reprint a whole file.

    By default the `module { ... }` nesting recorded on each Func at parse
    time is reproduced exactly -- dynamatic-opt always prints a wrapper and
    always expects one back, and --split-input-file fixtures carry more than
    one level. Pass wrap=False for the lit-test corpus, whose reconstructed
    fragments are not standalone modules and never had a wrapper."""
    if not funcs:
        return "module {\n}\n"
    if any(f.module_path for f in funcs):
        # The source had wrappers; reproduce them exactly, whatever `wrap`
        # says. Suppressing them here would not make the reprint "cleaner",
        # it would make it a different program.
        return _emit_level(funcs, 0) + "\n"
    # No wrapper in the source. Adding one is what lets dynamatic-opt accept
    # the reprint, but it also makes the reparse disagree about module_path
    # with the parse it came from -- so the self-round-trip test, which is
    # comparing exactly that, asks for wrap=False.
    body = "\n".join(func_to_text(f) for f in funcs)
    if wrap is False:
        return body
    return "module {\n" + _indent_block(body) + "\n}\n"


# ---------------------------------------------------------------------------
# But func_to_text() above numbers value references using whatever names the
# parser recorded (arg0, arg1, ... for declaration args re-synthesised from
# nothing -- see note in _reindex below). For a *defined* function, the
# original SSA names (results, and the argument names carried over from
# parsing) are reused directly, since Node.operands/results already store
# them; nothing needs renaming there. The only synthesis is declaration
# argument names, which are never referenced by anything (no body), so any
# stable spelling round-trips fine.


# ---------------------------------------------------------------------------
# --stats mode: inventory of op mnemonics and attribute keys, for building
# the op-to-cell mapping table.

def _collect_stats(funcs):
    op_counts: Dict[str, int] = {}
    attr_keys: Dict[str, int] = {}

    def walk_attrs(attrs):
        for k, v in attrs.items():
            attr_keys[k] = attr_keys.get(k, 0) + 1
            if isinstance(v, dict):
                walk_attrs(v)

    for func in funcs:
        walk_attrs(func.attrs)
        for node in func.nodes:
            op_counts[node.op] = op_counts.get(node.op, 0) + 1
            walk_attrs(node.attrs)
    return op_counts, attr_keys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("files", nargs="+", help="handshake-dialect .mlir file(s)")
    ap.add_argument(
        "--stats", action="store_true",
        help="print an inventory of op mnemonics and attribute keys instead of parsing quietly",
    )
    args = ap.parse_args()

    all_funcs = []
    bad = 0
    for path in args.files:
        with open(path) as fh:
            text = fh.read()
        try:
            funcs = parse_module(text, filename=path)
        except ParseError as e:
            print(e, file=sys.stderr)
            bad += 1
            continue
        all_funcs.extend(funcs)
        if not args.stats:
            print(f"{path}: {len(funcs)} handshake.func")

    if args.stats:
        op_counts, attr_keys = _collect_stats(all_funcs)
        print(f"{len(all_funcs)} functions, {sum(op_counts.values())} ops total\n")
        print("op mnemonic counts:")
        for op, count in sorted(op_counts.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {count:6d}  {op}")
        print("\nattribute keys:")
        for key, count in sorted(attr_keys.items(), key=lambda kv: (-kv[1], kv[0])):
            print(f"  {count:6d}  {key}")

    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
