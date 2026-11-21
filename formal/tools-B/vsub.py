"""A small Verilog-2005 front end for the subset bdc and cells/ use (shard B, probe Bmap).

Enough of Verilog to elaborate `cells/hw/gcd_rig.v` over bdc's emitted kernel and the frozen
`cells/rtl/*.v` WITHOUT yosys: the preprocessor (`define/`undef/`ifdef/`ifndef/`else/`endif,
macro use), ANSI module headers with parameters, wire/localparam/genvar declarations,
continuous assigns, module instances (named connections and parameter overrides), generate
if/else and for blocks with labels, and constant expressions. Function bodies are skipped (gcd_rig's `vector` only computes data, and
its call is an opaque expression); an always block is parsed but REFUSED at elaboration (none
is instantiated by gcd_hw). It raises on anything else it does not know.

Elaboration (`Elab`) produces:
* one bit id per bit of every declared net in every instance scope, named the way yosys names
  them (`scope.net[i]`, generate labels and `label[i]` loop scopes included);
* three union-finds over bits: `ufa` (every pure alias: port connections and assigns whose
  right side is wiring only: names, selects, concatenations, replications, constants),
  `ufp` (port connections only) and `ufw` (`ufa` without fan-out replications `{N{x}}`, N > 1:
  one class per physical WIRE, a fork's branches being different wires of one driver);
* the LUT primitive cells (`cells`), in elaboration order, with their INIT, pin bits and
  output bits;
* drivers that are not LUTs: constants and opaque (non-wiring) expressions, the latter with
  the expression's text and its input bits.
"""
import re

# ------------------------------------------------------------------ preprocessor

def strip_comments(s):
    out, i, n = [], 0, len(s)
    while i < n:
        if s.startswith("//", i):
            j = s.find("\n", i)
            i = n if j < 0 else j
        elif s.startswith("/*", i):
            j = s.find("*/", i + 2)
            assert j >= 0, "unterminated comment"
            out.append(" " * 0 + "\n" * s.count("\n", i, j))
            i = j + 2
        elif s[i] == '"':
            j = s.index('"', i + 1)
            out.append(s[i:j + 1])
            i = j + 1
        else:
            out.append(s[i])
            i += 1
    return "".join(out)


def preprocess(text, defines):
    """Line-based preprocessor. `defines` (dict) is updated in place (defines are global
    across files, in file order, as with a single yosys/iverilog invocation)."""
    text = strip_comments(text)
    out = []
    stack = []  # (active_before, this_branch_taken, any_taken)
    active = True
    for line in text.split("\n"):
        s = line.strip()
        m = re.match(r"`(ifdef|ifndef|elsif|else|endif|define|undef|default_nettype|timescale)\b\s*(.*)$", s)
        if m:
            d, rest = m.group(1), m.group(2).strip()
            if d in ("ifdef", "ifndef"):
                cond = (rest.split()[0] in defines) == (d == "ifdef")
                stack.append((active, cond))
                active = active and cond
            elif d == "elsif":
                outer, taken = stack[-1]
                cond = rest.split()[0] in defines
                active = outer and (not taken) and cond
                stack[-1] = (outer, taken or cond)
            elif d == "else":
                outer, taken = stack[-1]
                active = outer and not taken
                stack[-1] = (outer, True)
            elif d == "endif":
                active = stack.pop()[0]
            elif active and d == "define":
                mm = re.match(r"(\w+)\s*(.*)$", rest)
                defines[mm.group(1)] = mm.group(2).strip()
            elif active and d == "undef":
                defines.pop(rest.split()[0], None)
            out.append("")
            continue
        if not active:
            out.append("")
            continue
        def sub(mm):
            nm = mm.group(1)
            if nm not in defines:
                raise SyntaxError(f"undefined macro `{nm}")
            return defines[nm]
        out.append(re.sub(r"`(\w+)", sub, line))
    assert not stack, "unbalanced `ifdef"
    t = "\n".join(out)
    # attributes (* ... *)
    t = re.sub(r"\(\*[^()]*?\*\)", " ", t)
    return t


# ------------------------------------------------------------------ lexer

TOK = re.compile(r"""
  (?P<ws>\s+)
| (?P<num>(?:\d[\d_]*)?'[sS]?[bBhHdDoO][0-9a-fA-F_xXzZ?]+ | \d[\d_]*)
| (?P<str>"[^"]*")
| (?P<id>[A-Za-z_$][A-Za-z0-9_$]*)
| (?P<op>\+:|-:|<<<|>>>|===|!==|==|!=|<=|>=|&&|\|\||<<|>>|\*\*|~&|~\||~\^|\^~|[-+*/%<>!~&|^?:;,.#@=(){}\[\]])
""", re.X)


def lex(t):
    toks, i = [], 0
    while i < len(t):
        m = TOK.match(t, i)
        if not m:
            raise SyntaxError(f"bad char {t[i:i+20]!r}")
        i = m.end()
        k = m.lastgroup
        if k == "ws":
            continue
        toks.append((k, m.group(k)))
    toks.append(("eof", ""))
    return toks


def parse_num(s):
    s = s.replace("_", "")
    if "'" not in s:
        return int(s), None
    w, rest = s.split("'")
    rest = rest.lstrip("sS")
    base = {"b": 2, "h": 16, "d": 10, "o": 8}[rest[0].lower()]
    digits = rest[1:]
    if re.search(r"[xXzZ?]", digits):
        raise ValueError(f"x/z literal {s}")
    return int(digits, base), (int(w) if w else None)


# ------------------------------------------------------------------ parser

class P:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self, k=0):
        return self.t[self.i + k]

    def nxt(self):
        x = self.t[self.i]
        self.i += 1
        return x

    def at(self, v):
        return self.t[self.i][1] == v and self.t[self.i][0] in ("op", "id")

    def eat(self, v):
        x = self.nxt()
        if x[1] != v:
            raise SyntaxError(f"expected {v!r}, got {x!r} near {self.ctx()}")
        return x

    def opt(self, v):
        if self.at(v):
            self.i += 1
            return True
        return False

    def ident(self):
        x = self.nxt()
        if x[0] != "id":
            raise SyntaxError(f"expected identifier, got {x!r} near {self.ctx()}")
        return x[1]

    def ctx(self):
        return " ".join(v for _, v in self.t[max(0, self.i - 8):self.i + 8])

    # ---- expressions (precedence climbing)
    BIN = [["||"], ["&&"], ["|"], ["^", "^~", "~^"], ["&"], ["==", "!=", "===", "!=="],
           ["<", "<=", ">", ">="], ["<<", ">>", "<<<", ">>>"], ["+", "-"], ["*", "/", "%"], ["**"]]

    def expr(self):
        c = self.binary(0)
        if self.opt("?"):
            a = self.expr()
            self.eat(":")
            b = self.expr()
            return ("tern", c, a, b)
        return c

    def binary(self, lvl):
        if lvl == len(self.BIN):
            return self.unary()
        a = self.binary(lvl + 1)
        while self.peek()[0] == "op" and self.peek()[1] in self.BIN[lvl]:
            op = self.nxt()[1]
            b = self.binary(lvl + 1)
            a = ("bin", op, a, b)
        return a

    def unary(self):
        x = self.peek()
        if x[0] == "op" and x[1] in ("!", "~", "-", "+", "|", "&", "^", "~&", "~|", "~^"):
            self.nxt()
            return ("un", x[1], self.unary())
        return self.primary()

    def primary(self):
        x = self.nxt()
        if x[0] == "num":
            v, w = parse_num(x[1])
            return ("num", v, w)
        if x[0] == "str":
            return ("str", x[1][1:-1])
        if x[1] == "(":
            e = self.expr()
            self.eat(")")
            return e
        if x[1] == "{":
            first = self.expr()
            if self.at("{"):
                self.nxt()
                items = [self.expr()]
                while self.opt(","):
                    items.append(self.expr())
                self.eat("}")
                self.eat("}")
                return ("rep", first, items)
            items = [first]
            while self.opt(","):
                items.append(self.expr())
            self.eat("}")
            return ("cat", items)
        if x[0] == "id":
            nm = x[1]
            if self.at("("):
                self.nxt()
                args = [self.expr()]
                while self.opt(","):
                    args.append(self.expr())
                self.eat(")")
                return ("call", nm, args)
            e = ("id", nm)
            while self.at("["):
                self.nxt()
                a = self.expr()
                if self.opt(":"):
                    b = self.expr()
                    self.eat("]")
                    e = ("rng", e, a, b)
                elif self.opt("+:"):
                    b = self.expr()
                    self.eat("]")
                    e = ("pls", e, a, b)
                else:
                    self.eat("]")
                    e = ("idx", e, a)
            return e
        raise SyntaxError(f"bad expression at {x!r} near {self.ctx()}")

    # ---- declarations
    def rng(self):
        if self.at("["):
            self.nxt()
            a = self.expr()
            self.eat(":")
            b = self.expr()
            self.eat("]")
            return (a, b)
        return None

    def modules(self):
        mods = {}
        while self.peek()[0] != "eof":
            self.eat("module")
            m = self.module()
            mods[m["name"]] = m
        return mods

    def module(self):
        name = self.ident()
        params, ports = [], []
        if self.opt("#"):
            self.eat("(")
            while not self.at(")"):
                self.opt("parameter")
                typ = None
                if self.at("integer"):
                    self.nxt()
                    typ = "integer"
                r = self.rng()
                pn = self.ident()
                self.eat("=")
                params.append((pn, self.expr(), r))
                if not self.opt(","):
                    break
            self.eat(")")
        self.eat("(")
        while not self.at(")"):
            d = self.nxt()[1]
            assert d in ("input", "output", "inout"), (name, d)
            if self.at("wire") or self.at("reg"):
                self.nxt()
            r = self.rng()
            pn = self.ident()
            ports.append((pn, d, r))
            while self.at(","):
                if self.peek(1)[1] in ("input", "output", "inout"):
                    break
                self.nxt()
                ports.append((self.ident(), d, r))
            if not self.opt(","):
                break
        self.eat(")")
        self.eat(";")
        items = self.items(("endmodule",))
        self.eat("endmodule")
        return dict(name=name, params=params, ports=ports, items=items)

    def items(self, enders):
        its = []
        while not any(self.at(e) for e in enders):
            its.extend(self.item())
        return its

    def block(self):
        """generate body: `begin [: label] items end` or a single item."""
        if self.opt("begin"):
            lab = None
            if self.opt(":"):
                lab = self.ident()
            its = self.items(("end",))
            self.eat("end")
            return lab, its
        return None, self.item()

    def item(self):
        x = self.peek()
        v = x[1]
        if v in ("generate",):
            self.nxt()
            its = self.items(("endgenerate",))
            self.eat("endgenerate")
            return its
        if v in ("wire", "reg"):
            self.nxt()
            r = self.rng()
            out = []
            while True:
                n = self.ident()
                init = None
                if self.opt("="):
                    init = self.expr()
                out.append(("wire", n, r, init))
                if not self.opt(","):
                    break
            self.eat(";")
            return out
        if v in ("localparam", "parameter"):
            self.nxt()
            if self.at("integer"):
                self.nxt()
            r = self.rng()
            out = []
            while True:
                n = self.ident()
                self.eat("=")
                out.append(("lparam", n, self.expr(), r))
                if not self.opt(","):
                    break
            self.eat(";")
            return out
        if v == "genvar":
            self.nxt()
            self.ident()
            while self.opt(","):
                self.ident()
            self.eat(";")
            return []
        if v == "assign":
            self.nxt()
            out = []
            while True:
                lhs = self.expr()
                self.eat("=")
                out.append(("assign", lhs, self.expr()))
                if not self.opt(","):
                    break
            self.eat(";")
            return out
        if v == "if":
            self.nxt()
            self.eat("(")
            c = self.expr()
            self.eat(")")
            lab, th = self.block()
            el = None
            if self.opt("else"):
                if self.at("if"):
                    el = ("<elseif>", self.item())
                else:
                    el = self.block()
            return [("if", c, (lab, th), el)]
        if v == "for":
            self.nxt()
            self.eat("(")
            var = self.ident()
            self.eat("=")
            init = self.expr()
            self.eat(";")
            cond = self.expr()
            self.eat(";")
            v2 = self.ident()
            assert v2 == var
            self.eat("=")
            step = self.expr()
            self.eat(")")
            lab, its = self.block()
            return [("for", var, init, cond, step, lab, its)]
        if v == "function":
            while not self.at("endfunction"):
                self.nxt()
            self.nxt()
            return []
        if v == "always":
            self.nxt()
            self.eat("@")
            self.eat("(")
            depth = 1
            while depth:
                t = self.nxt()[1]
                depth += (t == "(") - (t == ")")
            self.skip_stmt()
            return [("always",)]
        if v == "begin":
            lab, its = self.block()
            return [("if", ("num", 1, None), (lab, its), None)]
        if x[0] == "id":
            mod = self.ident()
            pov = []
            if self.opt("#"):
                self.eat("(")
                while not self.at(")"):
                    if self.opt("."):
                        pn = self.ident()
                        self.eat("(")
                        pov.append((pn, self.expr()))
                        self.eat(")")
                    else:
                        pov.append((None, self.expr()))
                    if not self.opt(","):
                        break
                self.eat(")")
            inst = self.ident()
            self.eat("(")
            conns = []
            while not self.at(")"):
                self.eat(".")
                pn = self.ident()
                self.eat("(")
                e = None if self.at(")") else self.expr()
                self.eat(")")
                conns.append((pn, e))
                if not self.opt(","):
                    break
            self.eat(")")
            self.eat(";")
            return [("inst", mod, pov, inst, conns)]
        raise SyntaxError(f"unexpected {x!r} near {self.ctx()}")

    def skip_stmt(self):
        if self.opt("begin"):
            while not self.at("end"):
                self.skip_stmt()
            self.nxt()
            return
        while not self.at(";"):
            self.nxt()
        self.nxt()


def parse(texts, defines=None):
    """texts: list of (filename, source). Returns {module name: module}."""
    defines = {} if defines is None else defines
    mods = {}
    for fn, src in texts:
        t = preprocess(src, defines)
        try:
            ms = P(lex(t)).modules()
        except SyntaxError as e:
            raise SyntaxError(f"{fn}: {e}")
        for k, m in ms.items():
            m["file"] = fn
            assert k not in mods, f"module {k} defined twice"
            mods[k] = m
    return mods


# ------------------------------------------------------------------ constant evaluation

def mask(v, w):
    return v & ((1 << w) - 1) if w is not None else v


def ceval(e, env):
    """-> (value, width or None). env: name -> (value, width)."""
    k = e[0]
    if k == "num":
        return mask(e[1], e[2]), e[2]
    if k == "id":
        if e[1] not in env:
            raise KeyError(f"not a constant: {e[1]}")
        return env[e[1]]
    if k == "idx":
        v, w = ceval(e[1], env)
        i, _ = ceval(e[2], env)
        return (v >> i) & 1, 1
    if k == "rng":
        v, w = ceval(e[1], env)
        a, _ = ceval(e[2], env)
        b, _ = ceval(e[3], env)
        lo, hi = min(a, b), max(a, b)
        return mask(v >> lo, hi - lo + 1), hi - lo + 1
    if k == "cat":
        v, w = 0, 0
        for it in e[1]:
            x, xw = ceval(it, env)
            assert xw is not None, "unsized constant in concatenation"
            v = (v << xw) | mask(x, xw)
            w += xw
        return v, w
    if k == "rep":
        n, _ = ceval(e[1], env)
        x, xw = ceval(("cat", e[2]), env)
        v = 0
        for _ in range(n):
            v = (v << xw) | x
        return v, xw * n
    if k == "un":
        x, w = ceval(e[2], env)
        op = e[1]
        if op == "!":
            return int(x == 0), 1
        if op == "~":
            assert w is not None
            return mask(~x, w), w
        if op == "-":
            return -x, w
        if op == "+":
            return x, w
        if op == "|":
            return int(x != 0), 1
        raise ValueError(op)
    if k == "bin":
        a, aw = ceval(e[2], env)
        b, bw = ceval(e[3], env)
        op = e[1]
        w = None if aw is None or bw is None else max(aw, bw)
        r = {"+": lambda: a + b, "-": lambda: a - b, "*": lambda: a * b,
             "/": lambda: a // b, "%": lambda: a % b, "**": lambda: a ** b,
             "<<": lambda: a << b, ">>": lambda: a >> b,
             "&": lambda: a & b, "|": lambda: a | b, "^": lambda: a ^ b}.get(op)
        if r:
            return r(), w
        r = {"==": a == b, "!=": a != b, "<": a < b, "<=": a <= b, ">": a > b, ">=": a >= b,
             "&&": bool(a) and bool(b), "||": bool(a) or bool(b)}[op]
        return int(r), 1
    if k == "tern":
        c, _ = ceval(e[1], env)
        return ceval(e[2] if c else e[3], env)
    raise KeyError(f"not a constant expression: {e[0]}")


def etext(e):
    """Source-like text of an expression (names opaque drivers and inferred gates)."""
    k = e[0]
    if k == "num":
        return str(e[1]) if e[2] is None else f"{e[2]}'d{e[1]}"
    if k == "str":
        return f'"{e[1]}"'
    if k == "id":
        return e[1]
    if k == "idx":
        return f"{etext(e[1])}[{etext(e[2])}]"
    if k == "rng":
        return f"{etext(e[1])}[{etext(e[2])}:{etext(e[3])}]"
    if k == "pls":
        return f"{etext(e[1])}[{etext(e[2])} +: {etext(e[3])}]"
    if k == "cat":
        return "{" + ", ".join(etext(x) for x in e[1]) + "}"
    if k == "rep":
        return "{" + etext(e[1]) + "{" + ", ".join(etext(x) for x in e[2]) + "}}"
    if k == "un":
        return e[1] + etext(e[2])
    if k == "bin":
        return f"({etext(e[2])} {e[1]} {etext(e[3])})"
    if k == "tern":
        return f"({etext(e[1])} ? {etext(e[2])} : {etext(e[3])})"
    if k == "call":
        return f"{e[1]}(" + ", ".join(etext(x) for x in e[2]) + ")"
    raise ValueError(k)


# ------------------------------------------------------------------ elaboration

LUT_W = {"LUT1": 1, "LUT2": 2, "LUT3": 3, "LUT4": 4, "LUT5": 5, "LUT6": 6, "LUT6_2": 6}


class UF:
    def __init__(self):
        self.p = []

    def add(self):
        self.p.append(len(self.p))
        return len(self.p) - 1

    def find(self, x):
        p = self.p
        while p[x] != x:
            p[x] = p[p[x]]
            x = p[x]
        return x

    def union(self, a, b):
        a, b = self.find(a), self.find(b)
        if a != b:
            self.p[max(a, b)] = min(a, b)


class Scope:
    def __init__(self, path, module, env):
        self.path = path          # list of name components
        self.module = module      # module name of this instance (generate scopes: enclosing)
        self.env = env            # constants: name -> (value, width)
        self.nets = {}            # name -> (msb, lsb, vector?, [bit ids])
        self.parent = None        # enclosing scope for name lookup (generate blocks)
        self.gen = False

    def lookup(self, n):
        s = self
        while s is not None:
            if n in s.nets:
                return s.nets[n]
            if not s.gen:
                return None
            s = s.parent
        return None

    def const(self, n):
        return self.env.get(n)


class Elab:
    def __init__(self, mods):
        self.mods = mods
        self.ufa, self.ufp, self.ufw = UF(), UF(), UF()
        self.bitname = []         # bit id -> (path list, name string)
        self.cells = []           # LUT primitive instances
        self.opaque = {}          # bit id -> (scope path, expr text, [input bits], op)
        self.const = {}           # bit id -> 0/1
        self.top_inputs = {}      # name -> [bits]

    def newbit(self, path, name):
        b = self.ufa.add()
        assert self.ufp.add() == b
        assert self.ufw.add() == b
        self.bitname.append((tuple(path), name))
        return b

    def declare(self, sc, name, r):
        if name in sc.nets:
            return sc.nets[name]
        if r is None:
            msb, lsb, vec = 0, 0, False
        else:
            msb, _ = ceval(r[0], chain_env(sc))
            lsb, _ = ceval(r[1], chain_env(sc))
            vec = True
        w = abs(msb - lsb) + 1
        lo = min(msb, lsb)
        bits = [self.newbit(sc.path, f"{name}[{lo + i}]" if vec else name) for i in range(w)]
        sc.nets[name] = (msb, lsb, vec, bits)
        return sc.nets[name]

    # ---- net expressions -> list of bit items (LSB first): int bit id or ('k', v)
    def bits(self, e, sc, width=None):
        k = e[0]
        if k == "num":
            v, w = e[1], e[2]
            w = w if w is not None else (width or 32)
            return [("k", (v >> i) & 1) for i in range(w)]
        if k == "id":
            net = sc.lookup(e[1])
            if net is None:
                c = sc_const(sc, e[1])
                if c is None:
                    raise NameError(f"{'.'.join(sc.path)}: unknown name {e[1]}")
                v, w = c
                w = w if w is not None else (width or 32)
                return [("k", (v >> i) & 1) for i in range(w)]
            return list(net[3])
        if k in ("idx", "rng", "pls"):
            base = e[1]
            assert base[0] == "id", e
            net = sc.lookup(base[1])
            if net is None:  # select of a constant
                v, w = ceval(e, chain_env(sc))
                return [("k", (v >> i) & 1) for i in range(w)]
            msb, lsb, vec, bl = net
            lo = min(msb, lsb)
            if k == "idx":
                i, _ = ceval(e[2], chain_env(sc))
                return [bl[i - lo]]
            if k == "rng":
                a, _ = ceval(e[2], chain_env(sc))
                b, _ = ceval(e[3], chain_env(sc))
                return bl[min(a, b) - lo:max(a, b) - lo + 1]
            a, _ = ceval(e[2], chain_env(sc))
            w, _ = ceval(e[3], chain_env(sc))
            return bl[a - lo:a - lo + w]
        if k == "cat":
            out = []
            for it in reversed(e[1]):
                out.extend(self.bits(it, sc))
            return out
        if k == "rep":
            n, _ = ceval(e[1], chain_env(sc))
            one = self.bits(("cat", e[2]), sc)
            return one * n
        # opaque expression: fresh bits driven by it
        return self.opaque_bits(e, sc, width)

    def pure(self, e, sc):
        k = e[0]
        if k in ("num", "id"):
            return True
        if k in ("idx", "rng", "pls"):
            return True
        if k == "cat":
            return all(self.pure(x, sc) for x in e[1])
        if k == "rep":
            return all(self.pure(x, sc) for x in e[2])
        try:  # a constant expression (parameters only) is wiring too
            ceval(e, chain_env(sc))
            return True
        except (KeyError, ValueError, AssertionError):
            return False

    def refs(self, e, sc):
        """All net bits an opaque expression reads."""
        k = e[0]
        if k in ("id", "idx", "rng", "pls"):
            if self.pure(e, sc):
                return [b for b in self.bits(e, sc) if isinstance(b, int)]
        if k in ("num", "str"):
            return []
        if k == "cat":
            return [b for x in e[1] for b in self.refs(x, sc)]
        if k == "rep":
            return [b for x in e[2] for b in self.refs(x, sc)]
        if k == "un":
            return self.refs(e[2], sc)
        if k == "bin":
            return self.refs(e[2], sc) + self.refs(e[3], sc)
        if k == "tern":
            return self.refs(e[1], sc) + self.refs(e[2], sc) + self.refs(e[3], sc)
        if k == "call":
            return [b for x in e[2] for b in self.refs(x, sc)]
        raise ValueError(k)

    def ewidth(self, e, sc):
        k = e[0]
        if k == "un" and e[1] in ("|", "&", "^", "!", "~&", "~|", "~^"):
            return 1
        if k == "bin" and e[1] in ("==", "!=", "<", "<=", ">", ">=", "&&", "||", "===", "!=="):
            return 1
        if k == "bin":
            return mx(self.ewidth(e[2], sc), self.ewidth(e[3], sc))
        if k == "un":
            return self.ewidth(e[2], sc)
        if k == "tern":
            return mx(self.ewidth(e[2], sc), self.ewidth(e[3], sc))
        if k == "call":
            return None
        if k == "num":
            return e[2] or 32
        return len(self.bits(e, sc))

    def opaque_bits(self, e, sc, width):
        w = self.ewidth(e, sc)
        if w is None:
            w = width
        if width is not None:
            w = width
        ins = self.refs(e, sc)
        txt = etext(e)
        out = []
        for i in range(w):
            b = self.newbit(sc.path, f"<{txt}>[{i}]")
            op = "or" if (e[0] == "un" and e[1] == "|" and i == 0) else ("zero" if (e[0] == "un" and e[1] == "|") else "op")
            self.opaque[b] = (tuple(sc.path), txt, ins, op, i)
            out.append(b)
        return out

    def connect(self, a_bits, b_bits, port):
        """Alias two bit lists, LSB-aligned (shorter is zero-extended on the read side)."""
        for x, y in zip(a_bits, b_bits):
            self.alias(x, y, port)

    def alias(self, x, y, port, wire=True):
        if isinstance(x, tuple) and isinstance(y, tuple):
            return
        if isinstance(x, tuple):
            x, y = y, x
        if isinstance(y, tuple):  # bit tied to a constant
            r = self.const.setdefault(x, y[1])
            assert r == y[1], "bit tied to both constants"
            return
        self.ufa.union(x, y)
        if port:
            self.ufp.union(x, y)
        if port or wire:
            self.ufw.union(x, y)

    # ---- instances
    def elab_top(self, name, path, params=None):
        m = self.mods[name]
        sc = self.make_scope(m, path, params or {}, None)
        for pn, d, r in m["ports"]:
            if d == "input":
                self.top_inputs[pn] = sc.nets[pn][3]
        self.items(m["items"], sc)
        return sc

    def make_scope(self, m, path, pov, parent_sc):
        env = {}
        for pn, de, r in m["params"]:
            if pn in pov:
                v, w = pov[pn]
            else:
                v, w = ceval(de, env)
            if r is not None:
                hi, _ = ceval(r[0], env)
                lo, _ = ceval(r[1], env)
                w = abs(hi - lo) + 1
                v = mask(v, w)
            env[pn] = (v, w)
        sc = Scope(path, m["name"], env)
        for pn, d, r in m["ports"]:
            self.declare(sc, pn, r)
        return sc

    def items(self, items, sc):
        for it in items:
            k = it[0]
            if k == "wire":
                _, n, r, init = it
                net = self.declare(sc, n, r)
                if init is not None:
                    self.assign(net[3], init, sc)
            elif k == "lparam":
                _, n, e, r = it
                v, w = ceval(e, chain_env(sc))
                if r is not None:
                    hi, _ = ceval(r[0], chain_env(sc))
                    lo, _ = ceval(r[1], chain_env(sc))
                    w = abs(hi - lo) + 1
                    v = mask(v, w)
                sc.env[n] = (v, w)
            elif k == "assign":
                _, lhs, rhs = it
                lb = self.bits(lhs, sc)
                assert all(isinstance(b, int) for b in lb), "constant on an assign's left side"
                self.assign(lb, rhs, sc)
            elif k == "if":
                _, c, th, el = it
                cv, _ = ceval(c, chain_env(sc))
                pick = th if cv else el
                if pick is not None:
                    lab, its = pick
                    if lab == "<elseif>":
                        self.items(its, sc)
                    else:
                        self.genblock(sc, lab, its)
            elif k == "for":
                _, var, init, cond, step, lab, its = it
                v, _ = ceval(init, chain_env(sc))
                while True:
                    env = dict(chain_env(sc))
                    env[var] = (v, None)
                    if not ceval(cond, env)[0]:
                        break
                    self.genblock(sc, f"{lab}[{v}]", its, {var: (v, None)})
                    v, _ = ceval(step, env)
            elif k == "inst":
                self.inst(it, sc)
            elif k == "always":
                raise NotImplementedError(f"always block in {sc.module} (not used by gcd_hw)")
            else:
                raise ValueError(k)

    def genblock(self, sc, lab, its, extra=None):
        assert lab is not None, f"unlabelled generate block in {sc.module}"
        g = Scope(sc.path + [lab], sc.module, dict(extra or {}))
        g.parent, g.gen = sc, True
        self.items(its, g)

    def assign(self, lbits, rhs, sc):
        if self.pure(rhs, sc):
            rb = self.bits(rhs, sc, width=len(lbits))
            rb = rb + [("k", 0)] * (len(lbits) - len(rb))
            fan = fanout(rhs, sc)
            for x, y in zip(lbits, rb):
                self.alias(x, y, False, not fan)
        else:
            ob = self.opaque_bits(rhs, sc, len(lbits))
            for x, y in zip(lbits, ob):
                self.alias(x, y, False)

    def inst(self, it, sc):
        _, mod, pov, inst, conns = it
        env = chain_env(sc)
        if mod in LUT_W:
            pv = {pn: ceval(e, env) for pn, e in pov}
            init = pv["INIT"][0]
            pins, outs = {}, {}
            for pn, e in conns:
                if e is None:
                    continue
                b = self.bits(e, sc)
                assert len(b) == 1, (sc.path, inst, pn)
                (outs if pn.startswith("O") else pins)[pn] = b[0]
            self.cells.append(dict(path=tuple(sc.path + [inst]), type=mod, init=init, pins=pins,
                                   outs=outs, module=sc.module, scope=tuple(sc.path)))
            for o, b in outs.items():
                assert isinstance(b, int)
            return
        if mod not in self.mods:
            raise NameError(f"unknown module {mod} (instance {inst} in {sc.module})")
        m = self.mods[mod]
        names = [p[0] for p in m["params"]]
        povd = {}
        for j, (pn, e) in enumerate(pov):
            povd[pn if pn is not None else names[j]] = ceval(e, env)
        child = self.make_scope(m, sc.path + [inst], povd, sc)
        ports = {p[0]: p for p in m["ports"]}
        for pn, e in conns:
            if e is None:
                continue
            assert pn in ports, (mod, pn)
            cb = child.nets[pn][3]
            pb = self.bits(e, sc, width=len(cb))
            if len(pb) < len(cb):
                pb = pb + [("k", 0)] * (len(cb) - len(pb))
            self.connect(cb, pb, True)
        self.items(m["items"], child)


def fanout(e, sc):
    """A replication {N{x}} with N > 1 somewhere in a wiring expression: a fan-out copy
    (bd_fork's req_out, bd_join's ack_out), which `ufw` does not merge."""
    if e[0] == "rep":
        return ceval(e[1], chain_env(sc))[0] > 1 or any(fanout(x, sc) for x in e[2])
    if e[0] == "cat":
        return any(fanout(x, sc) for x in e[1])
    return False


def mx(a, b):
    return b if a is None else (a if b is None else max(a, b))


def chain_env(sc):
    env = {}
    chain = []
    s = sc
    while s is not None:
        chain.append(s)
        if not s.gen:
            break
        s = s.parent
    for s in reversed(chain):
        env.update(s.env)
    return env


def sc_const(sc, n):
    return chain_env(sc).get(n)
