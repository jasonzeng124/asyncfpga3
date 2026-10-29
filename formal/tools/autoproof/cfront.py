#!/usr/bin/env python3
"""C front end of autoproof (probe C-vk2): one C function -> a test-point automaton.

    python3 cfront.py FILE.c FUNC          # prints the automaton

Reads a small C subset, on purpose (anything else is refused with a message):
  * one function `int|unsigned F(T a, T b, ...)` with T in {int, unsigned, in_int_t};
  * statements: declarations `int x;` `int x = e;` (also `unsigned`), `x = e;`,
    `x op= e;` (op in + - * & | ^ << >>), `x++` `x--` `++x` `--x`, `if (c) s [else s]`,
    `while (c) s`, `do s while (c);`, `for (init; c; step) s`, `return e;`, blocks;
  * expressions: decimal/hex literals, variables, `+ - * & | ^ ~ << >> == != < <= > >=
    ! && || ?:`, unary `-`, casts `(int)` `(unsigned)`.
  No division/modulo (no `Ops` for them), no pointers, arrays, calls, `break`/`continue`.

Semantics (the SAME integer model as Formal.Net.GcdHw.Ops, i.e. the hardware's):
`int`/`unsigned` values are 32-bit patterns (Nat < 2^32); `+ - *` wrap (C leaves signed
overflow undefined: the transcription takes the two's complement wrap the circuit
computes); `>>` is arithmetic on `int` (shrsi) and logical on `unsigned` (shrui), `<<` is
shli; comparisons are signed unless an operand is unsigned (C's usual arithmetic
conversions for 32-bit int/unsigned); `!`, `&&`, `||`, `?:` and conditions use C's
"nonzero is true" (`!= 0`); a comparison, `!`, `&&`, `||` is a 0/1 value. `&&`/`||`
do not short-circuit, which is equivalent because expressions have no side effects.
An uninitialised local starts at 0 (C leaves it indeterminate; the generator's
co-simulation would expose a kernel that reads one).

Output: Expressions are tuples mirroring Lean's `E` (the same as dfimport's):
("var", k) ("lit", v) ("un", uop, w, a) ("bin", bop, w, a, b) ("sel", s, a, b).
The automaton (class CProg) has: `vars` (names; the parameters first, in order),
`entry` (the state at the first test point, over the parameters), `start`, `tests[p]`
(the condition of test point p, over the state there, a 0/1 value), `edges` =
(src, br, upd, dst, ret, note): from test point src on outcome br, the parallel
assignment upd (one expression per variable, over the state at src) then the test
point dst, or dst None and return ret (over the updated state).

A test point is a loop condition, or the condition of an `if` that contains a loop,
a `return` or a nested test point. An `if` whose arms are only assignments is
if-converted into `sel` expressions (pure, so this is exact).
"""
import re
import sys

M32 = 1 << 32

# ---------------------------------------------------------------------------
# lexer

TOK = re.compile(r"\s*(?:(//[^\n]*|/\*.*?\*/)|(0[xX][0-9a-fA-F]+[uU]?|\d+[uU]?)|([A-Za-z_]\w*)|"
                 r"(<<=|>>=|\+\+|--|&&|\|\||==|!=|<=|>=|<<|>>|\+=|-=|\*=|&=|\|=|\^=|[-+*/%&|^~!<>=?:;,(){}]))",
                 re.S)


def lex(src):
    src = re.sub(r"^\s*#.*$", "", src, flags=re.M)
    out, i = [], 0
    while i < len(src):
        m = TOK.match(src, i)
        if not m:
            if src[i:].strip() == "":
                break
            raise SyntaxError(f"cfront: cannot lex at {src[i:i + 30]!r}")
        i = m.end()
        if m.group(1):
            continue
        line = src.count("\n", 0, m.start(0)) + 1
        if m.group(2):
            out.append(("num", m.group(2), line))
        elif m.group(3):
            out.append(("id", m.group(3), line))
        else:
            out.append(("op", m.group(4), line))
    out.append(("eof", "", 0))
    return out


# ---------------------------------------------------------------------------
# parser -> AST
#   expr: ("num", v) ("id", name) ("un", op, e) ("bin", op, a, b) ("cond", c, a, b) ("cast", ty, e)
#   stmt: ("decl", ty, name, e|None) ("asg", name, e) ("if", c, s, s|None) ("while", c, s)
#         ("do", s, c) ("for", init, c, step, s) ("ret", e) ("blk", [s])

TYPES = {"int": "s", "unsigned": "u", "in_int_t": "s", "out_int_t": "s"}
BINPREC = [["||"], ["&&"], ["|"], ["^"], ["&"], ["==", "!="], ["<", "<=", ">", ">="], ["<<", ">>"],
           ["+", "-"], ["*"]]


class Parser:
    def __init__(self, toks):
        self.t = toks
        self.i = 0

    def peek(self, k=0):
        return self.t[self.i + k]

    def eat(self, v=None, kind=None):
        tk = self.t[self.i]
        if (v is not None and tk[1] != v) or (kind is not None and tk[0] != kind):
            raise SyntaxError(f"cfront: line {tk[2]}: expected {v or kind}, got {tk[1]!r}")
        self.i += 1
        return tk

    def at(self, v):
        return self.t[self.i][1] == v and self.t[self.i][0] in ("op", "id")

    def is_type(self):
        tk = self.peek()
        return tk[0] == "id" and tk[1] in TYPES

    def func(self, name):
        while True:
            if self.peek()[0] == "eof":
                raise SyntaxError(f"cfront: function {name} not found")
            if (self.is_type() and self.peek(1)[1] == name and self.peek(2)[1] == "("):
                break
            self.i += 1
        rty = TYPES[self.eat(kind="id")[1]]
        self.eat(name)
        self.eat("(")
        params = []
        while not self.at(")"):
            if not self.is_type():
                raise SyntaxError(f"cfront: line {self.peek()[2]}: unsupported parameter type {self.peek()[1]!r}")
            ty = TYPES[self.eat(kind="id")[1]]
            params.append((ty, self.eat(kind="id")[1]))
            if self.at(","):
                self.eat(",")
        self.eat(")")
        body = self.block()
        return rty, params, body

    def block(self):
        self.eat("{")
        ss = []
        while not self.at("}"):
            ss.append(self.stmt())
        self.eat("}")
        return ("blk", ss)

    def simple(self):
        """assignment-like statement without the trailing ';'"""
        if self.is_type():
            ty = TYPES[self.eat(kind="id")[1]]
            nm = self.eat(kind="id")[1]
            e = None
            if self.at("="):
                self.eat("=")
                e = self.expr()
            return ("decl", ty, nm, e)
        if self.at("++") or self.at("--"):
            op = self.eat()[1]
            nm = self.eat(kind="id")[1]
            return ("asg", nm, ("bin", op[0], ("id", nm), ("num", 1)))
        nm = self.eat(kind="id")[1]
        tk = self.eat(kind="op")[1]
        if tk in ("++", "--"):
            return ("asg", nm, ("bin", tk[0], ("id", nm), ("num", 1)))
        if tk == "=":
            return ("asg", nm, self.expr())
        if tk.endswith("=") and tk[:-1] in ("+", "-", "*", "&", "|", "^", "<<", ">>"):
            return ("asg", nm, ("bin", tk[:-1], ("id", nm), self.expr()))
        raise SyntaxError(f"cfront: unsupported statement at {nm} {tk}")

    def stmt(self):
        tk = self.peek()
        if tk[1] == "{":
            return self.block()
        if tk[0] == "id" and tk[1] == "if":
            self.eat()
            self.eat("(")
            c = self.expr()
            self.eat(")")
            s = self.stmt()
            e = None
            if self.peek()[1] == "else":
                self.eat()
                e = self.stmt()
            return ("if", c, s, e, tk[2])
        if tk[0] == "id" and tk[1] == "while":
            self.eat()
            self.eat("(")
            c = self.expr()
            self.eat(")")
            return ("while", c, self.stmt(), tk[2])
        if tk[0] == "id" and tk[1] == "do":
            self.eat()
            s = self.stmt()
            self.eat("while")
            self.eat("(")
            c = self.expr()
            self.eat(")")
            self.eat(";")
            return ("do", s, c, tk[2])
        if tk[0] == "id" and tk[1] == "for":
            self.eat()
            self.eat("(")
            init = None if self.at(";") else self.simple()
            self.eat(";")
            c = ("num", 1) if self.at(";") else self.expr()
            self.eat(";")
            step = None if self.at(")") else self.simple()
            self.eat(")")
            return ("for", init, c, step, self.stmt(), tk[2])
        if tk[0] == "id" and tk[1] == "return":
            self.eat()
            e = self.expr()
            self.eat(";")
            return ("ret", e, tk[2])
        if tk[0] == "id" and tk[1] in ("break", "continue", "goto", "switch"):
            raise SyntaxError(f"cfront: line {tk[2]}: `{tk[1]}` is not supported")
        if tk[1] == ";":
            self.eat()
            return ("blk", [])
        s = self.simple()
        self.eat(";")
        return s

    def expr(self):
        c = self.binary(0)
        if self.at("?"):
            self.eat("?")
            a = self.expr()
            self.eat(":")
            b = self.expr()
            return ("cond", c, a, b)
        return c

    def binary(self, lvl):
        if lvl == len(BINPREC):
            return self.unary()
        a = self.binary(lvl + 1)
        while self.peek()[0] == "op" and self.peek()[1] in BINPREC[lvl]:
            op = self.eat()[1]
            a = ("bin", op, a, self.binary(lvl + 1))
        return a

    def unary(self):
        tk = self.peek()
        if tk[0] == "op" and tk[1] in ("-", "~", "!", "+"):
            self.eat()
            return ("un", tk[1], self.unary())
        if tk[1] == "(" and self.peek(1)[0] == "id" and self.peek(1)[1] in TYPES and self.peek(2)[1] == ")":
            self.eat("(")
            ty = TYPES[self.eat()[1]]
            self.eat(")")
            return ("cast", ty, self.unary())
        if tk[1] == "(":
            self.eat("(")
            e = self.expr()
            self.eat(")")
            return e
        if tk[0] == "num":
            self.eat()
            s = tk[1].rstrip("uU")
            v = int(s, 16) if s.lower().startswith("0x") else int(s)
            return ("num", v, "u" if tk[1][-1] in "uU" or v >= 2 ** 31 else "s")
        if tk[0] == "id":
            self.eat()
            if self.at("("):
                raise SyntaxError(f"cfront: line {tk[2]}: function calls are not supported")
            return ("id", tk[1])
        raise SyntaxError(f"cfront: line {tk[2]}: unexpected {tk[1]!r}")


# ---------------------------------------------------------------------------
# expressions -> E (over variable slots)

def lit(v):
    return ("lit", v % M32)


def cmp(pred, a, b):
    return ("bin", ("cmpi", pred), 32, a, b)


def tobool(e, isb):
    return e if isb else cmp("ne", e, lit(0))


class Lower:
    def __init__(self, rty, params):
        self.vars = [nm for _, nm in params]
        self.types = {nm: ty for ty, nm in params}
        self.rty = rty

    def slot(self, nm):
        if nm not in self.types:
            raise SyntaxError(f"cfront: undeclared variable {nm}")
        return self.vars.index(nm)

    def declare(self, ty, nm):
        if nm in self.types:
            raise SyntaxError(f"cfront: variable {nm} declared twice (shadowing is not supported)")
        self.types[nm] = ty
        self.vars.append(nm)

    def ex(self, e):
        """-> (E, type 's'|'u', is_bool)"""
        k = e[0]
        if k == "num":
            return lit(e[1]), e[2] if len(e) > 2 else "s", False
        if k == "id":
            return ("var", self.slot(e[1])), self.types[e[1]], False
        if k == "cast":
            x, _, _ = self.ex(e[2])
            return x, e[1], False
        if k == "un":
            x, t, b = self.ex(e[2])
            if e[1] == "-":
                if x[0] == "lit":
                    return lit(-x[1]), t, False
                return ("bin", "subi", 32, lit(0), x), t, False
            if e[1] == "+":
                return x, t, b
            if e[1] == "~":
                return ("bin", "xori", 32, x, lit(M32 - 1)), t, False
            return cmp("eq", x, lit(0)), "s", True
        if k == "cond":
            c, _, cb = self.ex(e[1])
            a, ta, ab = self.ex(e[2])
            b, tb, bb = self.ex(e[3])
            return ("sel", tobool(c, cb), a, b), ("u" if "u" in (ta, tb) else "s"), ab and bb
        if k == "bin":
            op = e[1]
            a, ta, ab = self.ex(e[2])
            b, tb, bb = self.ex(e[3])
            t = "u" if "u" in (ta, tb) else "s"
            if op == "&&":
                return ("sel", tobool(a, ab), tobool(b, bb), lit(0)), "s", True
            if op == "||":
                return ("sel", tobool(a, ab), lit(1), tobool(b, bb)), "s", True
            ar = {"+": "addi", "-": "subi", "*": "muli", "&": "andi", "|": "ori", "^": "xori"}
            if op in ar:
                return ("bin", ar[op], 32, a, b), t, False
            if op == "<<":
                return ("bin", "shli", 32, a, b), ta, False
            if op == ">>":
                return ("bin", "shrsi" if ta == "s" else "shrui", 32, a, b), ta, False
            sp = {"==": "eq", "!=": "ne", "<": "slt", "<=": "sle", ">": "sgt", ">=": "sge"}
            up = {"==": "eq", "!=": "ne", "<": "ult", "<=": "ule", ">": "ugt", ">=": "uge"}
            if op in sp:
                return cmp((up if t == "u" else sp)[op], a, b), "s", True
            raise SyntaxError(f"cfront: operator {op} is not supported (no Ops semantics)")
        raise ValueError(e)

    def cond(self, e):
        x, _, b = self.ex(e)
        return tobool(x, b)


# ---------------------------------------------------------------------------
# AST -> CFG -> automaton

def subst(env, e):
    t = e[0]
    if t == "var":
        return env[e[1]] if e[1] < len(env) else ("lit", 0)
    if t == "lit":
        return e
    if t == "un":
        return ("un", e[1], e[2], subst(env, e[3]))
    if t == "bin":
        return ("bin", e[1], e[2], subst(env, e[3]), subst(env, e[4]))
    return ("sel", subst(env, e[1]), subst(env, e[2]), subst(env, e[3]))


def has_ctl(s):
    """does the statement contain a loop, a return or a non-convertible if"""
    k = s[0]
    if k in ("while", "do", "for", "ret"):
        return True
    if k == "blk":
        return any(has_ctl(x) for x in s[1])
    if k == "if":
        return has_ctl(s[2]) or (s[3] is not None and has_ctl(s[3]))
    return False


class CFG:
    """nodes: ("asg", slot, E_ast, next) ("ifc", cond_ast, then_stmt, else_stmt, next)
    ("test", cond_ast, tnext, fnext, line) ("ret", e_ast, line)"""

    def __init__(self, low):
        self.low = low
        self.nodes = []

    def new(self, n):
        self.nodes.append(list(n))
        return len(self.nodes) - 1

    def build(self, s, nxt):
        """returns the entry node of s, continuing with nxt"""
        k = s[0]
        L = self.low
        if k == "blk":
            for x in reversed(s[1]):
                nxt = self.build(x, nxt)
            return nxt
        if k == "decl":
            if s[3] is None:
                return self.new(("asg", L.slot(s[2]), ("num", 0), nxt))
            return self.new(("asg", L.slot(s[2]), s[3], nxt))
        if k == "asg":
            return self.new(("asg", L.slot(s[1]), s[2], nxt))
        if k == "ret":
            return self.new(("ret", s[1], s[2]))
        if k == "if":
            if not has_ctl(s):
                # declarations inside a converted if would be scoped: refuse
                return self.new(("ifc", s[1], s[2], s[3], nxt))
            t = self.build(s[2], nxt)
            f = self.build(s[3], nxt) if s[3] is not None else nxt
            return self.new(("test", s[1], t, f, s[4]))
        if k == "while":
            tn = self.new(("test", s[1], None, nxt, s[3]))
            body = self.build(s[2], tn)
            self.nodes[tn][2] = body
            return tn
        if k == "do":
            tn = self.new(("test", s[2], None, nxt, s[3]))
            body = self.build(s[1], tn)
            self.nodes[tn][2] = body
            return body
        if k == "for":
            tn = self.new(("test", s[2], None, nxt, s[5]))
            step = self.build(s[3], tn) if s[3] is not None else tn
            body = self.build(s[4], step)
            self.nodes[tn][2] = body
            return self.build(s[1], tn) if s[1] is not None else tn
        raise ValueError(s)


def sym_straight(cfg, node, env, seen=None):
    """run assignment nodes symbolically from node: -> ("test", node, env) | ("ret", E, env)"""
    L = cfg.low
    seen = set() if seen is None else seen
    while True:
        if node is None:
            raise SyntaxError("cfront: control reaches the end of the function without a return")
        n = cfg.nodes[node]
        if n[0] == "test":
            return ("test", node, env)
        if n[0] == "ret":
            return ("ret", subst(env, L.ex(n[1])[0]), env)
        if node in seen:
            raise SyntaxError("cfront: a loop without a test (infinite straight-line cycle)")
        seen.add(node)
        if n[0] == "asg":
            env = list(env)
            env[n[1]] = subst(env, L.ex(n[2])[0])
            node = n[3]
        elif n[0] == "ifc":
            c = subst(env, L.cond(n[1]))
            e1 = sym_stmt(L, n[2], env)
            e2 = sym_stmt(L, n[3], env) if n[3] is not None else env
            env = [a if a == b else ("sel", c, a, b) for a, b in zip(e1, e2)]
            node = n[4]


def sym_stmt(L, s, env):
    """symbolic execution of an assignment-only statement"""
    k = s[0]
    if k == "blk":
        for x in s[1]:
            env = sym_stmt(L, x, env)
        return env
    if k == "asg":
        env = list(env)
        env[L.slot(s[1])] = subst(env, L.ex(s[2])[0])
        return env
    if k == "if":
        c = subst(env, L.cond(s[1]))
        e1 = sym_stmt(L, s[2], env)
        e2 = sym_stmt(L, s[3], env) if s[3] is not None else env
        return [a if a == b else ("sel", c, a, b) for a, b in zip(e1, e2)]
    if k == "decl":
        raise SyntaxError("cfront: declaration inside an if-converted branch (declare it before)")
    raise SyntaxError(f"cfront: unexpected {k} in an if-converted branch")


class CProg:
    pass


def declare_all(L, s):
    """declare every local in program order (one function-wide scope)"""
    k = s[0]
    if k == "decl":
        L.declare(s[1], s[2])
    elif k == "blk":
        for x in s[1]:
            declare_all(L, x)
    elif k == "if":
        declare_all(L, s[2])
        if s[3] is not None:
            declare_all(L, s[3])
    elif k == "while":
        declare_all(L, s[2])
    elif k == "do":
        declare_all(L, s[1])
    elif k == "for":
        if s[1] is not None:
            declare_all(L, s[1])
        declare_all(L, s[4])


def front(path, func):
    src = open(path).read()
    rty, params, body = Parser(lex(src)).func(func)
    L = Lower(rty, params)
    declare_all(L, body)
    cfg = CFG(L)
    entry_node = cfg.build(body, None)
    nv = len(L.vars)
    ident = [("var", i) for i in range(nv)]
    tests = sorted((i for i, n in enumerate(cfg.nodes) if n[0] == "test"), key=lambda i: (cfg.nodes[i][4], i))
    pidx = {n: p for p, n in enumerate(tests)}
    P = CProg()
    P.vars = L.vars
    P.params = [nm for _, nm in params]
    P.types = L.types
    P.path, P.func = path, func
    # entry: locals start at 0
    init = [("var", i) if i < len(params) else ("lit", 0) for i in range(nv)]
    r = sym_straight(cfg, entry_node, init)
    if r[0] != "test":
        raise SyntaxError("cfront: the function has no test (no loop and no branch): nothing to cut")
    P.entry = r[2]
    P.start = pidx[r[1]]
    P.tests = [L.cond(cfg.nodes[n][1]) for n in tests]
    P.lines = [cfg.nodes[n][4] for n in tests]
    P.edges = []
    for p, n in enumerate(tests):
        for br, nxt in ((True, cfg.nodes[n][2]), (False, cfg.nodes[n][3])):
            r = sym_straight(cfg, nxt, ident)
            if r[0] == "test":
                P.edges.append((p, br, r[2], pidx[r[1]], ("lit", 0)))
            else:
                P.edges.append((p, br, r[2], None, r[1]))
    return P


# ---------------------------------------------------------------------------
# evaluation (mirrors Formal.Net.GcdHw.Ops / E.eval exactly, on Nat)

def ev(e, env):
    t = e[0]
    if t == "var":
        return env[e[1]] if e[1] < len(env) else 0
    if t == "lit":
        return e[1]
    if t == "sel":
        return ev(e[2], env) if ev(e[1], env) % 2 == 1 else ev(e[3], env)
    if t == "un":
        o, w, a = e[1], e[2], ev(e[3], env)
        if o in ("trunci", "extui"):
            return a % (1 << w)
        dw = o[1]
        x = a % (1 << w)
        return x if x < (1 << (w - 1)) else x + (1 << dw) - (1 << w)
    o, w, a, b = e[1], e[2], ev(e[3], env), ev(e[4], env)
    M = 1 << w
    if o == "addi":
        return (a + b) % M
    if o == "subi":
        return (a % M + M - b % M) % M
    if o == "muli":
        return (a * b) % M
    if o == "andi":
        return (a & b) % M
    if o == "ori":
        return (a | b) % M
    if o == "xori":
        return (a ^ b) % M
    if o == "shli":
        return 0 if b >= w else (a << b) % M
    if o == "shrui":
        return (a % M) >> b if b < 4096 else 0
    if o == "shrsi":
        x = a % M
        if x < (1 << (w - 1)):
            return x >> b if b < 4096 else 0
        return (M - 1) - (((M - 1 - x) >> b) if b < 4096 else 0)
    if isinstance(o, tuple):
        p = o[1]
        x, y = a % M, b % M
        sx, sy = (x + (1 << (w - 1))) % M, (y + (1 << (w - 1))) % M
        r = {"eq": x == y, "ne": x != y, "ult": x < y, "ule": x <= y, "ugt": y < x, "uge": y <= x,
             "slt": sx < sy, "sle": sx <= sy, "sgt": sy < sx, "sge": sy <= sx}[p]
        return 1 if r else 0
    raise ValueError(e)


def run(P, ins, fuel=100000):
    """-> (result or None, trace of (point, state, edge index))"""
    st = [ev(x, ins) for x in P.entry]
    p = P.start
    trace = []
    for _ in range(fuel):
        b = ev(P.tests[p], st) % 2 == 1
        ei = [i for i, e in enumerate(P.edges) if e[0] == p and e[1] == b][0]
        trace.append((p, st, ei))
        e = P.edges[ei]
        st2 = [ev(x, st) for x in e[2]]
        if e[3] is None:
            return ev(e[4], st2), trace
        p, st = e[3], st2
    return None, trace


def show(e, names):
    t = e[0]
    if t == "var":
        return names[e[1]] if e[1] < len(names) else f"v{e[1]}"
    if t == "lit":
        return str(e[1])
    if t == "sel":
        return f"({show(e[1], names)} ? {show(e[2], names)} : {show(e[3], names)})"
    if t == "un":
        return f"{e[1] if isinstance(e[1], str) else 'extsi'}{e[2]}({show(e[3], names)})"
    o = e[1]
    on = o[1] if isinstance(o, tuple) else o
    return f"{on}({show(e[3], names)}, {show(e[4], names)})"


def main():
    P = front(sys.argv[1], sys.argv[2])
    print("vars", P.vars)
    print("entry", [show(x, P.params) for x in P.entry], "start", P.start)
    for p, t in enumerate(P.tests):
        print(f"test {p} (line {P.lines[p]}): {show(t, P.vars)}")
    for e in P.edges:
        print(f"  {e[0]} {'T' if e[1] else 'F'} -> {e[3]}: " +
              ", ".join(f"{P.vars[i]}={show(x, P.vars)}" for i, x in enumerate(e[2]) if x != ("var", i)) +
              (f"  return {show(e[4], P.vars)}" if e[3] is None else ""))
    if len(sys.argv) > 3:
        ins = [int(x) % M32 for x in sys.argv[3:]]
        print("run", run(P, ins)[0])


if __name__ == "__main__":
    main()
