#!/usr/bin/env python3
"""cfront_w64_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py (and autoproof.py), CF_W64=1: 64-bit integers.

Types are 's' / 'u' (int / unsigned, 32 bits) and 'S' / 'U' (long long / unsigned long long, 64 bits; `long` is
read as 64 bits, LP64). Type names may be several words (`unsigned long long`, `long long int`, ...). Literal
suffixes u / l / ll / ul / ull, and C11 6.4.4.1's type rule (decimal unsuffixed: int, long; hex/octal unsuffixed:
int, unsigned, long, unsigned long; u: unsigned, unsigned long; l/ll: long, (hex) unsigned long; ul/ull: unsigned
long). Usual arithmetic conversions (C11 6.3.1.8) on + - * & | ^ comparisons ?: : both operands to the common type
(64-bit if either is; unsigned 64 if either is unsigned 64, else signed 64 -- long long represents every unsigned
int; for 32 bits the existing rule). A 32-bit operand widens by extsi (signed) or extui (unsigned); a narrowing
conversion (cast, assignment to a narrower variable, return from an int function) is trunci (modulo 2^32, the
gcc / two's-complement result). Shifts: the type of the promoted left operand, the count unconverted.
Conditions: `!= 0` at the operand's width. The transcription stays Ops / E (widths per operator).
autoproof's co-simulation then draws inputs and random states modulo 2^64 instead of 2^32 (M32 := 2^64)."""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
EXT = r'''

# ---------------------------------------------------------------------------
# CF_W64 (cfront_w64_patch.py): 64-bit integers. Redefines the pieces below when CF_W64=1.

if os.environ.get("CF_W64") == "1":
    TOK = re.compile(r"\s*(?:(//[^\n]*|/\*.*?\*/)|((?:0[xX][0-9a-fA-F]+|\d+)(?:[uU](?:ll|LL|l|L)?|(?:ll|LL|l|L)[uU]?)?)|"
                     r"([A-Za-z_]\w*)|"
                     r"(<<=|>>=|\+\+|--|&&|\|\||==|!=|<=|>=|<<|>>|\+=|-=|\*=|&=|\|=|\^=|[-+*/%&|^~!<>=?:;,(){}]))",
                     re.S)
    TYPEWORDS = {"int", "unsigned", "signed", "long"}

    def _W(t):
        return 64 if t in ("S", "U") else 32

    def _is_type(self, k=0):
        tk = self.peek(k)
        return tk[0] == "id" and (tk[1] in TYPES or tk[1] in TYPEWORDS)

    def _ty(self):
        ws = []
        while self.is_type() and not (ws and self.peek()[1] not in TYPEWORDS):
            ws.append(self.eat(kind="id")[1])
            if ws[-1] not in TYPEWORDS:
                break
        if len(ws) == 1 and ws[0] not in TYPEWORDS:
            return TYPES[ws[0]]
        if any(w not in TYPEWORDS for w in ws) or ws.count("long") > 2 or ("unsigned" in ws and "signed" in ws) \
                or ws.count("int") > 1 or ws.count("unsigned") + ws.count("signed") > 1:
            raise SyntaxError(f"cfront: unsupported type {' '.join(ws)!r}")
        uns = "unsigned" in ws
        if "long" in ws:
            return "U" if uns else "S"
        return "u" if uns else "s"

    def _func(self, name):
        while True:
            if self.peek()[0] == "eof":
                raise SyntaxError(f"cfront: function {name} not found")
            j = 0
            while self.is_type(j):
                j += 1
            if j and self.peek(j)[1] == name and self.peek(j + 1)[1] == "(":
                break
            self.i += 1
        rty = self.ty()
        self.eat(name)
        self.eat("(")
        params = []
        while not self.at(")"):
            if not self.is_type():
                raise SyntaxError(f"cfront: line {self.peek()[2]}: unsupported parameter type {self.peek()[1]!r}")
            ty = self.ty()
            params.append((ty, self.eat(kind="id")[1]))
            if self.at(","):
                self.eat(",")
        self.eat(")")
        body = self.block()
        return rty, params, body

    _old_simple = Parser.simple

    def _simple(self):
        if self.is_type():
            ty = self.ty()
            nm = self.eat(kind="id")[1]
            e = None
            if self.at("="):
                self.eat("=")
                e = self.expr()
            ds = [("decl", ty, nm, e)]
            while self.at(","):
                self.eat(",")
                nm = self.eat(kind="id")[1]
                e = None
                if self.at("="):
                    self.eat("=")
                    e = self.expr()
                ds.append(("decl", ty, nm, e))
            return ds[0] if len(ds) == 1 else ("blk", ds)
        return _old_simple(self)

    _old_unary = Parser.unary

    def _unary(self):
        tk = self.peek()
        if tk[1] == "(" and self.is_type(1):
            j = 1
            while self.is_type(j):
                j += 1
            if self.peek(j)[1] == ")":
                self.eat("(")
                ty = self.ty()
                self.eat(")")
                return ("cast", ty, self.unary())
        if tk[0] == "num":
            self.eat()
            m = re.fullmatch(r"(0[xX][0-9a-fA-F]+|\d+)([uUlL]*)", tk[1])
            body, suf = m.group(1), m.group(2).lower()
            hexa = body.lower().startswith("0x")
            octa = (not hexa) and len(body) > 1 and body.startswith("0")
            v = int(body, 16) if hexa else (int(body, 8) if octa else int(body))
            u, l = "u" in suf, "l" in suf
            if u and l:
                order = ["U"]
            elif u:
                order = ["u", "U"]
            elif l:
                order = ["S", "U"] if (hexa or octa) else ["S"]
            else:
                order = ["s", "u", "S", "U"] if (hexa or octa) else ["s", "S"]
            for t in order:
                lim = {"s": 2 ** 31, "u": 2 ** 32, "S": 2 ** 63, "U": 2 ** 64}[t]
                if v < lim:
                    return ("num", v, t)
            raise SyntaxError(f"cfront: line {tk[2]}: literal {tk[1]} does not fit any supported type")
        return _old_unary(self)

    def lit(v, w=32):
        return ("lit", v % (1 << w))

    def cmp(pred, a, b, w=32):
        return ("bin", ("cmpi", pred), w, a, b)

    def tobool(e, isb, w=32):
        return e if isb else cmp("ne", e, lit(0, w), w)

    def conv(x, tf, tt):
        wf, wt = _W(tf), _W(tt)
        if wf == wt:
            return x
        if wt < wf:
            return lit(x[1], wt) if x[0] == "lit" else ("un", "trunci", wt, x)
        if x[0] == "lit":
            v = x[1] % (1 << wf)
            if tf == "s" and v >= 2 ** 31:
                v += (1 << wt) - (1 << wf)
            return lit(v, wt)
        return ("un", ("extsi", wt), wf, x) if tf == "s" else ("un", "extui", wf, x)

    def common(ta, tb):
        if 64 in (_W(ta), _W(tb)):
            return "U" if "U" in (ta, tb) else "S"
        return "u" if "u" in (ta, tb) else "s"

    def _ex(self, e):
        """-> (E, type, is_bool)"""
        k = e[0]
        if k == "num":
            t = e[2] if len(e) > 2 else "s"
            return lit(e[1], _W(t)), t, False
        if k == "id":
            return ("var", self.slot(e[1])), self.types[e[1]], False
        if k == "cast":
            x, t, _ = self.ex(e[2])
            return conv(x, t, e[1]), e[1], False
        if k == "un":
            x, t, b = self.ex(e[2])
            w = _W(t)
            if e[1] == "-":
                if x[0] == "lit":
                    return lit(-x[1], w), t, False
                return ("bin", "subi", w, lit(0, w), x), t, False
            if e[1] == "+":
                return x, t, b
            if e[1] == "~":
                return ("bin", "xori", w, x, lit((1 << w) - 1, w)), t, False
            return cmp("eq", x, lit(0, w), w), "s", True
        if k == "cond":
            c, tc, cb = self.ex(e[1])
            a, ta, ab = self.ex(e[2])
            b, tb, bb = self.ex(e[3])
            t = common(ta, tb)
            return ("sel", tobool(c, cb, _W(tc)), conv(a, ta, t), conv(b, tb, t)), t, ab and bb and _W(t) == 32
        if k == "bin":
            op = e[1]
            a, ta, ab = self.ex(e[2])
            b, tb, bb = self.ex(e[3])
            if op == "&&":
                return ("sel", tobool(a, ab, _W(ta)), tobool(b, bb, _W(tb)), lit(0)), "s", True
            if op == "||":
                return ("sel", tobool(a, ab, _W(ta)), lit(1), tobool(b, bb, _W(tb))), "s", True
            if op in ("<<", ">>"):
                w = _W(ta)
                if op == "<<":
                    return ("bin", "shli", w, a, b), ta, False
                return ("bin", "shrsi" if ta in ("s", "S") else "shrui", w, a, b), ta, False
            t = common(ta, tb)
            w = _W(t)
            a, b = conv(a, ta, t), conv(b, tb, t)
            ar = {"+": "addi", "-": "subi", "*": "muli", "&": "andi", "|": "ori", "^": "xori"}
            if op in ar:
                return ("bin", ar[op], w, a, b), t, False
            sp = {"==": "eq", "!=": "ne", "<": "slt", "<=": "sle", ">": "sgt", ">=": "sge"}
            up = {"==": "eq", "!=": "ne", "<": "ult", "<=": "ule", ">": "ugt", ">=": "uge"}
            if op in sp:
                return cmp((up if t in ("u", "U") else sp)[op], a, b, w), "s", True
            raise SyntaxError(f"cfront: operator {op} is not supported (no Ops semantics)")
        raise ValueError(e)

    def _cond(self, e):
        x, t, b = self.ex(e)
        return tobool(x, b, _W(t))

    def _asg(self, slot, e):
        """the value an assignment / initialisation stores: converted to the variable's type"""
        x, t, _ = self.ex(e)
        return conv(x, t, self.types[self.vars[slot]])

    def _retv(self, e):
        x, t, _ = self.ex(e)
        return conv(x, t, self.rty)

    Parser.is_type = _is_type
    Parser.ty = _ty
    Parser.func = _func
    Parser.simple = _simple
    Parser.unary = _unary
    Lower.ex = _ex
    Lower.cond = _cond
    Lower.asg = _asg
    Lower.retv = _retv

    def sym_straight(cfg, node, env, seen=None):
        L = cfg.low
        seen = set() if seen is None else seen
        while True:
            if node is None:
                raise SyntaxError("cfront: control reaches the end of the function without a return")
            n = cfg.nodes[node]
            if n[0] == "test" and os.environ.get("CF_CONSTTEST") == "1" and "_hasvar" in globals():
                cc = subst(env, L.cond(n[1]))
                if not _hasvar(cc):
                    if node in seen:
                        raise SyntaxError("cfront: a cycle of constant tests")
                    seen.add(node)
                    node = n[2] if ev(cc, []) % 2 == 1 else n[3]
                    continue
            if n[0] == "test":
                return ("test", node, env)
            if n[0] == "ret":
                return ("ret", subst(env, L.retv(n[1])), env)
            if node in seen:
                raise SyntaxError("cfront: a loop without a test (infinite straight-line cycle)")
            seen.add(node)
            if n[0] == "asg":
                env = list(env)
                env[n[1]] = subst(env, L.asg(n[1], n[2]))
                node = n[3]
            elif n[0] == "ifc":
                c = subst(env, L.cond(n[1]))
                e1 = sym_stmt(L, n[2], env)
                e2 = sym_stmt(L, n[3], env) if n[3] is not None else env
                env = [a if a == b else ("sel", c, a, b) for a, b in zip(e1, e2)]
                node = n[4]

    def sym_stmt(L, s, env):
        k = s[0]
        if k == "blk":
            for x in s[1]:
                env = sym_stmt(L, x, env)
            return env
        if k == "asg":
            env = list(env)
            sl = L.slot(s[1])
            env[sl] = subst(env, L.asg(sl, s[2]))
            return env
        if k == "if":
            c = subst(env, L.cond(s[1]))
            e1 = sym_stmt(L, s[2], env)
            e2 = sym_stmt(L, s[3], env) if s[3] is not None else env
            return [a if a == b else ("sel", c, a, b) for a, b in zip(e1, e2)]
        if k == "decl":
            raise SyntaxError("cfront: declaration inside an if-converted branch (declare it before)")
        raise SyntaxError(f"cfront: unexpected {k} in an if-converted branch")

    def check_typedefs(path, src):
        texts = [src]
        for inc in re.findall(r'^\s*#\s*include\s+"([^"]+)"', src, re.M):
            h = os.path.join(os.path.dirname(os.path.abspath(path)), inc)
            if os.path.exists(h):
                texts.append(open(h).read())
        for t in texts:
            for ty, name in re.findall(r"typedef\s+([\w\s]+?)\s+(\w+)\s*;", t):
                if name in TYPES:
                    ws = ty.split()
                    if any(w not in TYPEWORDS for w in ws) or ws.count("long") == 1 and len(ws) == 1 and False:
                        raise SyntaxError(f"cfront: {name} is `{ty}`: unsupported")
                    uns = "unsigned" in ws
                    TYPES[name] = ("U" if uns else "S") if "long" in ws else ("u" if uns else "s")
'''
old = '\nif __name__ == "__main__":\n'
assert s.count(old) == 1
s = s.replace(old, EXT + old)
open(c, 'w').write(s)
a = os.path.join(sys.argv[1], 'autoproof', 'autoproof.py')
if not os.path.exists(a):
    sys.exit(0)
t = open(a).read()
old = "M32 = 1 << 32\n"
assert t.count(old) == 1
t = t.replace(old, "M32 = 1 << (64 if os.environ.get('CF_W64') == '1' else 32)\n")
open(a, 'w').write(t)
