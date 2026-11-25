"""C-8t: a small parser for the Lean terms in Formal/Net/CapstoneNet.lean (`ops`, `consT`, ...).

Terms are applications of names (`K.join`, `.bin`, `.cmpi`, `none`, ...) to atoms: numbers,
names, parenthesised terms or tuples, lists `[..]` and anonymous constructors `⟨..⟩`.
Result: ('app', head, [args]) | ('num', n) | ('name', s) | ('tuple', [..]) | ('list', [..]) |
('anon', [..]).
"""
import re

TOK = re.compile(r"\s*(?:(\d+)|([A-Za-z_.][A-Za-z_.0-9]*)|(.))", re.S)


def tokens(s):
    out = []
    pos = 0
    while pos < len(s):
        m = TOK.match(s, pos)
        if not m:
            break
        pos = m.end()
        if m.group(1) is not None:
            out.append(("num", int(m.group(1))))
        elif m.group(2) is not None:
            out.append(("name", m.group(2)))
        elif m.group(3) is not None and not m.group(3).isspace():
            out.append(("sym", m.group(3)))
    return out


class P:
    def __init__(self, s):
        self.t = tokens(s)
        self.i = 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else ("eof", None)

    def eat(self, v=None):
        tk = self.peek()
        if v is not None and tk[1] != v:
            raise ValueError(f"expected {v}, got {tk}")
        self.i += 1
        return tk

    def atom(self):
        k, v = self.peek()
        if k == "num":
            self.eat()
            return ("num", v)
        if k == "name":
            self.eat()
            return ("name", v)
        if v == "(":
            self.eat()
            xs = self.seq(")")
            return xs[0] if len(xs) == 1 else ("tuple", xs)
        if v == "[":
            self.eat()
            return ("list", self.seq("]"))
        if v == "⟨":
            self.eat()
            return ("anon", self.seq("⟩"))
        return None

    def seq(self, close):
        xs = []
        if self.peek()[1] == close:
            self.eat()
            return xs
        while True:
            xs.append(self.term())
            tk = self.eat()
            if tk[1] == close:
                return xs
            if tk[1] != ",":
                raise ValueError(f"bad separator {tk}")

    def term(self):
        h = self.atom()
        if h is None:
            raise ValueError(f"bad term at {self.peek()}")
        args = []
        while True:
            k, v = self.peek()
            if k in ("num", "name") or v in ("(", "[", "⟨"):
                args.append(self.atom())
            else:
                break
        if args:
            if h[0] != "name":
                raise ValueError("application of non-name")
            return ("app", h[1], args)
        return h


def parse(s):
    p = P(s)
    t = p.term()
    return t


def num(t):
    assert t[0] == "num", t
    return t[1]


def head(t):
    return t[1] if t[0] in ("app", "name") else None


def args(t):
    return t[2] if t[0] == "app" else []


def to_E(t):
    """Lean E -> walkcheck tuple form."""
    h = head(t)
    a = args(t)
    if h == ".var":
        return ("var", num(a[0]))
    if h == ".lit":
        return ("lit", num(a[0]))
    if h == ".un":
        o = a[0]
        if head(o) == ".extsi":
            op = ("extsi", num(args(o)[0]))
        else:
            op = head(o)[1:]
        return ("un", op, num(a[1]), to_E(a[2]))
    if h == ".bin":
        o = a[0]
        if head(o) == ".cmpi":
            op = ("cmpi", head(args(o)[0])[1:])
        else:
            op = head(o)[1:]
        return ("bin", op, num(a[1]), to_E(a[2]), to_E(a[3]))
    if h == ".sel":
        return ("sel", to_E(a[0]), to_E(a[1]), to_E(a[2]))
    raise ValueError(t)


def to_J(t):
    h = head(t)
    a = args(t)
    if h == ".direct":
        return ("direct", num(a[0]), num(a[1]))
    if h == ".fold":
        return ("fold", num(a[0]), num(a[1]), num(a[2]), num(a[3]), to_E(a[4]))
    if h == ".const":
        return ("const", num(a[0]), num(a[1]), to_E(a[2]))
    raise ValueError(t)


def nums(t):
    assert t[0] == "list", t
    return [num(x) for x in t[1]]


def to_K(t):
    """Lean `K NC` term -> dict."""
    h = head(t)
    a = args(t)
    k = h.split(".")[-1]
    if k == "forkG":
        return dict(k=k, i=num(a[0]), os=nums(a[1]))
    if k == "forkH":
        return dict(k=k, i=num(a[0]), os=[num(p[1][0]) for p in a[1][1]])
    if k == "join":
        return dict(k=k, ins=nums(a[0]), o=num(a[1]), e=to_E(a[2]), js=[to_J(j) for j in a[3][1]])
    if k == "bjoin":
        return dict(k=k, ins=nums(a[0]), o=num(a[1]), ec=to_E(a[2]), ed=to_E(a[3]))
    if k == "steerC":
        return dict(k=k, j=num(a[0]), t=num(a[1]), f=num(a[2]))
    if k == "steerD":
        return dict(k=k, j=num(a[0]), t=num(a[1]), f=num(a[2]), fd=to_E(a[3]))
    if k == "mux":
        return dict(k=k, c=num(a[0]), x=num(a[1]), y=num(a[2]), z=num(a[3]))
    if k == "muxn":
        return dict(k=k, c=num(a[0]), xs=[num(a[1]), num(a[2]), num(a[3])], z=num(a[4]))
    if k == "amerge":
        return dict(k=k, x=num(a[0]), y=num(a[1]), z=num(a[2]), w=num(a[3]))
    if k == "link":
        return dict(k=k, i=num(a[0]), o=num(a[1]))
    if k == "src":
        return dict(k=k, z=num(a[0]), which=num(a[1]), d=num(a[2]))
    if k == "sink":
        return dict(k=k, i=num(a[0]))
    raise ValueError(k)
