#!/usr/bin/env python3
"""check3 (probe C-11f): a Python mirror of Formal.Net.FasmDesign.Inst.check, run on the
generated Lean data (parsed back from C*.lean + Rho.lean). Used to locate a failing
instance quickly; the Lean `decide` is the check that counts.

    python3 check3.py LEANDIR
"""
import itertools
import re
import sys
import os

INPINS = {"lut6_2": ["I0", "I1", "I2", "I3", "I4", "I5"], "muxf7": ["I0", "I1", "S"], "muxf8": ["I0", "I1", "S"],
          "carry4": ["CI", "CYINIT", "DI0", "DI1", "DI2", "DI3", "S0", "S1", "S2", "S3"],
          "fdre": ["C", "CE", "D", "R", "Q", "M"], "fdse": ["C", "CE", "D", "S", "Q", "M"],
          "fdce": ["C", "CE", "CLR", "D", "Q", "M"], "fdpe": ["C", "CE", "PRE", "D", "Q", "M"], "buf": ["I"]}
T = {"FFQ_SYNC": 0xFFFFAAAA55550000, "FDRE_M": 0xAAFBAAEA00510040, "FDSE_M": 0xFFFBFFEA55515540,
     "FDCE_Q": 0x0F0F0A0A05050000, "FDCE_M": 0x0F0B0E0A05010400, "FDPE_Q": 0xFFFFFAFAF5F5F0F0,
     "FDPE_M": 0xFFFBFEFAF5F1F4F0}


def tb(init, ins):
    a = sum(int(v) << k for k, v in enumerate(ins))
    return bool((init >> a) & 1)


def inpins(kind):
    m = re.match(r"lut (\d)", kind)
    if m:
        return ["I%d" % i for i in range(int(m.group(1)))]
    return INPINS.get(kind.split()[0], [])


def out(kind, init, pin, ins):
    k = kind.split()[0]
    if kind.startswith("lut ") and pin == "O":
        return tb(init, ins)
    if k == "lut6_2":
        return tb(init, ins) if pin == "O6" else tb(init % 2 ** 32, ins[:5]) if pin == "O5" else None
    if k in ("muxf7", "muxf8") and pin == "O":
        return ins[1] if ins[2] else ins[0]
    if k == "buf" and pin == "O":
        return ins[0]
    if k == "carry4":
        ci, cy, d, s = ins[0], ins[1], ins[2:6], ins[6:10]
        c = [ci or cy]
        for i in range(4):
            c.append(c[i] if s[i] else d[i])
        if pin.startswith("CO"):
            return c[int(pin[2]) + 1]
        if pin.startswith("O"):
            i = int(pin[1]); return s[i] != c[i]
    if k in ("fdre", "fdse"):
        return tb(T["FFQ_SYNC"], ins) if pin == "Q" else tb(T["FDRE_M" if k == "fdre" else "FDSE_M"], ins)
    if k in ("fdce", "fdpe"):
        return tb(T[("FDCE_" if k == "fdce" else "FDPE_") + pin], ins)
    return None


RE_CELL = re.compile(r'⟨"([^"]*)", \((\.[^)]*?)\)|⟨"([^"]*)", (\.\w+)')


def parse_cell(txt):
    m = re.match(r'⟨"([^"]*)", (\((?:[^()]|\([^()]*\))*\)|\.\w+), 0x([0-9A-F]+), false, \[(.*?)\], \[(.*?)\]⟩$', txt)
    if not m:
        raise ValueError(txt[:200])
    name, kind, init, conn, inv = m.groups()
    kind = kind.strip("()").lstrip(".")
    kind = re.sub(r'"([^"]*)"', r"\1", kind)
    c = {}
    for pin, src in re.findall(r'\((\.\w+|\(\.other "\w+"\)), (\(\.(?:net \d+|const \w+)\))\)', conn):
        pin = pin.strip("()").replace('.other "', "").replace('"', "").lstrip(".")
        sm = re.match(r"\(\.net (\d+)\)", src)
        c[pin] = ("net", int(sm.group(1))) if sm else ("const", "true" in src)
    return {"name": name, "kind": kind, "init": int(init, 16), "conn": c,
            "inv": [x.strip().lstrip(".") for x in inv.split(",") if x.strip()]}


def parse_trie(path):
    txt = open(path).read()
    defs = dict(re.findall(r"def (rho\w*) : Trie :=\n(.*?)\n\n", txt, re.S))
    toks = re.findall(r"\(\.node|\(some \(\.net \d+\)\)|\(some \(\.const \w+\)\)|none|\.leaf|rho_\w+|\)", "")
    rho = {}

    def walk(body, key_of):
        toks = re.findall(r"\(\.node|\(some \(\.net \d+\)\)|\(some \(\.const \w+\)\)|none|\.leaf|rho_\w+|\)", body)
        pos = [0]

        def node(f):
            t = toks[pos[0]]; pos[0] += 1
            if t == ".leaf":
                return
            if t.startswith("rho_"):
                walk(defs[t], f); return
            assert t == "(.node", t
            v = toks[pos[0]]; pos[0] += 1
            if v != "none":
                m = re.match(r"\(some \(\.net (\d+)\)\)", v)
                rho[f(0)] = ("net", int(m.group(1))) if m else ("const", "true" in v)
            node(lambda n, f=f: f(2 * n + 1))
            node(lambda n, f=f: f(2 * n + 2))
            assert toks[pos[0]] == ")"; pos[0] += 1
        node(key_of)
    walk(defs["rho"], lambda n: n)
    return rho


def main():
    d = sys.argv[1]
    rho = parse_trie(os.path.join(d, "Rho.lean"))
    bad = 0
    total = 0
    for fn in sorted(os.listdir(d)):
        if not re.match(r"C\d+\.lean$", fn):
            continue
        txt = open(os.path.join(d, fn)).read()
        body = txt[txt.index("def insts"):txt.index("theorem ok")]
        for k, m in enumerate(re.finditer(r"  ⟨(⟨.*?⟩),\n   (none|some ⟨.*?⟩),\n   \[(.*?)\], \[(.*?)\]⟩", body)):
            total += 1
            p = parse_cell(m.group(1))
            l = None if m.group(2) == "none" else parse_cell(m.group(2)[5:])
            outs = re.findall(r"\(\.(\w+), \.(\w+)\)", m.group(3))
            supp = [int(x) for x in m.group(4).split(",") if x.strip()]
            why = check(rho, p, l, outs, supp)
            if why:
                bad += 1
                if bad <= 15:
                    print("FAIL %s[%d] %s / %s: %s" % (fn, k, p["name"], l and l["name"], why))
    print("check3: %d instances, %d fail" % (total, bad))
    sys.exit(1 if bad else 0)


def ren(rho, s):
    return s if s[0] == "const" else rho.get(s[1])


def check(rho, p, l, outs, supp):
    if p["kind"].startswith("opaque"):
        if l is None or not l["kind"].startswith("opaque"):
            return "opaque physical cell without an opaque logical cell"
        for q, s in p["conn"].items():
            if ren(rho, s) != l["conn"].get(q):
                return "opaque pin %s: %s vs %s" % (q, ren(rho, s), l["conn"].get(q))
        return None
    psrc = []
    for q in inpins(p["kind"]):
        s = p["conn"].get(q)
        r = ren(rho, s) if s else None
        if r is None:
            return "physical pin %s not renamed" % q
        psrc.append((q, r))
    for q, r in psrc:
        if r[0] == "net" and r[1] not in supp:
            return "phys pin %s reads %s outside supp" % (q, r)

    def val(env, s):
        return s[1] if s[0] == "const" else env[s[1]]

    def ev(c, srcs, pin, env):
        ins = [val(env, s) for _, s in srcs]
        ins = [(not v) if q in c["inv"] else v for (q, _), v in zip(srcs, ins)]
        return out(c["kind"], c["init"], pin, ins)
    if not outs:
        return "no output pairs"
    if l is None:
        for pp, _ in outs:
            s = ren(rho, p["conn"][pp]) if pp in p["conn"] else None
            if s is None:
                return "rt out not renamed"
            if s[0] == "net" and s[1] not in supp:
                return "rt source outside supp"
            for bits in itertools.product([False, True], repeat=len(supp)):
                env = dict(zip(supp, bits))
                if ev(p, psrc, pp, env) != val(env, s):
                    return "route-through %s != %s at %s" % (pp, s, env)
        return None
    lsrc = []
    for q in inpins(l["kind"]):
        s = l["conn"].get(q)
        if s is None:
            return "logical pin %s missing" % q
        if s[0] == "net" and s[1] not in supp:
            return "log pin %s outside supp" % q
        lsrc.append((q, s))
    pk, lk = p["kind"].split()[0], l["kind"].split()[0]
    if pk != "lut6_2":
        if pk == "buf":
            if lk != "buf":
                return "kind"
        elif pk != lk or (pk.startswith("fd") and p["init"] != l["init"]):
            return "kind/init %s %s %s %s" % (pk, lk, p["init"], l["init"])
    for pp, lp in outs:
        if pp not in p["conn"] or lp not in l["conn"] or ren(rho, p["conn"][pp]) != l["conn"].get(lp):
            return "out %s->%s renamed %s, logical %s" % (pp, lp, ren(rho, p["conn"][pp]), l["conn"].get(lp))
    for bits in itertools.product([False, True], repeat=len(supp)):
        env = dict(zip(supp, bits))
        for pp, lp in outs:
            a, b = ev(p, psrc, pp, env), ev(l, lsrc, lp, env)
            if a is None or a != b:
                return "%s/%s differ at %s: phys %s log %s" % (pp, lp, env, a, b)
    return None


if __name__ == "__main__":
    main()
