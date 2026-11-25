#!/usr/bin/env python3
"""lut_hazards.py [rtl/*.v] -- function-hazard census of every STATE LUT in the
library (a LUT whose output net is also one of its inputs: C-elements,
latches, arbiter state).  cells/rtl is read, never written.

For every stable state (inputs A, fed-back q with f(A, q) = q) and every
change A -> B of two or more non-feedback, non-constant pins, it checks every
order in which the pins could arrive (each intermediate vector, the fed-back q
held at its old value -- the loop is slower than a pin-to-pin skew):
  static  f(A,q) == f(B,q) but some intermediate differs      (a glitch)
  dynamic f(A,q) != f(B,q) and some order is non-monotone     (a double edge)
Transitions in which a reset pin changes are listed separately (reset is
quasi-static).  The result says only which transitions WOULD glitch a LUT;
whether a cell's protocol ever produces one is the judgement in f3_model.md.
"""
import glob, itertools, os, re, sys

RE_INST = re.compile(r"(LUT[1-6](?:_2)?)\s*#\(\s*\.INIT\(([^)]*)\)\s*\)\s*(\w+)\s*\((.*?)\);", re.S)
RE_MOD = re.compile(r"^\s*module\s+(\w+)", re.M)


def parse_init(s):
    s = s.strip().replace("_", "")
    m = re.match(r"(\d+)'h([0-9a-fA-F]+)", s)
    if m:
        return int(m.group(2), 16)
    return None


def lut_fn(init, nin):
    return lambda v: (init >> v) & 1


def census(path):
    src = open(path).read()
    mods = [(m.start(), m.group(1)) for m in RE_MOD.finditer(src)]
    out = []
    for m in RE_INST.finditer(src):
        kind, init_s, inst, body = m.groups()
        mod = [n for p, n in mods if p < m.start()][-1]
        init = parse_init(init_s)
        conns = dict(re.findall(r"\.(\w+)\(\s*([^()]*?)\s*\)", body))
        ins = ["I%d" % i for i in range(6) if "I%d" % i in conns]
        outs = [o for o in ("O", "O5", "O6") if o in conns]
        for o in outs:
            net = conns[o]
            fbk = [i for i in ins if conns[i] == net]
            if not fbk or init is None:
                continue
            n = 6 if kind in ("LUT6", "LUT6_2") else int(kind[3])
            width = 32 if (kind == "LUT6_2" and o == "O5") else (1 << n)
            if kind == "LUT6_2" and o == "O5":
                n = 5
            const = {i: int(conns[i][-1]) for i in ins if re.match(r"^1'b[01]$", conns[i])}
            live = [i for i in ins[:n] if i not in const and i not in fbk]
            rst = [i for i in live if re.search(r"rst|reset|clr", conns[i])]
            data = [i for i in live if i not in rst]
            fb = int(fbk[0][1:])

            def f(vals):
                v = 0
                for i, x in vals.items():
                    if int(i[1:]) < n:
                        v |= x << int(i[1:])
                return (init >> v) & 1 if v < width else 0
            haz = []
            for A in itertools.product((0, 1), repeat=len(live)):
                av = dict(zip(live, A))
                for q in (0, 1):
                    base = dict(const, **av)
                    base[fbk[0]] = q
                    for ff in fbk[1:]:
                        base[ff] = q
                    if f(base) != q:
                        continue          # not a stable state
                    for B in itertools.product((0, 1), repeat=len(live)):
                        ch = [p for p, a, b in zip(live, A, B) if a != b]
                        if len(ch) < 2:
                            continue
                        bv = dict(base, **dict(zip(live, B)))
                        fa, fb_ = q, f(bv)
                        bad = None
                        for order in itertools.permutations(ch):
                            cur, seq = dict(base), [fa]
                            for p in order:
                                cur[p] = bv[p]
                                seq.append(f(cur))
                            edges = sum(1 for x, y in zip(seq, seq[1:]) if x != y)
                            if edges > (1 if fa != fb_ else 0):
                                bad = order
                                break
                        if bad:
                            haz.append((av, q, {p: bv[p] for p in ch}, "dynamic" if fa != fb_ else "static",
                                        any(p in rst for p in ch)))
            out.append((os.path.basename(path), mod, inst, o, conns, data, rst, haz))
    return out


def main():
    files = sys.argv[1:] or sorted(glob.glob(os.path.join(os.path.dirname(__file__), "../../../rtl/*.v")))
    for p in files:
        for fn, mod, inst, o, conns, data, rst, haz in census(p):
            names = lambda d: ",".join("%s=%d" % (conns[k], v) for k, v in sorted(d.items()))
            nh = [h for h in haz if not h[4]]
            print("%-12s %-16s %-6s %-3s data pins %-28s reset %-8s hazardous multi-input changes: %d (+%d with reset)"
                  % (fn, mod, inst, o, ",".join(conns[d] for d in data), ",".join(conns[r] for r in rst) or "-",
                     len(nh), len(haz) - len(nh)))
            for av, q, chg, kind, _ in nh[:12]:
                print("      from {%s, q=%d} change {%s}: %s hazard" % (names(av), q, names(chg), kind))
            if len(nh) > 12:
                print("      ... %d more" % (len(nh) - 12))


if __name__ == "__main__":
    main()
