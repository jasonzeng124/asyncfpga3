#!/usr/bin/env python3
"""memvec.py -- write a v2 bench vector file (research/data/suite/bench/README.md).

    memvec.py KERNEL --call "W0 W1 ..." [--call ...] [--seed S] [--range LO,HI] [--fill SPEC] -o VEC.hex

The layout comes from the kernel's own handshake signature (build/frontend/K/comp/handshake_transformed.mlir), the
same one cells/hw/gen_bench.py builds the bench from: per call, the operand words (arguments in signature order, an
i64 as low word then high word), then every element of each memref argument in signature order.

--call gives one call's operand words (hex or decimal, as many as the signature needs); one --call per call.
A --call may also set one call's arrays, after the words: "W0 W1;a=SPEC;b=SPEC" (an array it does not name takes
the file-wide default below).  SPEC: const:V (every element V), rand:LO,HI (seeded uniform), seq:A,D (element i is
A + D * i), list:V0,V1,... (repeated to the depth); any of them may end in overrides @I=V (element I is V, e.g.
"const:999@599=1000": a loop's exit placed at one element).  The spec is written into the call's comment line.
Array contents are drawn per call from a seeded uniform range (--range=LO,HI with the "=" when LO is negative;
default -1000,1000, two's complement in
32 bits), so consecutive calls see different arrays.  --fill const:V fills every element with V instead (for
controls).  --perturb N:D adds D to element N of every array of every call (a negative control: same file, one
element different).  Expected values never come from here: research/tools/suite/oracle_mem.sh computes them
from the C.
"""
import argparse, os, random, re, sys

R = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..")
sys.path.insert(0, os.path.join(R, "bdc"))
from hs import parse  # noqa: E402


def signature(k):
    mlir = os.path.join(R, "build", "frontend", k, "comp", "handshake_transformed.mlir")
    f = [f for f in parse.parse_module(open(mlir).read(), filename=mlir) if not f.is_declaration][0]
    words, mems = 0, []
    for a in f.args:
        if a.raw.startswith("memref"):
            m = re.fullmatch(r"memref<(\d+)x[iu](\d+)>", a.raw)
            mems.append((a.name, int(m.group(1)), int(m.group(2))))
        elif not a.is_control:
            words += max(1, (a.width + 31) // 32)   # a scalar narrower than 32 bits takes one word (gen_bench.py)
    return words, mems


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("kernel")
    ap.add_argument("--call", action="append", default=[], help="one call's operand words")
    ap.add_argument("--calls", type=int, default=0, help="for a kernel with no operand word: this many calls")
    ap.add_argument("--seed", type=int, default=1)
    ap.add_argument("--range", default="-1000,1000")
    ap.add_argument("--fill", default="")
    ap.add_argument("--perturb", default="")
    ap.add_argument("-o", "--out", required=True)
    a = ap.parse_args()
    words, mems = signature(a.kernel)
    calls = [c.split(";")[0].split() for c in a.call] or [[] for _ in range(a.calls)]
    specs = [dict(x.strip().split("=", 1) for x in c.split(";")[1:] if x.strip()) for c in a.call] or [{} for _ in calls]
    for j, sp in enumerate(specs):
        for n in sp:
            if n not in [m[0] for m in mems]:
                sys.exit("memvec.py: call %d sets array %r, %s has %s" % (j, n, a.kernel, [m[0] for m in mems]))
    lo, hi = (int(x) for x in a.range.split(","))
    rng = random.Random(a.seed)
    out = ["// benchvec words=%d mems=%d" % (words, len(mems)),
           "// %s: %d operand word(s); memories %s; seed %d range %s%s%s" % (
               a.kernel, words, ", ".join("%s[%d] i%d" % m for m in mems) or "none", a.seed, a.range,
               (" fill " + a.fill) if a.fill else "", (" perturb " + a.perturb) if a.perturb else "")]
    for j, c in enumerate(calls):
        if len(c) != words:
            sys.exit("memvec.py: call %d has %d operand words, %s needs %d" % (j, len(c), a.kernel, words))
        out.append("// call %d%s" % (j, "".join(" %s=%s" % kv for kv in sorted(specs[j].items()))))
        out.append(" ".join("%08x" % (int(w, 0) & 0xFFFFFFFF) for w in c) if c else "")
        for name, depth, w in mems:
            sp = specs[j].get(name, "")
            sp, *over = sp.split("@")   # overrides: SPEC@I=V@J=W (element I is V), applied after SPEC
            if sp.startswith("const:"):
                vals = [int(sp[6:], 0)] * depth
            elif sp.startswith("rand:"):
                slo, shi = (int(x, 0) for x in sp[5:].split(","))
                vals = [rng.randint(slo, shi) for _ in range(depth)]
            elif sp.startswith("seq:"):
                b0, d0 = (int(x, 0) for x in sp[4:].split(","))
                vals = [b0 + d0 * i for i in range(depth)]
            elif sp.startswith("list:"):
                lv = [int(x, 0) for x in sp[5:].split(",")]
                vals = [lv[i % len(lv)] for i in range(depth)]
            elif sp:
                sys.exit("memvec.py: call %d: unknown array spec %r" % (j, sp))
            elif a.fill.startswith("const:"):
                vals = [int(a.fill[6:], 0)] * depth
            else:
                vals = [rng.randint(lo, hi) for _ in range(depth)]
            for o in over:
                oi, ov = (int(x, 0) for x in o.split("="))
                if not 0 <= oi < depth:
                    sys.exit("memvec.py: call %d: override @%s outside %s[%d]" % (j, o, name, depth))
                vals[oi] = ov
            if a.perturb:
                n, d = (int(x, 0) for x in a.perturb.split(":"))
                vals[n] += d
            mask = (1 << min(w, 32)) - 1
            vals = ["%08x" % (v & mask) for v in vals]
            out.append("// %s" % name)
            out += [" ".join(vals[i:i + 8]) for i in range(0, depth, 8)]
    with open(a.out, "w") as f:
        f.write("\n".join(l for l in out if l != "") + "\n")
    print("wrote %s: %d call(s), %d word(s) each" % (a.out, len(calls), words + sum(m[1] for m in mems)))


if __name__ == "__main__":
    main()
