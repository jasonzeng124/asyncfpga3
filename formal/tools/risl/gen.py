#!/usr/bin/env python3
"""Shard C (UNTRUSTED generator): reset quiet island data for Lean, from /tmp/claude-0/quiet/reset_island.txt.
Entries (node, value, forcing pins, rho) in blocks of <= B, routed by a balanced key tree."""
import sys
B = int(sys.argv[1]) if len(sys.argv) > 1 else 52
OUT = "/home/user/asyncfpga3/formal/lean/Formal/Net/CViewPS/"
rows = []
for ln in open("/tmp/claude-0/quiet/reset_island.txt"):
    f = ln.split()
    ps = [] if f[2] == '-' else [int(x) for x in f[2].split(',')]
    rows.append((int(f[0]), f[1] == '1', ps, int(f[3])))
rows.sort()
assert len({r[0] for r in rows}) == len(rows)
assert 186905 not in {r[0] for r in rows}
nb = (len(rows) + B - 1) // B
blks = [rows[i * len(rows) // nb:(i + 1) * len(rows) // nb] for i in range(nb)]
def tree(lo, hi):
    if hi - lo == 1: return "(.blk rb%d)" % lo
    mid = (lo + hi) // 2
    return "(.br %d %s %s)" % (blks[mid][0][0], tree(lo, mid), tree(mid, hi))
o = [
 "/-! GENERATED (shard C, /tmp/claude-0/risl/gen.py from the untrusted quiet study's reset_island.txt;",
 "kernel-checked in RIslChk*.lean, used in RIslPS.lean): the reset island of THE target. %d members" % len(rows),
 "(node, value during reset, forcing pins, rank ρ), in %d blocks of at most %d, routed by `rIsl`, a" % (nb, max(map(len, blks))),
 "search tree on node numbers. The only root is the reset node `rstPS`. -/", "",
 "namespace Formal.Net.CViewPS", "",
 "/-- A search tree of entries: `br k l r` sends nodes `< k` left; `blk es` holds the entries. -/",
 "inductive RTree where", "  | blk (es : List (Nat × Bool × List Nat × Nat))", "  | br (k : Nat) (l r : RTree)", ""]
for i, b in enumerate(blks):
    o.append("set_option maxRecDepth 100000 in")
    o.append("def rb%d : List (Nat × Bool × List Nat × Nat) := [" % i)
    o.append(",\n".join("  (%d, %s, [%s], %d)" % (n, 'true' if v else 'false', ", ".join(map(str, ps)), r) for n, v, ps, r in b) + "]")
    o.append("")
o += ["set_option maxRecDepth 100000 in", "def rIsl : RTree :=", "  " + tree(0, nb), "", "end Formal.Net.CViewPS", ""]
open(OUT + "RIslData.lean", "w").write("\n".join(o))
print("blocks", nb, "sizes", min(map(len, blks)), max(map(len, blks)))
