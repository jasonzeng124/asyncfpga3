#!/usr/bin/env python3
"""Independent re-check of tighten.py rule F with the chain-wire (hop) term.

usage: rulef_drain.py <cells dir> <routed sdf> <routed.json> [--osc X ...]

Structure (which cells form each fast-fall line, which pin of each stage is the ripple and which
the side tap) comes from routed.json (LUT INIT = AND, connections by net).  Delays come from my own
parse of the SDF (all triples are min=typ=max on this toolchain; first number used).  Time 0 = the
side-tap source pin falls.

  head:   f_0 = A(src -> head input, longest path) + arc_head
  i>=1:   f_i = min(tap_i + arc_tap_i,  f_{i-1} + hop_i + arc_rip_i)     (AND falls on earlier input)
  rule F (theirs):   drain_F = max_i f_i
  corrected:         every ripple INPUT must be low before that stage's tap sees the re-rise:
                     f_{i-1} + hop_i < t_reuse + tap_i   <=>  t_reuse >= f_{i-1} + hop_i - tap_i + 1
                     drain_C = max(drain_F, max_i (f_{i-1} + hop_i - tap_i + 1))
t_reuse is rule F's own (tighten.audit_fastfall: earliest tail fall + shortest tail->src path); the
module is imported only for that number and for its t_flush/margin, for comparison.
guard = max(0.2*drain, 200) as req_guard.  margin = t_reuse - drain - guard.
"""
import json, re, sys, os, pathlib
from collections import defaultdict

cells_dir, sdf_path, json_path = sys.argv[1], sys.argv[2], sys.argv[3]
osc = [sys.argv[i + 1] for i, a in enumerate(sys.argv) if a == "--osc"]

# ---------------- my own SDF parse
un = lambda s: s.replace("\\", "")
ic = {}                       # (srcpin, dstpin) -> ps
ic_into = defaultdict(list)   # dstpin -> [(srcpin, ps)]
iop = {}                      # (inst, in, out) -> ps
fwd = defaultdict(list)
inst = None
for line in open(sdf_path):
    m = re.search(r"\(INSTANCE\s+(\S*)\s*\)", line)
    if m:
        inst = un(m.group(1)); continue
    m = re.search(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)", line)
    if m and inst is not None:
        a, z, d = m.group(1), m.group(2), int(m.group(3))
        assert m.group(3) == m.group(5), line
        iop[(inst, a, z)] = d
        fwd[f"{inst}/{a}"].append((f"{inst}/{z}", d)); continue
    m = re.search(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)", line)
    if m:
        s, t, d = un(m.group(1)), un(m.group(2)), int(m.group(3))
        assert m.group(3) == m.group(5), line
        ic[(s, t)] = d; ic_into[t].append((s, d)); fwd[s].append((t, d))

def longest(src, dst, depth=10):
    best = None
    def go(p, t, seen, k):
        nonlocal best
        if p == dst:
            best = t if best is None else max(best, t); return
        if k == 0: return
        for q, d in fwd.get(p, ()):
            if q not in seen:
                go(q, t + d, seen | {q}, k - 1)
    go(src, 0, {src}, depth)
    return best

# ---------------- structure from routed.json
mod = json.load(open(json_path))["modules"]["top"]
cells = mod["cells"]
RE = re.compile(r"^(?P<base>.+)\.chain\.g\[(?P<i>\d+)\]\.u$")
chains = defaultdict(dict)
for name in cells:
    mm = RE.match(name)
    if mm: chains[mm.group("base")][int(mm.group("i"))] = name
def ins_of(c):
    return {p: v[0] for p, v in c["connections"].items() if p.startswith("A") and v}
def out_of(c):
    o = [(p, v[0]) for p, v in c["connections"].items() if p.startswith("O") and v]
    assert len(o) == 1; return o[0]
lines = {}
for base, st in chains.items():
    n = max(st) + 1
    if n < 2 or sorted(st) != list(range(n)): continue
    if not all(cells[st[i]]["parameters"].get("INIT") == "1000" and len(ins_of(cells[st[i]])) == 2
               for i in range(1, n)):
        continue                                    # not a FASTFALL (AND) line
    lines[base] = (n, [st[i] for i in range(n)])

# ---------------- rule F's t_reuse (and its own numbers) via tighten.py
sys.argv = ["tighten.py", sdf_path] + sum((["--osc", o] for o in osc), [])
sys.path.insert(0, os.path.join(cells_dir, "verify"))
os.chdir(cells_dir)
import tighten as T
edges, _, _, _ = T.parse_sdf(pathlib.Path(sdf_path))
dead, _ = T.false_arcs(edges)
for s in list(edges):
    edges[s] = [(d, w) for d, w in edges[s] if (s, d) not in dead]
back = defaultdict(set)
for s, l in edges.items():
    for d, _ in l: back[d].add(s)
for prefix in osc:
    for s in list(edges):
        i = T.pin_split(s)[0]
        if i == prefix or i.startswith(prefix + "."): edges[s] = []
stops = T.storage_nodes(edges)
timing = T.Timing(edges, stops)
F = {r[0]: r for r in T.audit_fastfall(edges, back, T.find_chains(edges), timing)}

allstages = []
rows = []
for base, (n, names) in sorted(lines.items()):
    c0 = cells[names[0]]
    (hpin, hnet), = ins_of(c0).items()
    hout, _ = out_of(c0)
    tapnet, prev_out_net = None, out_of(c0)[1]
    stages = []
    for i in range(1, n):
        c = cells[names[i]]
        ins = ins_of(c)
        rip = [p for p, v in ins.items() if v == prev_out_net]
        tap = [p for p, v in ins.items() if v != prev_out_net]
        assert len(rip) == 1 and len(tap) == 1, (base, i, ins)
        tn = ins[tap[0]]
        assert tapnet in (None, tn), (base, "taps from two nets"); tapnet = tn
        stages.append((names[i], rip[0], tap[0], out_of(c)[0]))
        prev_out_net = out_of(c)[1]
    # tap source pin: the SDF driver of every tap pin
    srcs = set()
    for nm, rp, tp, op in stages:
        srcs |= {s for s, _ in ic_into[f"{nm}/{tp}"]}
    assert len(srcs) == 1, (base, srcs); src = srcs.pop()
    a_head = longest(src, f"{names[0]}/{hpin}")
    if a_head is None:
        rows.append((base, n, None)); continue
    f = a_head + iop[(names[0], hpin, hout)]
    falls, need = [f], []
    prev_pin = f"{names[0]}/{hout}"
    for nm, rp, tp, op in stages:
        hop = ic[(prev_pin, f"{nm}/{rp}")]
        tap = ic[(src, f"{nm}/{tp}")]
        f_new = min(tap + iop[(nm, tp, op)], f + hop + iop[(nm, rp, op)])
        need.append((f + hop - tap + 1, nm, hop, tap, f)); allstages.append((hop - tap, nm))
        f = f_new; falls.append(f); prev_pin = f"{nm}/{op}"
    drainF = max(falls)
    worstneed = max(need)
    drainC = max(drainF, worstneed[0])
    r = F.get(base)
    t_reuse = r[3] if r and r[-1] is not None else None
    rows.append((base, n, drainF, drainC, worstneed, t_reuse, r))

def g(t): return max(int(0.2 * t), 200)
print(f"{len(lines)} FASTFALL (AND) lines in routed.json; rule F rows: {len(F)}; "
      f"lines rule F did not list: {sorted(set(lines) - set(F))}; rule F rows not FASTFALL-AND here: {sorted(set(F) - set(lines))}")
print(f"{'line':<52}{'N':>3}{'flushF(mine)':>13}{'flushF(theirs)':>15}{'t_reuse':>8}{'F raw':>7}{'F guarded':>10}"
      f"{'drainC':>8}{'C raw':>7}{'C guarded':>10}  worst stage (hop,tap,f_prev)")
out = []
for row in rows:
    if row[2] is None:
        print(f"{row[0]:<52} head not traced"); continue
    base, n, dF, dC, wn, tr, r = row
    if tr is None:
        print(f"{base:<52}{n:>3} rule F gave no t_reuse: {r}"); continue
    out.append((tr - dC - g(dC), tr - dC, base, n, dF, r[2], tr, tr - dF, r[5], dC, wn))
for cg, craw, base, n, dF, theirs, tr, fraw, fg, dC, wn in sorted(out):
    print(f"{base:<52}{n:>3}{dF:>13}{theirs:>15}{tr:>8}{fraw:>7}{fg:>10}{dC:>8}{craw:>7}{cg:>10}  "
          f"{wn[1].split('.chain.')[1]} hop {wn[2]} tap {wn[3]} f_prev {wn[4]}")
mism = [o for o in out if o[4] != o[5]]
print(f"\nlines with my flush != rule F's t_flush: {len(mism)}")
print(f"worst rule F guarded margin (theirs): {min(o[8] for o in out)}")
print(f"worst corrected RAW margin (t_reuse - drainC): {min(o[1] for o in out)}")
print(f"worst corrected GUARDED margin: {min(o[0] for o in out)}")
print(f"lines where the hop term binds (drainC > flush): {sum(1 for o in out if o[9] > o[4])}")
print(f"stages audited {len(allstages)}; with hop > tap: {sum(1 for x in allstages if x[0] > 0)}; max hop-tap {max(allstages)}")
print(f"lines with corrected raw < 0: {sum(1 for o in out if o[1] < 0)}; corrected guarded < 0: {sum(1 for o in out if o[0] < 0)}")
