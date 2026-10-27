#!/usr/bin/env python3
"""C-8s: tables for the H_WALK proof (Formal/Net/CapstoneWalkTab.lean).

For every circuit spine channel c (spL of C-8r): its GcdHw group grp c (the GcdHw spine channel
whose token it carries), its position rho c along the group's chain, adj c (false only for the
cascade's stage-1 output acc251, which is not on every path through group 251), al c (the GcdHw
channels whose consumption counts give c's visit count: [grp c], or [13, 27] for acc251) and lc c
(the GcdHw rule consuming grp c). NOT trusted: CapstoneWalkTab checks every property the proof
uses by kernel evaluation. Also self-checks the transition conditions in Python first.
Usage: walkgen.py [out.lean]
"""
import os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
NET = os.path.join(ROOT, "formal", "lean", "Formal", "Net")
sys.path.insert(0, os.path.join(ROOT, "formal", "tools", "dfimport"))
import mlir2lean  # noqa: E402

net = open(os.path.join(NET, "CapstoneNet.lean")).read()
names = re.findall(r'"([^"]*)"', re.search(r"def chanNames : List String := \[(.*?)\]\n", net).group(1))
NC = len(names)
opsL = [s.strip().rstrip(",") for s in re.search(r"def ops : List \(K NC\) := \[\n(.*?)\n\]", net, re.S).group(1).split("\n")]
consT = [int(x) for x in re.search(r"def consT : List \(Fin NO\) := \[(.*?)\]", net).group(1).split(",")]
spLt = re.search(r"def spL : List Bool := \[(.*?)\]", open(os.path.join(NET, "CapstoneCutSpine.lean")).read()).group(1)
sp = [x.strip() == "true" for x in spLt.split(",")]
g = mlir2lean.Graph(mlir2lean.default_mlir())
rules = list(g.rules)
spine = [int(x) for x in re.search(r"def spine : List Nat := \[(.*?)\]", open(os.path.join(NET, "GcdHw.lean")).read()).group(1).split(",")]

def op(c):
    s = opsL[consT[c]]
    k = re.match(r"K\.(\w+)", s).group(1)
    nums = lambda: [int(x) for x in re.findall(r"\d+", s)]
    if k == "link": return (k, nums()[1])
    if k == "bjoin":
        m = re.match(r"K\.bjoin \[([\d, ]*)\] (\d+)", s); return (k, int(m.group(2)), [int(x) for x in m.group(1).split(",")])
    if k == "forkG":
        m = re.match(r"K\.forkG (\d+) \[([\d, ]*)\]", s); return (k, [int(x) for x in m.group(2).split(",")])
    if k == "steerC":
        j, t, f = map(int, re.match(r"K\.steerC (\d+) (\d+) (\d+)", s).groups()); return (k, t, f)
    if k == "amerge":
        x, y, z, w = map(int, re.match(r"K\.amerge (\d+) (\d+) (\d+) (\d+)", s).groups()); return (k, x, y, z, w)
    return (k,)

# producer bjoin of each j channel
bjin = {}
for s in opsL:
    m = re.match(r"K\.bjoin \[(\d+), (\d+)\] (\d+)", s)
    if m: bjin[int(m.group(3))] = (int(m.group(1)), int(m.group(2)))
spC = [c for c in range(NC) if sp[c]]
grp = [0] * NC
for c in spC:
    n = names[c]
    m = re.fullmatch(r"g(\d+)\.\d+", n) or re.fullmatch(r"z(\d+)", n) or re.fullmatch(r"acc(\d+)", n)
    if m: grp[c] = int(m.group(1))
for c in spC:
    if names[c].startswith("j"): grp[c] = grp[bjin[c][1]]
ACC = names.index("acc251")
adj = [True] * NC; adj[ACC] = False
al = [[grp[c]] for c in range(NC)]; al[ACC] = [13, 27]

def succs(c):
    o = op(c)
    if o[0] in ("link", "bjoin"): return [o[1]]
    if o[0] == "forkG": return [x for x in o[1] if sp[x]][:1]
    if o[0] == "steerC": return [o[1], o[2]]
    if o[0] == "amerge": return [o[3]]
    if o[0] == "sink": return [None]
    raise ValueError(names[c], o)
rho = [0] * NC
for _ in range(20):
    for c in spC:
        for o in succs(c):
            if o is not None and grp[o] == grp[c]:
                rho[o] = max(rho[o], rho[c] + 1)
gcons = {}
for i, r in enumerate(rules):
    for ch in mlir2lean.Graph.rule_ins(r): gcons[ch] = i
lc = [gcons.get(grp[c], 0) if sp[c] else 0 for c in range(NC)]

# ---- self-check of the transition condition (mirrors CapstoneWalkTab.transOK)
def B(cur, c):
    if cur is None: return 0
    return 1 if (adj[c] and grp[c] == grp[cur] and rho[c] <= rho[cur]) else 0
def transOK(c, o, dg):
    for d in spC:
        lhs = B(c, d) + (1 if o == d else 0)
        rhs = (al[d].count(dg) if dg is not None else 0) + B(o, d)
        if lhs != rhs: return False, names[d]
    return True, None
bad = 0
for c in spC:
    for o in succs(c):
        stay = o is not None and grp[o] == grp[c]
        ok, d = transOK(c, o, None if stay else grp[c])
        if not ok:
            bad += 1; print("transOK fails", names[c], "->", names[o] if o is not None else None, "at", d, file=sys.stderr)
init_ok = all(B(2, d) == (1 if d == 2 else 0) for d in spC)
print(f"-- {len(spC)} spine channels; transitions bad={bad}; init_ok={init_ok}", file=sys.stderr)

L = lambda xs: "[" + ", ".join(xs) + "]"
out = []
out.append(f"def spN : List Nat := {L(str(c) for c in spC)}")
out.append(f"def grpL : List Nat := {L(str(x) for x in grp)}")
out.append(f"def rhoL : List Nat := {L(str(x) for x in rho)}")
out.append(f"def adjL : List Bool := {L('true' if x else 'false' for x in adj)}")
out.append(f"def alL : List (List Nat) := {L(L(str(y) for y in x) for x in al)}")
out.append(f"def lcL : List Nat := {L(str(x) for x in lc)}")
out.append(f"def recs : List (Nat × Nat × Nat × Bool × List Nat) := {L('(%d, %d, %d, %s, %s)' % (c, grp[c], rho[c], 'true' if adj[c] else 'false', L(str(y) for y in al[c])) for c in spC)}")
txt = "\n\n".join(out) + "\n"
if len(sys.argv) > 1:
    open(sys.argv[1], "w").write(txt)
else:
    print(txt)
sys.exit(1 if bad or not init_ok else 0)
