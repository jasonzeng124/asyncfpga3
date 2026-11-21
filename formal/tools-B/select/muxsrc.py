#!/usr/bin/env python3
"""UNTRUSTED measurement (shard B sub3): classify the collapsed data-pin source of every LatchViewPS latch,
find mux-like combinational sources, check coverage by LatchHold(Pin)PS* rows, and dump cones.
usage: muxsrc.py REPO SCRATCH"""
import json, sys, re, glob, os, collections, itertools, lzma
REPO, S = sys.argv[1:3]
N = json.load(open(os.path.join(S, "net.json"))); g = N["gates"]; names = N["nodes"]; NG = len(g)
B = json.load(open(os.path.join(S, "bnd.json")))
nidx = {n: i for i, n in enumerate(names)}
RST = nidx[B["boundary"]["rst"]]
env = {nidx[n] for n in B["env"] if n in nidx}
arbq = {nidx[a["q"]] for a in B["arbs"]}

def chain(n, stop=None):
    m, ch = n, []
    while m < NG and g[m]["k"] == 1 and g[m]["init"] == 2 and m != stop and len(ch) < 200:
        ch.append(m); m = g[m]["ins"][0]
    return m, ch
def src(n, stop=None): return chain(n, stop)[0]

# storage: k>=2 gate whose collapsed input is its own output (as latchtab.py), plus arbiters
storage = set(arbq)
for i, G in enumerate(g):
    if G["k"] >= 2 and any(src(n, i) == i for n in G["ins"]): storage.add(i)

# latch rows from LatchViewPS
rowre = re.compile(r"^  ⟨(\d+), (\d+), (\d+), (\d+), (true|false), (true|false), \[([^\]]*)\], \[([^\]]*)\], \[(.*)\]⟩[,\]]?$")
pinre = re.compile(r"\(\[([\d, ]*)\], (\d+)\)")
lat = {}
for f in sorted(glob.glob(os.path.join(REPO, "formal/lean/Formal/Cells/LatchViewPS/B*.lean"))):
    for ln in open(f):
        m = rowre.match(ln.rstrip("\n"))
        if m:
            q, e, d, j = map(int, m.groups()[:4])
            held = [x.strip() == "true" for x in m.group(7).split(",")]
            ov = [x.strip() == "true" for x in m.group(8).split(",")]
            pins = [(list(map(int, filter(None, a.replace(" ", "").split(",")))), int(s)) for a, s in pinre.findall(m.group(9))]
            lat[q] = dict(q=q, e=e, d=d, j=j, held=held, ov=ov, pins=pins)
celem = storage - set(lat) - arbq
print("latch rows", len(lat), "storage (incl arbs)", len(storage), "non-latch non-arb storage", len(celem))

# covered latches
cov = collections.defaultdict(set)
for d in ["LatchHoldPinPS", "LatchHoldPinPS2", "LatchHoldPinPS3", "LatchHoldPS", "LatchHoldPS2", "LatchHoldPS3"]:
    for f in glob.glob(os.path.join(REPO, "formal/lean/Formal/Cells", d, "B*.lean")):
        for q in re.findall(r"⟨c\d+, ⟨(\d+), ", open(f).read()): cov[d].add(int(q))
for d in cov: print("covered", d, len(cov[d]))
covered = set().union(*cov.values())
print("covered (union)", len(covered), "of which latch rows", len(covered & set(lat)))

def kind(n):
    if n == RST: return "rst"
    if n in arbq: return "arbiter"
    if n in lat: return "latch"
    if n in storage: return "celem/muxjoin"
    if n >= NG: return "undriven" + ("(env)" if n in env else "")
    if n in env: return "env"
    if g[n]["k"] == 0: return "const"
    return "comb"

def lutf(m):
    """INIT of comb gate m with collapsed pin sources; constant/rst pins substituted. Returns (live pin list, srcs, f)"""
    G = g[m]; k = G["k"]; ss = [src(n) for n in G["ins"]]
    fixed = {}
    for i, s in enumerate(ss):
        if s < NG and g[s]["k"] == 0: fixed[i] = g[s]["init"] & 1
    def f(v):
        w = [0] * k
        for i, b in fixed.items(): w[i] = b
        for i, b in v.items(): w[i] = b
        return (G["init"] >> sum(b << i for i, b in enumerate(w))) & 1
    return [i for i in range(k) if i not in fixed], ss, f

def muxlike(m):
    """all (s, a, b, inv) with: s=0 -> out == pin a (xor inv), s=1 -> out == pin b (xor inv), a != b, distinct source nodes"""
    live, ss, f = lutf(m); res = []
    for s in live:
        oth = [i for i in live if i != s]
        def eqpin(sv):
            out = []
            for a in oth:
                for inv in (0, 1):
                    if all(f({**dict(zip(oth, bits)), s: sv}) == (bits[oth.index(a)] ^ inv)
                           for bits in itertools.product([0, 1], repeat=len(oth))):
                        out.append((a, inv))
            return out
        A, Bv = eqpin(0), eqpin(1)
        for a, ia in A:
            for b, ib in Bv:
                if a != b and ss[a] != ss[b]: res.append((s, a, b, ia, ib))
    return res, live, ss

def depth(n, memo, stack=()):
    """(min, max) comb depth from node n to roots, and root set; n itself a comb gate counts 1"""
    n = src(n)
    if kind(n) != "comb": return 0, 0, frozenset([n])
    if n in memo: return memo[n]
    if n in stack: return 0, 0, frozenset(["CYCLE"])
    _, ss, _ = lutf(n); live = lutf(n)[0]
    rs = [depth(ss[i], memo, stack + (n,)) for i in live]
    if not rs: r = (1, 1, frozenset())
    else: r = (1 + min(x[0] for x in rs), 1 + max(x[1] for x in rs), frozenset().union(*(x[2] for x in rs)))
    memo[n] = r; return r

cls = collections.Counter(); comb = []
for q, L in lat.items():
    d = L["d"]
    if L["held"][d]: cls["tied(held const/rst)"] += 1; continue
    s = L["pins"][d][1]; kd = kind(s); cls[kd] += 1
    if kd == "comb": comb.append(q)
print("data-source classes", dict(cls))

# bel -> cell name
J = json.load(lzma.open(os.path.join(REPO, "formal/target/gcd_ps_e6bb4aec.routed.json.xz")))
bel = {}
for cn, c in J["modules"]["top"]["cells"].items():
    b = c["attributes"].get("NEXTPNR_BEL")
    if b: bel[b] = cn
del J
def cellname(m):
    nm = g[m]["name"]; mm = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])", nm)
    if mm: return bel.get("%s/%s%sLUT" % (mm.group(1), mm.group(2), mm.group(3)), "?")
    mm = re.match(r"(SLICE_X\d+Y\d+)\.(F7A|F7B|F8)", nm)
    if mm: return bel.get("%s/%sMUX" % (mm.group(1), mm.group(2)), "?")
    mm = re.match(r"(SLICE_X\d+Y\d+)\.([A-D])(\d)?", nm)
    if mm: return bel.get("%s/%s6LUT" % (mm.group(1), mm.group(2)), "?")
    return "?"

mux = {}; mstrict = 0; minv = 0
for q in comb:
    m = lat[q]["pins"][lat[q]["d"]][1]; r, live, ss = muxlike(m)
    if r:
        mux[q] = (m, r, live, ss)
        if any(x[3] == 0 and x[4] == 0 for x in r): mstrict += 1
        else: minv += 1
klive = collections.Counter(len(lutf(lat[q]["pins"][lat[q]["d"]][1])[0]) for q in comb)
print("comb sources: latches", len(comb), "distinct LUTs", len({lat[q]['pins'][lat[q]['d']][1] for q in comb}), "live-pin histogram", dict(sorted(klive.items())))
print("mux-like: latches", len(mux), "(non-inverting", mstrict, ", only with inversion", minv, ") distinct mux LUTs", len({v[0] for v in mux.values()}))
unc = sorted(q for q in mux if q not in covered)
print("mux-like NOT covered", len(unc), "; covered", len(mux) - len(unc))
print("comb non-mux NOT covered", len([q for q in comb if q not in mux and q not in covered]), "; all comb covered", len([q for q in comb if q in covered]))
print("other-class covered:", collections.Counter(kind(lat[q]['pins'][lat[q]['d']][1]) if not lat[q]['held'][lat[q]['d']] else 'tied' for q in covered if q in lat))
# instance-prefix histogram of uncovered mux latches
pref = collections.Counter(re.sub(r"\[\d+\]|_\d+\b|\$.*", "", ".".join(cellname(q).split(".")[:3])) for q in unc)
print("uncovered mux latches by cell-name prefix", pref.most_common(25))
memo = {}
out = []
for q in unc:
    m, r, live, ss = mux[q]; s, a, b, ia, ib = r[0]
    def cone(p):
        dmin, dmax, roots = depth(ss[p], memo); return dict(pin=p, src=ss[p], src_name=names[ss[p]], src_kind=kind(ss[p]), src_cell=cellname(ss[p]) if ss[p] < NG else "-",
               dmin=dmin, dmax=dmax, roots=sorted((names[x], kind(x), cellname(x) if x < NG else "-") for x in roots if x != "CYCLE") if len(roots) <= 40 else "%d roots" % len(roots),
               nroots=len(roots), rootkinds=dict(collections.Counter(kind(x) for x in roots if x != "CYCLE")))
    out.append(dict(latch=q, latch_name=g[q]["name"], latch_cell=cellname(q), mux=m, mux_name=g[m]["name"], mux_cell=cellname(m),
                    init=hex(g[m]["init"]), k=g[m]["k"], live=live, alts=r, select=cone(s), in0=cone(a), in1=cone(b)))
json.dump(out, open(os.path.join(S, "uncovered_mux.json"), "w"), indent=1)
json.dump(dict(classes=cls, covered=sorted(covered), comb=comb, mux=sorted(mux)), open(os.path.join(S, "summary.json"), "w"))
# select-depth stats
sd = collections.Counter((o["select"]["src_kind"]) for o in out); print("uncovered mux: select source kind", dict(sd))
print("uncovered mux: select dmax hist", dict(collections.Counter(o["select"]["dmax"] for o in out)))
print("uncovered mux: data dmax hist", dict(collections.Counter(max(o["in0"]["dmax"], o["in1"]["dmax"]) for o in out)))
