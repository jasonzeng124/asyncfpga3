#!/usr/bin/env python3
"""sdfmatch.py (shard A, 2026-11-17; untrusted): name the decoded bitstream's nets with nextpnr's instance names, when
only the FASM and the SDF of a build exist (research/data/board-august/: no yosys or routed JSON).

    python3 sdfmatch.py D0.json BUILD.sdf OUT.json [--check ROUTED.json]

Both sides become the same kind of graph: one node per driven output (a LUT's O6 or O5, a flop's Q, a MUXF7/F8's OUT,
a CARRY4 output, a PS7 pin), with typed input edges (pin name, source node). The decoded side splits a LUT6_2 into
its O6 and O5 halves by the pins each half's INIT depends on, as the SDF lists them as two cells. Clocks and
constants are left out. PS7 pins are anchored by name. Colours are then refined (Weisfeiler-Lehman: a node's colour is
its kind, its inputs' (pin, colour) and its sinks' (pin, colour)) until stable; every colour held by exactly one node
on each side gives a match. OUT maps SDF "cell/pin" -> decoded net name. --check compares with the truth when a
routed JSON (NEXTPNR_BEL) exists.
"""
import json, re, sys, collections, hashlib

d0f, sdff, outf = sys.argv[1:4]
chk = sys.argv[sys.argv.index("--check") + 1] if "--check" in sys.argv else None


def H(x): return hashlib.md5(repr(x).encode()).hexdigest()[:16]


def dep(init, k, j):
    return any(((init >> x) & 1) != ((init >> (x ^ (1 << j))) & 1) for x in range(1 << k))


# ---------------- decoded side
D = json.load(open(d0f))
dn = {}           # node -> dict(kind, ins=[(pin, srcnet)])
def srcnet(v):
    n = v["net"]
    if str(n).startswith("float") and v.get("_route"):
        m = re.search(r"PS7_(\w+)", v["_route"]["pips"][0][2]) if v["_route"]["pips"] else None
        if m: return "PS7:" + m.group(1)
    return n
def pinnum(v):
    sw = (v.get("_route") or {}).get("sinkwire")
    return sw[1][-1] if sw else None
for c in D["cells"]:
    k = c["kind"]; cn = c["conn"]
    if k == "lut6_2":
        I = c["init"]; ins = []
        for p, v in cn.items():
            if not isinstance(v, dict) or "net" not in v: continue
            n = pinnum(v)
            if n is None: continue
            ins.append((int(n), srcnet(v)))
        for out, kk in (("O6", 6), ("O5", 5)):
            init = I if kk == 6 else I & 0xFFFFFFFF
            used = [("A%d" % n, s) for n, s in ins if n <= kk and dep(init, kk, n - 1)]
            if used:
                dn[c["outs"][out]] = dict(kind="LUT", ins=sorted(used))
    elif k.startswith("fd") or k.startswith("ld"):
        ins = []
        for p, v in cn.items():
            if not isinstance(v, dict) or "net" not in v or p in ("C", "Q", "M"): continue
            ins.append(({"D": "D", "CE": "CE"}.get(p, "SR"), srcnet(v)))
        dn[c["outs"]["Q"]] = dict(kind="FF", ins=sorted(ins))
    elif k in ("muxf7", "muxf8"):
        ins = [({"I0": "0", "I1": "1", "S": "S0"}[p], srcnet(v)) for p, v in cn.items() if isinstance(v, dict) and "net" in v]
        dn[c["outs"]["O"]] = dict(kind="MUX", ins=sorted(ins))
    elif k == "carry4":
        ins = [(p, srcnet(v)) for p, v in cn.items() if isinstance(v, dict) and "net" in v]
        cell = c["name"]
        dn[cell] = dict(kind="CARRY", ins=sorted(ins))
        for o, n in c["outs"].items():
            dn[n] = dict(kind="CY" + o, ins=[("C", cell)])
# PS7 / other driven nets referenced but not produced by a cell: anchors (PS7) or leaves
for n in list(dn):
    for p, s in dn[n]["ins"]:
        if s not in dn:
            dn[s] = dict(kind=s if s.startswith("PS7:") else "EXT", ins=[])

# ---------------- SDF side
sn = {}; ctype = {}; curt = None; cin = collections.defaultdict(list)
for l in open(sdff):
    m = re.search(r'\(CELLTYPE "([^"]+)"\)', l)
    if m: curt = m.group(1)
    m = re.search(r"\(INSTANCE (.*)\)", l)
    if m: ctype[m.group(1)] = curt
    m = re.search(r"\(INTERCONNECT (\S+) (\S+) ", l)
    if m:
        s, d = m.group(1), m.group(2)
        sc, sp = s.rsplit("/", 1); dc, dp = d.rsplit("/", 1)
        if sc.startswith("PSEUDO") or "VCC" in sc or "GND" in sc: continue
        cin[dc].append((dp, sc, sp))
def snode(c, p):
    t = ctype.get(c, "?")
    if t == "PS7_PS7": return "PS7:" + p
    return c + "/" + p
for c, lst in cin.items():
    t = ctype.get(c, "?")
    if t == "SLICE_LUTX":
        sn[c + "/O"] = dict(kind="LUT", ins=sorted((p, snode(sc, sp)) for p, sc, sp in lst))
    elif t == "SLICE_FFX":
        sn[c + "/Q"] = dict(kind="FF", ins=sorted((p, snode(sc, sp)) for p, sc, sp in lst if p != "CK"))
    elif t == "SELMUX2_1":
        sn[c + "/OUT"] = dict(kind="MUX", ins=sorted((p, snode(sc, sp)) for p, sc, sp in lst))
    elif t == "CARRY4":
        sn[c] = dict(kind="CARRY", ins=sorted((p, snode(sc, sp)) for p, sc, sp in lst))
# normalise SDF source pin names to the node keys above
def canon(n):
    if n.startswith("PS7:"): return n
    c, p = n.rsplit("/", 1); t = ctype.get(c, "?")
    if t == "SLICE_LUTX": return c + "/O"
    if t == "SLICE_FFX": return c + "/Q"
    if t == "SELMUX2_1": return c + "/OUT"
    if t == "CARRY4":
        key = c + "/CY" + p
        if key not in sn: sn[key] = dict(kind="CY" + p, ins=[("C", c)])
        return key
    return n
for n in list(sn):
    sn[n]["ins"] = sorted((p, canon(s)) for p, s in sn[n]["ins"])
for n in list(sn):
    for p, s in sn[n]["ins"]:
        if s not in sn: sn[s] = dict(kind=s if s.startswith("PS7:") else "EXT", ins=[])
# decoded carry outputs named CY + CO0/O0 ...; SDF CY + CO3/O0: same spelling. Drop decoded CY nodes without sinks.
while True:
    used = set(s for v in dn.values() for _, s in v["ins"])
    drop = [n for n, v in dn.items() if (v["kind"].startswith("CY") or v["kind"] == "LUT") and n not in used]
    if not drop: break
    for n in drop: del dn[n]
    break

# ---------------- colour refinement
def refine(G):
    sinks = collections.defaultdict(list)
    for n, v in G.items():
        for p, s in v["ins"]: sinks[s].append((p, n))
    col = {n: H(v["kind"] if (v["kind"].startswith("PS7") or v["kind"] == "EXT") else (v["kind"], tuple(p for p, _ in v["ins"]))) for n, v in G.items()}
    return col, sinks
def step(G, col, sinks):
    return {n: H((col[n], tuple(sorted((p, col[s]) for p, s in G[n]["ins"])), tuple(sorted((p, col[t]) for p, t in sinks[n])))) for n in G}
cd, skd = refine(dn); cs, sks = refine(sn)
prev = -1
for it in range(60):
    cd, cs = step(dn, cd, skd), step(sn, cs, sks)
    bd = collections.Counter(cd.values()); bs = collections.Counter(cs.values())
    uniq = sum(1 for c, k in bd.items() if k == 1 and bs.get(c) == 1)
    print("iter %d: unique matched colours %d (decoded nodes %d, sdf nodes %d)" % (it, uniq, len(dn), len(sn)), file=sys.stderr)
    if uniq == prev: break
    prev = uniq
inv = {}
for n, c in cd.items():
    if bd[c] == 1 and bs.get(c) == 1: inv[c] = n
match = {n: inv[c] for n, c in cs.items() if c in inv}
json.dump(match, open(outf, "w"), indent=0)
print("matched %d of %d SDF nodes" % (len(match), len(sn)), file=sys.stderr)
if chk:
    R = json.load(open(chk))["modules"]["top"]["cells"]
    ok = bad = 0
    for s, dnet in match.items():
        if s.startswith("PS7") or "/" not in s: continue
        c = s.rsplit("/", 1)[0].replace("\\", "")
        b = R.get(c, {}).get("attributes", {}).get("NEXTPNR_BEL", "")
        m = re.match(r"(SLICE_X\d+Y\d+)/([A-D])(6LUT|5LUT|FF|5FF)", b)
        if not m: continue
        site, L, w = m.groups()
        want = {"6LUT": site + "." + L + "6", "5LUT": site + "." + L + "5", "FF": site + "." + L + "Q", "5FF": site + "." + L + "5Q"}[w]
        ok += want == dnet; bad += want != dnet
    print("check against routed JSON: %d right, %d wrong" % (ok, bad), file=sys.stderr)
if "--stats" in sys.argv:
    print("decoded kinds", collections.Counter(v["kind"] if not v["kind"].startswith("PS7") else "PS7" for v in dn.values()).most_common(12), file=sys.stderr)
    print("sdf kinds", collections.Counter(v["kind"] if not v["kind"].startswith("PS7") else "PS7" for v in sn.values()).most_common(12), file=sys.stderr)
    print("decoded EXT ex", [n for n, v in dn.items() if v["kind"] == "EXT"][:8], file=sys.stderr)
    print("sdf EXT ex", [n for n, v in sn.items() if v["kind"] == "EXT"][:8], file=sys.stderr)
    print("decoded PS7 ex", [n for n, v in dn.items() if v["kind"].startswith("PS7")][:5], file=sys.stderr)
    print("sdf PS7 ex", [n for n, v in sn.items() if v["kind"].startswith("PS7")][:5], file=sys.stderr)
    print("decoded LUT pin-count", collections.Counter(len(v["ins"]) for v in dn.values() if v["kind"] == "LUT"), file=sys.stderr)
    print("sdf LUT pin-count", collections.Counter(len(v["ins"]) for v in sn.values() if v["kind"] == "LUT"), file=sys.stderr)
