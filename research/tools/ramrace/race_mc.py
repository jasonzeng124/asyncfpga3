#!/usr/bin/env python3
"""race_mc.py NOSCATTER_WORK DECODED_ROUTED_JSON [RAMINST] [SRC] [N] -- Monte Carlo of the draws' within-die scatter
(cells/gls/gen.py GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_REGION=0.02, linear form) on ONE RAM setup race:
SRC (default bridge_i.mem_hreq) -> RAMINST's CLKARDCLK (shortest path) against -> each WEA / ADDR / DI pin (longest
path), with the nominal delays of a no-scatter baked netlist (bake_draw.sh ... noscatter).  As gen.py: a wire's factor
is the mean of (1 + 0.126 N) over the pips of its route (one N per pip, shared by every wire through that pip), times
its sink's region factor (1 + 0.02 N, one N per 10x10-slice region); a LUT arc gets its own (1 + 0.126 N) times its
cell's region factor.  Prints the nominal margin and the scatter's mean / sd / quantiles / P(margin < 0) per class."""
import collections, json, math, random, re, sys
W, J = sys.argv[1], sys.argv[2]
RAM = sys.argv[3] if len(sys.argv) > 3 else "c_000008"
SRC = sys.argv[4] if len(sys.argv) > 4 else "bridge_i.mem_hreq"
NS = int(sys.argv[5]) if len(sys.argv) > 5 else 20000
SW, SR = 0.126, 0.02
net_of, bel = {}, {}
for l in open(W + "/nets.map"):
    p = l.split(None, 1)
    if len(p) == 2 and not l.startswith("#"): net_of[p[1].strip()] = p[0]
for l in open(W + "/names.map"):
    p = l.split(None, 1)
    if len(p) == 2 and not l.startswith("#"): bel[p[0]] = p[1].strip()
fwd = collections.defaultdict(list); ram = {}; ramp = {}
ric = re.compile(r"ICBUF #\(\.D\((\d+)\)\) (\S+) \(\.I\((\S+)\), \.O\((\S+)\)\);")
rlut = re.compile(r"SLICE_LUTX #\((.*)\) (\S+) \((.*)\);")
rram = re.compile(r"RAMB18E1_RAMB18E1 #\((.*)\) (\S+) \((.*)\);")
for l in open(W + "/netlist_baked.v"):
    l = l.strip(); m = ric.match(l)
    if m:
        sink = bel[m.group(2)].split(" -> ")[1]
        fwd[m.group(3)].append((m.group(4), int(m.group(1)), ("W", sink))); continue
    m = rlut.match(l)
    if m:
        par = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(1))); con = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(3)))
        for k in range(1, 7):
            for o in ("O6", "O5"):
                d = par.get("TA%d%s" % (k, o))
                if d is not None and ("A%d" % k) in con and o in con:
                    fwd[con["A%d" % k]].append((con[o], int(d), ("L", bel[m.group(2)], "A%d%s" % (k, o))))
        continue
    m = rram.match(l)
    if m:
        ram[m.group(2)] = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(3)))
        ramp[m.group(2)] = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(1)))
src = net_of[SRC]
import heapq
best = {src: (0, [])}; pq = [(0, 0, src)]; cnt = 1
while pq:
    t, _, n = heapq.heappop(pq)
    if t > best[n][0]: continue
    for d, w, via in fwd.get(n, ()):
        if d not in best or t + w < best[d][0]:
            best[d] = (t + w, best[n][1] + [(via, w)]); heapq.heappush(pq, (t + w, cnt, d)); cnt += 1
worst = {src: (0, [])}
def dfs(n, t, seen, path, maxl=6):
    if len(path) >= maxl: return
    for d, w, via in fwd.get(n, ()):
        if d in seen: continue
        if d not in worst or t + w > worst[d][0]: worst[d] = (t + w, path + [(via, w)])
        dfs(d, t + w, seen | {d}, path + [(via, w)], maxl)
dfs(src, 0, {src}, [])
# pips and regions from the decoded routed JSON (gen.py's WireModel / RegionModel logic)
top = json.load(open(J))["modules"]["top"]; cells = top["cells"]; routes = {}
for nn in top["netnames"].values():
    r = nn.get("attributes", {}).get("ROUTING")
    if r and nn["bits"]: routes.setdefault(nn["bits"][0], r)
def pips_of(dst):
    cell, _, pin = dst.rpartition("/"); c = cells.get(cell)
    if c is None or pin not in c["connections"]: return None
    bit = c["connections"][pin][0]
    if bit not in routes: return None
    f = routes[bit].split(";"); par = {f[i]: f[i + 1] for i in range(0, len(f) - 2, 3)}
    b = c["attributes"].get("NEXTPNR_BEL", "")
    site, bb = b.split("/")[:2]; pre = "SITEWIRE/%s/" % site
    if bb.endswith("LUT"):
        sinks = [w for w in par if w.startswith(pre) and re.match(r"^%s[1-6]$" % bb[0], w[len(pre):])]
    else:
        sinks = [w for w in par if w.startswith(pre + pin)] or [w for w in par if w.startswith(pre) and par[w] and
                 not any(par.get(x, "").split("->")[0] == w for x in par)]
    if len(sinks) != 1: return None
    pips, w, seen = [], sinks[0], set()
    while w in par and par[w] and w not in seen:
        seen.add(w); pips.append(par[w]); w = par[w].split("->")[0]
    return pips or None
RS = re.compile(r"^[A-Z0-9_]*?_X(\d+)Y(\d+)/")
def region(inst):
    c = cells.get(inst)
    m = RS.match(c.get("attributes", {}).get("NEXTPNR_BEL", "")) if c else None
    return None if not m else (int(m.group(1)) // 10, int(m.group(2)) // 10)
def terms(path):
    out = []
    for via, d in path:
        if via[0] == "W":
            p = pips_of(via[1]); out.append(("W", d, tuple(p) if p else ("fallback:" + via[1],), region(via[1].rpartition("/")[0])))
        else:
            out.append(("L", d, (via[1] + via[2],), region(via[1])))
    return out
con, par = ram[RAM], ramp[RAM]
clk = best[con["CLKARDCLK"]]; tclk = terms(clk[1])
classes = {"ADDR": ("ADDRARDADDR", int(par["TSU_ADDR"])), "DI": ("DIADI", int(par["TSU_DI"])), "WE": ("WEA", int(par["TSU_WE"]))}
pinpaths = {cls: [(p, terms(worst[w][1])) for p, w in con.items() if p.startswith(pre) and w in worst]
            for cls, (pre, _) in classes.items()}
rng = random.Random(1)
def sample():
    npip, nreg, nlut = {}, {}, {}
    def pipf(p):
        if p not in npip: npip[p] = 1 + SW * rng.gauss(0, 1)
        return npip[p]
    def regf(r):
        if r is None: return 1
        if r not in nreg: nreg[r] = 1 + SR * rng.gauss(0, 1)
        return nreg[r]
    def val(ts):
        t = 0
        for kind, d, keys, r in ts:
            if kind == "W": f = sum(pipf(k) for k in keys) / len(keys)
            else:
                if keys not in nlut: nlut[keys] = 1 + SW * rng.gauss(0, 1)
                f = nlut[keys]
            t += max(0, d * f * regf(r))
        return t
    c = val(tclk)
    return {cls: c - max(val(ts) for _, ts in pinpaths[cls]) - classes[cls][1] for cls in classes if pinpaths[cls]}
nom = {cls: clk[0] - max(worst[con[p]][0] for p, _ in pinpaths[cls]) - classes[cls][1] for cls in classes if pinpaths[cls]}
res = collections.defaultdict(list)
for _ in range(NS):
    for k, v in sample().items(): res[k].append(v)
print("%s %s, source %s, clock path %d arcs (%d ps nominal), %d samples" % (RAM, bel.get(RAM), SRC, len(tclk), clk[0], NS))
for cls in res:
    v = sorted(res[cls]); n = len(v); mu = sum(v) / n; sd = math.sqrt(sum((x - mu) ** 2 for x in v) / n)
    q = lambda f: v[int(f * (n - 1))]
    print("  %-4s nominal %+5d ps | with scatter mean %+6.0f sd %4.0f  p01 %+5.0f p05 %+5.0f p50 %+5.0f  P(<0) %.3f  (scatter alone: sd %3.0f ps)"
          % (cls, nom[cls], mu, sd, q(.01), q(.05), q(.5), sum(1 for x in v if x < 0) / n, sd))
