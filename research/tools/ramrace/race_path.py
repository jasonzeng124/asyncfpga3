#!/usr/bin/env python3
"""race_path.py WORKDIR [WORKDIR2 ...] -- the two arcs-by-arc paths of umem0's WE race (bridge_i.mem_hreq -> the RAM's
CLKARDCLK, shortest; -> its latest WEA pin, longest), one column per work dir (netlist_baked.v delays)."""
import collections, re, sys
def load(W):
    net_of, bel = {}, {}
    for l in open(W + "/nets.map"):
        p = l.split(None, 1)
        if len(p) == 2 and not l.startswith("#"): net_of[p[1].strip()] = p[0]
    for l in open(W + "/names.map"):
        p = l.split(None, 1)
        if len(p) == 2 and not l.startswith("#"): bel[p[0]] = p[1].strip()
    fwd = collections.defaultdict(list); ram = {}
    ric = re.compile(r"ICBUF #\(\.D\((\d+)\)\) (\S+) \(\.I\((\S+)\), \.O\((\S+)\)\);")
    rlut = re.compile(r"SLICE_LUTX #\((.*)\) (\S+) \((.*)\);")
    rram = re.compile(r"RAMB18E1_RAMB18E1 #\((.*)\) (\S+) \((.*)\);")
    for l in open(W + "/netlist_baked.v"):
        l = l.strip(); m = ric.match(l)
        if m: fwd[m.group(3)].append((m.group(4), int(m.group(1)), "wire " + bel.get(m.group(2), m.group(2)).replace("INTERCONNECT ", ""))); continue
        m = rlut.match(l)
        if m:
            par = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(1))); con = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(3)))
            for k in range(1, 7):
                for o in ("O6", "O5"):
                    d = par.get("TA%d%s" % (k, o))
                    if d is not None and ("A%d" % k) in con and o in con:
                        fwd[con["A%d" % k]].append((con[o], int(d), "LUT  %s A%d->%s" % (bel.get(m.group(2)), k, o)))
            continue
        m = rram.match(l)
        if m: ram[m.group(2)] = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(3)))
    return net_of, bel, fwd, ram
def paths(W, ramname="c_000008"):
    net_of, bel, fwd, ram = load(W)
    src = net_of["bridge_i.mem_hreq"]
    import heapq
    best = {src: (0, [])}; pq = [(0, 0, src)]; cnt = 1          # shortest (the clock): Dijkstra, any depth
    while pq:
        t, _, n = heapq.heappop(pq)
        if t > best[n][0]: continue
        for d, w, via in fwd.get(n, ()):
            if d not in best or t + w < best[d][0]:
                best[d] = (t + w, best[n][1] + [(via, w)]); heapq.heappush(pq, (t + w, cnt, d)); cnt += 1
    worst = {src: (0, [])}                                       # longest simple path of <= 6 arcs (the payload)
    def dfs(n, t, seen, path):
        if len(path) >= 6: return
        for d, w, via in fwd.get(n, ()):
            if d in seen: continue
            if d not in worst or t + w > worst[d][0]: worst[d] = (t + w, path + [(via, w)])
            dfs(d, t + w, seen | {d}, path + [(via, w)])
    dfs(src, 0, {src}, [])
    con = ram[ramname]
    clk = best[con["CLKARDCLK"]]
    we = max((worst[w] for p, w in con.items() if p.startswith("WEA") and w in worst), key=lambda x: x[0])
    return clk, we
cols = [paths(W) for W in sys.argv[1:]]
for title, idx in (("CLK (shortest)", 0), ("WE (latest pin)", 1)):
    print(title)
    n = max(len(c[idx][1]) for c in cols)
    for i in range(n):
        row = [c[idx][1][i] if i < len(c[idx][1]) else ("", 0) for c in cols]
        print("  %-62s" % row[0][0][:62] + "".join("%7d" % r[1] for r in row))
    print("  %-62s" % "total" + "".join("%7d" % c[idx][0] for c in cols))
print("%-64s" % "CLK - WE - 532 (margin)" + "".join("%7d" % (c[0][0] - c[1][0] - 532) for c in cols))
