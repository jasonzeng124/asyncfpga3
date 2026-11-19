#!/usr/bin/env python3
"""ram_race_all.py WORKDIR -- ram_race.py for every RAM of a route and every request that reaches its clock: the
bench's host request flops (bridge_i.mem_hreq*) and the kernel's port slots (umem_controller*_s*_req nets).  One line
per (RAM, source, pin class): clock arrival, latest pin, margin = t_clk - t_pin - TSU (the GLS model's own TSU)."""
import collections, re, sys
W = sys.argv[1]
net_of, bel = {}, {}
for l in open(W + "/nets.map"):
    p = l.split(None, 1)
    if len(p) == 2 and not l.startswith("#"): net_of[p[1].strip()] = p[0]
for l in open(W + "/names.map"):
    p = l.split(None, 1)
    if len(p) == 2 and not l.startswith("#"): bel[p[0]] = p[1].strip()
fwd = collections.defaultdict(list); rams = []
ric = re.compile(r"ICBUF #\(\.D\((\d+)\)\) (\S+) \(\.I\((\S+)\), \.O\((\S+)\)\);")
rlut = re.compile(r"SLICE_LUTX #\((.*)\) (\S+) \((.*)\);")
rram = re.compile(r"RAMB18E1_RAMB18E1 #\((.*)\) (\S+) \((.*)\);")
for l in open(W + "/netlist_baked.v"):
    l = l.strip(); m = ric.match(l)
    if m: fwd[m.group(3)].append((m.group(4), int(m.group(1)))); continue
    m = rlut.match(l)
    if m:
        par = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(1))); con = dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(3)))
        for k in range(1, 7):
            for o in ("O6", "O5"):
                d = par.get("TA%d%s" % (k, o))
                if d is not None and ("A%d" % k) in con and o in con: fwd[con["A%d" % k]].append((con[o], int(d)))
        continue
    m = rram.match(l)
    if m: rams.append((m.group(2), dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(1))), dict(re.findall(r"\.(\w+)\(([^()]*)\)", m.group(3)))))
srcs = sorted(n for n in net_of if re.match(r"^bridge_i\.mem_hreq(\[\d+\])?$", n) or re.match(r"^bridge_i\.udut\.umem_controller\d+_s\d+_req$", n))
def walk(src, fwd=None, maxl=6):
    """early: shortest arrival (Dijkstra, any depth); late: longest SIMPLE path of at most maxl arcs (the payload is
    the request through the port's mux LUT(s): 3-5 arcs; the bound keeps C-element feedback loops out)."""
    import heapq
    early = {src: 0}; pq = [(0, src)]
    while pq:
        t, n = heapq.heappop(pq)
        if t > early.get(n, 1 << 60): continue
        for d, w, *_ in fwd.get(n, ()):
            if t + w < early.get(d, 1 << 60): early[d] = t + w; heapq.heappush(pq, (t + w, d))
    late = {src: 0}; lpath = {src: []}
    def dfs(n, t, seen, path):
        if len(path) >= maxl: return
        for d, w, *via in fwd.get(n, ()):
            if d in seen: continue
            if t + w > late.get(d, -1): late[d] = t + w; lpath[d] = path + [(via[0] if via else None, w)]
            dfs(d, t + w, seen | {d}, path + [(via[0] if via else None, w)])
    dfs(src, 0, {src}, [])
    return early, late, lpath
pt = open(W + "/point.txt").read().strip() if __import__("os").path.exists(W + "/point.txt") else "?"
for s in srcs:
    early, late, _ = walk(net_of[s], fwd)
    for inst, par, con in rams:
        if con["CLKARDCLK"] not in early: continue
        tc = early[con["CLKARDCLK"]]
        for cls, pre, tsu in (("ADDR", "ADDRARDADDR", "TSU_ADDR"), ("DI", "DIADI", "TSU_DI"), ("WE", "WEA", "TSU_WE")):
            pins = [(late[w], p) for p, w in con.items() if p.startswith(pre) and w in late]
            if not pins: continue
            t, p = max(pins)
            print("%-24s %-8s %-22s %-4s clk %5d  %-14s %5d  margin %+5d ps  [%s]" % (s.replace("bridge_i.", ""), inst,
                  bel.get(inst, "?").split("/")[0], cls, tc, p, t, tc - t - int(par[tsu]), pt))
