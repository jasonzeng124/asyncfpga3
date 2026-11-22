#!/usr/bin/env python3
"""sizewhatif.py GRAPHDIR SIZES_VH [--only RX] [--depth LINK] -- predicted period of a route's event graph if its matched
delays had SIZES_VH's lengths (lines SIZES_VH does not set: the kernel.v parameter defaults, as a build would get them),
same placement and wires.  Per line: BD_SZ_..._<INST> = the instance's udly (an operator) / rdly (a link; a pipe's last
stage), _UACK = every uack chain of the link, _SDELAY = the rdly of a pipe's stages 0..N-2.  --only RX: change only the
lines whose macro matches RX.  Prints the base and edited period and the critical cycle by instance."""
import os, re, sys, statistics as st
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from whatif import G

def chains(g):
    out = {}
    for n in g.nodes:
        m = re.match(r"(.*\.(udly|rdly|uack|us)\.chain)\.g\[(\d+)\]\.u$", n.get("cell", ""))
        if m:
            out.setdefault(m.group(1), {}).setdefault(n["edge"], {})[int(m.group(3))] = n["id"]
    return out

def set_chain(g, c, els_by_edge, N, gm):
    for e, els in els_by_edge.items():
        M = max(els) + 1; ids = set(els.values())
        inner = [a["w"] for a in g.arcs if a["u"] in ids and a["v"] in ids]
        el = st.median(inner) if inner else gm[e]
        if e == "F" and M > 1 and not inner:
            continue                       # fast fall: one element whatever the length
        last = els[M - 1]
        ex = [a for a in g.arcs if a["u"] == last and a["v"] not in ids]
        # tokens (offsets) along the chain: g[k] -> g[k+1]; a bypass keeps the ones it skips (event labels can step
        # inside a long chain)
        step = {}
        for a in g.arcs:
            if a["u"] in ids and a["v"] in ids: step[a["u"]] = (a["v"], a["o"])
        def offs(k0):
            x, o = els[k0], 0
            while x != last and x in step:
                x, d = step[x]; o += d
            return o
        if N >= M:
            for a in ex: a["w"] += (N - M) * el
        elif N >= 1:
            d = offs(N - 1)
            for a in ex: a["u"] = els[N - 1]; a["o"] += d
        else:
            ent = [a for a in g.arcs if a["v"] == els[0] and a["u"] not in ids]
            if len(ent) != 1: return False
            d = offs(0)
            for a in ex: a["u"] = ent[0]["u"]; a["w"] = max(0, a["w"] + ent[0]["w"] - el); a["o"] += ent[0]["o"] + d
    return True

def add_rdly(g, inst, N, gm):
    t, par, ports = g.verilog()[inst]
    cons = set()
    for n in g.downstream(ports["req_out"][0]): cons |= g.listing(n)
    cons = {x for x in cons - {inst} if g.verilog()[x][0] != "bd_fork"}
    nst = int(re.search(r"\.N\((\d+)\)", par).group(1)) if t == "bd_pipe" else 1
    cell = "bridge_i.udut.%s.ctl.u.u" % inst if nst == 1 else "bridge_i.udut.%s.many.stage[%d].u.ctl.u.u" % (inst, nst - 1)
    cn = {n["id"] for n in g.nodes if n.get("cell", "") == cell}
    k = 0
    for a in g.arcs:
        if a["u"] in cn and g.nodes[a["v"]]["inst"] in cons:
            a["w"] += N * gm[g.nodes[a["u"]]["edge"]]; k += 1
    return k

def main():
    gd, sz = sys.argv[1], sys.argv[2]
    only = re.compile(sys.argv[sys.argv.index("--only") + 1]) if "--only" in sys.argv else None
    g = G(gd); base = g.period()[0]
    for x in [sys.argv[i + 1] for i, a in enumerate(sys.argv) if a == "--depth"]:
        g.apply("depth:%s:3:1" % x)
    eR, eF = g.elem(); gm = {"R": eR, "F": eF}
    kv = open(gd + "/kernel.v").read()
    m = [x for x in re.finditer(r"module\s+(bdc_\w+)\s*#\((.*?)\)\s*\(", kv, re.S) if "DELAY_" in x.group(2)][-1]
    m = type("M", (), {"group": lambda self, k, _m=m: _m.group(2)})()
    defaults = {k: int(v) for k, v in re.findall(r"parameter\s+DELAY_(\w+)\s*=\s*(\d+)", m.group(1))}
    want = dict(defaults)
    for l in open(sz):
        mm = re.match(r"`define\s+BD_SZ_BRIDGE_I_UDUT_(\S+)\s+(\d+)", l)
        if mm and mm.group(1) in want: want[mm.group(1)] = int(mm.group(2))
    # the route's own values (what the graph was built with): its sizes = the kernel.v the graph dir holds is the
    # SAME text for every sizes file (parameters are overridden in the bench top), so read the chain lengths instead
    insts = {i.upper(): i for i in g.verilog()}
    ch = chains(g); changed = []
    for mac, N in sorted(want.items()):
        if only and not only.search(mac): continue
        kind = "main"; base_mac = mac
        for suf, kd in (("_UACK", "uack"), ("_SDELAY", "sdelay")):
            if mac.endswith(suf): kind = kd; base_mac = mac[:-len(suf)]
        inst = insts.get(base_mac)
        if inst is None: continue
        t, par, ports = g.verilog()[inst]
        nst = int(re.search(r"\.N\((\d+)\)", par).group(1)) if t == "bd_pipe" else 1
        pre = "bridge_i.udut.%s." % inst
        if kind == "uack":
            cs = [c for c in ch if c.startswith(pre) and c.endswith(".uack.chain")]
        elif kind == "sdelay":
            cs = [c for c in ch if c.startswith(pre) and c.endswith(".rdly.chain") and "many.stage[%d]" % (nst - 1) not in c]
        elif t in ("bd_link", "bd_pipe"):
            cs = [c for c in ch if c.startswith(pre) and c.endswith(".rdly.chain") and (nst == 1 or "many.stage[%d]" % (nst - 1) in c)]
        else:
            cs = [c for c in ch if c.startswith(pre) and c.endswith(".udly.chain")]
        if cs:
            cur = max(max(els) + 1 for els in ch[cs[0]].values())
            if cur == N: continue
            for c in cs: set_chain(g, c, ch[c], N, gm)
            changed.append("%s %d->%d" % (mac, cur, N))
        elif N > 0 and kind == "main" and t in ("bd_link", "bd_pipe"):
            if add_rdly(g, inst, N, gm): changed.append("%s 0->%d" % (mac, N))
        elif N > 0:
            changed.append("%s 0->%d(NOT MODELLED)" % (mac, N))
    lam, cyc = g.period(); by, flips = g.describe(cyc)
    print("%s base %.0f edited %.0f (%+.0f)" % (gd.rstrip("/").split("/")[-1], base, lam, lam - base))
    print("  changed: " + ", ".join(changed))
    print("  cycle: " + ", ".join(by) + "; polarity changes %d" % len(flips))

if __name__ == "__main__":
    main()
