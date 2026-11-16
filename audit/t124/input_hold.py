#!/usr/bin/env python3
"""T124b (audit, own code): input-boundary hold race of a kernel-input latch against a ZERO-HOLD sender, static, on
the BAKED netlist of one GLS corner (own graph t93/sta_lib, own latch mapping as t109/rule_h.py).
usage: input_hold.py WORKDIR ROUTED_JSON LINK_REGEX ACK_NETNAME
Per latch bit b of the matched link (the enable net en_w = its controller node, at its driver):
  close_b = ICBUF(en_w -> b's enable pin) + LUT arc(en pin -> O)
  t_ack   = shortest path en_w -> the kernel's input acknowledge net (OR-join through every cell: earliest ack fall)
  data_b  = interconnect delay from the D source (the sender's data net) to b's D pin(s) (max over its D pins: min would
            be the adversarial choice for hold, so take MIN)
  slack_b = t_ack + data_b - close_b   (the sender changes data the instant the ack falls: Spec.Env's broad rule)"""
import sys, os, re, json, heapq, collections
H = os.path.dirname(os.path.abspath(__file__)); sys.path.insert(0, os.path.join(H, '..', 't93'))
import sta_lib as S
W, RJ, RX, ACK = sys.argv[1:5]; rx = re.compile(RX)
N = S.Netlist(os.path.join(W, 'netlist_baked.v'))
m = list(json.load(open(RJ))["modules"].values())[0]
site_of_c, c_of_site = S.read_names_map(os.path.join(W, 'names.map'))
wire_of_name, name_of_wire = S.read_nets_map(os.path.join(W, 'nets.map'))
names_of_bit = collections.defaultdict(set)
for n, v in m["netnames"].items():
    for b in v["bits"]: names_of_bit[b].add(n)
def wire_of_bit(b):
    for n in names_of_bit[b]:
        if n in wire_of_name: return wire_of_name[n]
ic_src = {o: i for (i, o, d) in N.ic.values()}
ic_d = {o: d for (i, o, d) in N.ic.values()}
ack_w = wire_of_bit(m["netnames"][ACK]["bits"][0]); assert ack_w, ACK
luts = collections.defaultdict(list)
for cn, c in m["cells"].items():
    mm = re.match(r'(bridge_i\.udut\..*)\.lat\.(pair\[\d+\]|odd)\.u(\$LUT6|\$LUT5)?$', cn)
    if not mm or not rx.search(mm[1]): continue
    cc = c["connections"]; dirs = c.get("port_directions", {})
    ins = {b for p, bb in cc.items() if dirs.get(p) == "input" for b in bb if isinstance(b, int)}
    outs = {b for p, bb in cc.items() if dirs.get(p) == "output" for b in bb if isinstance(b, int)}
    luts[mm[1]].append((cn, c["attributes"].get("NEXTPNR_BEL"), ins, outs))
for inst, lst in sorted(luts.items()):
    allouts = set().union(*(o for _, _, _, o in lst))
    cand = [ins - allouts - {b for b in ins if any(n.startswith('$PACKER') for n in names_of_bit[b])} for _, _, ins, _ in lst]
    shared = set.intersection(*cand)
    if len(shared) != 1: print(inst, 'UNMAPPED', len(shared)); continue
    en_b = shared.pop(); en_w = wire_of_bit(en_b)
    best = {en_w: 0}; hq = [(0, en_w)]; prev = {}
    while hq:
        t, net = heapq.heappop(hq)
        if t > best.get(net, 1e18): continue
        if net == ack_w: break
        for (src, dst, d, kind, cell, pin) in N.fan.get(net, ()):
            if t + d < best.get(dst, 1e18): best[dst] = t + d; prev[dst] = (net, kind, cell, pin); heapq.heappush(hq, (t + d, dst))
    t_ack = best.get(ack_w)
    if os.environ.get('PATHS'):
        n = ack_w; P = []
        while n in prev:
            src, kind, cell, pin = prev[n]
            P.append(f"{best[n]:6d} {'STATE ' if (kind == 'lut' and n in N.state_nets) else ''}{kind}:{cell}.{pin} -> {name_of_wire.get(n, n)}"); n = src
        print('   ack path:'); [print('     ' + p) for p in reversed(P)]
    rows = []
    for (cn, bel, ins, outs), cs in zip(lst, cand):
        c = c_of_site.get(bel)
        if c is None or c not in N.cells: continue
        pins = N.cells[c]['pins']; out = N.cells[c]['out']
        d_ws = {wire_of_bit(b) for b in cs - {en_b}}
        close = None; dd = []
        for p, w in pins.items():
            if not p.startswith('A'): continue
            src = ic_src.get(w)
            if src == en_w: close = ic_d[w] + N.cells[c]['params'].get(f'T{p}{out}', 124); enp, en_ic = p, ic_d[w]
            elif src in d_ws: dd.append((ic_d[w] + N.cells[c]['params'].get(f'T{p}{out}', 124), name_of_wire.get(src, src)))
        if close is None or not dd: continue
        dmin = min(dd)
        rows.append((t_ack + dmin[0] - close, cn, close, dmin[0], dmin[1], c, enp, en_ic))
    rows.sort()
    if os.environ.get('JSON'):
        json.dump(dict(ack=ack_w, en=en_w, t_ack=t_ack, bits=[dict(slack=r[0], name=r[1], close=r[2], data=r[3], cell=r[5], enpin=r[6], en_ic=r[7]) for r in rows]), open(os.environ['JSON'], 'w'), indent=1)
    print(f"{inst}: en {name_of_wire.get(en_w, en_w)}  t_ack(en->{ACK}) = {t_ack} ps  bits {len(rows)}")
    for r in rows[:6]:
        print(f"   slack {r[0]:6d}  close {r[2]:5d}  data(src->D->O) {r[3]:5d}  {r[1]}  src {r[4]}")
