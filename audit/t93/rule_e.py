#!/usr/bin/env python3
"""T93 (audit, own code): static rule-E check at one bd_steer (default bridge_i.udut.ucond_br6).

usage: rule_e.py <workdir> <logical routed json> <launch-link> [--k K ...] [--plant ic_NNNNNN:ps ...] [--json out]

  <launch-link>  e.g. ulink_n7 : the bd_link whose C node (<link>.ctl.u.u) is the common launch event.
                 The s side starts at that C node and may traverse ONLY that link's latch LUTs (<link>.lat.*, via
                 their en pin, never their feedback pin; the d pin is not derived from this launch).
                 The req side starts at the same C node and may traverse ONLY the C-element LUTs whose logical
                 name is in REQ_STATE (the joins on the request path); every other state LUT is a cut.
  margin = min rise arrival of req at the steer LUT's req pin  -  max arrival of any change at its s pin.

Request side ("earliest rise", lower bound): every net in the req cone is assumed to make one 0->1 transition
caused by the launch; every input of a cone LUT that is NOT in the cone (rst, the join partner from another
channel, ...) is a free but stable value; the feedback pin of a C-element is held at 0 (output starts low).  The LUT
output rises at the earliest time the LUT function, evaluated on the per-pin delayed inputs (fid transport model),
can be 1: min over stable assignments N of the free pins with f(all-derived=0)=0, min over subsets S of derived pins
with f(S=1)=1, of max_{i in S} (arr_i + arc_i).  So an AND (delay-chain side tap, C-element) waits for its last
derived input, an OR takes its first.

Select side (latest change, upper bound): longest path over every arc in the cone (LUT arcs only on pins in the
function's support; all CARRY4 arcs, i.e. a full-length carry through every CARRY4 is assumed possible).
--k K additionally reports the select side with the uaddi0 adder restricted to its first K CARRY4 slices and to the
launching latch bits < 4K (bits >= 4K and slices >= K are taken as not toggling, i.e. counter < 2^(4K)).
"""
import sys, json, re, collections, argparse
sys.path.insert(0, '/home/user/asyncfpga3/audit/t93')
from sta_lib import Netlist, read_names_map, lut_eval

STEER = 'bridge_i.udut.ucond_br6'
P = 'bridge_i.udut.'
REQ_STATE = [P + 'uaddi0.ujoin.', P + 'ucmpi1.ujoin.', P + 'ucond_br6_j.']
ADDER = P + 'uaddi0.'

ap = argparse.ArgumentParser()
ap.add_argument('work'); ap.add_argument('rj'); ap.add_argument('link')
ap.add_argument('--k', type=int, action='append', default=[])
ap.add_argument('--bits', type=int, action='append', default=[])
ap.add_argument('--plant', action='append', default=[])
ap.add_argument('--json')
ap.add_argument('--transparent', action='append', default=[],
                help='downstream link treated as TRANSPARENT: its latch LUTs are traversed d->q and en->q on the s side '
                     'and its C node on the req side (instead of being cut)')
ap.add_argument('--quiet', action='store_true')
a = ap.parse_args()

plant = {}
for p in a.plant:
    n, d = p.split(':'); plant[n] = int(d)
nl = Netlist(a.work + '/netlist_baked.v', icbuf_override=plant)
site_of_c, c_of_site = read_names_map(a.work + '/names.map')
m = list(json.load(open(a.rj))['modules'].values())[0]
lname, cof, outbits = {}, {}, {}
bitnames = collections.defaultdict(set)
for n, v in m['netnames'].items():
    for b in v['bits']: bitnames[b].add(n)
for cn, c in m['cells'].items():
    bel = c['attributes'].get('NEXTPNR_BEL')
    if bel in c_of_site:
        lname[c_of_site[bel]] = cn; cof[cn] = c_of_site[bel]
        outs = [b for p_, bb in c['connections'].items() if c.get('port_directions', {}).get(p_) == 'output'
                for b in bb if isinstance(b, int)]
        outbits[c_of_site[bel]] = sorted(n for b in outs for n in bitnames[b])
def L(c): return lname.get(c, '?' + site_of_c.get(c, c))
def src_of(net):
    icn = nl.ic_by_out.get(net)
    return nl.ic[icn][0] if icn else net

# ---- steer LUTs and their req / s pins (mon_steer.py logic, re-derived: pin whose ICBUF source is the req net) ----
launch_c = cof[P + a.link + '.ctl.u.u']
launch_net = nl.cells[launch_c]['pins'][nl.cells[launch_c]['out']]
req_driver_net = None
steers = []
for suf in ('.u$LUT6', '.u$LUT5'):
    c = cof.get(STEER + suf)
    if c is None: continue
    cc = nl.cells[c]
    rp = sp = None
    for k in sorted(cc['support']):
        net = cc['pins'][f'A{k}']
        drv = nl.driver.get(src_of(net), ('?',))[0]
        if L(drv).startswith(STEER + '_j.'): rp = (f'A{k}', net)
        elif drv in nl.cells and nl.cells[drv]['type'] == 'SLICE_LUTX' and drv != c: sp = (f'A{k}', net)
    steers.append((c, STEER + suf, rp, sp))

# ---- state-node cut sets ----
state_cells = set(nl.state_nets.values())
latch_cells = {c for c in state_cells if L(c).startswith(P + a.link + '.lat.')}
launch_latches = set(latch_cells)
req_cells = {c for c in state_cells if any(L(c).startswith(x) for x in REQ_STATE)}
for t in a.transparent:
    latch_cells |= {c for c in state_cells if L(c).startswith(P + t + '.lat.')}
    req_cells |= {c for c in state_cells if L(c).startswith(P + t + '.ctl.')}

def arcs_ok(e, allowed, excluded):
    src, dst, d, kind, cell, pin = e
    if cell in excluded: return False
    if kind == 'lut':
        cc = nl.cells[cell]
        if int(pin[1:]) in cc['fb']: return False           # never through a feedback pin
        if cell in state_cells and cell not in allowed: return False
    return True

def cone(start, end, allowed, excluded=frozenset(), excl_nets=frozenset()):
    fw, stk = set(), [start]
    while stk:
        n = stk.pop()
        if n in fw or n in excl_nets: continue
        fw.add(n)
        for e in nl.fan[n]:
            if arcs_ok(e, allowed, excluded): stk.append(e[1])
    bw, stk = set(), [end]
    while stk:
        n = stk.pop()
        if n in bw or n not in fw: continue
        bw.add(n)
        for e in nl.fin[n]:
            if arcs_ok(e, allowed, excluded): stk.append(e[0])
    return bw

def topo(cn, allowed, excluded):
    indeg = {n: 0 for n in cn}
    edges = collections.defaultdict(list)
    for n in cn:
        for e in nl.fan[n]:
            if e[1] in cn and arcs_ok(e, allowed, excluded):
                edges[n].append(e); indeg[e[1]] += 1
    q = [n for n in cn if indeg[n] == 0]; order = []
    while q:
        n = q.pop(); order.append(n)
        for e in edges[n]:
            indeg[e[1]] -= 1
            if indeg[e[1]] == 0: q.append(e[1])
    if len(order) != len(cn):
        raise SystemExit(f'cycle in cone: {len(cn)-len(order)} nets not ordered')
    return order, edges

def longest(start, end, allowed, excluded=frozenset(), excl_nets=frozenset()):
    cn = cone(start, end, allowed, excluded, excl_nets)
    if end not in cn: return None, [], cn
    order, edges = topo(cn, allowed, excluded)
    arr = {start: 0}; pred = {}
    for n in order:
        if n not in arr: continue
        for e in edges[n]:
            t = arr[n] + e[2]
            if t > arr.get(e[1], -1): arr[e[1]] = t; pred[e[1]] = e
    path, n = [], end
    while n in pred: path.append(pred[n]); n = pred[n][0]
    return arr[end], path[::-1], cn

def earliest_rise(start, end, allowed, or_join=False):
    cn = cone(start, end, allowed)
    if end not in cn: return None, [], cn, []
    order, edges = topo(cn, allowed, frozenset())
    arr = {start: 0}; pred = {}; notes = []
    for n in order:
        if n == start: continue
        ins = [e for e in nl.fin[n] if e[0] in cn and arcs_ok(e, allowed, frozenset())]
        if not ins: continue
        kind = ins[0][3]
        if kind == 'ic':
            e = ins[0]; arr[n] = arr[e[0]] + e[2]; pred[n] = [e]; continue
        if kind != 'lut':
            # non-LUT on the request path: fall back to plain min (lower bound)
            e = min(ins, key=lambda e: arr[e[0]] + e[2]); arr[n] = arr[e[0]] + e[2]; pred[n] = [e]
            notes.append(f'non-LUT {e[4]} on req path, plain min'); continue
        cell = ins[0][4]; cc = nl.cells[cell]; out = cc['out']; init = cc['params']['INIT']
        D = {int(e[5][1:]): e for e in ins}
        fb = cc['fb']
        free = [k for k in cc['support'] if k not in D and k not in fb]
        best = None
        for na in range(1 << len(free)):
            base = {k: (na >> i) & 1 for i, k in enumerate(free)}
            base.update(cc['const'])
            for f in fb: base[f] = 0
            pins0 = dict(base); [pins0.__setitem__(k, 0) for k in D]
            if lut_eval(init, out, pins0) != 0: continue
            Dk = sorted(D)
            for s in range(1, 1 << len(Dk)):
                pins = dict(pins0)
                S = [Dk[i] for i in range(len(Dk)) if s >> i & 1]
                for k in S: pins[k] = 1
                if lut_eval(init, out, pins) != 1: continue
                t = max(arr[D[k][0]] + D[k][2] for k in S)
                if best is None or t < best[0]: best = (t, [D[k] for k in S], base)
        if or_join and L(cell).startswith(STEER + '_j.'):
            e = min(D.values(), key=lambda e: arr[e[0]] + e[2]); best = (arr[e[0]] + e[2], [e], {})
        if best is None:
            raise SystemExit(f'req cone LUT {cell} {L(cell)} cannot rise under the 0->1 assumption')
        arr[n] = best[0]; pred[n] = best[1]
        if len(D) > 1:
            notes.append(f'{L(cell)}: derived pins {sorted(D)}, rise needs {[e[5] for e in best[1]]}, free {base_str(best[2], free)}, '
                         f'pin arrivals+arc {dict((f"A{k}", arr[D[k][0]] + D[k][2]) for k in sorted(D))}, out {best[0]}')
    # critical path back-trace (through the input that set the max)
    path, n = [], end
    while n in pred:
        e = max(pred[n], key=lambda e: arr[e[0]] + e[2]); path.append(e); n = e[0]
    return arr.get(end), path[::-1], cn, notes

def plain_min(start, end, allowed):
    """diagnostic only: shortest path over every arc of the req cone (ignores AND/C-element semantics)."""
    cn = cone(start, end, allowed)
    order, edges = topo(cn, allowed, frozenset())
    arr = {start: 0}
    for n in order:
        if n not in arr: continue
        for e in edges[n]:
            t = arr[n] + e[2]
            if t < arr.get(e[1], 1 << 60): arr[e[1]] = t
    return arr.get(end)

def base_str(b, free): return {f'A{k}': b.get(k) for k in free}

def fmt_path(path, arr0=0):
    out, t = [], arr0
    for e in path:
        t += e[2]
        if e[3] == 'ic': continue
        out.append(f'    {t:7d}  {e[4]} {e[5]:<8s} +{e[2]:4d}  {L(e[4])[len(P):]}')
    return out

def adder_restrict(nbits):
    """cells that are static when the counter stays below 2^nbits: uaddi0 CARRY4 slices >= ceil(nbits/4) and the
    launching latch bits >= nbits never change (slice ceil(nbits/4)-1 is kept whole, so this is pessimistic by
    up to 3 bits of carry when nbits is not a multiple of 4)."""
    k = (nbits + 3) // 4
    excl = set()
    for c, cc in nl.cells.items():
        if cc['type'] != 'CARRY4': continue
        mm = re.search(r'slice\[(\d+)\]', L(c))
        if L(c).startswith(ADDER) and mm and int(mm[1]) >= k: excl.add(c)
    bits = {}
    for c in launch_latches:
        nets = [n for n in outbits.get(c, []) if re.search(r'_data\[\d+\]$', n)]
        bs = {int(re.search(r'\[(\d+)\]$', n)[1]) for n in nets}
        if len(bs) != 1: raise SystemExit(f'cannot get the bit of latch {L(c)}: {nets}')
        b = bs.pop(); bits[c] = b
        if b >= nbits: excl.add(c)
    return excl, bits

res = dict(work=a.work, link=a.link, plant=plant, steers=[])
for c, ln, rp, sp in steers:
    r = dict(lut=c, name=ln, req_pin=rp, s_pin=sp)
    if rp is None or sp is None:
        print(f'{ln}: could not map req/s pins ({rp}, {sp})'); res['steers'].append(r); continue
    smax, spath, scone = longest(launch_net, sp[1], latch_cells)
    rmin, rpath, rcone, notes = earliest_rise(launch_net, rp[1], req_cells)
    r['req_plain_min_diag'] = plain_min(launch_net, rp[1], req_cells)
    r['req_orjoin_diag'] = earliest_rise(launch_net, rp[1], req_cells, or_join=True)[0]
    r.update(s_max=smax, req_min=rmin, margin=(rmin - smax) if smax is not None and rmin is not None else None)
    scells = sorted({e[4] for n in scone for e in nl.fin[n] if e[0] in scone and e[3] != 'ic'})
    r['s_cone'] = dict(nets=len(scone), cells=len(scells),
                       latches=sorted(L(x)[len(P):] for x in scells if x in latch_cells),
                       carry4=sorted(L(x)[len(P):] for x in scells if nl.cells[x]['type'] == 'CARRY4'))
    rcells = sorted({e[4] for n in rcone for e in nl.fin[n] if e[0] in rcone and e[3] != 'ic'})
    r['req_cone_cells'] = [L(x)[len(P):] for x in rcells]
    r['req_notes'] = notes
    r['s_path'] = fmt_path(spath); r['req_path'] = fmt_path(rpath)
    r['restricted'] = {}
    for k in [4 * x for x in a.k] + a.bits:
        excl, bits = adder_restrict(k)
        smk, pk, _ = longest(launch_net, sp[1], latch_cells, excluded=excl)
        r['restricted'][k] = dict(s_max=smk, margin=(rmin - smk) if smk is not None else None,
                                  ncarry_excluded=sum(1 for x in excl if nl.cells[x]['type'] == 'CARRY4'),
                                  nlatch_excluded=sum(1 for x in excl if x in launch_latches), s_path=fmt_path(pk))
    res['steers'].append(r)
    if not a.quiet:
        print(f'== {ln} ({c} at {site_of_c[c]}), launch {a.link}.ctl  req pin {rp[0]} ({rp[1]}), s pin {sp[0]} ({sp[1]})')
        print(f'   s cone: {len(scone)} nets, {len(scells)} cells, latches {len(r["s_cone"]["latches"])}, CARRY4 {r["s_cone"]["carry4"] and len(r["s_cone"]["carry4"])}')
        print(f'   req cone cells: {r["req_cone_cells"]}')
        for x in notes: print('   req note:', x)
        print(f'   [diag] plain shortest req path (ignores AND/C semantics): {r["req_plain_min_diag"]} ps'
              f' -> margin {r["req_plain_min_diag"] - smax if smax is not None else None}')
        print(f'   [diag] req if {STEER}_j rose on its FIRST derived input (OR, wrong for a C-element): '
              f'{r["req_orjoin_diag"]} ps -> margin {r["req_orjoin_diag"] - smax if smax is not None else None}')
        print(f'   max s arrival {smax} ps   min req rise {rmin} ps   MARGIN {r["margin"]} ps')
        for k, v in r['restricted'].items():
            print(f'   counter < 2^{k} (adder slices < {(k+3)//4}, latch bits < {k}): max s {v["s_max"]}  margin {v["margin"]}  '
                  f'(excluded {v["ncarry_excluded"]} CARRY4, {v["nlatch_excluded"]} latch LUTs)')
        print('   critical s path (arrival, cell, arc, delay, logical):'); print('\n'.join(r['s_path']))
        for k, v in r['restricted'].items():
            print(f'   critical s path, counter < 2^{k}:'); print('\n'.join(v['s_path']))
        print('   critical req path:'); print('\n'.join(r['req_path']))
        # ICBUFs on the critical s path for the planted-error test
        print('   ICBUFs on critical s path:', [e[4] for e in spath if e[3] == 'ic'][:40])
        print('   ICBUFs on critical req path:', [e[4] for e in rpath if e[3] == 'ic'][:40])
if a.json: json.dump(res, open(a.json, 'w'), indent=1, default=str)
