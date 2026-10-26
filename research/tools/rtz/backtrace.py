import sys, re, collections, bisect, json
sys.path.insert(0, '/tmp/claude-0/-home-user-asyncfpga3/1493a6da-414d-591f-aed7-9ee9f21c4602/scratchpad/rtz')
from trace_lib import *
G, PRIMS = sys.argv[1], sys.argv[2]
dflt = load_prims_defaults(PRIMS)
icbuf, cells = load_netlist(G + '/netlist_baked.v')
drv = drivers(cells)
names = {}
for l in open(G + '/names.map'):
    p = l.split()
    if len(p) >= 2 and p[0].startswith('c_'): names[p[0]] = p[1]
netname = {}
for l in open(G + '/nets.map'):
    p = l.split()
    if len(p) >= 2: netname[p[0]] = p[1]
ev = load_vcd(G + '/rtz/v6.vcd', keep=lambda n: n.startswith('n'))
times = {n: [t for t, _ in e] for n, e in ev.items()}

def value_before(net, t):
    e = ev.get(net, []); i = bisect.bisect_left(times.get(net, []), t)
    return e[i-1][1] if i else None

def cause(net, t):
    if net not in drv: return None
    cell, port = drv[net]; typ, pd, cd = cells[cell]
    if typ == 'SLICE_FFX': return ('FF', cell)
    best = None
    for p, x in cd.items():
        if p in OUTS.get(typ, ()): continue
        if x.startswith('w'): src, D = icbuf[x]
        elif x.startswith('n'): src, D = x, 0
        else: continue
        key = 'T%s%s' % (p, port)
        arc = int(pd.get(key, dflt.get(typ, {}).get(key, 0)))
        tt = times.get(src, [])
        target = t - D - arc
        i = bisect.bisect_right(tt, target)
        if i == 0: continue
        te = tt[i-1]
        slack = target - te
        if slack < 0: continue
        if best is None or slack < best[0]:
            best = (slack, src, te, D, arc, p, ev[src][i-1][1])
    if best is None: return None
    slack, src, te, D, arc, p, v = best
    return dict(src=src, t=te, wire=D, arc=arc, slack=slack, pin=p, val=v, cell=names.get(cell, cell), port=port)

def chain(net, t, stop_t=None, stop=None, maxn=50000):
    out = []; n, tt = net, t
    for _ in range(maxn):
        c = cause(n, tt)
        if c is None or isinstance(c, tuple): out.append(('END', n, tt, c)); break
        out.append((n, tt, c))
        n, tt = c['src'], c['t']
        if stop and stop(n, tt): out.append(('STOP', n, tt, None)); break
        if stop_t is not None and tt <= stop_t: out.append(('STOP', n, tt, None)); break
    return out

def classify(cellname):
    nm = cellname.replace('urig.udut.', '')
    if not cellname.startswith('urig.udut.'): return ('rig:' + cellname.split('.')[1] if cellname.startswith('urig.') else 'top', '')
    parts = nm.split('.')
    inst = parts[0]
    role = 'other'
    if '.ctl.' in nm or nm.endswith('.ctl'): role = 'ctl'
    if '.rdly.' in nm: role = 'rdly'
    elif '.udly.' in nm or '.dly.' in nm: role = 'udly'
    elif '.lat.' in nm: role = 'latch'
    elif '.uack' in nm: role = 'ack'
    elif '.uj' in nm or 'join' in nm: role = 'join'
    elif '.ua' in nm: role = 'arb-ack'
    elif '.uarb' in nm: role = 'arb'
    return (inst, role)

if __name__ == '__main__':
    pass
