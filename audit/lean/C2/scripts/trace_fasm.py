"""Auditor's own FASM -> (INIT, A1..A6 source) extractor. Uses prjxray db only
(tile types, tileconn, segbits, package pins). Independent of fasm2lean.py.
usage: trace_fasm.py DB PART design.fasm design.xdc"""
import sys, json, re, os, csv
from collections import defaultdict
from prjxray.db import Database
DB, PART, FASM, XDC = sys.argv[1:5]
db = Database(DB, PART)
grid = db.grid()
feats = set(); inits = {}
for line in open(FASM):
    line = line.split('#')[0].strip()
    if not line: continue
    m = re.match(r'(\S+)\.INIT\[(\d+):0\]\s*=\s*\d+\'b([01]+)', line)
    if m: inits[m.group(1)] = int(m.group(3), 2); continue
    feats.add(line)
# wires -> nodes, restricted: union-find on all tileconn connections
parent = {}
def find(x):
    while parent.get(x, x) != x:
        parent[x] = parent.get(parent[x], parent[x]); x = parent[x]
    return x
members = defaultdict(list)
for c in db.connections().get_connections():
    a = (c.wire_a.tile, c.wire_a.wire); b = (c.wire_b.tile, c.wire_b.wire)
    ra, rb = find(a), find(b)
    if ra != rb: parent[ra] = rb
def node(tw):
    r = find(tw)
    if r not in members:
        pass
    return r
allw = defaultdict(list)
for tw in list(parent.keys()):
    allw[find(tw)].append(tw)
def node_wires(tw):
    r = find(tw); return allw.get(r, [tw]) if tw in parent else [tw]
ttype = {t: grid.gridinfo_at_tilename(t).tile_type for t in grid.tiles()}
pipcache = {}; segcache = {}
def pips_into(tt, w):
    if tt not in pipcache:
        d = defaultdict(list)
        for k, p in db.get_tile_type(tt).to_json()['pips'].items() if hasattr(db.get_tile_type(tt),'to_json') else []:
            d[p['dst_wire']].append(p['src_wire'])
        pipcache[tt] = d
    return pipcache[tt][w]
# raw json load for pips (simplest)
def tile_json(tt):
    p = os.path.join(DB, 'tile_type_%s.json' % tt)
    return json.load(open(p)) if os.path.exists(p) else {'pips': {}}
pj = {}
def pips_to(tt, w):
    if tt not in pj:
        d = defaultdict(list)
        for k, p in tile_json(tt)['pips'].items():
            d[p['dst_wire']].append((p['src_wire'], p))
        pj[tt] = d
    return pj[tt][w]
def segfeats(tt):
    if tt not in segcache:
        s = set(); p = os.path.join(DB, 'segbits_%s.db' % tt.lower())
        if os.path.exists(p):
            for l in open(p): s.add(l.split()[0])
        segcache[tt] = s
    return segcache[tt]
def active(tile, tt, dst, src):
    f = '%s.%s.%s' % (tt, dst, src)
    if f in segfeats(tt): return ('%s.%s.%s' % (tile, dst, src)) in feats
    # no config bits: fixed connection (site pin pass-throughs etc.)
    return True
STOP = re.compile(r'^(CLBL[LM]_[LM]_(A|B|C|D|AMUX|BMUX|CMUX|DMUX)|GND_WIRE|VCC_WIRE|[LR]IOI_ILOGIC[01]_D)$')
def trace(tile, wire, depth=0, path=()):
    for t, w in node_wires((tile, wire)):
        tt = ttype[t]
        if STOP.match(w): return (t, w, path + (w,))
        for src, p in pips_to(tt, w):
            if active(t, tt, w, src) and not (src == w):
                if ('INT' in tt and '%s.%s.%s' % (tt, w, src) not in segfeats(tt)): continue
                r = trace(t, src, depth+1, path + (w,))
                if r: return r
    return None
# ports: package pin -> port from xdc; IOB tile/site from package_pins.csv
pkg = {}
for row in csv.DictReader(open(os.path.join(DB, PART, 'package_pins.csv'))):
    pkg[row['pin']] = row
port_of_pin = {}
for l in open(XDC):
    m = re.search(r'PACKAGE_PIN (\S+) \[get_ports (\S+)\]', l)
    if m: port_of_pin[m.group(1)] = m.group(2)
ioi_port = {}
for pin, port in port_of_pin.items():
    site = pkg[pin]['site']; iob = pkg[pin]['tile']
    # IOB33 tile Y index of the site: even site Y -> IOB_Y1 (lower), odd -> IOB_Y0 (prjxray convention)
    sy = int(re.search(r'Y(\d+)', site).group(1))
    ioi_port[(iob, sy % 2)] = port
def describe(stop):
    t, w, path = stop
    if w == 'GND_WIRE': return 'GND'
    if w == 'VCC_WIRE': return 'VCC'
    m = re.match(r'[LR]IOI_ILOGIC([01])_D', w)
    if m:
        # IOI tile Xa Yb sits beside IOB tile at same X+? -> find IOB tile with same grid row pair
        gi = grid.gridinfo_at_tilename(t)
        return 'IOI %s ILOGIC%s' % (t, m.group(1))
    m = re.match(r'CLBL[LM]_([LM])_([A-D])(MUX)?$', w)
    return 'LUT %s %s %s' % (t, m.group(1) + m.group(2), 'MUX' if m.group(3) else 'O6')
for k, init in sorted(inits.items()):
    tile, slc, lut = k.split('.')[:3]
    LM = 'M' if slc.startswith('SLICEM') or (slc.endswith('X0') and 'CLBLM' in tile) else 'L'
    print('%s INIT=0x%016X' % (k, init))
    for i in range(1, 7):
        pin = 'CLBLM_%s_%s%d' % (LM, lut[0], i) if 'CLBLM' in tile else 'CLBLL_%s_%s%d' % (LM, lut[0], i)
        r = trace(tile, pin)
        print('   %s%d <- %s   via %s' % (lut[0], i, describe(r) if r else None, '<-'.join(reversed(r[2])) if r else ''))
print('OUTMUX feats:', sorted(f for f in feats if 'OUTMUX' in f))
print('IOB tiles of ports:', {p: (pkg[pin]['tile'], pkg[pin]['site']) for pin, p in port_of_pin.items()})
