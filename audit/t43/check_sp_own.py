# T43: are formal A's site/pin tables (P.sites, P.pins, Q.pins) and D2's extra rules prjxray-db facts?
# P.pins key ty*2+rank -> key L*6+j -> wire of site pin <L><j+1>; Q.pins key -> 0 AX, 1 BX, 2 CX, 3 CIN (NodeMergePin.expect).
# rank = prjxray's x_coord of the slice within the tile type (X0/X1).  usage: check_sp_own.py SP_DUMP DB_DUMP XRAYDIR
import json, re, sys, os
spd, dbd, xd = sys.argv[1:4]
TY, TILE, WIRE = {}, {}, {}
for l in open(dbd):
    f = l.split()
    if f[0] == 'TY': TY[int(f[1])] = f[2]
    elif f[0] == 'TILE': TILE[int(f[1])] = (f[2], int(f[3]))
    elif f[0] == 'WIRE': WIRE[int(f[1])] = f[2]
SITE, PIN, PIN2, RULE, PAIR = {}, [], [], {}, {}
for l in open(spd):
    f = l.split()
    if f[0] == 'SITE': SITE[int(f[1])] = (f[2], int(f[3]), int(f[4]))
    elif f[0] == 'PIN': PIN.append(tuple(map(int, f[1:4])))
    elif f[0] == 'PIN2': PIN2.append(tuple(map(int, f[1:4])))
    elif f[0] == 'WIRE': WIRE[int(f[1])] = f[2]
    elif f[0] == 'RULE': RULE[int(f[1])] = tuple(map(int, f[2:8]))
    elif f[0] == 'PAIR': PAIR.setdefault(int(f[1]), []).append((int(f[2]), int(f[3]), int(f[4])))
grid = json.load(open(os.path.join(xd, 'xc7z010/tilegrid.json'))); conn = json.load(open(os.path.join(xd, 'xc7z010/tileconn.json')))
tt = {}
def ttype(name):
    if name not in tt: tt[name] = json.load(open(os.path.join(xd, 'tile_type_%s.json' % name)))
    return tt[name]
def spw(s, pin):
    v = s['site_pins'].get(pin) if s else None
    return v['wire'] if isinstance(v, dict) else v
def site_by_rank(tyname, rank):
    ss = [s for s in ttype(tyname)['sites'] if s['type'].startswith('SLICE')]
    m = [s for s in ss if s['x_coord'] == rank]
    return m[0] if len(m) == 1 else None
# sites: name in tile's sites, and rank = x_coord of that site in the tile type (match by the site's X parity within tile)
bad_s = []
for i, (sn, ti, rk) in SITE.items():
    tname, ty = TILE[ti]; g = grid[tname]
    if sn not in g.get('sites', {}) or not g['sites'][sn].startswith('SLICE'): bad_s.append((i, sn, tname, 'not a slice of tile')); continue
    xs = sorted(int(re.search(r'X(\d+)', s).group(1)) for s, t in g['sites'].items() if t.startswith('SLICE'))
    myx = int(re.search(r'X(\d+)', sn).group(1))
    if xs.index(myx) != rk: bad_s.append((i, sn, tname, 'rank', rk))
print("sites", len(SITE), "bad:", len(bad_s), bad_s[:3])
bad_p = []
for (k, k2, w) in PIN:
    ty, rk = divmod(k, 2); L, j = divmod(k2, 6); s = site_by_rank(TY[ty], rk)
    pin = "ABCD"[L] + str(j + 1)
    if s is None or spw(s, pin) != WIRE.get(w): bad_p.append((TY[ty], rk, pin, WIRE.get(w), spw(s, pin)))
print("LUT pins", len(PIN), "bad:", len(bad_p), bad_p[:3])
bad_q = []
for (k, k2, w) in PIN2:
    ty, rk = divmod(k, 2); s = site_by_rank(TY[ty], rk); pin = ['AX', 'BX', 'CX', 'CIN'][k2]
    if s is None or spw(s, pin) != WIRE.get(w): bad_q.append((TY[ty], rk, pin, WIRE.get(w), spw(s, pin)))
print("select/CIN pins", len(PIN2), "bad:", len(bad_q), bad_q[:3])
idx = {}
for r in conn:
    idx.setdefault((r['tile_types'][0], r['tile_types'][1], r['grid_deltas'][0], r['grid_deltas'][1]), set()).update(tuple(p) for p in r['wire_pairs'])
bad_r = []
for i, (t1, t2, dxp, dxn, dyp, dyn) in RULE.items():
    key = (TY.get(t1), TY.get(t2), dxp - dxn, dyp - dyn)
    for (k, w1, w2) in PAIR.get(i, []):
        if key not in idx or (WIRE.get(w1), WIRE.get(w2)) not in idx[key]: bad_r.append((i, key, WIRE.get(w1), WIRE.get(w2)))
print("extra rules (D2)", len(RULE), "pairs", sum(len(v) for v in PAIR.values()), "not in tileconn:", len(bad_r), bad_r[:3])
print("VERDICT", "CONTAINED" if not (bad_s or bad_p or bad_q or bad_r) else "NOT CONTAINED")
