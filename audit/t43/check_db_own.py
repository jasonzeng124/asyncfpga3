# T43: is every entry of formal A's trusted NodeMerge DB (FormalWit/NM/DB.lean, dumped by ExportDB.lean) a fact of prjxray-db?
# Soundness of NodeMerge needs D's relation to be CONTAINED in prjxray's (a subset is fine), so: every tile's name/type/x/y
# must equal tilegrid.json; every rule must be a tileconn.json rule (same types, same grid delta); every pair (w1, w2) must
# be one of that rule's wire_pairs.  usage: check_db_own.py DUMP TILEGRID TILECONN
import json, sys
dump, tg, tc = sys.argv[1:4]
TY, TILE, WIRE, RULE, PAIR = {}, {}, {}, {}, {}
for l in open(dump):
    f = l.split()
    if f[0] == 'TY': TY[int(f[1])] = f[2]
    elif f[0] == 'TILE': TILE[int(f[1])] = (f[2], int(f[3]), int(f[4]), int(f[5]))
    elif f[0] == 'WIRE': WIRE[int(f[1])] = f[2]
    elif f[0] == 'RULE': RULE[int(f[1])] = tuple(map(int, f[2:8]))
    elif f[0] == 'PAIR': PAIR.setdefault(int(f[1]), []).append((int(f[2]), int(f[3]), int(f[4])))
grid = json.load(open(tg)); conn = json.load(open(tc))
bad_t = [(i, t) for i, t in TILE.items() if t[0] not in grid or grid[t[0]]['type'] != TY.get(t[1]) or grid[t[0]]['grid_x'] != t[2] or grid[t[0]]['grid_y'] != t[3]]
print("tiles", len(TILE), "of", len(grid), "in tilegrid; mismatching:", len(bad_t), bad_t[:3])
# index prjxray rules by (types, delta) -> set of wire pairs (a type pair and delta can occur in several entries)
idx = {}
for r in conn:
    key = (r['tile_types'][0], r['tile_types'][1], r['grid_deltas'][0], r['grid_deltas'][1])
    idx.setdefault(key, set()).update(tuple(p) for p in r['wire_pairs'])
bad_r, bad_p, npairs, flipped = [], [], 0, 0
for i, (t1, t2, dxp, dxn, dyp, dyn) in RULE.items():
    key = (TY.get(t1), TY.get(t2), dxp - dxn, dyp - dyn)
    if key not in idx:
        if (key[1], key[0], -key[2], -key[3]) in idx: flipped += 1
        bad_r.append((i, key)); continue
    for (k, w1, w2) in PAIR.get(i, []):
        npairs += 1
        if (WIRE.get(w1), WIRE.get(w2)) not in idx[key]: bad_p.append((i, k, WIRE.get(w1), WIRE.get(w2), key))
print("rules", len(RULE), "not a tileconn (types, delta):", len(bad_r), "(of which present only reversed:", flipped, ")", bad_r[:3])
print("pairs checked", npairs, "not among that rule's wire_pairs:", len(bad_p), bad_p[:3])
print("VERDICT", "CONTAINED" if not (bad_t or bad_r or bad_p) else "NOT CONTAINED")
