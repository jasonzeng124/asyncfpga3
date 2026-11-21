#!/usr/bin/env python3
"""cmp_routes.py A_DIR B_DIR TOP -- what differs between two nextpnr runs of one design (same input, same seed):
placement (every cell's NEXTPNR_BEL), cell parameters/attributes, per-net ROUTING, SDF lines, FASM lines."""
import json, sys, difflib, hashlib
A, B, T = sys.argv[1:4]
def md5(p): return hashlib.md5(open(p, 'rb').read()).hexdigest()[:8]
for ext in ('_routed.json', '.sdf', '.fasm'):
    pa, pb = '%s/%s%s' % (A, T, ext), '%s/%s%s' % (B, T, ext)
    print('%-14s %s %s %s' % (ext, md5(pa), md5(pb), 'IDENTICAL' if md5(pa) == md5(pb) else 'DIFFER'))
ja = json.load(open('%s/%s_routed.json' % (A, T)))['modules']['top']
jb = json.load(open('%s/%s_routed.json' % (B, T)))['modules']['top']
ca, cb = ja['cells'], jb['cells']
print('cells: %d / %d, same names: %s' % (len(ca), len(cb), set(ca) == set(cb)))
moved = [c for c in ca if c in cb and ca[c]['attributes'].get('NEXTPNR_BEL') != cb[c]['attributes'].get('NEXTPNR_BEL')]
print('placement: %d cells on a different bel' % len(moved))
pdiff = [c for c in ca if c in cb and ca[c].get('parameters') != cb[c].get('parameters')]
adiff = [c for c in ca if c in cb and ca[c].get('attributes') != cb[c].get('attributes')]
cdiff = [c for c in ca if c in cb and ca[c].get('connections') != cb[c].get('connections')]
print('cells with different parameters %d, attributes %d, connections %d' % (len(pdiff), len(adiff), len(cdiff)))
for c in (adiff + cdiff)[:6]:
    ka = {k: v for k, v in ca[c]['attributes'].items() if cb[c]['attributes'].get(k) != v}
    kb = {k: v for k, v in cb[c]['attributes'].items() if ca[c]['attributes'].get(k) != v}
    print('   %s %s: A %s | B %s' % (c[:70], ca[c]['attributes'].get('NEXTPNR_BEL'), ka, kb))
na, nb = ja['netnames'], jb['netnames']
rd = [n for n in na if n in nb and na[n].get('attributes', {}).get('ROUTING') != nb[n].get('attributes', {}).get('ROUTING')]
print('nets: %d / %d; ROUTING differs on %d: %s' % (len(na), len(nb), len(rd), rd[:8]))
for n in rd[:8]:
    ta = set(na[n]['attributes'].get('ROUTING', '').split(';')[0::3]); tb = set(nb[n]['attributes'].get('ROUTING', '').split(';')[0::3])
    print('   %s: wires only in A %d, only in B %d, common %d' % (n[:70], len(ta - tb), len(tb - ta), len(ta & tb)))
for ext in ('.sdf', '.fasm'):
    la = open('%s/%s%s' % (A, T, ext)).read().splitlines(); lb = open('%s/%s%s' % (B, T, ext)).read().splitlines()
    sa, sb = set(la), set(lb)
    print('%s lines only in A %d, only in B %d' % (ext, len(sa - sb), len(sb - sa)))
    for l in sorted(sa - sb)[:10]: print('   - ' + l.strip()[:200])
    for l in sorted(sb - sa)[:14]: print('   + ' + l.strip()[:200])
