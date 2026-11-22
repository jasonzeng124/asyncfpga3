#!/usr/bin/env python3
"""constpins_synth.py SYNTH.json -- cells in the post-synthesis netlist with a constant ("0"/"1") on a pin that
becomes a slice bypass pin: MUXF7/MUXF8 S, FD*/LD* D (and, for reference, CE/R/S/PRE/CLR)."""
import json, sys, collections
m = json.load(open(sys.argv[1]))['modules']
cnt = collections.Counter(); ex = collections.defaultdict(list)
for mn, md in m.items():
    for cn, c in md.get('cells', {}).items():
        t = c['type']
        for p, bits in c.get('connections', {}).items():
            if any(b in ('0', '1') for b in bits):
                if t in ('MUXF7', 'MUXF8') or (t.startswith('FD') or t.startswith('LD')):
                    k = (t, p, ''.join(str(b) for b in bits if b in ('0', '1')))
                    cnt[k] += 1
                    if len(ex[k]) < 3: ex[k].append('%s/%s' % (mn[:40], cn[:70]))
for k, n in sorted(cnt.items()):
    print('%5d %s %s=%s   e.g. %s' % (n, k[0], k[1], k[2], ex[k]))
