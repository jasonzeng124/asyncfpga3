#!/usr/bin/env python3
"""C-8x4: the SAMPLED channels of gcd_hw (rows needed for the data field), from C-8x2's
classes.tsv. A channel is sampled iff its consumer captures the bus: a latch D with data pins
(not a W=0 control stage), a steer / mux / 3-input-mux select LUT, or the environment reading
out0 (chan 416). Everything else is a ghost (combinational consumer, sink, W=0 stage).
Prints the Lean list `sampIds` and a per-producer-kind summary.
Run from formal/lean:  python3 Wip/C8x4/sampled.py
"""
import csv, collections, os
here = os.path.dirname(os.path.abspath(__file__))
rows = list(csv.reader(open(os.path.join(here, '..', 'C8x2', 'classes.tsv')), delimiter='\t'))[1:]
def sampled(r):
    return (('latch-D' in r[7] and 'W=0' not in r[8]) or 'select' in r[7] or r[0] == '416')
samp = [int(r[0]) for r in rows if sampled(r)]
print('sampIds (%d):' % len(samp))
print('[' + ', '.join(map(str, samp)) + ']')
print('by producer kind:', dict(collections.Counter(rows[c][1] for c in samp)))
print('by row:', dict(collections.Counter(rows[c][8] for c in samp)))
ghost = [r for r in rows if not sampled(r)]
print('ghosts: %d; by consumer:' % len(ghost), dict(collections.Counter(r[7] for r in ghost)))
