#!/usr/bin/env python3
"""constsinks.py ROUTED.json [FASM] -- every sink of nextpnr's constant nets ($PACKER_GND_NET / $PACKER_VCC_NET)
on a slice bel, and whether the net's ROUTING reaches that sink's site wire.

Sink site wire per bel pin (xc7 SLICEL/SLICEM, nextpnr-xilinx chipdb names):
  F7AMUX/S0 -> AX, F7BMUX/S0 -> CX, F8MUX/S0 -> BX            (the F7/F8 select is the slice bypass pin)
  xFF/D     -> xFFMUX_OUT,  x5FF/D -> x5FFMUX_OUT              (the FF's D comes out of its input mux)
  xFF/SR, CE                                                   (SRUSEDMUX / CEUSEDMUX: constants are not routed)
  xnLUT/Ak  -> the LUT input site wire (after fixupRouting the port is the TILE pin; the site wire is not
               recorded in the JSON, so a LUT sink is 'routed' iff the net reaches a site wire xk' of that LUT)
Prints one line per unrouted non-LUT sink, and counts.  With FASM, also says whether the FASM has the slice
bypass pin / FFMUX feature for that sink."""
import json, re, sys, collections
j = json.load(open(sys.argv[1]))
m = j['modules']['top']
cells = m['cells']
fasm = None
if len(sys.argv) > 2:
    fasm = set(l.split('=')[0].strip() for l in open(sys.argv[2]) if l.strip() and not l.startswith('#'))
nets = {}
for nn, nd in m['netnames'].items():
    nets.setdefault(nd['bits'][0], nn) if len(nd['bits']) == 1 else None
const_bits = {}
for nn, nd in m['netnames'].items():
    if nn in ('$PACKER_GND_NET', '$PACKER_VCC_NET'):
        const_bits[nd['bits'][0]] = (nn, nd)
wires = {}
for b, (nn, nd) in const_bits.items():
    t = nd['attributes'].get('ROUTING', '').split(';')
    wires[nn] = set(t[i] for i in range(0, len(t) - 2, 3))
cnt = collections.Counter()
rows = []
for cn, c in cells.items():
    belname = c.get('attributes', {}).get('NEXTPNR_BEL', '')
    if not belname.startswith('SLICE_'):
        continue
    site, bel = belname.split('/')
    for p, bl in c['connections'].items():
        if c['port_directions'].get(p) != 'input' or not bl or bl[0] not in const_bits:
            continue
        nn = const_bits[bl[0]][0]
        v = 1 if nn.endswith('VCC_NET') else 0
        sw = None
        if re.match(r'F7[AB]MUX$', bel) and p == 'S0':
            sw = {'F7AMUX': 'AX', 'F7BMUX': 'CX'}[bel]
        elif bel == 'F8MUX' and p == 'S0':
            sw = 'BX'
        elif re.match(r'[A-D]5?FF$', bel) and p == 'D':
            sw = bel + 'MUX_OUT'
        elif re.match(r'[A-D][56]LUT$', bel):
            kind = 'LUT/' + p
            routed = any(w.startswith('SITEWIRE/%s/%s' % (site, bel[0])) and re.match(r'.*/[A-D][1-6]$', w)
                         for w in wires[nn])  # coarse: any input of that LUT position on this net
            cnt[('LUT pin', v, 'some LUT input of this position on the net' if routed else 'no input of this LUT position routed')] += 1
            continue
        else:
            cnt[('other %s/%s' % (re.sub(r'[A-D]', 'x', bel), p), v, 'not checked')] += 1
            continue
        full = 'SITEWIRE/%s/%s' % (site, sw)
        routed = full in wires[nn]
        cnt[('%s/%s' % (re.sub(r'^[A-D]', 'x', bel), p), v, 'routed' if routed else 'UNROUTED')] += 1
        if not routed:
            rows.append('UNROUTED %s=%d %s/%s (%s) cell %s' % (nn, v, belname, p, sw, cn[:90]))
for r in sorted(rows):
    print(r)
for k, n in sorted(cnt.items(), key=str):
    print('%6d  %s' % (n, ' | '.join(str(x) for x in k)))
