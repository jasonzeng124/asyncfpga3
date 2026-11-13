# T90: for each (routed.json, BEL) given, print the LUT cell's INIT, its pin->net map and whether its output is constant
# given that pins on GND/VCC nets take those values. usage: constlut.py ROUTED.json SLICE/BEL[:O5|O6] ...
import json, sys, itertools
J = json.load(open(sys.argv[1])); m = J['modules'][next(iter(J['modules']))] if 'modules' in J else J
cells = m['cells']; nets = {}
for n, d in m['netnames'].items():
    for b in d['bits']: nets.setdefault(b, n)
for arg in sys.argv[2:]:
    bel, _, out = arg.partition(':')
    hits = [(c, d) for c, d in cells.items() if d.get('attributes', {}).get('NEXTPNR_BEL', '') == bel]
    for c, d in hits:
        p = d.get('parameters', {}); init = p.get('INIT', '?'); conn = d['connections']
        pins = {k: nets.get(v[0], v[0]) if v else None for k, v in conn.items()}
        print(arg, d['type'], c[:90]); print('   INIT', init, ' ports', {k: (str(v)[:50]) for k, v in pins.items()})
        print('   attrs', {k: v for k, v in d.get('attributes', {}).items() if k.startswith('X_ORIG')})
        if init != '?' and d['type'] in ('SLICE_LUTX',):
            bits = init if set(init) <= {'0', '1'} else bin(int(init, 2 if set(init) <= {'0','1'} else 16))[2:]
            L = len(bits); val = [int(b) for b in bits[::-1]]  # LSB = index 0
            ins = [k for k in ('A1', 'A2', 'A3', 'A4', 'A5', 'A6') if k in pins]
            fixed = {k: (0 if pins[k] and 'GND' in pins[k] else 1 if pins[k] and 'VCC' in pins[k] else None) for k in ins}
            free = [k for k in ins if fixed[k] is None]
            outs = set()
            for asg in itertools.product([0, 1], repeat=len(free)):
                a = dict(zip(free, asg)); idx = 0
                for i, k in enumerate(ins):
                    v = fixed[k] if fixed[k] is not None else a[k]
                    idx |= v << i
                if idx < L: outs.add(val[idx])
            print('   free inputs', free, ' output values reachable (6-input index, pins A1..A6 = bits 0..5)', outs)
