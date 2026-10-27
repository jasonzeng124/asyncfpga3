# Independent extraction: yosys JSON (own synthesis) vs Cells.lean (regex parse).
import json, re, sys, glob, os
jd, lean = sys.argv[1], sys.argv[2]
L = open(lean).read()
defs = re.split(r'\ndef ', L)[1:]
leand = {}
for d in defs:
    name = d.split()[0]
    cells = re.findall(r'\{ name := "([^"]*)", kind := \.(\w+)(?: (\d+))?, init := (0x[0-9A-Fa-f]+|\d+), keep := (\w+),\s*conn := \[(.*?)\] \}', d, re.S)
    out = {}
    for n, k, w, init, keep, conn in cells:
        cs = dict((p, v) for p, v in re.findall(r'\(\.(\w+), \.([^)]*)\)', conn))
        out[n] = (k+(w or ''), int(init, 0), cs)
    ins = re.search(r'inputs := \[(.*?)\]\n', d).group(1)
    outs = re.search(r'outputs := \[(.*?)\]\n', d).group(1)
    leand[name] = (out, ins, outs)
bad = 0
for f in sorted(glob.glob(jd+'/*.json')):
    name = os.path.basename(f)[:-5]
    J = json.load(open(f))
    (mn, m), = [(k, v) for k, v in J['modules'].items()]
    lc, ins, outs = leand[name]
    jc = {}
    for cn, c in m['cells'].items():
        t = c['type']
        kind = {'IBUF':'ibuf','OBUF':'obuf'}.get(t)
        if t.startswith('LUT'): kind = 'lut'+t[3:]
        if kind is None: kind = t
        init = int(c['parameters'].get('INIT', '0'), 2) if 'INIT' in c['parameters'] else 0
        cs = {}
        for p, bits in c['connections'].items():
            b = bits[0]
            cs[p] = ('net %d' % b) if isinstance(b, int) else ('const ' + ('true' if b == '1' else 'false'))
        jc[cn] = (kind, init, cs)
    # ports
    jin = ', '.join('("%s", %d)' % (p, v['bits'][0]) for p, v in m['ports'].items() if v['direction']=='input')
    ok = (jc == lc)
    nl = len([1 for v in jc.values() if v[0].startswith('lut')])
    print(name, 'cells', len(jc), 'luts', nl, 'MATCH' if ok else 'MISMATCH')
    if not ok:
        bad += 1
        for k in set(jc)|set(lc):
            if jc.get(k) != lc.get(k): print('  ', k, jc.get(k), lc.get(k))
print('lean defs', sorted(leand)); print('BAD', bad)
