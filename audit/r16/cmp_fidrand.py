# compare iverilog end-of-step outputs with the Lean formula
#   O(t) = F(k -> A_k(t - D_k)),  D_k = max(T_k + off_k - 1, 0) + 1,  A_k(s<0) = A_k(0)
# usage: cmp_fidrand.py stim.json log LV
import sys, json, collections
st = json.load(open(sys.argv[1])); lv = int(sys.argv[3]); END = st['END']
def off6(k): return [(5*lv)//2, (3*lv)//2, lv//2, -(lv//2), -((3*lv)//2), -((5*lv)//2)][k]
def off5(k): return [2*lv, lv, 0, -lv, -2*lv][k]
def pd(T, o): return max(T + o - 1, 0) + 1
def sig(ts):   # end-of-step value at integer time s (toggle list)
    import bisect
    return lambda s: bisect.bisect_right(ts, max(s, 0)) % 2 == 1
obs = collections.defaultdict(list)
for l in open(sys.argv[2]):
    p = l.split()
    if p and p[0] == 'O': obs[(int(p[1]), p[2])].append((int(p[4]), p[3]))
def eos(evs):  # end-of-step value function from observed change list (last change in a step wins)
    d = {}
    for t, v in evs: d[t] = v
    ts = sorted(d)
    import bisect
    def f(s):
        i = bisect.bisect_right(ts, s) - 1
        return d[ts[i]] if i >= 0 else 'z'
    return f, ts
bad = 0; checked = 0; xwin_ok = 0; xwin_n = 0
for i, c in enumerate(st['cells']):
    A = [sig(w) for w in c['w']]
    outs = []
    if c['kind'] == 'lut':
        D6 = [pd(c['T6'][k], off6(k)) for k in range(6)]
        D5 = [pd(c['T5'][k], off5(k)) for k in range(5)]
        I = c['INIT']
        outs.append(('6', D6, lambda a: (I >> sum(a[k] << k for k in range(6))) & 1))
        outs.append(('5', D5, lambda a: (I >> sum(a[k] << k for k in range(5))) & 1))
    else:
        D = [pd(c['T'][k], 0) for k in range(3)]
        outs.append(('6', D, lambda a: a[1] if a[2] else a[0]))
    for o, D, F in outs:
        f, ts = eos(obs[(i, o)])
        mx = max(D)
        # X window: Verilog output must be x before the last copy's first update
        xwin_n += 1
        if all(f(s) in ('x', 'z') for s in range(0, mx - 1)): xwin_ok += 1
        for t in range(mx, END):
            e = str(int(F([int(A[k](t - D[k])) for k in range(len(D))])))
            checked += 1
            if f(t) != e:
                bad += 1
                if bad < 10: print('MISMATCH cell', i, c['kind'], 'O' + o, 't', t, 'iv', f(t), 'lean', e, 'D', D)
print(f'LV={lv} cells={len(st["cells"])} outputs={xwin_n} samples={checked} mismatches={bad} xwindow_ok={xwin_ok}/{xwin_n}')
