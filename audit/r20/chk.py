# audit r16: classify each copy's q trace (after TB) by the resolver decision it printed,
# and test: rejected/back runt emitted full swing; commit trp>0 -> two rising edges;
# output constant after decision+trp; final value.  Same-time edges collapsed (end-of-step).
import sys, re, collections
lines = open(sys.argv[1]).read().splitlines()
cfg = dict(re.findall(r'(\w+)=(\d+)', lines[0])); cfg = {k:int(v) for k,v in cfg.items()}
ev = collections.defaultdict(list); dec = {}; fin = {}
for l in lines:
    m = re.match(r'E (\d+) (\S) (\d+)', l)
    if m:
        g, v, t = int(m[1]), m[2], int(m[3])
        if t < cfg['TB']: continue
        e = ev[g]
        if e and e[-1][0] == t: e.pop()          # same-step: keep end-of-step value
        if e and e[-1][1] == v: continue
        if not e and v == '0': continue
        e.append((t, v)); continue
    m = re.match(r'RUNT tb_c2r\.c\[(\d+)\].* t=(\d+) runt=(\d+)', l)
    if m: dec.setdefault(int(m[1]), []).append(('reject', int(m[2]), 0)); continue
    m = re.match(r'META tb_c2r\.c\[(\d+)\].* t=(\d+) runt=(\d+).*runt_val=(\d) -> (\d) after (\d+)', l)
    if m:
        k = 'commit' if m[4] == m[5] else 'back'
        dec.setdefault(int(m[1]), []).append((k, int(m[2]), int(m[6]))); continue
    m = re.match(r'F (\d+) (\S)', l)
    if m: fin[int(m[1])] = m[2]
t0 = cfg['TB'] + cfg['TA']; w = cfg['W']
cnt = collections.Counter(); bad = 0
for g in sorted(fin):
    e = ev[g]; d = dec.get(g, [])
    if cfg['W2'] == 0:
        if not d: exp = [(t0, '1')]; k = 'wide'
        else:
            k, td, trp = d[0]
            if k == 'commit' and trp > 0: exp = [(t0,'1'), (t0+w,'0'), (t0+w+trp,'1')]
            elif k == 'commit': exp = [(t0,'1')]; k = 'commit0'
            else: exp = [(t0,'1'), (t0+w,'0')]
        ok = (e == exp) and len(d) <= 1
        cnt[k] += 1
        if not ok: bad += 1; print('MISMATCH', g, d, e, exp)
    else:
        cnt[(tuple(x[0] for x in d), fin[g])] += 1
        print('copy', g, 'dec', d, 'edges', e, 'final', fin[g])
print('CFG', cfg, 'counts', dict(cnt), 'mismatches', bad, 'finals', collections.Counter(fin.values()))
