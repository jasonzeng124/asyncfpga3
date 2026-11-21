"""Check tb_late runs against GLSResolveGen.late_runt (and GLSResolve.follow_lost / out_runt).
Mux times: b's edges + 50 (A2 arc). L = 200. Only the resolver's printed decisions are read."""
import re, sys, os
L = int(os.environ.get("CHK_L", "200"))   # negative control: CHK_L=210 must mismatch
stats, bad = {}, 0
for f in sys.argv[1:]:
    log = open(f).read().splitlines()
    hd = [l for l in log if l.startswith('LATE')][0]
    tb, w, w2 = (int(x) for x in re.search(r'tb=(\d+) w=(\d+) w2=(\d+)', hd).groups())
    t0 = tb + 50; t1 = t0 + w + 1
    dec = []
    for l in log:
        if 'META' in l or 'RUNT' in l:
            t = int(re.search(r't=(\d+)', l).group(1)); p = int(re.search(r'runt=(\d+)', l).group(1))
            if 'rejected' in l: dec.append((t, p, 'reject', 0))
            else:
                rv, ch = re.search(r'runt_val=(.) -> (.) after (\d+)', l).groups()[:2]
                trp = int(re.search(r'after (\d+)', l).group(1))
                dec.append((t, p, 'commit' if rv == ch else 'back', trp))
    q, last = [], None
    for l in log:
        m = re.match(r'(\d+) q=(.)', l)
        if m and int(m.group(1)) >= tb and m.group(2) != last:
            q.append((int(m.group(1)), m.group(2))); last = m.group(2)
    if not dec:
        bad += 1; stats['no_decision'] = stats.get('no_decision', 0) + 1
        print('MISMATCH', f, 'no decision printed, q edges', q[:6]); continue
    d1 = dec[0]; ok = d1[0] == t0 + w and d1[1] == w
    if d1[2] == 'commit':
        case = 'first_commit'; exp = [(t0, '1'), (t0 + w, '0')] + ([(t0 + w + d1[3], '1')] if d1[3] else [])
        if not d1[3]: exp = [(t0, '1')]
    else:
        I = t0 + w + d1[3] + L + 1
        if t1 + w2 <= I:
            case = 'follow_lost'; exp = [(t0, '1'), (t0 + w, '0')]
        elif I < t1 + w2 < I + L:
            case = 'late_runt'; e = t1 + w2
            d2 = dec[1]; ok = ok and d2[0] == e and d2[1] == e - I
            exp = [(t0, '1'), (t0 + w, '0'), (I, '1'), (e, '0')]
            if d2[2] == 'commit': exp = exp + [(e + d2[3], '1')] if d2[3] else exp[:3]
            case += '_' + d2[2]
        else:
            case = 'late_wide'; exp = [(t0, '1'), (t0 + w, '0'), (I, '1')]   # not a theorem here
    ok = ok and q == exp
    stats[case] = stats.get(case, 0) + 1
    if not ok: bad += 1; print('MISMATCH', f, case, dec, q, exp)
print('runs checked:', len(sys.argv) - 1, 'cases:', stats, 'mismatches:', bad)
