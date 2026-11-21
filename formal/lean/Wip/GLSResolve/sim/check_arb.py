"""Check tb_arb runs against GLSResolveGen (arb_near_tie, arb_double_ack, arb_gap_closed).
Expected edges come from the Lean closed forms; from the log only the resolver's printed
decisions (outcome, runt width, trp) and the A0 net's rise (the environment) are taken.
Delays of tb_arb: ustate sees r1 at TB+50; D1 = D2 = 300 (q wire 100 + ugrant arc 50 +
grant wire 100 + ua arc 50); A0 at every LUT pin = A0 + 150; ua loop L2 = 200."""
import re, sys
def edges(log, name):
    out, last = [], None
    for l in log:
        m = re.match(r'(\d+) .*\b%s=(.)' % name, l)
        if m:
            v = m.group(2)
            if v != last: out.append((int(m.group(1)), v)); last = v
    return out
def at(ev, t):
    v = None
    for (u, x) in ev:
        if u <= t: v = x
    return v
stats, bad = {}, 0
for f in sys.argv[1:]:
    log = open(f).read().splitlines()
    tie = [l for l in log if l.startswith('TIE')][0]
    TB = int(re.search(r'tb=(\d+)', tie).group(1))
    T0 = TB + 50
    ml = [l for l in log if 'u_st' in l and ('META' in l or 'RUNT' in l) and int(re.search(r't=(\d+)', l).group(1)) > TB]
    if not ml:   # no decision printed (e.g. +META_OFF=1): every resolver form has <= 3 q edges
        q = [e for e in edges(log, 'q') if e[0] >= TB]
        if len(q) > 3: bad += 1; print('MISMATCH', f, 'no decision, q has', len(q), 'edges')
        stats['no_decision'] = stats.get('no_decision', 0) + 1
        continue
    m = ml[0]
    w = int(re.search(r'runt=(\d+)', m).group(1))
    if 'rejected' in m: out, trp = 'reject', 0
    else:
        trp = int(re.search(r'after (\d+)', m).group(1))
        out = 'commit' if re.search(r'runt_val=(.) -> (.)', m).group(1) == re.search(r'-> (.)', m).group(1) else 'back'
    q = [e for e in edges(log, 'q') if e[0] >= TB]
    exp = [(T0, '1'), (T0 + w, '0')] + ([(T0 + w + trp, '1')] if out == 'commit' else [])
    if out == 'commit' and trp == 0: exp = [(T0, '1')]
    ok = q == exp
    A0 = [e for e in edges(log, 'A0') if e[0] > TB and e[1] == '1']
    sA = A0[0][0] + 150
    A1, A2 = at(edges(log, 'A1'), 10**9), at(edges(log, 'A2'), 10**9)
    case = out
    if sA < T0 + w + 300:
        case = out + '_A0_before_grant'   # A0 overlaps the first runt at ua1/ua2: q checked only
        e1 = e2 = None
    elif out == 'commit':
        G1 = T0 + w + trp + 300
        e1 = '1'
        if T0 + w + 300 <= sA and sA + 200 <= G1: case, e2 = 'double_ack', '1'   # arb_double_ack
        elif G1 <= sA: case, e2 = 'gap_closed', '0'                              # arb_gap_closed
        else:                                                                    # ua2 runt (grun_runt_o)
            a2 = [l for l in log if 'u_a2' in l and ('META' in l or 'RUNT' in l)]
            w2 = int(re.search(r'runt=(\d+)', a2[0]).group(1))
            ok = ok and w2 == G1 - sA
            c2 = ('rejected' not in a2[0]) and re.search(r'runt_val=(.) -> (.)', a2[0]).group(1) == re.search(r'-> (.)', a2[0]).group(1)
            case, e2 = 'ua2_runt_' + ('commit' if c2 else 'nocommit'), ('1' if c2 else '0')
            # the ua2 runt is emitted on A2 in full: A2 = 1 on [sA, G1)
            ea2 = [e for e in edges(log, 'A2') if e[0] >= sA]
            ok = ok and ea2[:2] == [(sA, '1'), (G1, '0')]
    else:
        e1, e2 = '0', '1'   # client 2 keeps q = 0 (hand-derived, not a theorem here)
    if e1 is not None: ok = ok and A1 == e1 and A2 == e2
    stats[case] = stats.get(case, 0) + 1
    if not ok:
        bad += 1; print('MISMATCH', f, out, w, trp, 'q', q, 'exp', exp, 'sA', sA, 'A1', A1, 'A2', A2)
print('runs checked:', len(sys.argv) - 1, 'cases:', stats, 'mismatches:', bad)
