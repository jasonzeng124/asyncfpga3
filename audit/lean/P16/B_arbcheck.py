"""Auditor P16: independent check of the Bwit3 arbiter traces (B_arbdump.out).
Own LUT decoding from cells/rtl/bd_arb.v INIT strings (not formal's genF); recompute the
four combB checks, the winner table, C-element acks, and contention statistics."""
import re, sys
src = open('/root/wt-f14/cells/rtl/bd_arb.v').read()
# take INITs from the bd_arbiter module only
mod = src[src.index('module bd_arbiter'):]
inits = dict(re.findall(r"LUT6_2 #\(\.INIT\(64'h([0-9A-Fa-f_]+)\)\)\s*(\w+)", mod)[i][::-1] for i in range(2))
inits = {k: int(v.replace('_', ''), 16) for k, v in inits.items()}
print('INITs from bd_arb.v (bd_arbiter):', {k: hex(v) for k, v in inits.items()})
def lut6(init, ins):  # ins = [I0..I5]
    idx = sum(int(b) << i for i, b in enumerate(ins)); return (init >> idx) & 1
def o6(init, i5): return lut6(init, i5)  # I5 explicit in ins
def o5(init, ins5): return (init >> sum(int(b) << i for i, b in enumerate(ins5))) & 1
# ustate: I0=r1 I1=r2 I2=q I3=rst I4=A0 I5=1 ; O6=q O5=R0
def qF(r1, r2, q, rst, a0): return lut6(inits['ustate'], [r1, r2, q, rst, a0, 1])
def r0F(r1, r2, q, rst, a0): return o5(inits['ustate'], [r1, r2, q, rst, a0])
# ugrant: I0=r1 I1=r2 I2=q I3=0 I4=0 I5=1 ; O5=g1 O6=g2
def g1F(r1, r2, q): return o5(inits['ugrant'], [r1, r2, q, 0, 0])
def g2F(r1, r2, q): return lut6(inits['ugrant'], [r1, r2, q, 0, 0, 1])
# compare with formal's genF table dump
txt = open(sys.argv[1]).read()
lq = {}
for m in re.finditer(r"LUT rst=(\w+) qF=\[([^\]]*)\] r0F=\[([^\]]*)\]", txt):
    rst = m.group(1) == 'true'
    fq = [int(x) for x in m.group(2).split(',')]; fr = [int(x) for x in m.group(3).split(',')]
    mq = [qF(i & 1, i >> 1 & 1, i >> 2 & 1, int(rst), i >> 3 & 1) for i in range(16)]
    mr = [r0F(i & 1, i >> 1 & 1, i >> 2 & 1, int(rst), i >> 3 & 1) for i in range(16)]
    print(f'rst={rst}: qF genF==INIT {fq == mq}, r0F genF==INIT {fr == mr}')
m = re.search(r"g1\)=\[([^\]]*)\] gF true \(g2\)=\[([^\]]*)\]", txt)
fg1 = [int(x) for x in m.group(1).split(',')]; fg2 = [int(x) for x in m.group(2).split(',')]
print('g1 genF==INIT', fg1 == [g1F(i & 1, i >> 1 & 1, i >> 2 & 1) for i in range(8)],
      'g2 genF==INIT', fg2 == [g2F(i & 1, i >> 1 & 1, i >> 2 & 1) for i in range(8)])

def L(s): s = s.strip()[1:-1]; return [int(x) for x in s.split(',')] if s.strip() else []
def bv(l, t): return sum(1 for e in l if e < t) % 2  # pin read
def cl(l, t): return bv(l, t + 1)                     # node
NB = 768
arbs = []
for blk in re.split(r'\nARB ', txt)[1:]:
    head = blk.split('\n')[0]; n = int(head.split()[0])
    d = {k: v for k, v in re.findall(r'  (\w+)=(.*)', blk)}
    a = {k: L(d[k]) for k in ['xrq', 'yrq', 'xak', 'yak', 'zrq', 'zak', 'q', 'g1', 'g2']}
    a['tab'] = [x.strip() == 'true' for x in d['tab'][1:-1].split(',')] if d['tab'] != '[]' else []
    a['n'] = n; arbs.append(a)
allok = True
for a in arbs:
    n = a['n']; r1, r2, Q, A0 = a['xrq'], a['yrq'], a['q'], a['zak']
    bad = []
    for t in range(NB + 1):
        rst = 1 if t < 2 else 0
        p = (bv(r1, t), bv(r2, t), bv(Q, t))
        if cl(Q, t + 1) != qF(*p, rst, bv(A0, t)): bad.append(('q', t))
        if cl(a['zrq'], t + 1) != r0F(*p, rst, bv(A0, t)): bad.append(('R0', t))
        if cl(a['g1'], t + 1) != g1F(*p): bad.append(('g1', t))
        if cl(a['g2'], t + 1) != g2F(*p): bad.append(('g2', t))
    # winner table: per z.req rising edge (even index), is g2 high at that rise
    win = []
    for k in range(0, len(a['zrq']), 2):
        e = a['zrq'][k]
        win.append(bool(cl(a['g2'], e)))  # g2 node at the R0 node edge
    padded = win + ([False] if len(win) % 2 else [])
    # contention: intervals where both requests high (pin values)
    both = [t for t in range(NB) if bv(r1, t) and bv(r2, t)]
    def segs(ts):
        out = []
        for t in ts:
            if out and out[-1][1] == t - 1: out[-1][1] = t
            else: out.append([t, t])
        return out
    # nearest edge separations
    def mind(A, B): return min((abs(x - y) for x in A for y in B), default=None)
    a0f = a['zak'][1::2]
    reqedges = r1 + r2
    print(f"ARB {n}: combB(own INIT) violations {len(bad)} {bad[:4]}; tab {a['tab']} own {padded} eq {a['tab'] == padded}; "
          f"tokens z {len(a['zrq'])//2}; both-high segments {segs(both)}; "
          f"min|r1 edge - r2 edge| {mind(r1, r2)}; min|req edge - A0 fall| {mind(reqedges, a0f)}; "
          f"min|req rise - other req fall| {mind(r1[0::2], r2[1::2])},{mind(r2[0::2], r1[1::2])}")
    allok &= not bad and a['tab'] == padded
print('ALL OK' if allok else 'MISMATCH')

# --- appended: C-element ack semantics and double-ack check on the channel traces ---
print('ack checks (channel level):')
for a in arbs:
    n = a['n']; xa, ya, g1, g2, A0 = a['xak'], a['yak'], a['g1'], a['g2'], a['zak']
    both = [t for t in range(NB) if bv(xa, t) and bv(ya, t)]
    # ua = C(g, A0): an ack edge to v needs g and A0 both at v shortly before (within 4 ticks)
    def cel_ok(ak, g):
        bad = []
        for k, e in enumerate(ak):
            v = 1 if k % 2 == 0 else 0
            if not any(cl(g, e - d) == v and bv(A0, e - d + 1) == v for d in range(1, 5)): bad.append(e)
        return bad
    print(f"  ARB {n}: x.ack&y.ack both high at {len(both)} ticks; x.ack edges w/o C(g1,A0) support {cel_ok(xa, g1)}; "
          f"y.ack edges w/o C(g2,A0) support {cel_ok(ya, g2)}")

# --- appended: rival request edges vs the A0 fall that reopens q (bd_arb.v's runt condition) ---
print('rival-request edge vs A0-fall distance (ticks), per served token:')
for a in arbs:
    if not a['zrq']: continue
    out = []
    for k in range(0, len(a['zak']), 2):
        if k + 1 >= len(a['zak']): break
        fall = a['zak'][k + 1]; won2 = a['tab'][k // 2] if k // 2 < len(a['tab']) else False
        rival = a['xrq'] if won2 else a['yrq']
        d = min((abs(fall - e) for e in rival), default=None)
        out.append((('y' if won2 else 'x') + ' won', fall, d))
    print(f"  ARB {a['n']}: {out}")
