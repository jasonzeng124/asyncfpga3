#!/usr/bin/env python3
"""check_env.py -- UNTRUSTED (lead, 2026-10-31): evaluate ArbEnv's window fields (Events9ArbB1.ArbEnv) on a GLS event
log, exactly as the Lean states them for a fixed-delay behaviour, for all four readers (g1, g2, s1, s2) of every
arbiter.   python3 -I check_env.py EVLOG INFO.json XAN.txt T_AFTER
EVLOG: the EV lines of a run with gen_evmon.py's monitor; INFO.json: its delay file; XAN.txt: xarbnet's bands of the
same route and corner (slow); T_AFTER: only events after this time count (rig reset release).
Fields (per reader with request s, literal e = q (g1, s1) or !q (g2, s2), ustate request delay DQ, A0 delay DA,
bands lo/hi Dr, lo/hi Dq; the R0 readers' bands are xarbnet's R0 bands minus 2, as in ArbEdgeS):
  nore : each flip of e away at tau  -> s low on [tau - DQ, tau + hiDq + 2 - loDr)
  rise : each rise of s at sigma     -> every u in [sigma + loDr - hiDq, sigma + hiDr + 2 - loDq) with e(u) is Settled
  flip : each flip of e toward at tau -> every u in [tau, tau + hiDq + 2 - loDq) is Settled
  C    : each fall of s at sigma      -> A0 high on [sigma + Dr - Dq - DA, + 2) (reader point delays Dr, Dq)
Settled u = A0 read low at u (A0 at u - DA) and q constant from u while that read stays low.
Negative controls: CTRL_DA=d adds d to DA (A0 read at the wrong time), CTRL_E=e widens the nore/rise/flip windows."""
import sys, os, json, re, bisect, collections
CDA = int(os.environ.get("CTRL_DA", "0")); CE = int(os.environ.get("CTRL_E", "0"))   # negative controls
log, infof, xanf, tafter = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4])
info = json.load(open(infof))
B = {}
for ln in open(xanf):
    m = re.search(r"arbiter (\S+)\.ustate\$LUT6: ArbOK \w+; K \d+, ctl lo \d+; Dq g1/g2/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\)/\((\d+), (\d+)\), Dr1 g1/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\), Dr2 g2/R0 \((\d+), (\d+)\)/\((\d+), (\d+)\)", ln)
    if m:
        v = list(map(int, m.groups()[1:]))
        B[m.group(1)] = dict(g1=((v[6], v[7]), (v[0], v[1])), g2=((v[10], v[11]), (v[2], v[3])),
                             s1=((v[8] - 2, v[9] - 2), (v[4] - 2, v[5] - 2)), s2=((v[12] - 2, v[13] - 2), (v[4] - 2, v[5] - 2)))
ev = collections.defaultdict(list)
for ln in open(log):
    if ln.startswith("EV "):
        _, t, tag, k, val = ln.split()
        ev[(tag, k)].append((int(t), 1 if val == "1" else (0 if val == "0" else None)))
class Sig:
    def __init__(s, ch): s.t = [t for t, _ in ch]; s.v = [v for _, v in ch]
    def at(s, t):
        i = bisect.bisect_right(s.t, t) - 1
        return s.v[i] if i >= 0 else None
    def edges(s, frm, to):   # (t, old, new) with frm <= t
        return [(s.t[i], s.v[i - 1] if i else None, s.v[i]) for i in range(len(s.t)) if s.t[i] >= frm]
    def runs(s, val, lo, hi):   # maximal intervals [a, b) within [lo, hi) where value == val
        out = []; cur = None
        pts = sorted(set([lo] + [t for t in s.t if lo < t < hi]))
        for k, p in enumerate(pts):
            nxt = pts[k + 1] if k + 1 < len(pts) else hi
            if s.at(p) == val: out.append((p, nxt))
        m = []
        for a, b in out:
            if m and m[-1][1] == a: m[-1] = (m[-1][0], b)
            else: m.append((a, b))
        return m
def shifted(sig, d):  # read through a fixed delay d
    return Sig([(t + d, v) for t, v in zip(sig.t, sig.v)])
tot = collections.Counter(); bad = collections.Counter(); ex = {}
for name, I in sorted(info.items()):
    tag = name.split("udut.")[-1]
    if name not in B: continue
    q = Sig(ev[(tag, "q")]); A0 = Sig(ev[(tag, "A0")]); R = {1: Sig(ev[(tag, "r1")]), 2: Sig(ev[(tag, "r2")])}
    A0r = shifted(A0, I["DA"] + CDA)          # ustate's A0 read, as a function of ustate time
    end = max([tafter + 1] + q.t + A0r.t + R[1].t + R[2].t) + 10000
    # non-settled ustate times: A0 read not low, or before the last q change of the A0-read-low run
    nonset = [(a, b) for (a, b) in A0r.runs(1, tafter, end)] + [(a, b) for (a, b) in A0r.runs(None, tafter, end)]
    for (p, p2) in A0r.runs(0, tafter, end):
        ch = [t for t in q.t if p < t <= p2 - 1]
        if ch: nonset.append((p, max(ch)))
    def settled_all(lo, hi, cond=None):   # every u in [lo, hi) (with cond(u)) settled?
        for (a, b) in nonset:
            x, y = max(a, lo), min(b, hi)
            if x < y:
                if cond is None: return False
                for (c, d) in cond(x, y):
                    if c < d: return False
        return True
    for rd, (b, inv) in (("g1", (1, False)), ("g2", (2, True)), ("s1", (1, False)), ("s2", (2, True))):
        (loDr, hiDr), (loDq, hiDq) = B[name][rd]
        s = R[b]; DQ = I[f"DQ{b}"]; P = I["readers"][rd]
        ev_q = q.edges(tafter, end)
        away = [t for t, o, n in ev_q if o is not None and n is not None and ((o, n) == ((1, 0) if not inv else (0, 1)))]
        toward = [t for t, o, n in ev_q if o is not None and n is not None and ((o, n) == ((0, 1) if not inv else (1, 0)))]
        ev_s = s.edges(tafter, end)
        rises = [t for t, o, n in ev_s if (o, n) == (0, 1)]; falls = [t for t, o, n in ev_s if (o, n) == (1, 0)]
        e_true = (lambda x, y: q.runs(0 if inv else 1, x, y))
        for tau in away:
            tot[(rd, "nore")] += 1
            lo, hi = tau - DQ, tau + hiDq + 2 - loDr + CE
            if lo < hi and (s.runs(1, lo, hi) or s.runs(None, lo, hi)):
                bad[(rd, "nore")] += 1; ex.setdefault((rd, "nore"), (tag, tau))
        for sg in rises:
            tot[(rd, "rise")] += 1
            if not settled_all(sg + loDr - hiDq, sg + hiDr + 2 - loDq + CE, e_true):
                bad[(rd, "rise")] += 1; ex.setdefault((rd, "rise"), (tag, sg))
        for tau in toward:
            tot[(rd, "flip")] += 1
            if not settled_all(tau, tau + hiDq + 2 - loDq + CE):
                bad[(rd, "flip")] += 1; ex.setdefault((rd, "flip"), (tag, tau))
        for sg in falls:
            tot[(rd, "C")] += 1
            lo = sg + P["Dr"] - P["Dq"] - I["DA"] - CDA
            if A0.runs(0, lo, lo + 2) or A0.runs(None, lo, lo + 2):
                bad[(rd, "C")] += 1; ex.setdefault((rd, "C"), (tag, sg))
for k in sorted(tot):
    print(f"{k[0]} {k[1]}: {tot[k]} events, {bad[k]} violations" + (f" (first: {ex[k]})" if bad[k] else ""))
