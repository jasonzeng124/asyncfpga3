#!/usr/bin/env python3
"""Shard C (UNTRUSTED): path-targeted adversary for one C-element race "c falls before its input returns".
Iterates simadv.py: in the current run, for every fall of c (C-element node, both inputs low), the next rise of
either input x/y; take the tightest such race, trace (transport) the cause chain of c's fall and of the input's
rise back to their latest common event A, put every arc on A -> c at the slow end ((1+k) FAST_MAX) and every
arc on A -> input rise (and c's pin reading it) at the fast end ((1-k) FAST_MIN); everything else mid-window.
Repeat until the result is wrong or nothing new is added.
usage: adv.py NET BND P C X Y XPIN YPIN [pairs...]   (kappa = P/25, corner 0)"""
import json, subprocess, sys, os
NET, BND, P, C, X, Y, XP, YP = sys.argv[1:9]
pairs = sys.argv[9:] or ["1071,462"]
P = int(P); XP = int(XP); YP = int(YP)
W = os.environ.get("ADVW", "/tmp")
tag = os.environ.get("ADVTAG", "adv")
cls = {"S": [], "F": []}
seen = set()
names = json.load(open(NET))["nodes"]
for it in range(int(os.environ.get("ADVIT", "12"))):
    cf = "%s/%s_c%d.json" % (W, tag, it); json.dump(cls, open(cf, "w"))
    wf = "%s/%s_w%d.json" % (W, tag, it)
    cmd = ["python3", os.path.join(os.path.dirname(os.path.abspath(__file__)), "simadv.py"), NET, BND, "--pairs", *pairs,
           "--corner", "0", "--kappa", str(P / 25), "--classes", cf, "--data0", "--full", "--R", "400000", "--su", "1000",
           "--datachange", "broad", "--nextreq", "seq", "--tmax", os.environ.get("ADVTMAX", "3000000"),
           "--why", wf, "--whynodes", C, X, Y]
    if os.environ.get("ADVDUMP") : cmd += ["--dump", "%s/%s_d%d.json" % (W, tag, it)]
    r = subprocess.run(cmd, capture_output=True, text=True)
    res = [l for l in r.stdout.splitlines() if l.startswith("RESULT")]
    simline = [l for l in r.stderr.splitlines() if l.startswith("sim:")][-1:]
    print("iter %d: |S| %d |F| %d  %s %s" % (it, len(cls["S"]), len(cls["F"]), res, simline), flush=True)
    if not res or "MISMATCH" in res[0]:
        print("FAIL FOUND at iter", it); break
    WY = json.load(open(wf))
    rises = {k: [(t, ch) for t, v, ch in WY[k] if v] for k in (X, Y)}
    best = None
    cid = names.index(C)
    for t, v, ch in WY[C]:
        if v: continue
        for k, pin in ((X, XP), (Y, YP)):
            nxt = [(tr, chr_) for tr, chr_ in rises[k] if tr > t and not any(n == cid and tt == t for n, tt, p in chr_)]
            if nxt:
                tr, chr_ = nxt[0]
                m = tr - t
                if best is None or m < best[0]: best = (m, t, ch, k, pin, tr, chr_)
    if best is None: print("no race"); break
    m, t, ch, k, pin, tr, chr_ = best
    sc = {(n, tt): i for i, (n, tt, p) in enumerate(ch)}
    A = None
    for j, (n, tt, p) in enumerate(chr_):
        if (n, tt) in sc: A = (sc[(n, tt)], j); break
    if A is None: print("no common ancestor; margin", m); break
    new = 0
    for (n, tt, p) in ch[:A[0]]:
        if p >= 0 and (n, p) not in seen: seen.add((n, p)); cls["S"].append([names[n], p]); new += 1
    for (n, tt, p) in chr_[:A[1]]:
        if p >= 0 and (n, p) not in seen: seen.add((n, p)); cls["F"].append([names[n], p]); new += 1
    if (C, pin) not in seen: seen.add((C, pin)); cls["F"].append([C, pin]); new += 1
    print("  race: c falls %d, %s rises %d (margin %d); A = %s@%d; chain lens %d / %d; new arcs %d" %
          (t, k, tr, m, names[ch[A[0]][0]], ch[A[0]][1], A[0], A[1], new), flush=True)
    if new == 0: print("fixpoint"); break
