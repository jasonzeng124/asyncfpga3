"""Shard C (UNTRUSTED): event-structure local check for the latches-first machine, LATCH FLIPS AS EVENTS.
Events = every node flip of one recorded run (control fire, env move, latch flip in a closure).
Candidate order P (immediate causes), from a replay of the recorded run:
  non-latch event of v: v's previous event + the latest event (as of the step at which v last became enabled)
      of every node x in R_v = supp(v) (+ supp(c) for RT blockers c of v; env guard inputs for env nodes)
      that is SENSITIVE at that moment (flipping x alone makes v not enabled)        [default --cause sens]
      --cause all : every node of R_v (not only sensitive ones)
  latch event of L (in the closure of step i): L's previous event + the latest event (as of step i's own flip)
      of every node of supp(L) sensitive at that moment (flipping it alone makes L not excited)
Local check for node v, S_v = events of nodes in R_v + causes of v's events + causes of latch events in S_v.
  A latch event of S_v is "known" if all its causes are in S_v (its readiness is decidable locally), else "free".
  Local search from the empty ideal (over-approximates the projection of every reachable global ideal):
     moves: (1) add ALL known latch events whose causes are in J (a latch round), if any;
            (2) add any minimal free latch event;   (3) if no known latch event is ready: add any minimal non-latch event.
  At every visited local ideal J:
     latch v:     excited(v, state(J))  <=>  next event of v exists and its causes are in J
     non-latch v (only when no known latch event is ready = locally closed):
                  enabled(v, state(J)) <=> next event of v exists and its causes are in J
     enabled = excited and no RT blocker excited (control); env guard (+ out0 data == gcd for out0_ack rise).
usage: check2.py prep.txt init.txt events.txt a b rt.txt [--cause sens|all] [--maxfail N] [--cert FILE] [--witness]"""
import sys, collections, math, time, bisect, resource
sys.path.insert(0, "/tmp/claude-0/occ")
from net import Net
opts = sys.argv[1:]
args = []
skip = False
for k, a in enumerate(opts):
    if skip: skip = False; continue
    if a in ("--cause", "--maxfail", "--cert", "--extra-rt", "--only", "--witdir"): skip = True; continue
    if a.startswith("--"): continue
    args.append(a)
prep, initf, evf, A, B, rtf = args[:6]; A = int(A); B = int(B)
CAUSE = opts[opts.index("--cause") + 1] if "--cause" in opts else "sens"
MAXFAIL = int(opts[opts.index("--maxfail") + 1]) if "--maxfail" in opts else 30
CERT = opts[opts.index("--cert") + 1] if "--cert" in opts else None
WIT = "--witness" in opts
t0 = time.time()
N = Net(prep); init = [int(c) for c in open(initf).read().strip()]
isL = {g[0]: bool(g[4]) for g in N.stor}; sOf = N.storOf
byName = {N.names[g[0]]: g[0] for g in N.stor}
rtl = [l.split() for l in open(rtf) if l.strip()]
rt = [(byName[a], byName[b]) for a, b in rtl]
blockers = collections.defaultdict(list)
for c, b in rt: blockers[b].append(c)
want = math.gcd(A, B)
REQ, PACK, OACK = N.REQ, N.PACK, N.OACK
ENVN = {REQ, PACK, OACK}
def suppN(n):
    if n in sOf: return set(N.gsupp(sOf[n])) | {n}
    if n == REQ: return set().union(*[N.supp(x) for x in (REQ, N.AACK, N.BACK, N.SACK, PACK, N.OREQ, OACK)])
    if n == PACK: return {REQ, PACK}
    if n == OACK: return set().union(N.supp(N.OREQ), {OACK}, *[N.supp(x) for x in N.OD])
    raise Exception(n)
SUP = {}
def sup(n):
    if n not in SUP: SUP[n] = suppN(n)
    return SUP[n]
def Rset(v):
    r = set(sup(v))
    if v in sOf and not isL[v]:
        for b in blockers.get(v, ()): r |= sup(b)
    return r
# ---- events
steps = collections.OrderedDict()
for l in open(evf):
    if l.startswith("#"): continue
    n, m, r = map(int, l.split())
    assert r in (-1, 0), "multi-round closure in the recorded run: not handled"
    steps.setdefault(m, [[], []])[0 if r == -1 else 1].append(n)
steps = list(steps.values())
for o, la in steps: assert len(o) == 1
NS = len(steps)
evn = []; evstep = []  # event -> node, step
stepOwnEv = []; stepLamEv = []
for i, (o, la) in enumerate(steps):
    stepOwnEv.append(len(evn)); evn.append(o[0]); evstep.append(i)
    stepLamEv.append([])
    for l in la: stepLamEv[i].append(len(evn)); evn.append(l); evstep.append(i)
NE = len(evn)
evOf = collections.defaultdict(list)
for e, n in enumerate(evn): evOf[n].append(e)
# ---- enabledness
def nbits(val, nodes): return sum(val[x] << i for i, x in enumerate(nodes))
def enabled_full(val, v, nreq, noack):
    if v in sOf:
        ex = lambda s: N.ev(N.stor[sOf[s]]) != val[s]
        return ex(v) and not any(ex(c) for c in blockers.get(v, ()))
    if v == REQ:
        k = (nreq + 1) // 2; kout = (noack + 1) // 2
        if not val[REQ]: return bool(not val[N.AACK] and not val[N.BACK] and not val[N.SACK] and not val[PACK] and k < 1 and k <= kout and not val[N.OREQ] and not val[OACK])
        return bool(val[N.AACK] and val[N.BACK] and val[N.SACK] and val[PACK])
    if v == PACK: return val[REQ] != val[PACK]
    if v == OACK:
        if not val[OACK]: return bool(val[N.OREQ]) and nbits(val, N.OD) == want
        return not val[N.OREQ]
NONL = [g[0] for g in N.stor if not g[4]] + [REQ, PACK, OACK]
LATCHES = [g[0] for g in N.stor if g[4]]
# ---- replay: causes
N.val = list(init); val = N.val
lastEv = {}  # node -> latest event id so far
causes = [None] * NE
nreq = noack = 0
def sensitive(v, test, R):
    out = set()
    for x in R:
        if x == v: continue
        val[x] ^= 1; N.settle([x]); r = test(); val[x] ^= 1; N.settle([x])
        if not r: out.add(x)
    return out
def snapshot(v, R, test):
    S = R if CAUSE == "all" else sensitive(v, test, R)
    if v in sOf and not isL[v]: S = set(S) | set(blockers.get(v, ()))   # RT blockers' own latest events
    return {lastEv[x] for x in S if x in lastEv and x != v}
en = {}; pend = {}
for v in NONL:
    en[v] = enabled_full(val, v, 0, 0)
    if en[v]: pend[v] = snapshot(v, Rset(v), lambda: enabled_full(val, v, 0, 0))
for i in range(NS):
    u = steps[i][0][0]; e = stepOwnEv[i]
    assert en[u], ("replay: own node not enabled", i, N.names[u])
    c = set(pend[u])
    if u in lastEv: c.add(lastEv[u])
    causes[e] = c
    val[u] ^= 1; N.settle([u]); lastEv[u] = e
    for le in stepLamEv[i]:
        lam = evn[le]
        assert N.ev(N.stor[sOf[lam]]) != val[lam]
        c = snapshot(lam, sup(lam), lambda: N.ev(N.stor[sOf[lam]]) != val[lam])
        if lam in lastEv: c.add(lastEv[lam])
        causes[le] = c
    la = steps[i][1]
    for l in la: val[l] ^= 1
    if la: N.settle(la)
    for le in stepLamEv[i]: lastEv[evn[le]] = le
    if u == REQ: nreq += 1
    if u == OACK: noack += 1
    for v in NONL:
        e2 = enabled_full(val, v, nreq, noack)
        if e2 and not en[v]:
            pend[v] = snapshot(v, Rset(v), lambda: enabled_full(val, v, nreq, noack))
        en[v] = e2
    assert not any(N.ev(N.stor[sOf[l]]) != val[l] for l in steps[i][1])
anc = [0] * NE
for e in range(NE):
    a = 0
    for j in causes[e]: a |= anc[j] | (1 << j)
    anc[e] = a
ncause = sum(len(c) for c in causes)
print("events %d (non-latch %d, latch %d), cause edges %d, replay+order %.1fs" % (NE, NS, NE - NS, ncause, time.time() - t0), flush=True)
# ---- cone evaluation
CONE = {}
def cone_of(x):
    if x in CONE: return CONE[x]
    seen = set(); st = [x]; g = set()
    while st:
        y = st.pop()
        if y in seen: continue
        seen.add(y)
        if y in N.combOf: g.add(N.combOf[y]); st.extend(N.comb[N.combOf[y]][2])
    CONE[x] = g; return g
def gates_for(v):
    xs = []
    if v in sOf:
        xs = list(N.stor[sOf[v]][2])
        if not isL[v]:
            for c in blockers.get(v, ()): xs += N.stor[sOf[c]][2]
    elif v == REQ: xs = [N.AACK, N.BACK, N.SACK, N.OREQ]
    elif v == OACK: xs = [N.OREQ] + N.OD
    g = set()
    for x in xs: g |= cone_of(x)
    return sorted(g, key=lambda c: N.rank[N.comb[c][0]])
fails = []; totIdeals = 0; maxS = 0; maxIdeals = 0; worst = None; stats = []
def check_node(v):
    global totIdeals, maxS, maxIdeals, worst
    latch = isL.get(v, False)
    R = Rset(v)
    Sset = set()
    for n in R: Sset.update(evOf.get(n, ()))
    for e in evOf.get(v, ()): Sset |= causes[e]
    if "--lclose1" in opts:
        for e in list(Sset):
            if isL.get(evn[e], False): Sset |= causes[e]
    else:  # transitive: causes of latch events until non-latch events (every latch event of S_v is "known")
        st = [e for e in Sset if isL.get(evn[e], False)]
        while st:
            e = st.pop()
            for c in causes[e]:
                if c not in Sset:
                    Sset.add(c)
                    if isL.get(evn[c], False): st.append(c)
    S = sorted(Sset); li = {s: k for k, s in enumerate(S)}; nS = len(S)
    full = 0
    for s in S: full |= 1 << s
    def tolocal(a):
        m = 0
        while a:
            low = a & -a; j = low.bit_length() - 1; m |= 1 << li[j]; a ^= low
        return m
    pred = [tolocal(anc[s] & full) for s in S]
    isLat = [isL.get(evn[s], False) for s in S]
    known = [isLat[k] and causes[S[k]] <= Sset for k in range(nS)]
    cmask = [sum(1 << li[j] for j in causes[S[k]] if j in li) for k in range(nS)]
    knownL = [k for k in range(nS) if known[k]]
    freeL = [k for k in range(nS) if isLat[k] and not known[k]]
    nonL = [k for k in range(nS) if not isLat[k]]
    leaves = sorted(R); lk = {n: k for k, n in enumerate(leaves)}
    gates = gates_for(v)
    initvb = sum(init[n] << k for n, k in lk.items())
    fmask = [(1 << lk[evn[s]]) if evn[s] in lk else 0 for s in S]
    vev = [li[e] for e in evOf.get(v, ())]
    vcause = [cmask[k] for k in vev]
    reqmask = sum(1 << li[e] for e in evOf.get(REQ, ()) if e in li)
    oackmask = sum(1 << li[e] for e in evOf.get(OACK, ()) if e in li)
    memo = {}
    def values(vb):
        d = {n: (vb >> k) & 1 for n, k in lk.items()}
        for c in gates:
            g = N.comb[c]; a = 0
            for j, x in enumerate(g[2]):
                if d[x]: a |= 1 << j
            d[g[0]] = (g[3] >> a) & 1
        return d
    def exc(d, s):
        g = N.stor[sOf[s]]; a = 0
        for j, x in enumerate(g[2]):
            if d[x]: a |= 1 << j
        return ((g[3] >> a) & 1) != d[s]
    def enab(vb, J):
        key = (vb, bin(J & reqmask).count("1"), bin(J & oackmask).count("1"))
        if key in memo: return memo[key]
        d = values(vb)
        if latch: r = exc(d, v)
        elif v in sOf: r = exc(d, v) and not any(exc(d, c) for c in blockers.get(v, ()))
        else: r = enabled_full(d, v, key[1], key[2])
        memo[key] = r; return r
    seen = {0: initvb}; stack = [0]; nf = 0; nid = 0
    while stack:
        J = stack.pop(); vb = seen[J]; nid += 1
        kr = [k for k in knownL if not (J >> k) & 1 and (cmask[k] & ~J) == 0]
        closed = not kr
        if latch or closed:
            lhs = enab(vb, J)
            nxt = None
            for q, k in enumerate(vev):
                if not (J >> k) & 1: nxt = q; break
            rhs = nxt is not None and (vcause[nxt] & ~J) == 0
            if lhs != rhs:
                nf += 1
                if len(fails) < MAXFAIL:
                    miss = [S[q] for q in range(nS) if nxt is not None and (vcause[nxt] >> q) & 1 and not (J >> q) & 1]
                    fails.append(dict(node=N.names[v], latch=latch, lhs=lhs, next=(S[vev[nxt]] if nxt is not None else None),
                                      missing=["%d:%s" % (m, N.names[evn[m]]) for m in miss], J=[S[q] for q in range(nS) if (J >> q) & 1]))
        succ = []
        if kr:
            m = 0
            for k in kr: m |= 1 << k
            succ.append((m, kr))
        for k in freeL:
            if not (J >> k) & 1 and (pred[k] & ~J) == 0: succ.append((1 << k, [k]))
        if closed:
            for k in nonL:
                if not (J >> k) & 1 and (pred[k] & ~J) == 0: succ.append((1 << k, [k]))
        for m, ks in succ:
            J2 = J | m
            if J2 not in seen:
                x = vb
                for k in ks: x ^= fmask[k]
                seen[J2] = x; stack.append(J2)
    totIdeals += nid; maxS = max(maxS, nS)
    if nid > maxIdeals: maxIdeals = nid; worst = N.names[v]
    stats.append((N.names[v], nS, nid, nf, len(freeL)))
    return nf
nodes = [g[0] for g in N.stor] + [REQ, PACK, OACK]
if "--only" in opts:
    nodes = [n for n in nodes if N.names[n] in opts[opts.index("--only") + 1].split(",")]
totf = 0
for v in nodes: totf += check_node(v)
print("pair %d,%d: cause=%s RT orders %d; nodes checked %d, events %d, max |S_v| %d, local ideals visited %d (max %d at %s), FAILURES %d, %.1fs"
      % (A, B, CAUSE, len(rt), len(nodes), NE, maxS, totIdeals, maxIdeals, worst, totf, time.time() - t0))
print("  maxrss %d MB" % (resource.getrusage(resource.RUSAGE_SELF).ru_maxrss // 1024))
print("  largest:", sorted(stats, key=lambda s: -s[2])[:5])
nfree = sum(s[4] for s in stats); print("  free latch events (summed over nodes): %d" % nfree)
for f in fails: print("  FAIL", f["node"], "latch" if f["latch"] else "", "enabled" if f["lhs"] else "NOT enabled", "next", f["next"], "missing", f["missing"], "J", sorted(f["J"]) if "--only" in opts else sorted(f["J"])[-4:])
# ---- witnesses: replay the global down-closure of each failing local ideal on the real machine
if WIT:
    seenw = set(); newrt = set()
    for f in fails:
        J = 0
        for s in f["J"]: J |= anc[s] | (1 << s)
        if (f["node"], J) in seenw: continue
        seenw.add((f["node"], J))
        N.val = list(init); val = N.val; nreq = noack = 0; ok = True; hist = []
        v = byName.get(f["node"]) if f["node"] in byName else {N.names[REQ]: REQ, N.names[PACK]: PACK, N.names[OACK]: OACK}[f["node"]]
        lastExc = None; lostBy = None; enAt = None; nst = 0; sched = []
        for i in range(NS):
            if not (J >> stepOwnEv[i]) & 1:
                continue
            u = steps[i][0][0]
            if u in ENVN: sched.append("env%d" % ({REQ: -1, PACK: -3, OACK: -5}[u] - val[u]))
            else: sched.append(N.names[u])
            if not enabled_full(val, u, nreq, noack): ok = "own node not enabled at step %d" % i; break
            val[u] ^= 1; N.settle([u])
            while True:  # Jacobi rounds of the real machine
                ex = [l for l in LATCHES if N.ev(N.stor[sOf[l]]) != val[l]]
                if not ex: break
                for l in ex: val[l] ^= 1
                N.settle(ex)
            if u == REQ: nreq += 1
            if u == OACK: noack += 1
            nst += 1
            if v in ENVN or not isL.get(v):
                ev2 = enabled_full(val, v, nreq, noack)
                if ev2 and not lastExc: enAt = (i, nst)
                if lastExc and not ev2 and u != v and lostBy is None:
                    how = "excitation lost" if (v in ENVN or N.ev(N.stor[sOf[v]]) == val[v]) else "blocked by " + ",".join(N.names[c] for c in blockers.get(v, ()) if N.ev(N.stor[sOf[c]]) != val[c])
                    lostBy = (i, N.names[u], how, "enabled since step %s, %d witness steps in between" % (enAt[0], nst - enAt[1] - 1))
                lastExc = ev2
        wit_ok = ok is True
        key = (f["node"], lostBy[1] if lostBy else None)
        print("  WITNESS %s (local ideal of %d events): replay of the %d non-latch steps of down(J) on the real machine: %s; enabled-then-disabled: %s"
              % (f["node"], len(f["J"]), nst, "VALID" if wit_ok else ok, lostBy))
        if wit_ok and lostBy and lostBy[2] == "excitation lost":
            newrt.add((f["node"], lostBy[1]))
            if "--witdir" in opts:
                fn = "%s/wit_%s_%d.txt" % (opts[opts.index("--witdir") + 1], f["node"], len(sched))
                with open(fn, "w") as fo: fo.write("%s\n" % f["node"] + "\n".join(sched) + "\n")
    if newrt:
        print("  suggested RT orders (v before the disabling node):")
        for a, b in sorted(newrt): print("    %s %s" % (a, b))
        if "--extra-rt" in opts:
            with open(opts[opts.index("--extra-rt") + 1], "w") as fo:
                for a, b in sorted(newrt): fo.write("%s %s\n" % (a, b))
if CERT:
    with open(CERT, "w") as f:
        f.write("# event: node | causes (event ids)\n")
        for e in range(NE): f.write("%d | %s\n" % (evn[e], " ".join(map(str, sorted(causes[e])))))
