import re
s = open("datal.py").read()
def rep(a, b, cnt=1):
    global s
    assert s.count(a) == cnt, (a, s.count(a)); s = s.replace(a, b)
# globals
rep("memo = {}; inprog = set();", "TRUNC = []; WB = [None]\nNOTRK = set(x for x in os.environ.get('NOTRUNC', '').split(',') if x)\nNOTRQ = set(x for x in os.environ.get('NOTRUNCQ', '').split(',') if x)\nmemo = {}; inprog = set();")
# window: record end-binding pin
rep("""            B, b = best[0], best[1]
            if b < 0:""", """            B, b = best[0], best[1]
            bnd_ = None
            for u, w in pins_w:
                if w["B"] is None: continue
                d = sep(B, w["B"])
                if d == NEG: continue
                r_ = pwin(z, u)[0] + w["b"] + d
                if bnd_ is None or r_ < bnd_[0]: bnd_ = (r_, u, w.get("key"))
            WB[0] = bnd_
            if b < 0:""")
rep("""        obl("CovTime end (no Sep between pin windows)", NEG, (nm[z], tuple(Bs), tuple(CTX[-1]) if CTX else ())); B = min(Bs, key=lambda e: tm[e]); b = 0""",
    """        obl("CovTime end (no Sep between pin windows)", NEG, (nm[z], tuple(Bs), tuple(CTX[-1]) if CTX else ())); B = min(Bs, key=lambda e: tm[e]); b = 0; WB[0] = ("covfail",)""")
rep("""    if not Bs: B = None; b = 0
    else:""", """    WB[0] = None
    if not Bs: B = None; b = 0
    else:""")
# comb_seg: keep binding
rep("""    A, a, B, b = window(pins_w, z)
    for (u, tk) in pend: PEND.append((INSTACK[-1], z, u, tk, (A, a, B, b)))
    return dict(A=A, a=a, B=B, b=b, val=val, kind="comb", cov=[(u, w.get("key")) for u, w in pins_w])""",
"""    A, a, B, b = window(pins_w, z); bnd_ = WB[0]
    for (u, tk) in pend: PEND.append((INSTACK[-1], z, u, tk, (A, a, B, b)))
    return dict(A=A, a=a, B=B, b=b, val=val, kind="comb", cov=[(u, w.get("key")) for u, w in pins_w], bind=bnd_)""")
rep("""    return dict(A=segs[0]["A"], a=segs[0]["a"], B=segs[-1]["B"], b=segs[-1]["b"], val=val, kind="comb-chain")""",
    """    return dict(A=segs[0]["A"], a=segs[0]["a"], B=segs[-1]["B"], b=segs[-1]["b"], val=val, kind="comb-chain", bind=segs[-1].get("bind"))""")
# latch phases: record pins/binding
rep("""                AU, aU, BU2, bU2 = window(pinsU, Q)
                chain.append(dict(ph="U'", A=AU, a=aU, B=BU2, b=bU2, k=kk))""",
    """                AU, aU, BU2, bU2 = window(pinsU, Q)
                chain.append(dict(ph="U'", A=AU, a=aU, B=BU2, b=bU2, k=kk, bind=WB[0], pins=[(u, w.get("key"), w["B"], w["b"]) for u, w in pinsU]))""")
rep("""        A, a, B, b = window(pinsT, Q)
        chain.append(dict(ph="T", A=A, a=a, B=B, b=b, k=kk))""",
    """        A, a, B, b = window(pinsT, Q)
        chain.append(dict(ph="T", A=A, a=a, B=B, b=b, k=kk, bind=WB[0], pins=[(u, w.get("key"), w["B"], w["b"]) for u, w in pinsT], tclose=tclose, topen=topen))""")
rep("""        _, _, BU, bU = window(pinsU, Q) if pinsU else (None, 0, None, 0)
        chain.append(dict(ph="U", A=A, a=a + fhi, B=BU, b=bU, k=kk))""",
    """        WB[0] = None
        _, _, BU, bU = window(pinsU, Q) if pinsU else (None, 0, None, 0)
        chain.append(dict(ph="U", A=A, a=a + fhi, B=BU, b=bU, k=kk, bind=WB[0], pins=[(u, w.get("key"), w["B"], w["b"]) for u, w in pinsU], tclose=tclose))""")
rep("""        chain.append(dict(ph="H", A=eid[(e, kk)], a=ehi, B=Bh, b=elo, k=kk + 1))""",
    """        chain.append(dict(ph="H", A=eid[(e, kk)], a=ehi, B=Bh, b=elo, k=kk + 1, bind=("enable", e)))""")
if 'chain.append(dict(ph="H", A=None' in s:
    rep("""chain.append(dict(ph="H", A=None, a=0, B=eid[(e, kk)] if kk < len(ev[e]) else None, b=elo, k=kk))""",
        """chain.append(dict(ph="H", A=None, a=0, B=eid[(e, kk)] if kk < len(ev[e]) else None, b=elo, k=kk, bind=("enable", e)))""")
rep("""                chain.append(dict(ph="U'", A=chain[-1]["A"], a=chain[-1]["a"], B=None, b=0, k=kk))""",
    """                chain.append(dict(ph="U'", A=chain[-1]["A"], a=chain[-1]["a"], B=None, b=0, k=kk, bind=None))""")
# truncation
rep("""    for i_, (c1, c2) in enumerate(zip(chain, chain[1:])):
        if c1["B"] is None: continue
        if c2["A"] is None: continue
        d = sep(c2["A"], c1["B"])
        if d == NEG or c1["b"] + d - c2["a"] < 0:
            stats["latch claim truncated at a failing union (%s->%s)" % (c1["ph"], c2["ph"])] += 1
            chain = chain[:i_ + 1]; break""",
"""    trunc = None; full = list(chain)
    for i_, (c1, c2) in enumerate(zip(chain, chain[1:])):
        if c1["B"] is None: continue
        if c2["A"] is None: continue
        d = sep(c2["A"], c1["B"])
        if d == NEG or c1["b"] + d - c2["a"] < 0:
            kd_ = "%s->%s" % (c1["ph"], c2["ph"])
            sup = (kd_ in NOTRK) or (nm[Q] in NOTRQ)
            trunc = dict(Q=Q, key=INSTACK[-1], kind=kd_, e=e, emd=emd, elo=elo, ehi=ehi, i=i_, nph=len(chain), c1=dict(c1), c2=dict(c2), d=d,
                         margin=(c1["b"] + d - c2["a"]) if d != NEG else NEG, suppressed=sup, sb=sb, se=se, val=val,
                         Dp=[(j, g[Q]["pins"][j]["src"], g[Q]["pins"][j]["win"][c]) for j in Dp], phases=[(p_["ph"], p_["A"], p_["a"], p_["B"], p_["b"]) for p_ in chain])
            TRUNC.append(trunc)
            if sup: stats["SUPPRESSED truncation (%s)" % kd_] += 1; continue
            stats["latch claim truncated at a failing union (%s->%s)" % (c1["ph"], c2["ph"])] += 1
            chain = chain[:i_ + 1]; break""")
rep("""    return dict(A=chain[0]["A"], a=chain[0]["a"], B=chain[-1]["B"], b=chain[-1]["b"], val=val, kind="latch",
                phases=[(ph["ph"], ph["B"]) for ph in chain], cov=COVL.get(Q, []))""",
"""    return dict(A=chain[0]["A"], a=chain[0]["a"], B=chain[-1]["B"], b=chain[-1]["b"], val=val, kind="latch",
                phases=[(ph["ph"], ph["B"]) for ph in chain], cov=COVL.get(Q, []), trunc=trunc if (trunc and not trunc["suppressed"]) else None, bind=chain[-1].get("bind"))""")
rep("memo.clear(); OBL.clear(); stats.clear();", "memo.clear(); OBL.clear(); stats.clear(); TRUNC.clear();")
rep("""pickle.dump(dict(OBL=OBL, G=G_, stats=dict(stats)), open("/tmp/claude-0/bsub1/tocc/datal_c%s%s.pkl" % (c_, PS), "wb"))""",
"""OUTP = os.environ.get("OUTP", "/tmp/claude-0/bsub1/tocc/datal_t_c%s%s.pkl" % (c_, PS))
MEMO = {k: {kk: vv for kk, vv in v_.items()} for k, v_ in memo.items() if isinstance(v_, dict)}
pickle.dump(dict(OBL=OBL, G=G_, stats=dict(stats), TRUNC=TRUNC, MEMO=MEMO), open(OUTP, "wb"))""")
open("datal_t.py", "w").write(s)
print("ok")
