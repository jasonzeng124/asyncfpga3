# arbh1 (UNTRUSTED): for the latches X36Y63.B6, X36Y68.B6, X37Y47.B6 (D = X39Y53.B6 = X38Y51.A6 | X38Y53.A6) and each
# close of their enable: D as read at the close, D's next change, its exact cause event, causal relation with the close,
# Sep(close -> cause) and the hold margin Sep + lo(cause->D) + lo(D->Q) - hi(en->Q).  usage: arbh1.py c
import sys
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[x]: x for x in range(len(nm))}
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2])
D = N["SLICE_X39Y53.B6"]
def pw(v, w):
    for p in g[v]["pins"]:
        if p["live"] and p["src"] == w: return p["win"][c]
def hv(n):
    b, ts = hist[n]; return b, ts
Dins = [N["SLICE_X38Y51.A6"], N["SLICE_X38Y53.A6"]]
out = []
for qn in ("SLICE_X36Y63.B6", "SLICE_X36Y68.B6", "SLICE_X37Y47.B6", "SLICE_X36Y69.B6"):
    Q = N[qn]; fb, en = C["LATCH"][Q]; pe, act = en[0]; e = g[Q]["pins"][pe]["src"]
    elo, ehi, emd = g[Q]["pins"][pe]["win"][c]; dlo, dhi, dmd = pw(Q, D)
    print("== %s  enable %s (transparent when %d) en pin [%d,%d]  D pin [%d,%d]" % (qn, nm[e], act, elo, ehi, dlo, dhi))
    for k, t in enumerate(ev[e]):
        if valat(e, t) == bool(act): continue   # opening
        tclose_read = t + emd
        tnext_open = ev[e][k + 1] if k + 1 < len(ev[e]) else None
        dv = valat(D, tclose_read - dmd)
        _, dts = hist[D]
        nxt = [x for x in dts if x + dmd > tclose_read - 0]
        tn = nxt[0] if nxt else None
        info = "close %s read@%d D=%d next open %s; D next change @%s" % (s_(eid[(e, k)]), tclose_read, dv, tnext_open, tn)
        if tn is not None:
            # D's change: which input changed?
            causes = []
            for w in Dins:
                lo, hi, md = pw(D, w); tw = ev[w]; i = bisect_right(tw, tn - md) - 1
                if i >= 0 and tw[i] + md == tn: causes.append(eid[(w, i)])
            for cz in causes:
                lo, hi, md = pw(D, el[cz][0]); x = eid[(e, k)]
                sp = sep23(x, cz); lq = bool(leqP(x, cz)); lq2 = bool(leqP(cz, x))
                f4 = form4(cz, x) if not lq else None
                marg = (sp + lo + dlo - ehi) if sp is not None else None
                info += "\n     cause %s: close<=cause %s, cause<=close %s, Sep(close->cause) %s, hold margin(k0) %s, flip kappa %s; D change read at Q %+d ps after close read; next open %s" % (
                    s_(cz), lq, lq2, sp, marg, ("%.3f" % (((sp + lo + dlo) - ehi) / ((sp + lo + dlo) + ehi))) if sp is not None else None,
                    tn + dmd - tclose_read, ("before" if tnext_open is not None and tnext_open + emd < tn + dmd else "after"))
        print("  " + info)
