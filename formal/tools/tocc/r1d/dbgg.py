# r1d debug: run GuardTime for the guards of the given data nodes (one pass) and print the claim-end path
import sys, os
ZS = sys.argv[2].split(","); NMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 3
src = open("/tmp/claude-0/r1d/datal.py").read(); src = src[:src.index("# ---------------- guards")]
exec(src)
def s_(e): return "%s(%d)@%d" % (nm[el[e][0]], el[e][1], el[e][2]) if e is not None else None
def mid_(v, w): return dl[(v, w)][2] if (v, w) in dl else 1
n_ = 0
for (v, z), gl in DATAG.items():
    if nm[z] not in ZS: continue
    for (st, en_, val) in gl:
        u, j = st; S = eid[(u, j)]; E = eid[en_] if en_ else None
        ts = ev[u][j] + mid_(v, u); te_ = (ev[en_[0]][en_[1]] + mid_(v, en_[0])) if en_ else ts
        CTX.append(tuple(sorted([S] + ([E] if E is not None else []))))
        GTOP = (E, pwin(v, z)[0], hi_(v, u)) if E is not None else None
        cz = claim(z, ts - mid_(v, z), te_ - mid_(v, z)); GTOP = None; CTX.pop()
        d = sep(E, cz["B"]) if (E is not None and cz["B"] is not None) else None
        me = (d + pwin(v, z)[0] + cz["b"] - hi_(v, u)) if d not in (None, NEG) else d
        if me is None or me >= 0: continue
        print("GUARD", nm[v], nm[z], "S", s_(S), "E", s_(E), "end margin", me)
        k = cz["key"]; seen = set()
        while k not in seen:
            seen.add(k); w = memo[k]
            print("   ", nm[k[0]], k[1:4], w["kind"], "A", s_(w["A"]), w["a"], "B", s_(w["B"]), w["b"], w.get("phases"), "trunc", s_(w.get("trunc")) if w.get("trunc") is not None else None)
            nxt = [kk for u_, kk in (w.get("cov") or []) if kk in memo and isinstance(memo[kk], dict) and memo[kk]["B"] == w["B"]]
            if not nxt: break
            k = nxt[0]
        n_ += 1
        if n_ >= NMAX: break
    if n_ >= NMAX: break
print("stats", {k: v for k, v in stats.items() if "restart" in k or "anchor" in k or "retry" in k or "trunc" in k})
for t in TRUNC[:60]: print("TRUNC", nm[t[0]], t[1], t[2], s_(t[3]), s_(t[4]), t[5:])
for (n, t, tr, r0, r1, ob) in RSDBG[:40]:
    print("RS", nm[n], t, tr[0], s_(tr[1]), "r0 B", s_(r0["B"]), r0["b"], r0.get("phases"), "| r1", (s_(r1["A"]), r1["a"], s_(r1["B"]), r1["b"], r1.get("phases"), r1.get("bad"), s_(r1.get("trunc")) if r1.get("trunc") is not None else None) if isinstance(r1, dict) else r1, ob)
def path(k, ind="  "):
    seen = set()
    while k not in seen:
        seen.add(k); w = memo[k]
        print(ind, nm[k[0]], k[1:5], w["kind"], "A", s_(w["A"]), w["a"], "B", s_(w["B"]), w["b"], w.get("phases"), "trunc", s_(w.get("trunc")) if w.get("trunc") is not None else None)
        for u_, kk in (w.get("cov") or []):
            if kk in memo: print(ind, "    cov", nm[u_], kk[1:5], "A", s_(memo[kk]["A"]), memo[kk]["a"], "B", s_(memo[kk]["B"]), memo[kk]["b"])
        nxt = [kk for u_, kk in (w.get("cov") or []) if kk in memo and isinstance(memo[kk], dict) and memo[kk]["B"] == w["B"]]
        if not nxt: break
        k = nxt[0]
for (n, t, tr, r0, r1, ob) in RSDBG:
    if nm[n] in os.environ.get("RSP", "").split(",") and isinstance(r1, dict):
        print("RESTART PATH", nm[n], t, tr); path(r1["key"]); break
