import sys, os
c_ = sys.argv[1]; NG = int(sys.argv[2]) if len(sys.argv) > 2 else 2
sys.argv = ["datal.py", c_]
os.environ["NPASS"] = "1"
src = open("/tmp/claude-0/tocc/datal.py").read(); src = src[:src.index("# ---------------- loop covers")]
exec(src)
def walk(key, E, depth, seen):
    w = memo.get(key)
    if not isinstance(w, dict) or depth > 14 or key in seen: return
    seen.add(key)
    B = w["B"]
    if B is None: return
    s = sep(E, B)
    tag = "ok" if s != NEG else "NOT after E"
    print("  " * depth + "%s %s [%s] B=%s(%d)@%d b=%d %s %s" % (nm[key[0]], w["kind"], key[1:3] if len(key) > 2 else "", nm[el[B][0]], el[B][1], el[B][2], w["b"], tag, w.get("phases", "")))
    if s != NEG: return
    for u, k2 in w.get("cov", []):
        if k2 is None: continue
        w2 = memo.get(k2)
        if isinstance(w2, dict) and w2["B"] is not None and sep(E, w2["B"]) == NEG: walk(k2, E, depth + 1, seen)
n = 0
for x in G_:
    if len(x) != 7: continue
    v, z, ms, me, cz, st, en_ = x
    if me >= 0 or en_ is None: continue
    E = eid[en_]
    print("GUARD v=%s z=%s S=%s(%d)@%d E=%s(%d)@%d" % (nm[v], nm[z], nm[st[0]], st[1], ev[st[0]][st[1]], nm[en_[0]], en_[1], et[E]))
    walk(cz["key"], E, 1, set())
    n += 1
    if n >= NG: break
