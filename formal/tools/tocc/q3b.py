import sys, pickle
c = sys.argv[1]; U_ = sys.argv[2].split(":"); W_ = sys.argv[3].split(":")
sys.argv = ["ao.py", c, "0", "--prevanc", "--cyc"]
src = open("/tmp/claude-0/tocc/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
idn = {n: i for i, n in enumerate(nm)}
U = eid[(idn[U_[0]], int(U_[1]))]; W = eid[(idn[W_[0]], int(W_[1]))]
print("U", el[U], "W", el[W], "U<=W in CP:", bool(leqP(U, W)), "form4:", form4(U, W))
# walk back from W: at each event, show alternatives with whether U is below each cause; follow the alternative lacking U
e = W
for step in range(25):
    v, k, t = el[e]
    alts_info = [[(nm[el[p][0]], el[p][1], el[p][2], bool(leqP(U, p))) for p in a] for a in alts[e]]
    print(" ", nm[v], k, t, "prev<=U?", prev[e] is not None and bool(leqP(U, prev[e])), alts_info)
    # pick an alternative with no cause above U
    nxt = None
    for a in alts[e]:
        if not any(leqP(U, p) for p in a):
            nxt = max(a, key=lambda p: el[p][2]) if a else None; break
    if nxt is None or v in envnode: break
    e = nxt
