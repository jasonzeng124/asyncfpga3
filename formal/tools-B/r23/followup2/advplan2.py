"""trace the simulated causal path of a flip back to a source (latest-arriving changed input each step), per corner"""
import sys, json, pickle
from bisect import bisect_right
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
from classify import load
C = load(); g = C["gates"]; nm = C["names"]; idx = {n: i for i, n in enumerate(nm)}
def trace(H, c, node, t, stop, tmin):
    hist = H["hist"]; path = []
    while node != stop and node in g:
        best = None
        for j, p in enumerate(g[node]["pins"]):
            if not p["live"] or p["src"] == node: continue
            md = p["win"][c][2]; fl = hist.get(p["src"], (0, []))[1]
            i = bisect_right(fl, t - md) - 1
            if i >= 0 and fl[i] >= tmin and (best is None or fl[i] + md > best[0]): best = (fl[i] + md, p["src"], fl[i])
        if best is None: break
        path.append([nm[node], nm[best[1]]]); node, t = best[1], best[2]
    return path, nm[node]
for c in (0, 1):
    H = pickle.load(open("hist_c%d.pkl" % c, "rb")); hist = H["hist"]
    def flips(n, lo, hi): return [x for x in hist[idx[n]][1] if lo <= x <= hi]
    a = idx["SLICE_X30Y76.A6"]
    # the reopen of X30Y76.A6 whose propagation re-opens X36Y71.A6: take X36Y71.A6's flip and D's last flip before it
    en = flips("SLICE_X36Y71.A6", 0, 10**9); dd = hist[idx["SLICE_X34Y77.D5"]][1]
    # pick the X36Y71.A6 flip that X37Y71.B5's root used (k=4 counted from t0 events)
    t0 = H["R"] - 1; enl = [x for x in en if x > t0]; te = enl[4]
    td = max(x for x in dd if x < te); ta = max(x for x in hist[a][1] if x < td)
    pe, se = trace(H, c, idx["SLICE_X36Y71.A6"], te, a, ta); pd, sd = trace(H, c, idx["SLICE_X34Y77.D5"], td, a, ta)
    print("c=%d reopen X36Y71.A6@%d, D last flip @%d, X30Y76.A6 @%d; enable path %d hops (to %s), D path %d hops (to %s)" % (c, te, td, ta, len(pe), se, len(pd), sd))
    slow = pd + [["SLICE_X37Y71.B5", "SLICE_X34Y77.D5"]]; fast = pe + [["SLICE_X37Y71.B5", "SLICE_X36Y71.A6"]]
    json.dump({"slowpins": slow, "fastpins": fast}, open("adv2_setup_c%d.json" % c, "w"))
    json.dump({"slowpins": slow, "fastpins": fast, "allfast": False, "pos": 1}, open("adv2_setup_restslow_c%d.json" % c, "w"))
    print("   D path:", [x[0] for x in pd]); print("   en path:", [x[0] for x in pe])
