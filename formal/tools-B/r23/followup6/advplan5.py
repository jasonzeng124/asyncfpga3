import sys, json, pickle
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
exec(open("advplan2.py").read().split("for c in (0, 1):")[0])
for c in (0, 1):
    H = pickle.load(open("hist_c%d.pkl" % c, "rb")); hist = H["hist"]; t0 = H["R"] - 1
    ev_ = lambda n: [x for x in hist[idx[n]][1] if x > t0]
    ta = ev_("SLICE_X22Y87.A6")[0]; tb = ev_("SLICE_X27Y80.A6")[2]
    pa, _ = trace(H, c, idx["SLICE_X22Y87.A6"], ta, -1, ta - 40000)
    pb, _ = trace(H, c, idx["SLICE_X27Y80.A6"], tb, -1, tb - 40000)
    nb = set(x[0] for x in pb) | set(x[1] for x in pb)
    k = next((i for i, x in enumerate(pa) if x[1] in nb), len(pa))
    kb = next((i for i, x in enumerate(pb) if x[1] in set(y[1] for y in pa[:k + 1]) | set(y[0] for y in pa[:k + 1])), len(pb))
    slow = pa[:k + 1] + [["SLICE_X22Y87.D5", "SLICE_X22Y87.A6"], ["SLICE_X22Y81.B5", "SLICE_X22Y87.D5"]]
    fast = pb[:kb + 1] + [["SLICE_X27Y80.B6", "SLICE_X27Y80.A6"], ["SLICE_X22Y81.B5", "SLICE_X27Y80.B6"]]
    print(c, "data re-latch @%d, select latch open @%d; slow %d hops, fast %d hops" % (ta, tb, len(slow), len(fast)))
    for tag, extra in (("mid", {}), ("allfast", {"allfast": True})):
        json.dump(dict(slowpins=slow, fastpins=fast, **extra), open("adv5_%s_c%d.json" % (tag, c), "w"))
