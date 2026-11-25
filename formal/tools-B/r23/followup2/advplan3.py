import sys, json, pickle
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
exec(open("advplan2.py").read().split("for c in (0, 1):")[0])
for c in (0, 1):
    H = pickle.load(open("hist_c%d.pkl" % c, "rb")); hist = H["hist"]; t0 = H["R"] - 1
    def evs(n): return [x for x in hist[idx[n]][1] if x > t0]
    t69 = evs("SLICE_X36Y69.A6")[4]; t71 = evs("SLICE_X36Y71.A6")[4]; t76 = evs("SLICE_X30Y76.A6")[2]
    # common start: trace both back until they meet
    p69, s69 = trace(H, c, idx["SLICE_X36Y69.A6"], t69, -1, t76 - 60000)
    p71, s71 = trace(H, c, idx["SLICE_X36Y71.A6"], t71, -1, t76 - 60000)
    n71 = set(x[0] for x in p71) | set(x[1] for x in p71)
    k = next((i for i, x in enumerate(p69) if x[1] in n71), len(p69))
    slow = p69[:k + 1] + [["SLICE_X36Y69.B6", "SLICE_X36Y69.A6"]]
    fast = [x for x in p71 if x[0] not in set(y[0] for y in slow)] + [["SLICE_X37Y71.B5", "SLICE_X36Y71.A6"]]
    print("c=%d X36Y69.A6(4)@%d X36Y71.A6(4)@%d X30Y76.A6(2)@%d; slow branch %d hops to meet %s; fast %d" % (c, t69, t71, t76, len(slow), p69[k][1] if k < len(p69) else None, len(fast)))
    for tag, extra in (("mid", {}), ("allfast", {"allfast": True})):
        json.dump(dict(slowpins=slow, fastpins=fast, **extra), open("adv3_%s_c%d.json" % (tag, c), "w"))
