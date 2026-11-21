import sys, json, pickle
sys.path.insert(0, "/tmp/claude-0/bsub1/tocc")
exec(open("advplan2.py").read().split("for c in (0, 1):")[0])
for c in (0, 1):
    H = pickle.load(open("hist_c%d.pkl" % c, "rb")); hist = H["hist"]; t0 = H["R"] - 1
    EN = idx["SLICE_X30Y76.A6"]; evs = [x for x in hist[EN][1] if x > t0]
    fast = set()
    for k in (0, 2):
        p, s = trace(H, c, EN, evs[k], -1, evs[k] - 40000)
        fast |= set(tuple(x) for x in p)
    for q in C["LATCH"]:
        for j, pp in enumerate(g[q]["pins"]):
            if pp["src"] == EN: fast.add((nm[q], nm[EN]))
    json.dump({"fastpins": [list(x) for x in fast], "pos": 1}, open("adv4_bankopen_c%d.json" % c, "w"))
    print(c, len(fast))
