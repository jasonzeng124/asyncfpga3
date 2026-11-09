# gate sets: non-common pasts of A = X22Y87.A6(0) and B = X27Y80.A6(2) in the mid-run certificate (CP order); usage sets.py c
import sys, json
cc = sys.argv[1]
sys.argv = ["ao.py", cc, "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
N = {nm[n]: n for n in EX}
A = eid[(N["SLICE_X22Y87.A6"], 0)]; B = eid[(N["SLICE_X27Y80.A6"], 2)]
pa = VCP[A][enode] > ek; pb = VCP[B][enode] > ek
onlyA = set(el[e][0] for e in np.nonzero(pa & ~pb)[0]); onlyB = set(el[e][0] for e in np.nonzero(pb & ~pa)[0])
both = onlyA & onlyB
print("c=%s: events only-below-A %d (nodes %d), only-below-B %d (nodes %d), nodes in both %d, common-past events %d" % (
    cc, int((pa & ~pb).sum()), len(onlyA), int((pb & ~pa).sum()), len(onlyB), len(both), int((pa & pb).sum())))
envA = [nm[n] for n in onlyA if n in envnode]; envB = [nm[n] for n in onlyB if n in envnode]
print("  env nodes only-A %s only-B %s; nodes in both: %s" % (envA, envB, [nm[n] for n in both][:10]))
json.dump(dict(hiG=sorted(nm[n] for n in onlyA - both), loG=sorted(nm[n] for n in onlyB - both), both=sorted(nm[n] for n in both)),
          open("/tmp/claude-0/arbh/sets_c%s.json" % cc, "w"))
