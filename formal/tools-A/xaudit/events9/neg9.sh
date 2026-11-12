#!/usr/bin/env bash
# Probe HDsub negative controls on seed d slow (each MUTATED certificate must be REJECTED:
# the mutated guarded pin residual, every other item as in the unmutated run).
#  NEGwsEnd : umux3.uxa pin0's BACK-G dsub line gets wS = the guard's iX (its LINE judgement:
#             not an unlabelled S -> D walk) -> wsOK false -> that pin residual
#  NEGwsTok : new valid log lines (refl D, r1 ...) = a walk S -> D with 2 tokens (shortest, found
#             by BFS on the certificate's nodes with Net4.off); umux3.uxa pin0's BACK-G dsub
#             line gets wS = it -> WSOK's t <= 1 fails -> that pin residual
#  POSws1   : the same construction with 1 token -> must be ACCEPTED (CLEAN, as unmutated)
#  NEGwsMissing: the same line without its wS field -> rejected
#  NEGnows  : cert9.py --no-ws (no dsub line has wS) -> all 63 guarded pins residual
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
I=${I:-/tmp/events6/out}; O=${O:-/tmp/events9/out}; s=d; c=slow
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
mkdir -p $O/$s
[ -f $O/$s/cert_slow.json ] || python3 "$HERE/cert9.py" $I/$s/skel.json $I/$s/skel_slow.bands.json $O/$s/cert_slow.json > /dev/null
python3 "$HERE/cert9.py" $I/$s/skel.json $I/$s/skel_slow.bands.json $O/$s/cert_NEGnows.json --no-ws > /dev/null
python3 - $O/$s/cert_slow.json $O/$s <<'PY'
import json, sys, copy
from collections import deque
src, od = sys.argv[1], sys.argv[2]
c0 = json.load(open(src)); N = c0["nodes"]
j = next(i for i, n in enumerate(N) if n["name"] == "urig.udut.umux3.uxa.u")
g0 = c0["guards"][f"{j}/0"]; S = g0["S"]; D = c0["hyp"][g0["iB"]]["a"]
def off(n, p):  # Net4.off = offB (v src ^ inv ^ neg) (v n), as Events5.Net4.off
    pin = N[n]["pins"][p]; vs = N[pin["src"]]["v"] ^ pin["inv"] ^ pin["neg"]; return 0 if vs == N[n]["v"] else 1
def walk(tok):  # a shortest r1-walk S -> D (non-merge nodes, non-guard pins) with exactly tok tokens
    prev = {(S, 0): None}; q = deque([(S, 0)])
    while q:
        n, t = q.popleft()
        if (n, t) == (D, tok):
            path, st = [], (n, t)
            while prev[st] is not None: (pn, pt), p = prev[st]; path.append((pn, p)); st = (pn, pt)
            return path  # (node, pin) from the D end back to S
        if N[n]["mg"]: continue
        for p, pin in enumerate(N[n]["pins"]):
            if pin["pk"] == "guard": continue
            s = (pin["src"], t + off(n, p))
            if s[1] <= tok and s not in prev: prev[s] = ((n, t), p); q.append(s)
    return None
def append_walk(c, path):  # refl D, then r1 lines prepending each node; returns the S -> D line
    c["log"].append({"k": "refl", "a": D})
    for n, p in path:
        c["log"].append({"k": "r1", "n": n, "p": p, "r": len(c["log"]) - 1})
    return len(c["log"]) - 1
for tag in ("NEGwsEnd", "NEGwsTok", "NEGwsMissing", "POSws1"):
    c = copy.deepcopy(c0)
    g = c["guards"][f"{j}/0"]
    h = c["hyp"][g["iB"]]
    if tag == "NEGwsEnd":
        print(f"{tag}: hyp {g['iB']} wS {h['wS']} -> {g['iX']} (the LINE walk, not an S -> D walk)")
        h["wS"] = g["iX"]
    elif tag == "NEGwsTok":   # a VALID S -> D walk with 2 tokens: rejected only by WSOK's t <= 1
        path = walk(2); assert path, "no 2-token walk S -> D"
        h["wS"] = append_walk(c, path)
        print(f"{tag}: hyp {g['iB']} wS -> new log line {h['wS']}: walk S {S} -> D {D} via {len(path)} r1 steps, 2 tokens (expected by Net4.off)")
    elif tag == "POSws1":     # positive control: the same construction with 1 token must be ACCEPTED
        path = walk(1); assert path, "no 1-token walk S -> D"
        h["wS"] = append_walk(c, path)
        print(f"{tag}: hyp {g['iB']} wS -> new log line {h['wS']}: walk S {S} -> D {D} via {len(path)} r1 steps, 1 token")
    else:
        print(f"{tag}: hyp {g['iB']} wS {h.pop('wS')} removed")
    json.dump(c, open(f"{od}/cert_{tag}.json", "w"))
PY
one() { "$HERE/xe9.sh" $I/$s/skel.json $I/$s/skel_slow.bands.json "$1" 2>&1 | grep -v '^\[slot\]' > "$2"; }
for t in NEGwsEnd NEGwsTok NEGwsMissing NEGnows POSws1; do
  one $O/$s/cert_$t.json "$HERE/xe9_d_slow_$t.txt"
done
for t in NEGwsEnd NEGwsTok NEGwsMissing NEGnows POSws1; do
  f="$HERE/xe9_d_slow_$t.txt"
  echo "$t: $(grep -h 'hypothesis judgements' $f | cut -c30-200) | $(grep -c 'RESIDUAL Guard' $f) guard residual | $(grep 'RESIDUAL Guard' $f | head -1 | cut -c1-220) | $(tail -1 $f | cut -c1-40)"
done
