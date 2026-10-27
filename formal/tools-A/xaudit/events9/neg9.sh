#!/usr/bin/env bash
# Probe HDsub negative controls on seed d slow (each MUTATED certificate must be REJECTED:
# the mutated guarded pin residual, every other item as in the unmutated run).
#  NEGwsEnd : umux3.uxa pin0's BACK-G dsub line gets wS = the guard's iX (a closed walk D -> D,
#             wrong start: not from the label source S) -> wsOK false -> that pin residual
#  NEGwsTok : a new (valid) log line r1(S, pin 0, iX) is appended: a walk S -> D with
#             off(S pin0) + t(iX) tokens; umux3.uxa pin0's BACK-G dsub line gets wS = it.
#             Rejected iff that walk has 2 tokens (dsub9 needs <= 1)
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
src, od = sys.argv[1], sys.argv[2]
c0 = json.load(open(src))
j = next(i for i, n in enumerate(c0["nodes"]) if n["name"] == "urig.udut.umux3.uxa.u")
for tag in ("NEGwsEnd", "NEGwsTok", "NEGwsMissing"):
    c = copy.deepcopy(c0)
    g = c["guards"][f"{j}/0"]
    h = c["hyp"][g["iB"]]
    if tag == "NEGwsEnd":
        print(f"{tag}: hyp {g['iB']} wS {h['wS']} -> {g['iX']} (closed walk D -> D)")
        h["wS"] = g["iX"]
    elif tag == "NEGwsTok":
        c["log"].append({"k": "r1", "n": g["S"], "p": 0, "r": g["iX"]})
        print(f"{tag}: log line {len(c['log']) - 1} = r1(S {g['S']}, pin 0, iX {g['iX']}); hyp {g['iB']} wS {h['wS']} -> it")
        h["wS"] = len(c["log"]) - 1
    else:
        print(f"{tag}: hyp {g['iB']} wS {h.pop('wS')} removed")
    json.dump(c, open(f"{od}/cert_{tag}.json", "w"))
PY
one() { "$HERE/xe9.sh" $I/$s/skel.json $I/$s/skel_slow.bands.json "$1" 2>&1 | grep -v '^\[slot\]' > "$2"; }
for t in NEGwsEnd NEGwsTok NEGwsMissing NEGnows; do
  one $O/$s/cert_$t.json "$HERE/xe9_d_slow_$t.txt"
done
for t in NEGwsEnd NEGwsTok NEGwsMissing NEGnows; do
  f="$HERE/xe9_d_slow_$t.txt"
  echo "$t: $(grep -h 'hypothesis judgements' $f | cut -c30-200) | $(grep -c 'RESIDUAL Guard' $f) guard residual | $(grep 'RESIDUAL Guard' $f | head -1 | cut -c1-220) | $(tail -1 $f | cut -c1-40)"
done
