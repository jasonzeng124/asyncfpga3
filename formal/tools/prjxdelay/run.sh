#!/usr/bin/env bash
# Probe C-10c end to end: route 4 seeds of each ring design (skips routes
# already in build/), compute the prjxray ring periods, compare.
#     formal/tools/prjxdelay/run.sh        # ~10 min with 4 cores, mostly nextpnr
# Results: build/analysis.txt (vs current SDF), build/analysis_prepatch.txt
# (vs the emulated pre-lut-perm-sink SDF, which is what silicon was compared
# against), build/analysis_extra.txt (decomposition, ring 0).
set -euo pipefail
H=$(cd "$(dirname "$0")" && pwd); cd "$H"
SEEDS="default 1 2 3"
for t in ro_top ro_many_top; do
    for s in $SEEDS; do
        [ -s build/${t}_s$s/$t.sdf ] || ./route.sh $t $s &
    done
    wait
done
for t in ro_top ro_many_top; do
    for s in $SEEDS; do
        python3 ringdelay.py build/${t}_s$s $t --json build/${t}_s$s/prjx.json > build/${t}_s$s/prjx.txt &
    done
    wait
done
M="build/ro_many_top_sdefault/prjx.json build/ro_many_top_s1/prjx.json build/ro_many_top_s2/prjx.json build/ro_many_top_s3/prjx.json"
T="build/ro_top_sdefault/prjx.json build/ro_top_s1/prjx.json build/ro_top_s2/prjx.json build/ro_top_s3/prjx.json"
python3 analyze.py $M -- $T > build/analysis.txt
python3 analyze.py --prepatch $M -- $T > build/analysis_prepatch.txt
python3 analyze.py --extra $M -- $T > build/analysis_extra.txt
grep -h "^nextpnr" build/*/toolchain.txt | sort | uniq -c
tail -12 build/analysis_extra.txt
