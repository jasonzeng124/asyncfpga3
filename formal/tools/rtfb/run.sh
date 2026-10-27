#!/usr/bin/env bash
# Probe C-10f end to end.
#   formal/tools/rtfb/run.sh [--no-route] [--no-lean]
#  1. Muller pipeline (10d's pipe/), seeds 1..8: route + read back (route_muller.sh, ~15 s each),
#     RT_FB per stage (muller_rt.sh: 11b fasm2lean + 10d rt_all.py, unchanged) -> Lean data
#     RtFbM64S2..8 (seed 1 = 10d's RoutedMuller64S1), summary build/muller/summary.txt,
#     common-corner evidence build/muller/point_summary.txt
#  2. gcd_hw seeds d,2,3,4 (C-10e's routes: formal/tools/tcheck/route.sh SEED must have run;
#     ~15 min per seed for the bitstream when 10e's did not finish), whole-design RT_FB
#     (rtfb_design.py) -> Lean data RtFbGcdS{d,2,3,4}, summary RtFbGcd.lean (lean_gcd.py)
#  3. formal/check.sh on every RtFb*.lean
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
cd "$HERE"
for s in 1 2 3 4 5 6 7 8; do
    [ "${1:-}" = --no-route ] || ./route_muller.sh $s 64
    if [ $s = 1 ]; then ./muller_rt.sh 1 64; else ./muller_rt.sh $s 64 --lean; fi
done
python3 -I summarize.py build/muller/muller64_s{1,2,3,4,5,6,7,8}.rt.txt | tee build/muller/summary.txt
for s in 1 2 3 4 5 6 7 8; do B=build/muller/muller64_s$s
    python3 -I rtfb_design.py $B.fromBit.fasm --routed ${B}_routed.json --report $B.point.txt \
        --variants indep,pFmin,pFmax,pSmin,pSmax > /dev/null
    echo "s$s $(grep -E '^p[FS]m' $B.point.txt | awk '{printf "%s %s %s  ", $1,$3,$5}')"
done | tee build/muller/point_summary.txt
python3 -I rtfb_design.py build/muller/muller64_s3.fromBit.fasm --routed build/muller/muller64_s3_routed.json \
    --sdf build/muller/muller64_s3.sdf --report /dev/null --dump SLICE_X40Y98.CLUT:slowE \
    | sed -n '/== concrete/,/violation/p' > build/muller/worst_s3_slowE.txt
for s in d 2 3 4; do ./gcd_rt.sh $s --lean > build/gcd_$s.out; done
python3 -I lean_gcd.py d 2 3 4
case " $* " in *" --no-lean "*) exit 0;; esac
cd "$REPO/formal"
./check.sh Formal/Timing/RtFbCore.lean $(for s in 2 3 4 5 6 7 8; do echo Formal/Timing/RtFbM64S$s.lean; done) \
    Formal/Timing/RtFbMuller.lean $(for s in d 2 3 4; do echo Formal/Timing/RtFbGcdS$s.lean; done) Formal/Timing/RtFbGcd.lean
