#!/usr/bin/env bash
# Probes C-10f / C-10f2 end to end.
#   formal/tools/rtfb/run.sh [--no-route] [--no-lean] [--freq100]
#  1. Muller pipeline (10d's pipe/), seeds 1..8: route + read back (route_muller.sh, --freq 100),
#     RT_FB per stage (muller_rt.sh: 10d's rt_all.py = C-10f numbers, rtfb_design.py RTFB_NO_HOP
#     must agree with it, rtfb_design.py WITH the OUTMUX hop -> Lean data RtFbM64S1..8, every
#     C-element), RtFbMuller.lean (lean_muller.py), summaries build/muller/summary{,0}.txt,
#     common-corner evidence build/muller/point_summary.txt
#  2. gcd_hw seeds d,2,3,4: route (route_gcd.sh = C-10e's recipe, no --freq, as C-10f), whole-design
#     RT_FB (gcd_rt.sh -> Lean data RtFbGcdS{d,2,3,4}), RtFbGcd.lean (lean_gcd.py)
#     --freq100: also the same 4 seeds with NEXTPNR_FREQ=100 -> RtFbGcdF100S*, RtFbGcdF100.lean
#  3. formal/check.sh on every RtFb*.lean
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
cd "$HERE"
NOROUTE=0; NOLEAN=0; F100=0
for a in "$@"; do case $a in --no-route) NOROUTE=1;; --no-lean) NOLEAN=1;; --freq100) F100=1;; esac; done
for s in 1 2 3 4 5 6 7 8; do
    [ $NOROUTE = 1 ] || ./route_muller.sh $s 64
    ./muller_rt.sh $s 64 --lean
done
python3 -I summarize.py build/muller/muller64_s{1,2,3,4,5,6,7,8}.rtd.txt | tee build/muller/summary.txt
python3 -I summarize.py build/muller/muller64_s{1,2,3,4,5,6,7,8}.rtd0.txt > build/muller/summary0.txt
python3 -I lean_muller.py
for s in 1 2 3 4 5 6 7 8; do B=build/muller/muller64_s$s
    python3 -I rtfb_design.py $B.fromBit.fasm --routed ${B}_routed.json --report $B.point.txt \
        --variants indep,pFmin,pFmax,pSmin,pSmax > /dev/null
    echo "s$s $(grep -E '^p[FS]m' $B.point.txt | awk '{printf "%s %s %s  ", $1,$3,$5}')"
done | tee build/muller/point_summary.txt
NPR=$(awk '/nextpnr sha256/{print $3}' build/muller/muller64_s1.toolchain)
for s in d 2 3 4; do
    [ $NOROUTE = 1 ] || ./route_gcd.sh $s
    ./gcd_rt.sh $s - --lean > build/gcd_$s.out
done
python3 -I lean_gcd.py --nextpnr "$NPR" d 2 3 4
LF=()
if [ $F100 = 1 ]; then
    for s in d 2 3 4; do
        [ $NOROUTE = 1 ] || ./route_gcd.sh $s 100
        ./gcd_rt.sh $s 100 --lean > build/gcd_${s}_f100.out
    done
    python3 -I lean_gcd.py --freq 100 --nextpnr "$NPR" d 2 3 4
    LF=($(for s in d 2 3 4; do echo Formal/Timing/RtFbGcdF100S$s.lean; done) Formal/Timing/RtFbGcdF100.lean)
fi
[ $NOLEAN = 1 ] && exit 0
cd "$REPO/formal"
./check.sh Formal/Timing/RtFbCore.lean $(for s in 1 2 3 4 5 6 7 8; do echo Formal/Timing/RtFbM64S$s.lean; done) \
    Formal/Timing/RtFbMuller.lean $(for s in d 2 3 4; do echo Formal/Timing/RtFbGcdS$s.lean; done) Formal/Timing/RtFbGcd.lean \
    "${LF[@]}"
