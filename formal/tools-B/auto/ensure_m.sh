#!/usr/bin/env bash
# tools-B/auto/ensure_m.sh RUNDIR  (shard B): make RUNDIR/w/m usable by every tool that runs simx directly (xsweep, ctlsweep,
# weaksweep, steermargin): the simx binary (compiled from formal/tools/margin/simx.cpp if no draw dir kept one), net.simx
# (simx_conv.py), gclass.txt (research's draw classes, written by draws.py into each draw dir). Prints what was missing.
D=$1; M=$D/w/m; H=$(cd "$(dirname "$0")/../../tools/margin" && pwd)
[ -f $M/net.json ] || { echo "ensure_m: no $M/net.json"; exit 1; }
if [ ! -x $M/simx ]; then s=$(ls $D/d1*/simx 2>/dev/null | head -1); if [ -n "$s" ]; then cp $s $M/simx; else g++ -O2 -std=c++17 -o $M/simx $H/simx.cpp; fi; echo "ensure_m: simx"; fi
[ -f $M/net.simx ] || { python3 $H/simx_conv.py $M/net.json $M/bnd.json $M/net.simx > /dev/null 2>&1; echo "ensure_m: net.simx"; }
if [ ! -f $M/gclass.txt ]; then g=$(ls $D/d1*/gclass.txt $D/j/d1*/gclass.txt 2>/dev/null | head -1); [ -n "$g" ] && cp $g $M/gclass.txt && echo "ensure_m: gclass.txt"; fi
exit 0
