#!/usr/bin/env bash
# cost.sh HWDIR DESIGN WORK K VECFILE -- what the runt monitor costs, on one route and one draw (bench_gate.sh draw:K's
# delay model, the bits-decoded netlist, fid): the netlist is built once (build_ps.sh PS_RUNTS=1), then compiled four
# ways and each run timed with the gate's plusargs:
#   base    the gate's own run_baked.vvp (no monitor)
#   mon     + runt_mon.v (gen_runt_mon.py; +RUNT_MAXLINES=1000000, every pulse printed, for the check below)
#   vcdw    + $dumpvars of the watched nets only (the same nets as the monitor)
#   vcdall  + $dumpvars(1, tb_ps.dut): every net of the decoded netlist (what research/data/suite/hangs did)
# Prints one line per variant: wall s, user s, max RSS MB, compile wall s, output MB.  The VCDs are kept for
# vcd_pulses.py (the monitor's counts checked against an independent reading of the same run); delete them after.
set -euo pipefail
HW=$(cd "$1" && pwd); D=$2; mkdir -p "$3"; W=$(cd "$3" && pwd); K=$4; VEC=$(readlink -f "$5")
R=$(cd "$(dirname "$0")/../../../.." && pwd); G=$R/cells/gls
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; PX=$TC/openxc7-src/prjxray
XS=$W/xray.sdf
[ -f "$XS" ] || PYTHONPATH=$PX python3 "$G/fid/xray_delay.py" --routed "$HW/${D}_routed.json" --sdf "$HW/$D.sdf" --out "$XS" > "$W/xray.log" 2>&1
export GLS_SDF=$XS GLS_MODEL=fid PS_DESIGN=$D PS_HOST=ps7_bench.v PYTHONPATH=$PX
read XC XR XK <<< "$(python3 -c "import random; r=random.Random(7919*$K+17); a=r.uniform(.20,.31); b=r.uniform(.20,.31); u=r.random(); lo,hi=0.20,1.0; print(*['%.4f'%v for v in (a, b, lo+u*(hi-lo))])")"
python3 "$R/research/tools/band_inst_list.py" "$HW/${D}_routed.json" '\.chain\.g\[\d+\]\.u$' $XC "$W/chains_$K.band" > /dev/null
export GLS_SDF_FIELD=band GLS_SDF_BAND=$XR GLS_SDF_BAND_CELL=CARRY4=$XK,SELMUX2_1=$XK,SLICE_FFX=$XK,RAMB18E1_RAMB18E1=$XK \
       GLS_SDF_BAND_INST=@$W/chains_$K.band GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=$K
B=$W/b
[ -f "$B/runt_mon.v" ] || PS_RUNTS=1 "$R/research/tools/compile_slot.sh" "$G/ps/build_ps.sh" "$HW" "$B" "" bit > "$W/build.log" 2>&1
cd "$B"; rm -f gate.vvp run_baked.vvp
python3 - <<'PY'
import re
w = [l.split("\t")[6] for l in open("runt_nets.tsv") if not l.startswith("#")]
open("dumpw.v", "w").write("module dumpw; initial begin $dumpfile(\"w.vcd\");\n" +
    "".join("  $dumpvars(0, tb_ps.dut.%s);\n" % x for x in w) + "end endmodule\n")
open("dumpall.v", "w").write("module dumpall; initial begin $dumpfile(\"all.vcd\"); $dumpvars(1, tb_ps.dut); end endmodule\n")
PY
PA="+FCLK_PS=12000 +MODE=1 +NRUNS=2 +VECFILE=$VEC +TBATCH=1200000 +TEND=20000000"
for v in base mon vcdw vcdall; do
  case $v in base) X="";; mon) X=runt_mon.v;; vcdw) X=dumpw.v;; vcdall) X=dumpall.v;; esac
  t0=$(date +%s.%N)
  # shellcheck disable=SC2086
  "$R/research/tools/compile_slot.sh" iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I"$G" -I. -o $v.vvp "$G/ps/tb_ps.v" \
      netlist_baked.v "$G/prims.v" "$G/ps/ps7_bench.v" $X 2>&1 | grep -v 'procedural continuous' || true
  t1=$(date +%s.%N)
  # shellcheck disable=SC2086
  /usr/bin/time -f "%e %U %M" -o $v.time vvp $v.vvp $PA $( [ $v = mon ] && echo +RUNT_MAXLINES=1000000 ) > $v.log 2>&1 || true
  rm -f $v.vvp
  out=$(du -cm $v.log $( [ $v = vcdw ] && echo w.vcd ) $( [ $v = vcdall ] && echo all.vcd ) 2>/dev/null | tail -1 | cut -f1)
  read e u m < $v.time
  printf "%-7s run wall %7.1f s  user %7.1f s  maxRSS %6.0f MB  compile wall %5.1f s  output %s MB  batches %s  %s\n" $v $e $u \
    $(echo "$m / 1024" | bc -l) $(echo "$t1 - $t0" | bc -l) $out "$(grep -c '^BENCHRES' $v.log)" "$(grep -o 'BENCHSUMMARY.*' $v.log | head -1)"
done | tee "$W/cost.txt"
# the gate's result must not depend on the monitor: every BENCHRES line identical with and without it
for v in mon vcdw vcdall; do
  cmp -s <(grep '^BENCHRES' base.log) <(grep '^BENCHRES' $v.log) && echo "$v: BENCHRES identical to base" || echo "$v: BENCHRES DIFFER from base"
done | tee -a "$W/cost.txt"
