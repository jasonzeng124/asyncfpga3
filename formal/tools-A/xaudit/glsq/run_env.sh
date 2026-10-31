#!/usr/bin/env bash
# glsq: ArbEnv window fields (check_env.py) on one gcd_hw R5 seed, 16 vectors.   run_env.sh <seed|d> -> out2/env_<seed>/
set -u
G="$(cd "$(dirname "$0")" && pwd)"; SRC=${SRC:-$HOME/gcdsrc520}; s=$1; O=$G/out2/env_$s; mkdir -p $O
X=$G/../arbnet/results/xan_${s}_slow.txt
cd $SRC/cells; export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
/home/user/asyncfpga3/cells/verify/toolchain.sh > $O/toolchain.txt 2>&1 || { echo "toolchain FAIL"; exit 1; }
if [ $s = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$s; fi
BD_SIZES=$SRC/research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw > $O/build.log 2>&1
md5sum build/hw/gcd_hw/gcd_hw.sdf build/hw/gcd_hw/gcd_hw_routed.json > $O/md5.txt
bash gls/build.sh gcd_hw > $O/gls_build.log 2>&1
cd build/gls/gcd_hw
python3 -I $G/gen_evmon.py . $O/info.json > evmon.v 2> $O/evmon_gen.err
iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o run_ev.vvp $SRC/cells/gls/tb_run.v netlist_baked.v $SRC/cells/gls/prims.v evmon.v 2>&1 | grep -v procedural
for v in $(seq 0 15); do vvp run_ev.vvp +VEC=$v +TEND=150000 +QUIET=200000 > $O/ev_v$v.log 2>&1 & if (( v % 3 == 2 )); then wait; fi; done; wait
for v in $(seq 0 15); do f=$O/ev_v$v.log; r=$(grep -o "t_rst_rel=[0-9]*" $f | cut -d= -f2)
  { grep -h '^SUMMARY' $f | cut -c1-40; python3 -I $G/check_env.py $f $O/info.json $X ${r:-0}; } > $O/check_v$v.txt; rm -f $f
done
python3 - $O <<'PY'
import sys, glob, re, collections
O = sys.argv[1]; tot = collections.Counter(); bad = collections.Counter(); ok = 0
for f in sorted(glob.glob(O + "/check_v*.txt")):
    t = open(f).read(); ok += "errs=0" in t
    for m in re.finditer(r"^(\S+) (\S+): (\d+) events, (\d+) violations", t, re.M):
        tot[(m.group(1), m.group(2))] += int(m.group(3)); bad[(m.group(1), m.group(2))] += int(m.group(4))
lines = [f"{k[0]} {k[1]}: {tot[k]} events, {bad[k]} violations" for k in sorted(tot)]
open(O + "/summary.txt", "w").write(f"vectors errs=0: {ok}/16\n" + "\n".join(lines) + "\n")
print(O.split("/")[-1], f"errs0 {ok}/16", "total events", sum(tot.values()), "violations", sum(bad.values()))
PY
