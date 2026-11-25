#!/usr/bin/env bash
# glsq: nore (gen_noremon.py) and pointwise C (POINT=1 gen_cwmon.py) monitors on one gcd_hw R5 seed (no scatter),
# 16 vectors each.   run_edge.sh <seed|d>   -> out2/edge_<seed>/{nore,cwpt}_table.txt
set -u
G="$(cd "$(dirname "$0")" && pwd)"; SRC=${SRC:-$HOME/gcdsrc520}; s=$1; O=$G/out2/edge_$s; mkdir -p $O
X=$G/../arbnet/results/xan_${s}_slow.txt
cd $SRC/cells; export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
/home/user/asyncfpga3/cells/verify/toolchain.sh > $O/toolchain.txt 2>&1 || { echo "toolchain FAIL"; exit 1; }
if [ $s = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$s; fi
BD_SIZES=$SRC/research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw > $O/build.log 2>&1
md5sum build/hw/gcd_hw/gcd_hw.sdf build/hw/gcd_hw/gcd_hw_routed.json > $O/md5.txt
bash gls/build.sh gcd_hw > $O/gls_build.log 2>&1
cd build/gls/gcd_hw
python3 -I $G/gen_noremon.py . $X > nore.v 2> $O/nore_gen.err
POINT=1 python3 -I $G/gen_cwmon.py . $X > cwpt.v 2> $O/cwpt_gen.err
for m in nore cwpt; do
  iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o run_$m.vvp $SRC/cells/gls/tb_run.v netlist_baked.v $SRC/cells/gls/prims.v $m.v 2>&1 | grep -v procedural
  for v in $(seq 0 15); do vvp run_$m.vvp +VEC=$v +TEND=150000 +QUIET=200000 > $O/${m}_v$v.log 2>&1 & if (( v % 3 == 2 )); then wait; fi; done; wait
  for v in $(seq 0 15); do f=$O/${m}_v$v.log; r=$(grep -o "t_rst_rel=[0-9]*" $f | cut -d= -f2)
    echo "vec $v: $(grep -h '^SUMMARY' $f | cut -c1-36) events $(awk -v r=${r:-0} '/(NORE_FLIP|CW_FALL)/ && $2>r' $f | wc -l) viol $(awk -v r=${r:-0} '/(NORE_VIOL|CW_VIOL)/ && $2>r' $f | wc -l)"
    grep -E "^SUMMARY|_VIOL" $f | head -50 > $O/${m}_v$v.txt; rm -f $f
  done > $O/${m}_table.txt
done
echo "$s: md5 $(cut -c1-8 $O/md5.txt | tr '\n' ' ') nore $(awk '{e+=$(NF-2); v+=$NF} END{print e" events "v" viol"}' $O/nore_table.txt) | cwpt $(awk '{e+=$(NF-2); v+=$NF} END{print e" events "v" viol"}' $O/cwpt_table.txt) | errs0 $(grep -c 'errs=0' $O/cwpt_table.txt)/16"
