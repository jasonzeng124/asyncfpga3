#!/usr/bin/env bash
# glsq: rebuild gcd_hw R5 at one seed in the exported tree $SRC (git archive 520a43f), build the research GLS,
# run the QQuiet monitor on 16 vectors and ord_static.  run_seed.sh <seed|d>   -> $OUT/<seed>/...
set -u
G="$(cd "$(dirname "$0")" && pwd)"; SRC=${SRC:-$HOME/gcdsrc520}; OUT=${OUT:-$G/out}
s=$1; mkdir -p $OUT/$s
cd $SRC/cells; export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
/home/user/asyncfpga3/cells/verify/toolchain.sh > $OUT/$s/toolchain.txt 2>&1 || { echo "toolchain FAIL"; exit 1; }
if [ $s = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$s; fi
BD_SIZES=$SRC/research/data/gcd_hw_sizes_R5.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw > $OUT/$s/build.log 2>&1
md5sum build/hw/gcd_hw/gcd_hw.sdf build/hw/gcd_hw/gcd_hw_routed.json > $OUT/$s/md5.txt
bash gls/build.sh gcd_hw > $OUT/$s/gls_build.log 2>&1
cd build/gls/gcd_hw
cp provenance.txt $OUT/$s/
python3 -I $G/gen_qqmon.py . > qqmon.v 2> $OUT/$s/qqmon_gen.err
iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o run_qq.vvp $SRC/cells/gls/tb_run.v netlist_baked.v $SRC/cells/gls/prims.v qqmon.v 2>&1 | grep -v procedural
python3 -I $G/ord_static.py . > $OUT/$s/ord_static.txt
for v in $(seq 0 15); do vvp run_qq.vvp +VEC=$v +TEND=150000 +QUIET=200000 > $OUT/$s/qq_v$v.log 2>&1 & if (( v % 3 == 2 )); then wait; fi; done; wait
for v in $(seq 0 15); do f=$OUT/$s/qq_v$v.log; tr=$(grep -o "t_rst_rel=[0-9]*" $f | cut -d= -f2)
  echo "vec $v: $(grep -h '^SUMMARY' $f | cut -c1-40) flips $(grep -c QQ_FLIP $f) viol_after_rst $(awk -v r=${tr:-0} '/QQ_VIOL/ && $2>r' $f | wc -l) viol_before $(awk -v r=${tr:-0} '/QQ_VIOL/ && $2<=r' $f | wc -l)"
done > $OUT/$s/qq_table.txt
# keep only the summary and violation lines of the logs (they are large)
for v in $(seq 0 15); do grep -E "^SUMMARY|^QQ_VIOL|ANNOTATE|SDF (WARN|ERR)" $OUT/$s/qq_v$v.log > $OUT/$s/qq_v$v.txt; rm -f $OUT/$s/qq_v$v.log; done
echo "$s: flips $(grep -o "flips [0-9]*" $OUT/$s/qq_table.txt | awk "{a+=\$2}END{print a}") viol_after_rst $(grep -o "viol_after_rst [0-9]*" $OUT/$s/qq_table.txt | awk "{a+=\$2}END{print a}") | ord $(tail -1 $OUT/$s/ord_static.txt)"
