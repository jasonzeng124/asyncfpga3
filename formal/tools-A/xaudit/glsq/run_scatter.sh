#!/usr/bin/env bash
# glsq: the GLS of the route currently built in $SRC/cells/build/hw/gcd_hw, with GLS_SCATTER=$SIG and draws
# $DRAWS; per draw: gls/build.sh, QQuiet monitor on 16 vectors, ord_static.   run_scatter.sh <tag>
set -u
G="$(cd "$(dirname "$0")" && pwd)"; SRC=${SRC:-$HOME/gcdsrc520}; OUT=${OUT:-$G/out2}; tag=$1
for dr in ${DRAWS:-1 2 3}; do
  o=$OUT/${tag}_s${SIG}_d$dr; mkdir -p $o
  cd $SRC/cells && GLS_SCATTER=$SIG GLS_SCATTER_SEED=$dr bash gls/build.sh gcd_hw > $o/gls_build.log 2>&1
  cd build/gls/gcd_hw; cp provenance.txt $o/
  python3 -I $G/gen_qqmon.py . > qqmon.v 2> $o/qqmon_gen.err
  iverilog -gspecify -DGLS_TRANSPORT_IC -I. -o run_qq.vvp $SRC/cells/gls/tb_run.v netlist_baked.v $SRC/cells/gls/prims.v qqmon.v 2>&1 | grep -v procedural
  python3 -I $G/ord_static.py . > $o/ord_static.txt
  for v in $(seq 0 15); do vvp run_qq.vvp +VEC=$v +TEND=150000 +QUIET=200000 > $o/qq_v$v.log 2>&1 & if (( v % 3 == 2 )); then wait; fi; done; wait
  for v in $(seq 0 15); do f=$o/qq_v$v.log; tr=$(grep -o "t_rst_rel=[0-9]*" $f | cut -d= -f2)
    echo "vec $v: $(grep -h '^SUMMARY' $f | cut -c1-40) flips $(grep -c QQ_FLIP $f) viol_after_rst $(awk -v r=${tr:-0} '/QQ_VIOL/ && $2>r' $f | wc -l)"
    grep -E "^SUMMARY|^QQ_VIOL|^RESULT" $f > $o/qq_v$v.txt; rm -f $f
  done > $o/qq_table.txt
  echo "$tag sigma $SIG draw $dr: errs0 $(grep -c 'errs=0' $o/qq_table.txt)/16 flips $(grep -o 'flips [0-9]*' $o/qq_table.txt | awk '{a+=$2}END{print a}') viol_after_rst $(grep -o 'viol_after_rst [0-9]*' $o/qq_table.txt | awk '{a+=$2}END{print a}') | ord $(tail -1 $o/ord_static.txt)"
done
