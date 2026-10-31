#!/usr/bin/env bash
# glsq: rerun ord_static (request pairs from the R0 INIT support) on the seed-4 scatter draws of run_scatter.sh,
# GLS rebuild only, no simulation.  Needs the seed-4 route built; checks its md5 against out2/4.  -> out2/ordscat.txt
set -u
G="$(cd "$(dirname "$0")" && pwd)"; SRC=${SRC:-$HOME/gcdsrc520}; O=$G/out2/ordscat; mkdir -p $O
cd $SRC/cells
want=$(grep routed.sdf $G/out2/seed4_s0.05_d1/provenance.txt | awk '{print $3}')
have=$(md5sum build/hw/gcd_hw/gcd_hw.sdf | awk '{print $1}')
[ "$want" = "$have" ] || { echo "ordscat: route is not seed 4 ($have != $want)"; exit 1; }
for sd in 0.05:1 0.05:2 0.05:3 0.10:1 0.10:2; do SIG=${sd%:*}; dr=${sd#*:}
  GLS_SCATTER=$SIG GLS_SCATTER_SEED=$dr bash gls/build.sh gcd_hw > $O/gls_${SIG}_d$dr.log 2>&1
  ( cd build/gls/gcd_hw && cp provenance.txt $O/prov_${SIG}_d$dr.txt && python3 -I $G/ord_static.py . > $O/ord_${SIG}_d$dr.txt )
  echo "sigma $SIG draw $dr: $(tail -1 $O/ord_${SIG}_d$dr.txt) | worst pair: $(grep FAIL $O/ord_${SIG}_d$dr.txt | sort -t' ' -k1 | head -1 | cut -c1-160)"
done | tee $O/../ordscat.txt
