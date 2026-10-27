#!/usr/bin/env bash
# Reproduce every GLS audit result.  Reads the research prims.v in place (read-only).
set -euo pipefail
cd "$(dirname "$0")"
P=/home/user/wt-research/cells/gls/prims.v
md5sum "$P" > prims.md5; { iverilog -V 2>&1 || true; } | head -1 > iverilog_version.txt
# 1/2: directed LUT stimuli, baked params vs $sdf_annotate
iverilog -gspecify -o lut_baked.vvp tb_lut_delay.v $P && vvp lut_baked.vvp > lut_baked.log
iverilog -gspecify -DANNOT -o lut_annot.vvp tb_lut_delay.v $P && vvp lut_annot.vvp > lut_annot.log
grep "^OUT" lut_baked.log | sort -s -k2,2 > lut_baked.out; grep "^OUT" lut_annot.log | sort -s -k2,2 > lut_annot.out
# wires: baked (-DGLS_TRANSPORT_IC, as build.sh) vs annotated (specify)
iverilog -gspecify -DGLS_TRANSPORT_IC -o ic_baked.vvp tb_ic_delay.v $P && vvp ic_baked.vvp > ic_baked.log
iverilog -gspecify -DANNOT -o ic_annot.vvp tb_ic_delay.v $P && vvp ic_annot.vvp > ic_annot.log
grep "^OUT" ic_baked.log | sort -s -k2,2 > ic_baked.out; grep "^OUT" ic_annot.log | sort -s -k2,2 > ic_annot.out
# 1: random-trace model fit
: > fit_results.txt; : > apparent_results.txt
for cfg in "0x96 124 124 124 1" "0x96 124 124 124 7" "0xE8 124 124 124 3" "0x6A 150 100 60 5" "0xE8 150 100 60 11" "0x96 516 124 60 13"; do
  set -- $cfg; L=rand_$1_$2_$3_$4_s$5.log
  iverilog -gspecify -P tb.INIT=$1 -P tb.D1=$2 -P tb.D2=$3 -P tb.D3=$4 -P tb.SEED=$5 -o r.vvp tb_lut_rand.v $P && vvp r.vvp > $L
  { echo "== $L"; python3 fit_delay.py $L $1 $2 $3 $4; } >> fit_results.txt
  if [ "$2$3$4" = 124124124 ]; then python3 apparent.py $L $1 >> apparent_results.txt; fi
done
# 4: Kleene
python3 kleene_check.py > kleene_results.txt
# 5: impact
iverilog -gspecify -o imp.vvp tb_impact.v $P && vvp imp.vvp | grep -v finish > impact_1200.log
for T in 1110 1130 1150 1170 1190 1210 1223 1225 1250; do iverilog -gspecify -P tb.TCAP=$T -o imp.vvp tb_impact.v $P && vvp imp.vvp | grep captured; done > impact_sweep.log
rm -f *.vvp vec.txt
cat fit_results.txt apparent_results.txt kleene_results.txt impact_1200.log impact_sweep.log
