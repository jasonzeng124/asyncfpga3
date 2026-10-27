#!/usr/bin/env bash
# audit: run C-10c pipeline from the 55fde94 snapshot, max 2 concurrent routes
source ~/auditlogs/export_dev2.sh
cd /home/user/asyncfpga3/audit/p2py/f10c/formal/tools/prjxdelay
for t in ro_top ro_many_top; do
  for pair in "default 1" "2 3"; do
    for s in $pair; do [ -s build/${t}_s$s/$t.sdf ] || ./route.sh $t $s & done; wait
  done
done
for t in ro_top ro_many_top; do
  for pair in "default 1" "2 3"; do
    for s in $pair; do python3 ringdelay.py build/${t}_s$s $t --json build/${t}_s$s/prjx.json > build/${t}_s$s/prjx.txt & done; wait
  done
done
M="build/ro_many_top_sdefault/prjx.json build/ro_many_top_s1/prjx.json build/ro_many_top_s2/prjx.json build/ro_many_top_s3/prjx.json"
T="build/ro_top_sdefault/prjx.json build/ro_top_s1/prjx.json build/ro_top_s2/prjx.json build/ro_top_s3/prjx.json"
python3 analyze.py $M -- $T > build/analysis.txt
python3 analyze.py --prepatch $M -- $T > build/analysis_prepatch.txt
python3 analyze.py --extra $M -- $T > build/analysis_extra.txt
sha256sum build/*/*.fasm | cut -c1-16
echo DONE
