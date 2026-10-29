#!/usr/bin/env bash
# genonly.sh GENPY OUTDIR REGION WIRE [K=V...]: run a gen.py on s2x's inputs, print md5 of netlist_baked.v
set -u
G=$1; O=$2; REG=$3; WIRE=$4; shift 4
S=/root/r19work/s2x; mkdir -p $O; cp $S/routed.json $S/routed.sdf $O/
cp $G /root/wt-r19/cells/gls/gen_audit_tmp.py
export GLS_WORK=$O GLS_SDF_FIELD=band GLS_MODEL=fid
unset GLS_SDF
if [ "$REG" != 0 ]; then export GLS_SCATTER_REGION=$REG GLS_SCATTER=$WIRE GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1; fi
for kv in "$@"; do export "$kv"; done
cd $O && python3 /root/wt-r19/cells/gls/gen_audit_tmp.py > gen.out 2>&1; echo "rc $? $(md5sum < netlist_baked.v | cut -c1-8)"
rm -f /root/wt-r19/cells/gls/gen_audit_tmp.py
