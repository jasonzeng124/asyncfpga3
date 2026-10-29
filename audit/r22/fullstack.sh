#!/bin/bash
# Full stack as seeds_fid.py's sim(): build_fid.sh HW WORK bit, then run_fid.sh WORK -j 1,
# env GLS_SDF=<xray sdf> GLS_SDF_FIELD=$COL GLS_MODEL=fid PYTHONPATH=prjxray. Only difference: build_fid_mon.sh
# (= build_fid.sh + the passive r22mon.v monitor). WORK under /root (vvp files stay out of the repo).
# usage: fullstack.sh HW WORK COL LOGDIR
source /root/audit-tc/openxc7/export.sh
HW=$1; WORK=$2; COL=${3:-max}; LOGDIR=$4
export GLS_SDF=$HW/gcd_hw_xray.sdf GLS_SDF_FIELD=$COL GLS_MODEL=fid PYTHONPATH=/root/audit-tc/openxc7-src/prjxray
mkdir -p $LOGDIR
/usr/bin/time -v /home/user/asyncfpga3/audit/r22/mon/build_fid_mon.sh $HW $WORK bit > $LOGDIR/build_fid.log 2>&1
echo "build rc=$?" >> $LOGDIR/build_fid.log
ls -la $WORK/run_baked.vvp >> $LOGDIR/build_fid.log || exit 1
/root/wt-r22/cells/gls/fid/run_fid.sh $WORK -j 1 > $LOGDIR/run_fid.log 2>&1
echo "run rc=$?" >> $LOGDIR/run_fid.log
mkdir -p $LOGDIR/sweep; cp $WORK/sweep/v*.log $LOGDIR/sweep/; cp $WORK/provenance.txt $WORK/fid/equiv.txt $WORK/r22sig.vh $LOGDIR/ 2>/dev/null
