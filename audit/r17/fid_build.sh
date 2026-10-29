#!/bin/bash
# usage: fid_build.sh HWDIR WORK REGION WIRE DRAW   (research build_fid.sh at efc6538, band column, region+wire scatter
#   exactly as seeds_fid.py sets it: GLS_SCATTER_REGION=REGION GLS_SCATTER=WIRE GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=DRAW)
source ~/audit-tc/openxc7/export.sh >/dev/null 2>&1
export TC=~/audit-tc XRAY_DB=~/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7
export PYTHONPATH=$TC/openxc7-src/prjxray
export GLS_SDF=$1/gcd_hw_xray.sdf GLS_SDF_FIELD=band GLS_MODEL=fid
if [ "$3" != 0 ]; then export GLS_SCATTER_REGION=$3 GLS_SCATTER=$4 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=$5; fi
echo "cmd: $(env | grep ^GLS_ | sort | tr '\n' ' ') build_fid.sh $1 $2 bit"
date; ~/r17work/wt-s9/cells/gls/fid/build_fid.sh $1 $2 bit; echo "EXIT $?"; date
