#!/bin/bash
# usage: fid_build.sh WT HWDIR WORK COL   (research's build_fid.sh ... bit with the full stack env)
source ~/audit-tc/openxc7/export.sh >/dev/null 2>&1
export TC=~/audit-tc XRAY_DB=~/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7
export PYTHONPATH=$TC/openxc7-src/prjxray
export GLS_SDF=$2/gcd_hw_xray.sdf GLS_SDF_FIELD=$4 GLS_MODEL=fid
echo "cmd: GLS_SDF=$GLS_SDF GLS_SDF_FIELD=$4 GLS_MODEL=fid $1/cells/gls/fid/build_fid.sh $2 $3 bit"
date; $1/cells/gls/fid/build_fid.sh $2 $3 bit; echo "EXIT $?"; date
