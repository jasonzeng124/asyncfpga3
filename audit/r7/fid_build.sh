#!/bin/bash
# usage: fid_build.sh HWDIR WORK COL   (research's build_fid.sh with the full stack env)
source ~/audit-tc/openxc7/export.sh >/dev/null 2>&1
export TC=~/audit-tc XRAY_DB=~/audit-tc/openxc7/share/nextpnr/prjxray-db/zynq7
export PYTHONPATH=$TC/openxc7-src/prjxray
export GLS_SDF=$1/gcd_hw_xray.sdf GLS_SDF_FIELD=$3 GLS_MODEL=fid
echo "cmd: GLS_SDF=$GLS_SDF GLS_SDF_FIELD=$3 GLS_MODEL=fid ~/wt-r7x/cells/gls/fid/build_fid.sh $1 $2 bit"
date; ~/wt-r7x/cells/gls/fid/build_fid.sh $1 $2 bit; echo "EXIT $?"; date
