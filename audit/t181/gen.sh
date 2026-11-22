#!/bin/bash
# gen.sh MLIR OUTDIR [extra env...]: regenerate formal's Lean file for xorshift from MLIR with the item-43 knobs
M=$(readlink -f $1); O=$2; shift 2
RS=/root/wt-r181; H=/root/wt-f181/formal/tools-A/rewrite
FX=$(mktemp -d /root/t181/fx.XXXX); mkdir -p $FX/xorshift/comp; cp $M $FX/xorshift/comp/handshake_transformed.mlir
REL=$(python3 -c "import os,sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))" $FX $RS/cloud/fixtures)
mkdir -p $O
env BDC_AUTO=1 BDC_AUTO_REWRITES=0 BDC_FORK_OUT_LINK=n11__0,n32__2 "$@" AP_DEC=1 FIXDIR=$REL NSUF=BQ TAILN=5 $H/ringfuse_autoproof.sh $RS $O xorshift
