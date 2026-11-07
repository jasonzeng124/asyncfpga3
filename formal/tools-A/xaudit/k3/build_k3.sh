#!/usr/bin/env bash
# Probe K3: build <k>_hw (gen_rig.py's <k>_rig.v + <k>_hw.v, the gcd_hw/collatz_hw recipe on
# ipow or xorshift) in an EXPORTED copy of the tree, outside the repo (k2/build_k2.sh generalised).
#
#   k3/build_k3.sh <kernel> [seed ...]     # seeds: "d" = no NEXTPNR_SEED, else a number
#   SRC=~/k3src_<k> OUT=~/k3out/<k> REV=HEAD NEXTPNR_FREQ=100
#
# Recipe: BD_SIZES=<sizes renamed for the rig> BDC_SELECT_PADS=<{}> BD_RLOC=v4 NEXTPNR_FREQ=100 \
#           [NEXTPNR_SEED=N] ./hw/build_hw.sh <k>_hw
# Differences from K2 (collatz): --freq 100 is passed (build_hw.sh's NEXTPNR_FREQ; CLAUDE.md
# "always pass --freq"; gcd_hw/collatz_hw were built without it); BD_DSP is build_hw.sh's
# default (1, the shipped config: ipow's two muli map to DSP48E1).
# Sizes (research data, identical blobs on HEAD and origin/claude/research, = C-10n's):
#   ipow     research/data/ipow_dsp1_sizes_T9.vh (3c6a8aa1)   xorshift research/data/xorshift_sizes_T3.vh (9a9008d4)
# renamed BD_SZ_UUT_<X> -> BD_SZ_URIG_UDUT_<X>; harness (BD_SZ_UPIPE_*) lines dropped.  Measured on
# fusion_bench's soak harness, not on this rig: re-audited here, not assumed.
set -euo pipefail
K3="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$K3/../../../.." && pwd)"
K=$1; shift
case $K in
  ipow) SZ=research/data/ipow_dsp1_sizes_T9.vh ;;
  xorshift) SZ=research/data/xorshift_sizes_T3.vh ;;
  *) echo "kernel ipow|xorshift"; exit 2 ;;
esac
U=$(echo $K | tr a-z A-Z)
SRC=${SRC:-$HOME/k3src_$K}
OUT=${OUT:-$HOME/k3out/$K}
REV=${REV:-HEAD}
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
export NEXTPNR_FREQ=${NEXTPNR_FREQ:-100}

if [ ! -e "$SRC/.k3-rev" ]; then
    mkdir -p "$SRC"
    git -C "$REPO" archive "$REV" | tar -C "$SRC" -xf -
    git -C "$REPO" rev-parse "$REV" > "$SRC/.k3-rev"
    mkdir -p "$SRC/build/frontend"
    cp -r "$SRC/cloud/fixtures/frontend/$K" "$SRC/build/frontend/$K"
fi
python3 "$K3/gen_rig.py" $K "$SRC/cells/hw/" > /dev/null

python3 - "$SRC/cells/hw/build_hw.sh" $K $U <<'PY'
import sys
p, k, U = sys.argv[1:4]; s = open(p).read()
if f"{k}_hw)" not in s:
    case = r'''@K@_hw)
    # probe K3 (formal/tools-A/xaudit/k3): the gcd_hw case with bdc_@K@, no probes.
    KERNEL=../build/gen/@K@_kernel.v
    SRCS="rtl/*.v $KERNEL hw/@K@_rig.v hw/$TOP.v"
    mkdir -p ../build/gen
    ( cd .. && python3 bdc/emit.py \
        build/frontend/@K@/comp/handshake_transformed.mlir \
        --no-top -o build/gen/@K@_kernel.v )
    if [ -n "${BD_SIZES:-}" ] && [ "$BD_SIZES" != none ]; then
        mkdir -p build/gen
        python3 - "$KERNEL" build/gen/@K@_hw_dut_params.vh <<'PY2'
import re, sys
src, out = sys.argv[1:3]
ps = re.findall(r"parameter\s+DELAY_(\w+)\s*=\s*(\d+)", open(src).read())
if not ps:
    sys.exit(f"{src}: no DELAY_ parameters -- nothing to size")
m = lambda i: "BD_SZ_URIG_UDUT_" + i.upper()
lines = [f"`ifndef {m(i)}\n `define {m(i)} {d}\n`endif" for i, d in ps]
lines.append("`define @U@_DUT_PARAMS " + ", ".join(f".DELAY_{i}(`{m(i)})" for i, _ in ps))
open(out, "w").write("\n".join(lines) + "\n")
PY2
        SRCS="rtl/*.v $KERNEL $BD_SIZES build/gen/@K@_hw_dut_params.vh hw/@K@_rig.v hw/$TOP.v"
        echo "build_hw.sh: applying $(grep -c '^`define' "$BD_SIZES") measured delay size(s) from $BD_SIZES" >&2
    fi
    ;;
'''.replace("@K@", k).replace("@U@", U)
    assert "multn_ps)\n" in s
    s = s.replace("multn_ps)\n", case + "multn_ps)\n", 1)
    open(p, "w").write(s)
PY

SIZES="$SRC/research/data/${K}_hw_sizes_rig.vh"
{ echo "// $SZ renamed for ${K}_rig (uut -> urig.udut), harness lines dropped (probe K3)"
  grep '^`define BD_SZ_UUT_' "$SRC/$SZ" | sed 's/BD_SZ_UUT_/BD_SZ_URIG_UDUT_/'
} > "$SIZES"
echo '{}' > "$SRC/cells/hw/${K}_hw_pads.json"

mkdir -p "$OUT"
T=${K}_hw
for s in "${@:-d}"; do
    "$SRC/cells/verify/toolchain.sh" > "$OUT/toolchain_$s.txt" 2>&1 || { echo "toolchain.sh FAILED: no result"; cat "$OUT/toolchain_$s.txt"; exit 1; }
    rm -rf "$SRC/cells/build/hw/$T"
    (
      cd "$SRC/cells"
      if [ "$s" = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$s; fi
      BD_SIZES=$SIZES BDC_SELECT_PADS=$SRC/cells/hw/${K}_hw_pads.json BD_RLOC=v4 \
        ./hw/build_hw.sh $T
    ) > "$OUT/build_$s.log" 2>&1 || echo "seed $s: build_hw.sh exit $? (see $OUT/build_$s.log; the bitstream step fails without textx)"
    mkdir -p "$OUT/$s"
    for f in ${T}_routed.json $T.sdf $T.json $T.fasm pnr.log toolchain.txt synth.log rloc.log; do
        [ -e "$SRC/cells/build/hw/$T/$f" ] && cp "$SRC/cells/build/hw/$T/$f" "$OUT/$s/"
    done
    ( cd "$OUT/$s" && md5sum $T.sdf ${T}_routed.json 2>/dev/null || echo "NO ROUTE: $(grep -m1 ERROR pnr.log)" ) | sed "s|^|$s |"
    grep -m1 -o "target frequency [0-9.]* MHz" "$OUT/$s/pnr.log" 2>/dev/null | sed "s|^|$s |" || true
done
