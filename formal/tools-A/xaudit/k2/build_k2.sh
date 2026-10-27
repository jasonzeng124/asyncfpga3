#!/usr/bin/env bash
# Probe K2: build collatz_hw (k2/collatz_rig.v + k2/collatz_hw.v, the gcd_hw recipe on the
# collatz kernel) in an EXPORTED copy of the tree, outside the repo, so nothing in the shared
# tree is written (no worktree: `git worktree add` writes .git).
#
#   k2/build_k2.sh [seed ...]        # seeds: "d" = no NEXTPNR_SEED, else a number
#   SRC=~/k2src OUT=~/k2out REV=HEAD
#
# Recipe = BOARD-QUEUE #2's gcd_hw command with the kernel swapped:
#   BD_SIZES=<collatz T3 sizes, renamed for the rig> BDC_SELECT_PADS=<{}> BD_RLOC=v4 \
#     [NEXTPNR_SEED=N] ./hw/build_hw.sh collatz_hw            (no --freq, as #2)
# build_hw.sh has no collatz_hw case, so the exported copy gets one, a copy of the gcd_hw
# case without --probe (patch_build_hw below).  Sizes: research/data/collatz_sizes_T3.vh
# (route-measured on fusion_bench's soak harness, instance `uut`), renamed
# BD_SZ_UUT_<X> -> BD_SZ_URIG_UDUT_<X>; the BD_SZ_UPIPE_* (harness spine) lines dropped.
# Pads: {} = bdc/emit.py's default SELECT_PAD on every select, which is what the T3 build used
# (fusion_bench sets no BDC_SELECT_PADS).  The T3 sizes were audited on THAT harness's routes,
# not on these: rules A/E/... are re-run here (audit_k2.sh) and reported, not assumed.
set -euo pipefail
K2="$(cd "$(dirname "$0")" && pwd)"
REPO="$(cd "$K2/../../../.." && pwd)"
SRC=${SRC:-$HOME/k2src}
OUT=${OUT:-$HOME/k2out}
REV=${REV:-HEAD}
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}

if [ ! -e "$SRC/.k2-rev" ]; then
    mkdir -p "$SRC"
    git -C "$REPO" archive "$REV" | tar -C "$SRC" -xf -
    git -C "$REPO" rev-parse "$REV" > "$SRC/.k2-rev"
    mkdir -p "$SRC/build/frontend"
    cp -r "$SRC/cloud/fixtures/frontend/collatz" "$SRC/build/frontend/collatz"
fi
cp "$K2/collatz_rig.v" "$K2/collatz_hw.v" "$SRC/cells/hw/"

python3 - "$SRC/cells/hw/build_hw.sh" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()
if "collatz_hw)" not in s:
    case = r'''collatz_hw)
    # probe K2 (formal/tools-A/xaudit/k2): the gcd_hw case with bdc_collatz, no probes.
    KERNEL=../build/gen/collatz_kernel.v
    SRCS="rtl/*.v $KERNEL hw/collatz_rig.v hw/$TOP.v"
    mkdir -p ../build/gen
    ( cd .. && python3 bdc/emit.py \
        build/frontend/collatz/comp/handshake_transformed.mlir \
        --no-top -o build/gen/collatz_kernel.v )
    if [ -n "${BD_SIZES:-}" ] && [ "$BD_SIZES" != none ]; then
        mkdir -p build/gen
        python3 - "$KERNEL" build/gen/collatz_hw_dut_params.vh <<'PY2'
import re, sys
src, out = sys.argv[1:3]
ps = re.findall(r"parameter\s+DELAY_(\w+)\s*=\s*(\d+)", open(src).read())
if not ps:
    sys.exit(f"{src}: no DELAY_ parameters -- nothing to size")
m = lambda i: "BD_SZ_URIG_UDUT_" + i.upper()
lines = [f"`ifndef {m(i)}\n `define {m(i)} {d}\n`endif" for i, d in ps]
lines.append("`define COLLATZ_DUT_PARAMS " + ", ".join(f".DELAY_{i}(`{m(i)})" for i, _ in ps))
open(out, "w").write("\n".join(lines) + "\n")
PY2
        SRCS="rtl/*.v $KERNEL $BD_SIZES build/gen/collatz_hw_dut_params.vh hw/collatz_rig.v hw/$TOP.v"
        echo "build_hw.sh: applying $(grep -c '^`define' "$BD_SIZES") measured delay size(s) from $BD_SIZES" >&2
    fi
    ;;
'''
    s = s.replace("multn_ps)\n", case + "multn_ps)\n", 1)
    open(p, "w").write(s)
PY

SIZES="$SRC/research/data/collatz_hw_sizes_T3rig.vh"
{ echo "// research/data/collatz_sizes_T3.vh renamed for collatz_rig (uut -> urig.udut), harness lines dropped (probe K2)"
  grep '^`define BD_SZ_UUT_' "$SRC/research/data/collatz_sizes_T3.vh" | sed 's/BD_SZ_UUT_/BD_SZ_URIG_UDUT_/'
} > "$SIZES"
echo '{}' > "$SRC/cells/hw/collatz_hw_pads.json"

mkdir -p "$OUT"
for s in "${@:-d}"; do
    "$SRC/cells/verify/toolchain.sh" > "$OUT/toolchain_$s.txt" 2>&1 || { echo "toolchain.sh FAILED: no result"; cat "$OUT/toolchain_$s.txt"; exit 1; }
    rm -rf "$SRC/cells/build/hw/collatz_hw"
    (
      cd "$SRC/cells"
      if [ "$s" = d ]; then unset NEXTPNR_SEED; else export NEXTPNR_SEED=$s; fi
      BD_SIZES=$SIZES BDC_SELECT_PADS=$SRC/cells/hw/collatz_hw_pads.json BD_RLOC=v4 \
        ./hw/build_hw.sh collatz_hw
    ) > "$OUT/build_$s.log" 2>&1 || echo "seed $s: build_hw.sh exit $? (see $OUT/build_$s.log; the bitstream step fails without textx)"
    mkdir -p "$OUT/$s"
    for f in collatz_hw_routed.json collatz_hw.sdf collatz_hw.json collatz_hw.fasm pnr.log toolchain.txt synth.log rloc.log; do
        [ -e "$SRC/cells/build/hw/collatz_hw/$f" ] && cp "$SRC/cells/build/hw/collatz_hw/$f" "$OUT/$s/"
    done
    ( cd "$OUT/$s" && md5sum collatz_hw.sdf collatz_hw_routed.json 2>/dev/null || echo "NO ROUTE: $(grep -m1 ERROR pnr.log)" ) | sed "s|^|$s |"
done
