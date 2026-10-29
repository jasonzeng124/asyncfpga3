#!/usr/bin/env bash
# Probe C-11g: route a compiled kernel STANDALONE (the soak top of bdc/emit.py) with the
# recipe of formal/tools/kcheck/route.sh (C-10n: cells/flow.sh with BD_TOP_V/BD_TOP_M,
# research's sizes, BD_DSP, private git-archive copy, --freq patched into the copy's nextpnr
# line), then make the .bit from nextpnr's FASM and READ IT BACK as route.sh (11f) does.
#   formal/tools/fasm2lean3/kroute.sh KERNEL SEED       (KERNEL a row of kcheck/kernels.tsv)
# Outputs: build/k_<KERNEL>/s<SEED>/ (large), fixture/<KERNEL>_<SEED>.* (small, reviewable).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
K=$1; SEED=$2
B=$HERE/build/k_$K; SRC=$B/src; FIX=$HERE/fixture; mkdir -p "$B" "$FIX"
row=$(awk -F'\t' -v k="$K" '$1==k' "$REPO/formal/tools/kcheck/kernels.tsv")
[ -n "$row" ] || { echo "kroute.sh: kernel $K not in kcheck/kernels.tsv" >&2; exit 2; }
MLIR=$(echo "$row" | cut -f2); SIZES=$(echo "$row" | cut -f3)
export BD_DSP=$(echo "$row" | cut -f4)
FREQ=100
if [ ! -e "$SRC/.rev" ]; then
  rm -rf "$SRC"; mkdir -p "$SRC"
  git -C "$REPO" archive HEAD cells bdc | tar -C "$SRC" -xf -
  n=$(grep -c -- '--router "$BD_ROUTER" \\$' "$SRC/cells/flow.sh" || true)
  [ "$n" = 1 ] || { echo "kroute.sh: flow.sh's nextpnr line changed ($n matches); refusing to patch" >&2; exit 2; }
  sed -i 's|--router "$BD_ROUTER" \\$|--router "$BD_ROUTER" --freq "$KCHECK_FREQ" --timing-allow-fail \\|' "$SRC/cells/flow.sh"
  grep -q -- '--freq "$KCHECK_FREQ"' "$SRC/cells/flow.sh" || { echo "kroute.sh: --freq patch did not apply" >&2; exit 2; }
  cp "$REPO/$MLIR" "$SRC/input.mlir"
  case "$SIZES" in
    none) : > "$SRC/sizes.vh" ;;
    research:*) git -C "$REPO" show "origin/claude/research:${SIZES#research:}" > "$SRC/sizes.vh"
                echo "$SIZES $(git -C "$REPO" rev-parse "origin/claude/research:${SIZES#research:}")" > "$SRC/sizes.src" ;;
    *) cp "$REPO/$SIZES" "$SRC/sizes.vh" ;;
  esac
  ( cd "$SRC" && python3 bdc/emit.py input.mlir -o top.v )
  grep -oE '^module bdc_[A-Za-z0-9_]+_top' "$SRC/top.v" | head -1 | cut -d' ' -f2 > "$SRC/top.name"
  git -C "$REPO" rev-parse HEAD > "$SRC/.rev"
fi
TOPM=$(cat "$SRC/top.name")
O=$B/s$SEED; rm -rf "$O"; mkdir -p "$O"
"$SRC/cells/verify/toolchain.sh" > "$O/toolchain.log" 2>&1 || { cat "$O/toolchain.log"; echo "toolchain.sh FAILED: nothing routed is a result"; exit 1; }
env_seed=(); [ "$SEED" = d ] || env_seed=(NEXTPNR_SEED=$SEED)
set +e
env -u BD_RESIZE_SEEDS -u BD_NO_TIGHTEN "${env_seed[@]}" KCHECK_FREQ=$FREQ BD_DSP=$BD_DSP \
    BD_TOP_V="$SRC/top.v" BD_TOP_M="$TOPM" BD_OUT="$O/pnr" \
    $( [ -s "$SRC/sizes.vh" ] && echo BD_SIZES="$SRC/sizes.vh" || echo BD_NO_TIGHTEN=1 ) \
    timeout 2h "$SRC/cells/flow.sh" > "$O/flow.log" 2>&1
rc=$?
set -e
echo "$rc" > "$O/flow.rc"
P=$O/pnr
[ -s "$P/soak.fasm" ] || { echo "$K seed $SEED: NO ROUTE (flow.sh exit $rc)"; exit 1; }
F=$O/$K
cp "$P/soak.fasm" "$F.fasm"; cp "$P/soak.json" "$F.json"; cp "$P/soak_routed.json" "$F.routed.json"; cp "$P/soak.xdc" "$F.xdc"
PRJ=$TC/openxc7-src/prjxray; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PART=xc7z010clg400-1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/fasm2frames.py" \
    --db-root "$DB" --part "$PART" "$F.fasm" > "$F.frames" 2> "$F.frames.log"
"$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$PART/part.yaml" --part_name "$PART" \
    --frm_file "$F.frames" --output_file "$F.bit" > "$F.bit.log" 2>&1
PYTHONPATH="$PRJ:$PRJ/third_party/fasm" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" --part "$PART" \
    --bitread "$TC/openxc7/bin/bitread" "$F.bit" > "$F.fromBit.fasm" 2> "$F.bit2fasm.log"
X=$FIX/${K}_$SEED
{ echo "nextpnr sha256  $(sha256sum "$TC/openxc7/bin/nextpnr-xilinx" | cut -c1-16)"; cat "$O/toolchain.log"; } > "$X.toolchain"
grep -E "fasm_audit|FASM AUDIT" "$O/flow.log" | tail -3 > "$X.audit" || true
{ echo "flow.sh exit $rc"; grep -E "freq|Max frequency|PASS|FAIL" "$P/pnr.log" | tail -6; } > "$X.pnr" || true
python3 "$HERE/trim.py" --kernel "$K" "$SEED"     # fixture/<K>_<SEED>.{synth.json,hint.json,fasm,fromBit.fasm}.xz, .xdc
( cd "$O" && sha256sum "$K.fasm" "$K.fromBit.fasm" "$K.json" "$K.bit" ) > "$X.sha256"
echo "$K seed $SEED: routed (flow.sh exit $rc), .bit read back"
