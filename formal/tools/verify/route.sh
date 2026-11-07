#!/usr/bin/env bash
# Probe C-vk: kcheck/route.sh (C-10n) with the build directory moved to $VERIFY_BUILD/routes/<k>
# (default <repo>/build/verify), so verify can route without touching kcheck/build. Same flow:
# git-archived cells+bdc, bdc/emit.py, cells/flow.sh, --freq $KCHECK_FREQ (default 100 MHz).
#   formal/tools/verify/route.sh KERNEL prep|SEED     (kernel row from formal/tools/kcheck/kernels.tsv)
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd); TSV=$REPO/formal/tools/kcheck/kernels.tsv
K=$1; SEED=$2
B=${VERIFY_BUILD:-$REPO/build/verify}/routes/$K; SRC=$B/src
row=$(awk -F'\t' -v k="$K" '$1==k' "$TSV")
[ -n "$row" ] || { echo "route.sh: kernel $K not in kernels.tsv" >&2; exit 2; }
MLIR=${KCHECK_MLIR:-$(echo "$row" | cut -f2)}
SIZES=${KCHECK_SIZES:-$(echo "$row" | cut -f3)}
export BD_DSP=${BD_DSP:-$(echo "$row" | cut -f4)}
FREQ=${KCHECK_FREQ:-100}
mkdir -p "$B"
if [ ! -e "$SRC/.kcheck-rev" ]; then
  rm -rf "$SRC"; mkdir -p "$SRC"
  git -C "$REPO" archive HEAD cells bdc | tar -C "$SRC" -xf -
  n=$(grep -c -- '--router "$BD_ROUTER" \\$' "$SRC/cells/flow.sh" || true)
  [ "$n" = 1 ] || { echo "route.sh: flow.sh's nextpnr line changed ($n matches); refusing to patch" >&2; exit 2; }
  sed -i 's|--router "$BD_ROUTER" \\$|--router "$BD_ROUTER" --freq "$KCHECK_FREQ" --timing-allow-fail \\|' "$SRC/cells/flow.sh"
  grep -q -- '--freq "$KCHECK_FREQ"' "$SRC/cells/flow.sh" || { echo "route.sh: --freq patch did not apply" >&2; exit 2; }
  cp "$REPO/$MLIR" "$SRC/input.mlir"
  case "$SIZES" in
    none) : > "$SRC/sizes.vh" ;;
    research:*) git -C "$REPO" show "origin/claude/research:${SIZES#research:}" > "$SRC/sizes.vh"
                echo "$SIZES $(git -C "$REPO" rev-parse "origin/claude/research:${SIZES#research:}")" > "$SRC/sizes.src" ;;
    *) cp "$SIZES" "$SRC/sizes.vh"; echo "$SIZES $(sha256sum < "$SIZES" | cut -c1-16)" > "$SRC/sizes.src" ;;
  esac
  ( cd "$SRC" && python3 bdc/emit.py input.mlir -o top.v )
  grep -oE '^module bdc_[A-Za-z0-9_]+_top' "$SRC/top.v" | head -1 | cut -d' ' -f2 > "$SRC/top.name"
  git -C "$REPO" rev-parse HEAD > "$SRC/.kcheck-rev"
fi
TOPM=$(cat "$SRC/top.name")
if [ -s "$SRC/sizes.vh" ]; then
  used=0; tot=0
  for m in $(grep -oE '^`define BD_SZ_[A-Z0-9_]+' "$SRC/sizes.vh" | cut -d' ' -f2); do
    tot=$((tot+1)); grep -q "\`$m\b\|ifdef $m\b\|ifndef $m\b" "$SRC/top.v" && used=$((used+1))
  done
  echo "sizes: $used of $tot macros referenced by top.v" > "$B/sizes_use.txt"
fi
[ "$SEED" = prep ] && { echo "prepared $SRC (top $TOPM; $(cat "$B/sizes_use.txt" 2>/dev/null))"; exit 0; }
O=$B/s$SEED; rm -rf "$O"; mkdir -p "$O"
"$SRC/cells/verify/toolchain.sh" > "$O/toolchain.log" 2>&1 || { echo "seed $SEED: toolchain.sh FAILED: nothing routed is a result"; exit 1; }
env_seed=(); [ "$SEED" = d ] || env_seed=(NEXTPNR_SEED=$SEED)
set +e
env -u BD_RESIZE_SEEDS -u BD_NO_TIGHTEN "${env_seed[@]}" KCHECK_FREQ=$FREQ BD_DSP=$BD_DSP \
    BD_TOP_V="$SRC/top.v" BD_TOP_M="$TOPM" BD_OUT="$O/pnr" \
    $( [ -s "$SRC/sizes.vh" ] && echo BD_SIZES="$SRC/sizes.vh" || echo BD_NO_TIGHTEN=1 ) \
    timeout 4h "$SRC/cells/flow.sh" > "$O/flow.log" 2>&1
rc=$?
set -e
echo "$rc" > "$O/flow.rc"
P=$O/pnr
if [ ! -s "$P/soak.sdf" ]; then echo "seed $SEED: NO ROUTE (flow.sh exit $rc; $(grep -m1 -E 'ERROR|FAILED' "$O/flow.log" "$P/pnr.log" 2>/dev/null | head -1))"; exit 0; fi
grep -q -- "--freq" "$P/pnr.log" 2>/dev/null || grep -q "Target frequency\|frequency" "$P/pnr.log" || echo "seed $SEED: WARNING no frequency line in pnr.log"
sha256sum "$P/soak.sdf" "$P/soak_routed.json" "$P/soak.fasm" > "$O/sha.txt"
echo "seed $SEED: routed (flow.sh exit $rc$( [ "$rc" = 0 ] || echo ": $(grep -m1 -E 'FAILED|VIOLAT|zero' "$O/flow.log" | head -1)"))"
