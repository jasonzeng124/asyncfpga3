#!/usr/bin/env bash
# Probe C-10n: build ONE routed design of a compiled kernel with the project's own flow,
# in a private exported copy of the tree (nothing under cells/, bdc/ or build/ of the shared
# tree is written).
#   formal/tools/kcheck/route.sh KERNEL SEED          (called by run.sh; SEED = number or d)
# Recipe = research's `bdc/fusion_bench.py --mlir <kernel> --sizes <sizes> --route` minus its
# routed GLS: bdc/emit.py (with the soak top) -> cells/flow.sh with BD_TOP_V/BD_TOP_M,
# BD_SIZES, BD_OUT, NEXTPNR_SEED, BD_DSP.  flow.sh runs its own gates (fracture, fasm_audit,
# BUFG, SETUPHOLD, zero_arcs) and toolchain.sh; a gate failure is recorded, not hidden.
# ONE deviation, in the private copy only: flow.sh passes no --freq, so the copy's nextpnr line
# gets `--freq $KCHECK_FREQ --timing-allow-fail` (CLAUDE.md: always pass --freq).  The patch is
# asserted to apply exactly once and its presence is checked in pnr.log's command echo.
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
K=$1; SEED=$2
B=$HERE/build/$K; SRC=$B/src
row=$(awk -F'\t' -v k="$K" '$1==k' "$HERE/kernels.tsv")
[ -n "$row" ] || { echo "route.sh: kernel $K not in kernels.tsv" >&2; exit 2; }
MLIR=${KCHECK_MLIR:-$(echo "$row" | cut -f2)}
SIZES=${KCHECK_SIZES:-$(echo "$row" | cut -f3)}
export BD_DSP=${BD_DSP:-$(echo "$row" | cut -f4)}
FREQ=${KCHECK_FREQ:-100}
mkdir -p "$B"
# 1. one exported source copy per kernel (git archive of HEAD: cells/, bdc/)
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
# how many size macros name an instance the emitted top actually declares (a stale sizes file
# would silently size nothing)
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
