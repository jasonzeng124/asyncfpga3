#!/usr/bin/env bash
# Probe C-10n: the verified timing checker on any compiled kernel, row by row against the
# project's own post-route rules.
#
#   formal/tools/kcheck/run.sh KERNEL [SEED...]        (default seeds: 1 2 3 4)
#
# KERNEL is a row of kernels.tsv (mlir, sizes file, BD_DSP); KCHECK_MLIR / KCHECK_SIZES override.
#  0. cells/verify/toolchain.sh (exit on failure; fingerprint -> results/<k>/toolchain.txt);
#     the tcheck snapshot (build/tcheck_snap: a copy of formal/tools/tcheck's Lean package,
#     built with slot.sh, sync.sh --check run on the original) and its toy/cert self-tests
#  1. route.sh KERNEL prep, then route.sh KERNEL SEED, at most KCHECK_JOBS (default 2) nextpnr
#     jobs at once (SKIP_ROUTE=1 reuses existing routes)
#  2. check.sh KERNEL SEED for every routed seed (KCHECK_JOBS at once)
#  3. summarize.py, pointcheck.py (fixed-point margins of the disagreeing rows), summarize.py
#     again -> results/<k>/{agree,disagree,rows,routes,pointcheck}.tsv, summary.txt
# Env: KCHECK_FRONT_REV (git rev of tcheck's Python front end to snapshot, default HEAD, or
#      "worktree"), KCHECK_FREQ (MHz, default 100), KCHECK_FRONT (tcheck front-end dir, default ../tcheck),
#      KCHECK_EXE (tcheck binary), KCHECK_TAG (suffix for check outputs and results, e.g.
#      "postfix": build/<k>/s<seed>/check_<tag>/, results/<k>_<tag>/), BD_DSP.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
K=${1:?usage: run.sh KERNEL [SEED...]}; shift
SEEDS=${*:-1 2 3 4}
JOBS=${KCHECK_JOBS:-2}
R=$HERE/results/$K${KCHECK_TAG:+_$KCHECK_TAG}; mkdir -p "$R" "$HERE/build/$K"
export PATH=$HOME/.elan/bin:$PATH
"$REPO/cells/verify/toolchain.sh" > "$R/toolchain.txt" 2>&1 || { cat "$R/toolchain.txt"; echo "toolchain.sh FAILED: nothing routed is a result"; exit 1; }
"$HOME/dev2/lib/fpgatoolchain/openxc7/bin/nextpnr-xilinx" --version >> "$R/toolchain.txt" 2>&1
grep -E "sha256|Version" "$R/toolchain.txt"
SNAP=$HERE/build/tcheck_snap
if [ -z "${KCHECK_EXE:-}" ]; then
  "$HERE/../tcheck/sync.sh" --check > /dev/null || { echo "tcheck sync.sh --check: DRIFT"; exit 1; }
  if [ ! -x "$SNAP/.lake/build/bin/tcheck" ]; then
    rm -rf "$SNAP"; mkdir -p "$SNAP"
    ( cd "$HERE/../tcheck" && cp -r lakefile.toml lean-toolchain lake-manifest.json Main.lean Tcheck Formal test "$SNAP/" )
    ( cd "$SNAP" && FORMAL_SLOT_CWD=$SNAP "$REPO/formal/slot.sh" lake build 2>&1 | grep -E "error|Build completed" ) || exit 1
  fi
  EXE=$SNAP/.lake/build/bin/tcheck
  for t in toy toycert; do
    "$EXE" "$SNAP/test/$t.tc" 2>/dev/null | diff -q - "$SNAP/test/$t.expected" > /dev/null \
      && echo "  $t self-test ok" || { echo "  $t self-test FAILED"; exit 1; }
  done
  echo "tcheck snapshot $(cd "$SNAP" && cat Main.lean Tcheck/*.lean Formal/*/*.lean | sha256sum | cut -c1-16)" >> "$R/toolchain.txt"
fi
# front-end snapshot: tcheck's Python front end is edited by other probes while this runs, so
# every check of this run uses one frozen copy (the helper dirs it imports are symlinked so that
# extract.py's HERE.parent lookups still resolve)
if [ -z "${KCHECK_FRONT:-}" ]; then
  T=$HERE/build/tools; mkdir -p "$T"
  ln -sfn "$REPO/formal/tools/fasm2lean" "$T/fasm2lean"; ln -sfn "$REPO/formal/tools/prjxdelay" "$T/prjxdelay"
  FS=$T/front_${K}_$(date -u +%m%d%H%M%S); mkdir -p "$FS"
  REV=${KCHECK_FRONT_REV:-HEAD}       # a git rev (default HEAD: reproducible), or "worktree"
  if [ "$REV" = worktree ]; then cp "$HERE/../tcheck/"*.py "$FS/"
  else for f in $(git -C "$REPO" ls-tree --name-only "$REV" formal/tools/tcheck/ | grep '\.py$'); do
         git -C "$REPO" show "$REV:$f" > "$FS/$(basename "$f")"; done
       echo "front end from git $REV = $(git -C "$REPO" rev-parse --short "$REV")" | tee -a "$R/toolchain.txt"; fi
  export KCHECK_FRONT=$FS
fi
( cd "$KCHECK_FRONT" && echo "front end $KCHECK_FRONT: $(cat *.py | sha256sum | cut -c1-16);" \
  "vs git HEAD: $(for f in *.py; do git -C "$REPO" show HEAD:formal/tools/tcheck/$f 2>/dev/null | cmp -s - $f || printf '%s ' "$f"; done)" \
  "(listed files differ from HEAD); OUTMUX driver hop (C-10m) present: $(grep -q NO_DRVHOP extract.py && echo yes || echo no)" ) | tee -a "$R/toolchain.txt"
"$HERE/route.sh" "$K" prep || exit 1
if [ -z "${SKIP_ROUTE:-}" ]; then
  printf '%s\n' $SEEDS | xargs -P "$JOBS" -I{} "$HERE/route.sh" "$K" {}
fi
printf '%s\n' $SEEDS | xargs -P "$JOBS" -I{} "$HERE/check.sh" "$K" {}
python3 "$HERE/summarize.py" "$K" $SEEDS > /dev/null      # disagree.tsv for pointcheck
python3 "$HERE/pointcheck.py" "$K" > /dev/null
python3 "$HERE/summarize.py" "$K" $SEEDS
