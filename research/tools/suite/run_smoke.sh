#!/usr/bin/env bash
# run_smoke.sh SEED JOBS KERNEL... -- research/tools/suite/smoke.sh for every KERNEL in both flows (default, then
# BDC_AUTO=1), JOBS at a time (the cores your budget gives you). Makes the two build trees first, once: a plain copy of
# cells/ bdc/ build/frontend as research/data/alltable/run_default.sh makes; the auto tree also gets
# research/tools/fifteen/pre_{dec,eq2}.py for bdc/auto.py's MLIR rewrites. Vectors: kernels/K/vec.hex, expected values
# kernels/K/vec.exp (research/tools/suite/oracle.sh). One line per route appended to $RUNS/smoke.txt.
set -euo pipefail
S=$1; J=$2; shift 2
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:?set RUNS}; export R S RUNS
for F in default auto; do
  T=$RUNS/tree_$F
  [ -d "$T/cells" ] && continue
  mkdir -p "$T/build"; cp -r "$R/cells" "$R/bdc" "$T/"; cp -r "$R/build/frontend" "$T/build/"; rm -rf "$T/cells/build"
  if [ "$F" = auto ]; then
    mkdir -p "$T/research/tools/fifteen"; cp "$R/research/tools/fifteen/"pre_{dec,eq2}.py "$T/research/tools/fifteen/"
  fi
done
for K in "$@"; do echo "$K default"; echo "$K auto"; done | xargs -P "$J" -L 1 bash -c \
  '"$R/research/tools/suite/smoke.sh" "$0" "$S" "$1" "$R/kernels/$0/vec.hex" "$R/kernels/$0/vec.exp" >> "$RUNS/smoke.txt" 2>&1'
