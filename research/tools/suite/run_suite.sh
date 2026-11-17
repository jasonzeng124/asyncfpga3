#!/usr/bin/env bash
# run_suite.sh [-j JOBS] [-s "SEEDS"] [-d NDRAWS] [-m MAXIT] [KERNEL...] -- the one command for the compiler suite
# (PROGRAM "A benchmark suite for the compiler", owner 2026-11-17): every kernel through the automatic path
# (research/tools/suite/suite_one.sh: BDC_AUTO=1, the flow's own sizing, the draws, the metrics) on every seed, JOBS at
# a time, then the table (suite_table.py) into $RUNS/suite/TABLE.md.  KERNEL defaults to the suite's list,
# research/tools/suite/kernels.txt (one name per line; the rows of kernels/SUITE.md).  Defaults: seeds "1 2 3 4" (the
# four-seed rule), 4 draws per route, MAXIT 4, JOBS 4.  Each job holds one route or one simulation at a time; the GLS
# compiles share research/tools/compile_slot.sh's slots.
set -uo pipefail
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/home/user/runs}; export RUNS
J=4; SEEDS="1 2 3 4"; ND=4; MAXIT=4
while getopts "j:s:d:m:" o; do case $o in j) J=$OPTARG;; s) SEEDS=$OPTARG;; d) ND=$OPTARG;; m) MAXIT=$OPTARG;; *) exit 2;; esac; done
shift $((OPTIND - 1))
KS=("$@"); [ ${#KS[@]} -gt 0 ] || mapfile -t KS < <(grep -v '^#' "$R/research/tools/suite/kernels.txt" | awk 'NF {print $1}')
mkdir -p "$RUNS/suite"; export CA_JOBS=${CA_JOBS:-2} DRAW_JOBS=${DRAW_JOBS:-2}
for k in "${KS[@]}"; do for s in $SEEDS; do echo "$k $s"; done; done |
  xargs -P "$J" -L 1 bash -c '"$0" "$1" "$2" '"$ND $MAXIT"' > /dev/null 2>&1' "$R/research/tools/suite/suite_one.sh"
files=(); for k in "${KS[@]}"; do for s in $SEEDS; do files+=("$RUNS/suite/${k}_$s/result.txt"); done; done
python3 "$R/research/tools/suite/suite_table.py" "${files[@]}" | tee "$RUNS/suite/TABLE.md"
