#!/bin/sh
# run.sh OUTDIR -- the whole independent liveness check: validation (34 configs) + every fixture x {def, auto, autorw}
# x {floor on, off}; writes OUTDIR/{validation.jsonl,results.jsonl,RESULTS.md,graphs/}.  python3 only.
# Knobs: LIVE_RS (research tree, default /home/user/rs), LIVE_FIXTURES, LIVE_JOBS (2), LIVE_MEM_GB (2.5 per process),
# LIVE_TIMEOUT (900 s per search), LIVE_MAX_STATES (3000000), LIVE_ONLY (comma list of fixtures).
set -e
OUT=${1:?usage: run.sh OUTDIR}
HERE=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
rm -f "$OUT/results.jsonl" "$OUT/validation.jsonl"
python3 "$HERE/validate.py" "$OUT"
python3 "$HERE/run_all.py" "$OUT"
python3 "$HERE/gen_md.py" "$OUT"
echo "wrote $OUT/RESULTS.md"
