#!/usr/bin/env bash
# Probe C-10n: on ONE routed design (route.sh's output), run the project's own post-route rules
# and tcheck's rule families, and compare them row by row.
#   formal/tools/kcheck/check.sh KERNEL SEED          (called by run.sh)
# Project rules (cells/verify, from the exported copy, as fusion_bench runs them):
#   tighten.py SDF (A, H, I, F, D...), skew.py SDF -v (E, every gate), arb_fork.py SDF (J)
# tcheck (formal/tools/tcheck): extract.py --rules2 AEFJWR --cert (the C-10h run4.sh
# configuration: H, I, A, E/E0, F/Fc, J0/Jx/Jp, W, R/Rc, Hc), then the compiled checker.
# Comparison: tcheck's compare.py (H, I, Hc vs tighten) and kcheck/compare2k.py (A, E, F, J).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
K=$1; SEED=$2
B=$HERE/build/$K; SRC=$B/src; O=$B/s$SEED; P=$O/pnr
FRONT=${KCHECK_FRONT:-$HERE/../tcheck}
EXE=${KCHECK_EXE:-$HERE/build/tcheck_snap/.lake/build/bin/tcheck}
[ -s "$P/soak.sdf" ] || { echo "seed $SEED: no route"; exit 0; }
C=$O/check${KCHECK_TAG:+_$KCHECK_TAG}; mkdir -p "$C"
SDF=$P/soak.sdf
( cd "$SRC/cells" && python3 verify/tighten.py "$SDF" > "$C/tighten.log" 2>&1; echo $? > "$C/tighten.rc"
  python3 verify/skew.py "$SDF" -v > "$C/skew_v.log" 2>&1; echo $? > "$C/skew.rc"
  python3 verify/arb_fork.py "$SDF" > "$C/arbfork.log" 2>&1; echo $? > "$C/arbfork.rc" )
python3 "$FRONT/extract.py" "$P" soak --cells "$SRC/cells" --rules2 AEFJWR --cert \
    --out "$C/obl.tc" --json "$C/obl.json" 2> "$C/extract.log" \
    || { echo "seed $SEED: extract FAILED"; tail -5 "$C/extract.log"; exit 1; }
"$EXE" "$C/obl.tc" > "$C/t.out" 2> "$C/t.err" || { echo "seed $SEED: tcheck exit $?"; tail -3 "$C/t.err"; }
grep -E "^[HI] " "$C/t.out" > "$C/thi.out"
grep -E "^Hc " "$C/t.out" | sed 's/^Hc /H /' > "$C/thc.out"
python3 "$FRONT/compare.py" "$C/thi.out" "$C/tighten.log" --tsv "$C/compare_hi.tsv" > "$C/compare_hi.log"
python3 "$FRONT/compare.py" "$C/thc.out" "$C/tighten.log" --tsv "$C/compare_hc.tsv" > "$C/compare_hc.log"
python3 "$HERE/compare2k.py" "$C" > "$C/compare2.log"
rm -f "$C/obl.tc.gz"; gzip -f "$C/obl.tc"        # ~100s of MB; kept compressed for diag.py
echo "seed $SEED: $(grep '^extract:' "$C/extract.log" | tail -1) / $(tail -1 "$C/t.err")"
