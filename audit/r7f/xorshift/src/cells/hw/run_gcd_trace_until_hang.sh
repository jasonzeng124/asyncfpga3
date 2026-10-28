#!/usr/bin/env bash
# Catch an INTERMITTENT gcd batch hang and report which state it hung in.
#
#   hw/run_gcd_trace_until_hang.sh [n] [attempts]
#
# The hang this chases is intermittent: on the same bitstream and the same
# seed, a 64-run batch either finishes in ~40k aclk cycles (~410 us) or parks
# forever at a random run index (16, 26, 61 observed).  A single trace run is
# therefore not evidence of anything -- a green one only means this attempt
# was one of the good ones.  This loops until it CATCHES a bad one, then
# stops, because the whole point is the o_req_s bit at the moment of the hang:
#
#   o_req_s = 1 -> parked in S_RTZ    (request raised, never returned to zero)
#   o_req_s = 0 -> parked in S_WAIT_RES (no request ever observed)
#
# Self-reporting: it prints its own verdict and exits nonzero only when it
# fails to learn anything (no hang seen in the budget), so a green exit here
# means "hang caught and characterised", NOT "board is healthy".
set -u
cd "$(dirname "$0")/.."   # -> cells/

N=${1:-64}
ATTEMPTS=${2:-8}
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
BIT=build/hw/gcd_bench_gen/gcd_bench_gen.bit
[ -x "$XSDB" ] || { echo "missing xsdb at $XSDB"; exit 2; }
[ -e "$BIT" ]  || { echo "missing $BIT"; exit 2; }

hangs=0; passes=0
for i in $(seq 1 "$ATTEMPTS"); do
    log=/tmp/trace_hunt_${i}.log
    echo "=== attempt $i/$ATTEMPTS (n=$N) -> $log ==="
    hw/board.sh "$XSDB" hw/xsdb_gcd_trace.tcl "$BIT" 0xACE12345 "$N" > "$log" 2>&1
    v=$(grep -m1 '^VERDICT:' "$log" || echo "VERDICT: (none -- run produced no verdict)")
    echo "  $v"
    if echo "$v" | grep -q 'COMPLETED'; then
        passes=$((passes + 1))
        continue
    fi
    hangs=$((hangs + 1))
    echo
    echo "################ HANG CAUGHT on attempt $i ################"
    sed -n '/=== gcd batch trace/,$p' "$log"
    echo "###########################################################"
    echo
    echo "SUMMARY: caught a hang after $passes clean batch(es) in $i attempt(s)."
    echo "         The o_req_s column above is the answer; the VERDICT block"
    echo "         says which half of the handshake it implicates."
    exit 0
done

echo
echo "SUMMARY: $passes/$ATTEMPTS batches completed and NO hang was caught."
echo "         That is NOT a clean bill of health -- the hang is intermittent"
echo "         and was seen 3 times earlier today at n=64 and n=8000. It means"
echo "         this budget was too small; re-run with more attempts, or with a"
echo "         larger n (a longer batch has more runs to hang on)."
exit 1
