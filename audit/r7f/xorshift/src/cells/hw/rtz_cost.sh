#!/usr/bin/env bash
# What does the RETURN-TO-ZERO half of the four-phase handshake cost?
#
# gen_bench.py runs two counters over the same batch.  lat_ctr starts at
# S_ISSUE and stops when the result is captured; cycles keeps counting through
# S_ACK, S_RTZ and S_NEXT.  So (cycles/run - latmin) is the tail: the harness
# acknowledging, the KERNEL lowering o_req, and the FSM getting back to S_PREP.
#
# The interesting term is the middle one.  A four-phase matched delay is paid on
# BOTH edges -- the request edge and the return to zero -- so this tail should
# scale with how much matched delay the kernel carries, and the null (one
# deliberate bd_delay #(.N(10))) should be the floor.  That is a prediction,
# which is why it is worth measuring rather than asserting.
#
# ONLY A ROW WITH latmin == latmax GIVES AN EXACT TAIL.  cycles/run is a mean
# over the batch and latmin is a minimum over it, so where the latency varies
# run to run the difference is inflated by however far the mean sits above the
# min -- which for xorshift at 256 rounds is 7 cycles of pure artefact.  The
# table below prints EXACT or approx per row; only take the exact ones
# seriously, and get more of them by choosing an input the kernel handles
# deterministically.
#
# One pass, FIXED N=200, 3 batches per target, oracle asserted on each.
set -u
cd "$(dirname "$0")/.."
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
CLK=${CLK:-0x00100A00}
TARGETS=${*:-gcd_null ipow_null collatz_null isprime_null xorshift ipow collatz collatz64 isprime gcd}
OUT=build/hw/rtz_cost.tsv
printf 'target\tcycles_per_run\tlatmin\tlatmax\ttail\texact\n' > "$OUT"
printf '%-14s %12s %8s %8s %8s %7s\n' target cycles/run latmin latmax tail exact
for T in $TARGETS; do
    case "$T" in
        *_null) K=${T%_null}; BIT=build/hw/${T}_bench_gen/${T}_bench_gen.bit ;;
        *)      K=$T;         BIT=${BITOVERRIDE_XORSHIFT:-}
                if [ "$T" = xorshift ] && [ -n "${BITOVERRIDE_XORSHIFT:-}" ]; then BIT=$BITOVERRIDE_XORSHIFT
                else BIT=build/hw/${T}_bench_gen/${T}_bench_gen.bit; fi ;;
    esac
    [ -e "$BIT" ] || { echo "  $T: no bitstream"; continue; }
    read -r GOLD OP0 OP1 <<<"$(awk -v k="$T" '$1==k {print $2, $3, $4; exit}' hw/golden_sig.txt)"
    LOG=build/hw/_rtz_${T}.log
    if ! hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "$T" 200 "$CLK" "$GOLD" "$OP0" "$OP1" 3 > "$LOG" 2>&1; then
        echo "  $T FAILED"; grep -m1 "ORACLE FAILED\|ERROR" "$LOG" || tail -3 "$LOG"; continue
    fi
    read -r CPR LO HI <<<"$(awk '/^[0-9]+\t[0-9]+\t/ {n++; s+=$2; if(lo==""||$4<lo)lo=$4; if($5>hi)hi=$5} END {printf "%.3f %s %s", s/n/200, lo, hi}' "$LOG")"
    TAIL=$(python3 -c "print(f'{$CPR - $LO:.3f}')")
    EXACT=$([ "$LO" = "$HI" ] && echo EXACT || echo approx)
    printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$T" "$CPR" "$LO" "$HI" "$TAIL" "$EXACT" >> "$OUT"
    printf '%-14s %12s %8s %8s %8s %7s\n' "$T" "$CPR" "$LO" "$HI" "$TAIL" "$EXACT"
done
echo "wrote $OUT"
