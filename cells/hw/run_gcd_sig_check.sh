#!/usr/bin/env bash
# Step 2 of the measurement task: host-independent validation of gcd on the
# board before trusting any latency number from it.
#
#   hw/run_gcd_sig_check.sh [seed_hex] [n]
#
# Computes the expected SIG/LASTOP0/LASTOP1 in Python (host_gcd_replay.py,
# an independent re-derivation from the same LFSR seed -- see that file's
# header) and hands them to xsdb_gcd_sig_check.tcl, which programs the
# board, runs the SAME UNIFORM-mode batch, and asserts board==host itself
# (self-reporting PASS/FAIL, no human reads a register dump). Takes the
# board lock via board.sh.
set -eu
cd "$(dirname "$0")/.."   # -> cells/

SEED=${1:-0xACE12345}
N=${2:-64}

BIT=build/hw/gcd_bench_gen/gcd_bench_gen.bit
[ -e "$BIT" ] || { echo "missing $BIT -- build it first: hw/build_bench.sh gcd"; exit 2; }

echo "== host replica (seed=$SEED n=$N) =="
EXP=$(python3 hw/host_gcd_replay.py "$SEED" "$N")
echo "$EXP"
EXP_SIG=$(echo "$EXP" | awk -F= '/^SIG=/{print $2}')
EXP_OP0=$(echo "$EXP" | awk -F= '/^LASTOP0=/{print $2}')
EXP_OP1=$(echo "$EXP" | awk -F= '/^LASTOP1=/{print $2}')

XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
[ -x "$XSDB" ] || { echo "missing xsdb at $XSDB"; exit 2; }

echo
echo "== board run + self-assert =="
hw/board.sh "$XSDB" hw/xsdb_gcd_sig_check.tcl "$BIT" "$SEED" "$N" "$EXP_SIG" "$EXP_OP0" "$EXP_OP1"
