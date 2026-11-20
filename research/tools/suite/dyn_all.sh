#!/usr/bin/env bash
# dyn_all.sh OUTROOT KERNEL... -- Dynamatic's own circuit for each kernel, exported, checked and routed:
#   1. buffers as research/tools/suite/dynamatic_est.py places them (on-merges, then canonicalize / hoist), then
#      dynamatic-opt --lower-handshake-to-hw;
#   2. research/tools/suite/dyn_export.py (our export-rtl for the integer subset);
#   3. dynamatic_est.py on the kernel's suite vectors (the C checks every result) and research/tools/suite/dyn_vsim.py:
#      the exported Verilog in iverilog on the same calls, results and cycles against the estimator's;
#   4. research/tools/suite/dyn_route.sh on placer seeds DYN_SEEDS (default 1 2 3 4).
# Writes OUTROOT/K/{hw.mlir, v/, est.txt, vsim.txt, route/, route.txt} and one summary line per kernel to stdout:
#   K | export ok|FAILED | vsim N calls D differ | period mean (range) n | cycles per iteration (the estimator's)
set -uo pipefail
OR=$1; shift
R=$(cd "$(dirname "$0")/../../.." && pwd)
DYN=${DYN:-$HOME/dynamatic}; DOPT=$DYN/build/bin/dynamatic-opt
for K in "$@"; do
  W=$OR/$K; rm -rf "$W"; mkdir -p "$W"
  FX=$R/build/frontend/$K/comp/handshake_transformed.mlir
  [ -f "$FX" ] || { echo "$K | no fixture"; continue; }
  "$DOPT" "$FX" --handshake-set-buffering-properties=version=fpga20 \
      "--handshake-place-buffers=algorithm=on-merges timing-models=$DYN/data/components.json" > "$W/buffered.mlir" 2> "$W/dopt.err" \
    && "$DOPT" "$W/buffered.mlir" --handshake-canonicalize --handshake-hoist-ext-instances > "$W/export.mlir" 2>> "$W/dopt.err" \
    && "$DOPT" "$W/export.mlir" --lower-handshake-to-hw > "$W/hw.mlir" 2>> "$W/dopt.err" \
    || { echo "$K | dynamatic-opt FAILED ($(tail -1 "$W/dopt.err" | cut -c1-100))"; continue; }
  python3 "$R/research/tools/suite/dyn_export.py" "$W/hw.mlir" "$W/v" > "$W/export.log" 2>&1 \
    || { echo "$K | export FAILED ($(tail -1 "$W/export.log" | cut -c1-140))"; continue; }
  case $K in
    xorshift) V=research/data/eventgraph/gate/xor19.hex;; collatz) V=research/data/eventgraph/gate/col18.hex;;
    collatz64) V=research/data/eventgraph/gate/c6419.hex;; ipow) V=research/data/eventgraph/gate/ipow17.hex;;
    isprime) V=research/data/alltable/isp17.hex;; gcd) V=research/data/eventgraph/gate/gcd18.hex;;
    *) V=kernels/$K/vec.hex; [ -f "$R/$V" ] || V=research/data/suite/vec/$K.hex;;
  esac
  ( cd "$R" && timeout 3600 python3 research/tools/suite/dynamatic_est.py "$K" "$V" ) > "$W/est.txt" 2>&1
  cpi=$(grep -oP '^cycles per iteration: \K[0-9.]+' "$W/est.txt" | head -1)
  vs=$(timeout 3600 python3 "$R/research/tools/suite/dyn_vsim.py" "$W/v" "$K" "$W/est.txt" > "$W/vsim.txt" 2>&1; tail -1 "$W/vsim.txt" | cut -c1-120)
  "$R/research/tools/suite/dyn_route.sh" "$K" "$W/v" "$W/route" ${DYN_SEEDS:-1 2 3 4} > "$W/route.txt" 2>&1
  echo "$K | export ok | $vs | $(tail -1 "$W/route.txt") | est cycles per iteration ${cpi:-NA}"
done
