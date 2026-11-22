#!/usr/bin/env bash
# dyn_forcemc.sh OUTDIR name [name ...] -- ANALYSIS ONLY: what the LSQ tests would need if Dynamatic placed memory
# controllers instead of load-store queues.
#
# bdc/frontend.sh step 7 runs --mark-memory-interfaces, which lets Dynamatic place an LSQ where it cannot prove two
# accesses independent; bdc lowers no `lsq`. compile.sh's other branch, --force-memory-interface="force-mc=true",
# places memory controllers everywhere. This reruns steps 7 (from cf_consumed_pragmarkers.mlir) and 8 with that
# option into OUTDIR/<name>/, never into build/frontend, so no fixture changes. Then:
#   python3 research/tools/suite/dyn_blockers.py-style analysis on OUTDIR/<name>/handshake_transformed.mlir
# (research/data/suite/dyn/forcemc.tsv). Whether an MC with bdc's program-order token chain is a CORRECT substitute
# for the LSQ is not shown by this and is open (research/data/suite/dyn/README.md).
set -euo pipefail
cd "$(dirname "$0")/../../.."
OUT=$1; shift
DOPT=dynamatic/build/bin/dynamatic-opt
for n in "$@"; do
  C=build/frontend/$n/comp; O=$OUT/$n
  [ -s "$C/cf_consumed_pragmarkers.mlir" ] || { echo "$n: no frontend output (run bdc/frontend.sh $n)"; continue; }
  mkdir -p "$O"
  "$DOPT" "$C/cf_consumed_pragmarkers.mlir" --force-memory-interface="force-mc=true" > "$O/cf_mem_interface_marked.mlir"
  "$DOPT" "$O/cf_mem_interface_marked.mlir" --lower-cf-to-handshake > "$O/handshake.mlir"
  "$DOPT" "$O/handshake.mlir" \
    --handshake-deactivate-mem-dependencies --handshake-replace-memory-interfaces \
    --handshake-remove-unused-memrefs --handshake-optimize-bitwidths \
    --handshake-materialize --handshake-infer-basic-blocks > "$O/handshake_transformed.mlir"
  echo "$n: $O/handshake_transformed.mlir"
done
