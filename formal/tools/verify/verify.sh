#!/usr/bin/env bash
# verify (probe C-vk): from a kernel's handshake MLIR to a proof or a counterexample trace.
#   formal/tools/verify/verify.sh KERNEL [--mlir FILE] [--c FILE] [--vecs "a,b a,b"]
#                                 [--route DIR_OR_TC ...] [--out DIR] [--no-lean] [--no-cap]
# KERNEL is a key of formal/tools/verify/kernels.py. See formal/notes/C-vk-verify.md.
# Exit 0 PASS, 1 FAIL (counterexample or failed check), 2 not proved.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
exec python3 "$HERE/verify.py" "$@"
