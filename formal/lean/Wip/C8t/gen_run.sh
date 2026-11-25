#!/usr/bin/env bash
# C-8t: regenerate Formal/Net/CapstoneWitnessRun.lean (needs CapstoneWitnessTok built).
#   Wip/C8t/gen_run.sh          # writes the file
#   Wip/C8t/gen_run.sh --check  # compares with the file on disk
set -euo pipefail
cd "$(dirname "$0")/../.."
export PATH=$HOME/.elan/bin:$PATH; export LEAN_PATH=$PWD/.lake/build/lib/lean
tmp=$(mktemp)
../slot.sh lean Wip/C8t/RunGen.lean > "$tmp"
grep -m1 "^firings" "$tmp" >&2
sed -n '/^import/,$p' "$tmp" > "$tmp.lean"
if [ "${1:-}" = "--check" ]; then
  cmp -s "$tmp.lean" Formal/Net/CapstoneWitnessRun.lean && echo "gen_run: ok" || { echo "gen_run: DRIFT"; exit 1; }
else
  cp "$tmp.lean" Formal/Net/CapstoneWitnessRun.lean; echo "wrote Formal/Net/CapstoneWitnessRun.lean"
fi
rm -f "$tmp" "$tmp.lean"
