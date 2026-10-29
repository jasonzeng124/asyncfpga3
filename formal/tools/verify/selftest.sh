#!/usr/bin/env bash
# Self-test of formal/tools/verify (probe C-vk). Positive runs must PASS, negative controls
# must FAIL with a printed counterexample. Logs go to $OUT (default build/verify/selftest).
#   formal/tools/verify/selftest.sh            # everything (~15-25 min, mostly Lean on gcd)
#   formal/tools/verify/selftest.sh --quick    # no Lean (search, transcription skipped, capnet, tcheck)
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; ROOT="$(cd "$HERE/../../.." && pwd)"
OUT=${OUT:-$ROOT/build/verify/selftest}; mkdir -p "$OUT"
Q=""; [ "${1:-}" = --quick ] && Q="--no-lean"
FIX=$ROOT/cloud/fixtures/frontend
fail=0
expect() {  # expect NAME WANT_RC GREP_PATTERN -- verify args...
  local name=$1 want=$2 pat=$3; shift 4
  "$HERE/verify.sh" "$@" --out "$OUT/$name" > "$OUT/$name.log" 2>&1; local rc=$?
  local v; v=$(grep -E '^(summary|VERDICT)' "$OUT/$name.log" | tr '\n' ' ')
  local rcok=0; { [ "$want" = X ] && [ "$rc" != 1 ]; } || [ "$rc" = "$want" ] && rcok=1
  if [ $rcok = 1 ] && grep -qE "$pat" "$OUT/$name.log"; then echo "ok    $name (exit $rc) $v"
  else echo "WRONG $name: exit $rc (want $want), pattern '$pat' $(grep -cE "$pat" "$OUT/$name.log") hits; $v"; fail=1; fi
}
P=0; [ -n "$Q" ] && P=2      # without Lean a positive run is "not proved" (exit 2)

# positives
expect gcd       $P 'token search: PASS'                      -- gcd $Q --route "$HERE/test/pass.tc"
expect ipow      $P 'token search: PASS'                      -- ipow $Q
expect collatz   $P 'token search: PASS'                      -- collatz $Q
expect xorshift  2  'token search: PASS'                      -- xorshift $Q
# negative control 1: gcd with subi1's operands swapped (0 - diff -> diff - 0)
python3 "$HERE/mutate.py" "$FIX/gcd/comp/handshake_transformed.mlir" "$OUT/gcd_subi1.mlir" --swap subi1 2>/dev/null
expect neg-gcd-subi1 1 'COUNTEREXAMPLE  input'                -- gcd $Q --mlir "$OUT/gcd_subi1.mlir" --vecs "35,14 12,18 48,180"
# negative control 2: ipow against a wrong C reference
expect neg-ipow-wrongC 1 'COUNTEREXAMPLE  input'              -- ipow $Q --c "$HERE/test/ipow_wrong.c" --no-cap
# negative control 3: ipow with the shift amount constant2 (e >> 1) changed to 2
python3 "$HERE/mutate.py" "$FIX/ipow/comp/handshake_transformed.mlir" "$OUT/ipow_c2.mlir" --const constant2=2 2>/dev/null \
  && expect neg-ipow-const 1 'COUNTEREXAMPLE  input'          -- ipow $Q --mlir "$OUT/ipow_c2.mlir"
# negative control 4 (timing): tcheck's toy obligations (one FAIL, one ILLFORMED row)
expect neg-timing 1 'COUNTEREXAMPLE ROW  toy-fail'            -- ipow --no-lean --no-cap --route "$ROOT/formal/tools/tcheck/test/toy.tc"
# equivalent mutant (subi0 swapped: |b-a| = |a-b|): no counterexample may be reported
python3 "$HERE/mutate.py" "$FIX/gcd/comp/handshake_transformed.mlir" "$OUT/gcd_subi0.mlir" --swap subi0 2>/dev/null
# (exit 2 = not proved is the honest outcome: the hand proof is syntactic and need not survive;
#  stage 2d still proves the vectors)
expect equiv-gcd-subi0 X 'token search: PASS'                 -- gcd $Q --mlir "$OUT/gcd_subi0.mlir" --no-cap --vecs "12,18 35,14 48,180"
# the reduction is exact for terminal stores: reduced and full search agree (ipow, small vectors)
for m in "" "--no-por"; do
  python3 "$HERE/tokensearch.py" "$FIX/ipow/comp/handshake_transformed.mlir" --c "$ROOT/kernels/ipow/ipow.c" \
    --func ipow --vecs "3,7 7,-2 -3,5" --terminals $m | grep '^  terminal' > "$OUT/terms$m.txt"
done
cmp -s "$OUT/terms.txt" "$OUT/terms--no-por.txt" && echo "ok    reduced == full search terminal stores (ipow, 3 vectors)" \
  || { echo "WRONG reduced and full search differ"; fail=1; }
[ $fail -eq 0 ] && echo "selftest: OK" || echo "selftest: FAIL"
exit $fail
