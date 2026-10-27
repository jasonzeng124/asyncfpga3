#!/usr/bin/env bash
# C-8y drift check for the capnet pipeline (seconds; no Lean):
#  1. gcd regression: capnet.py with the gcd profile reproduces C-8l's CapstoneLinks.lean,
#     C-8m's CapstoneNet.lean and C-8r's spL byte for byte (the generalisation changed nothing).
#  2. ipow drift: regenerating IpowCapLinks/Ring/Net and re-instantiating the 8 copied proof
#     files from the CURRENT gcd sources gives the committed IpowCap*.lean (so a change in bdc,
#     the MLIR, or a gcd proof file shows up here).
#     (`capnet.py walktab` also reproduces C-8s's walkgen.py tables for gcd.)
#  3. H_WALK on vectors (now also PROVED in IpowCapWalk.lean; the vector check stays as a cross-check) (walkcheck.py), plus its two negative controls (must FAIL).
#   formal/tools/capnet/check.sh [--kernel ipow]
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
NET="$HERE/../../lean/Formal/Net"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
fail=0
python3 "$HERE/capnet.py" --kernel gcd --gcd-compat links -o "$TMP/l.lean" 2>/dev/null
python3 "$HERE/capnet.py" --kernel gcd --gcd-compat net -o "$TMP/n.lean" 2>/dev/null
python3 "$HERE/capnet.py" --kernel gcd --gcd-compat spine > "$TMP/s.txt" 2>/dev/null
cmp -s "$TMP/l.lean" "$NET/CapstoneLinks.lean" && echo "[capnet] gcd links: identical to C-8l" || { echo "[capnet] gcd links DIFFER"; fail=1; }
cmp -s "$TMP/n.lean" "$NET/CapstoneNet.lean" && echo "[capnet] gcd net: identical to C-8m" || { echo "[capnet] gcd net DIFFERS"; fail=1; }
[ "$(cat "$TMP/s.txt")" = "$(sed -n 's/^def spL : List Bool := //p' "$NET/CapstoneCutSpine.lean")" ] \
  && echo "[capnet] gcd spine: identical to C-8r" || { echo "[capnet] gcd spine DIFFERS"; fail=1; }
python3 "$HERE/capnet.py" --kernel gcd walktab > "$TMP/w.txt" 2>/dev/null
python3 -I "$HERE/../../lean/Wip/C8s/walkgen.py" > "$TMP/w8s.txt" 2>/dev/null
diff -q -B "$TMP/w.txt" "$TMP/w8s.txt" >/dev/null && echo "[capnet] gcd walk tables: identical to C-8s's walkgen" \
  || { echo "[capnet] gcd walk tables DIFFER from C-8s"; fail=1; }
K=ipow; P=IpowCap
mkdir -p "$TMP/k"
python3 "$HERE/capnet.py" --kernel $K links -o "$TMP/k/${P}Links.lean" 2>/dev/null || fail=1
python3 "$HERE/capnet.py" --kernel $K ring -o "$TMP/k/${P}Ring.lean" 2>/dev/null || fail=1
python3 "$HERE/capnet.py" --kernel $K net -o "$TMP/k/${P}Net.lean" 2>/dev/null || fail=1
python3 "$HERE/instantiate.py" --kernel $K --out-dir "$TMP/k" 2>/dev/null || { echo "[capnet] instantiate FAILED"; fail=1; }
for f in "$TMP"/k/*.lean; do
  b=$(basename "$f")
  cmp -s "$f" "$NET/$b" && echo "[capnet] $K: $b matches" || { echo "[capnet] $K: DRIFT in $b"; diff "$NET/$b" "$f" | head -5; fail=1; }
done
out=$(python3 "$HERE/walkcheck.py" --kernel $K 20 | tail -1)
grep -q "walkcheck: ok" <<<"$out" \
  && echo "[capnet] $K: walkcheck ok (H_WALK on 55 vectors)" || { echo "[capnet] $K: walkcheck FAILED"; fail=1; }
for n in 1 2; do
  out=$(NEG=$n python3 "$HERE/walkcheck.py" --kernel $K 2 | tail -1)
  grep -q FAILURES <<<"$out" \
    && echo "[capnet] $K: walkcheck negative control NEG=$n fails as it must ($out)" || { echo "[capnet] NEG=$n did not fail"; fail=1; }
done
[ $fail -eq 0 ] && echo "[capnet] OK" || echo "[capnet] FAIL"
exit $fail
