#!/usr/bin/env bash
# C-8t negative controls: each Wip/C8t/neg/Neg*.lean must report exactly one error, at its
# "MUST FAIL" theorem (the "must SUCCEED" claims of NegStart must pass).
cd "$(dirname "$0")/../.."
export PATH=$HOME/.elan/bin:$PATH; export LEAN_PATH=$PWD/.lake/build/lib/lean
bad=0
for f in Wip/C8t/neg/Neg*.lean; do
  out=$(../slot.sh lean "$f" 2>&1 | grep -v '^\[slot')
  nerr=$(printf '%s\n' "$out" | grep -c ': error')
  want=$(grep -n -A1 'MUST FAIL' "$f" | sed -n '2p' | cut -d- -f1)
  at=$(printf '%s\n' "$out" | grep ': error' | head -1 | cut -d: -f2)
  if [ "$nerr" = 1 ] && [ "$at" = "$want" ]; then echo "$f: rejected as required (line $at)";
  else echo "$f: NOT AS REQUIRED ($nerr errors, first at line $at, want line $want)"; printf '%s\n' "$out" | head -5; bad=1; fi
done
[ $bad = 0 ] && echo "negctl: ok" || { echo "negctl: FAIL"; exit 1; }
