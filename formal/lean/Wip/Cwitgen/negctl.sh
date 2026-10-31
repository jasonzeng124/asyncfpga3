#!/usr/bin/env bash
# C-witgen negative controls: each file must be rejected exactly at the theorem after its
# "MUST FAIL" comment, and nowhere else. Regenerate with formal/tools/capwit3/gen_neg3.py.
set -uo pipefail
cd "$(dirname "$0")/../../.."     # formal/
ok=1
for f in NegSettled NegInit; do
  p=Wip/Cwitgen/neg/$f.lean
  want=$(awk '/MUST FAIL/{getline; print NR; exit}' lean/$p)
  got=$(./slot.sh lake env lean $p 2>&1 | grep -o "^$p:[0-9]*:[0-9]*: error" | cut -d: -f2 | sort -u | tr '\n' ' ')
  if [ "$got" = "$want " ]; then echo "$f: rejected at line $want only (ok)"; else echo "$f: FAILED (errors at: $got; wanted $want)"; ok=0; fi
done
[ $ok = 1 ] && echo "negctl: ok" || { echo "negctl: FAIL"; exit 1; }
