#!/usr/bin/env bash
# C-8s negative controls: mutated copies of CapstoneWalkTab must be REJECTED by kernel decide.
#  Neg1: the lab2 oracle check expects the label of the OTHER input (kk == bn (c != y)).
#  Neg2: acc251 marked adj (as if on every path through group 251).
#  Neg3: the walk's steer select inverted relative to the run (grp t == gf, grp f == gt).
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; LEAN="$HERE/../.."
T="$LEAN/Formal/Net/CapstoneWalkTab.lean"
export PATH=$HOME/.elan/bin:$PATH
tmp=$(mktemp -d); rc=0
run() { name=$1; shift
  python3 - "$T" "$tmp/$name.lean" "$@" <<'PY'
import sys
s=open(sys.argv[1]).read(); n=0
for i in range(3, len(sys.argv), 2):
    old, new = sys.argv[i], sys.argv[i+1]
    assert old in s, old; s=s.replace(old, new, 1)
open(sys.argv[2],'w').write(s)
PY
  if (cd "$LEAN" && ../slot.sh lake env lean "$tmp/$name.lean" 2>&1 | grep -q "error"); then echo "$name: rejected (ok)"; else echo "$name: ACCEPTED (BAD)"; rc=1; fi; }
run Neg1 ".lab2 gi => gi == idx && al z == [res] && kk == bn (c == y)" ".lab2 gi => gi == idx && al z == [res] && kk == bn (c != y)"
python3 - <<PY
PY
ACCN=$(python3 -c "print(463)")
run Neg2 "def adj (c : Fin NC) : Bool := adjL.getD c.val true" "def adj (c : Fin NC) : Bool := if c.val = $ACCN then true else adjL.getD c.val true"
run Neg3 "grp t == gt && grp f == gf" "grp t == gf && grp f == gt"
rm -rf "$tmp"; exit $rc
