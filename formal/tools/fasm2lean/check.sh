#!/usr/bin/env bash
# Track 11b end to end, from the committed fixtures (no routing needed):
#
#     formal/tools/fasm2lean/check.sh          (~1 min; ./route.sh SEED re-routes)
#
# 1. For seeds 1..4: extract the physical netlist from nextpnr's FASM AND from
#    the FASM read back out of the .bit (bitread + bit2fasm); they must be the
#    same netlist (same INITs, same pin sources).  The Lean data is generated
#    from the read-back one: Formal/Net/Fasm/CePairS<n>.lean.
# 2. Compile Formal/Net/Fasm/{Basic,CePairS1..4,CePair}.lean, check the textual
#    scan and that every theorem uses only propext / Quot.sound.
# 3. Negative controls, made in the BITS (FASM features), not in Lean:
#    (a) one INIT bit of the q1 LUT flipped, (b) two INT pips re-pointed so
#    the q1 LUT's pins B2/B3 swap rst and b.  Each is extracted the same way
#    into Wip/C11b/ and `Spec` must be DISPROVED by decide (the import sees it).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN=$(cd "$HERE/../../lean" && pwd)
FIX=$HERE/fixture
TMP=${TMPDIR:-/tmp}/fasm2lean.$$; mkdir -p "$TMP"; trap 'rm -rf "$TMP"' EXIT
F2L="python3 $HERE/fasm2lean.py"
fail=0

echo "== 1. FASM vs bitstream read-back =="
for s in 1 2 3 4; do
    $F2L "$FIX/ce_pair_s$s.fasm" "$HERE/ce_pair.xdc" --ns CePairS$s --json "$TMP/a$s.json" > /dev/null 2> "$TMP/a$s.log" \
        || { cat "$TMP/a$s.log"; fail=1; continue; }
    $F2L "$FIX/ce_pair_s$s.fromBit.fasm" "$HERE/ce_pair.xdc" --ns CePairS$s --json "$TMP/b$s.json" \
        --out "$LEAN/Formal/Net/Fasm/CePairS$s.lean" 2> "$TMP/b$s.log" || { cat "$TMP/b$s.log"; fail=1; continue; }
    if python3 - "$TMP/a$s.json" "$TMP/b$s.json" <<'EOF'
import json, sys
a, b = (json.load(open(f)) for f in sys.argv[1:])
key = lambda r: (r["inputs"], [(l["site"], l["init"], [p["src"] for p in l["pins"]]) for l in r["luts"]],
                 [(o["port"], o["src"]) for o in r["outs"]])
sys.exit(0 if key(a) == key(b) else 1)
EOF
    then echo "  seed $s: same netlist from FASM and from .bit  ($(tail -1 "$TMP/b$s.log" | sed 's/fasm2lean: //'))"
    else echo "  seed $s: FASM and .bit DISAGREE"; fail=1; fi
done

echo "== 2. Lean =="
export PATH=$HOME/.elan/bin:$PATH
cd "$LEAN"; export LEAN_PATH=$PWD/.lake/build/lib/lean
mkdir -p .lake/build/lib/lean/Formal/Net/Fasm .lake/build/lib/lean/Wip/C11b
python3 ../scan.py Formal/Net/Fasm/*.lean || { echo "  forbidden token"; fail=1; }
[ -f .lake/build/lib/lean/Formal/Cells/CElemTiming.olean ] || \
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Cells/CElemTiming.olean Formal/Cells/CElemTiming.lean || fail=1
# CePair's Core twin (probe 11e) needs Formal.Net.CoreLut (Core.Lut only)
[ -f .lake/build/lib/lean/Formal/Net/CoreLut.olean ] || \
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/CoreLut.olean Formal/Net/CoreLut.lean || fail=1
for m in Basic CePairS1 CePairS2 CePairS3 CePairS4 CePair; do
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/Fasm/$m.olean Formal/Net/Fasm/$m.lean \
        > "$TMP/$m.log" 2>&1 && echo "  ok  Formal/Net/Fasm/$m.lean" \
        || { echo "  FAIL Formal/Net/Fasm/$m.lean"; head -20 "$TMP/$m.log"; fail=1; }
done
cat > "$TMP/ax.lean" <<'EOF'
import Formal.Net.Fasm.CePair
open Formal.Net.Fasm.CePair
#print axioms next_state_s1
#print axioms next_state_s2
#print axioms next_state_s3
#print axioms next_state_s4
#print axioms perm_matters_s1
#print axioms swap_caught_s1
#print axioms q1_loop_s1
#print axioms q1_follow_hold_s1
#print axioms q1_kleene_s1
#print axioms q1_kleene_s1_core
#print axioms q1_follow_hold_s1_ps
EOF
../slot.sh lean "$TMP/ax.lean" > "$TMP/ax.log" 2>&1
sed 's/^/  /' "$TMP/ax.log"
if grep -q "sorryAx\|error" "$TMP/ax.log" || grep "depends on axioms" "$TMP/ax.log" \
        | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' | grep -qv '^\(propext\|Quot.sound\|Classical.choice\)$'; then
    echo "  non-standard axiom"; fail=1
fi

echo "== 3. negative controls in the bits =="
mut() {  # name kind expect(caught|refused)
    python3 "$HERE/mutate.py" "$2" "$FIX/ce_pair_s1.fromBit.fasm" "$TMP/$1.fasm" || { fail=1; return; }
    if ! $F2L "$TMP/$1.fasm" "$HERE/ce_pair.xdc" --ns Wip$1 --out "$LEAN/Wip/C11b/$1.lean" 2> "$TMP/$1.log"; then
        if [ "$3" = refused ]; then echo "  $1: refused by fasm2lean: $(tail -1 "$TMP/$1.log" | cut -c1-110)"
        else echo "  $1: fasm2lean refused it, expected a Lean disproof"; cat "$TMP/$1.log"; fail=1; fi
        return
    fi
    [ "$3" = refused ] && { echo "  $1: fasm2lean ACCEPTED a short"; fail=1; return; }
    sed -i "s/namespace Formal.Net.Fasm.Wip$1/namespace Wip.C11b.$1/; s/end Formal.Net.Fasm.Wip$1/end Wip.C11b.$1/" "$LEAN/Wip/C11b/$1.lean"
    ../slot.sh lean -o ".lake/build/lib/lean/Wip/C11b/$1.olean" "Wip/C11b/$1.lean" > "$TMP/$1.l1" 2>&1 || { cat "$TMP/$1.l1"; fail=1; return; }
    printf 'import Formal.Net.Fasm.CePair\nimport Wip.C11b.%s\nopen Formal.Net.Fasm.CePair\n/-- the defect is caught -/\ntheorem caught : ¬ Spec Wip.C11b.%s.net Wip.C11b.%s.ports := by decide\n' "$1" "$1" "$1" > "$LEAN/Wip/C11b/${1}Caught.lean"
    if ../slot.sh lean "Wip/C11b/${1}Caught.lean" > "$TMP/$1.l2" 2>&1; then
        echo "  $1: caught (not Spec, proved by decide)"
    else echo "  $1: NOT caught -- the import is blind to it"; head -5 "$TMP/$1.l2"; fail=1; fi
}
mut MutInit init caught
mut MutPips pips caught
mut MutShort short refused

[ $fail -eq 0 ] && echo "fasm2lean check PASS" || { echo "fasm2lean check FAIL"; exit 1; }
