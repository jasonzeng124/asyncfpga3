#!/usr/bin/env bash
# Probe C-11c end to end, from the committed fixtures (no routing needed):
#
#     formal/tools/fasm2lean2/check.sh        (~3-5 min; ./route.sh SEED re-routes one seed)
#
# 0. the fixtures were routed by the checked toolchain (nextpnr fingerprint).
# 1. seeds 1..4: the physical netlist from nextpnr's FASM and from the FASM
#    read back from the .bit are the same; Formal/Net/FasmLink/S<n>.lean,
#    regenerated from the read-back one, equals the committed file (drift).
# 2. compose.py: the Lean composition LinkArb.insts of 11a's cell netlists
#    = yosys's own flattening of link_arb.
# 3. Lean: Formal/Net/FasmLink/{Basic,LinkArb,S1..S4,Proofs}.lean compile,
#    scan.py clean, the theorems use only propext / Quot.sound / Classical.choice.
# 4. negative controls injected in the BITS of seed 1 (mutate2.py), extracted
#    the same way into Wip/C11c/: INIT bit flipped / IMUX pip re-pointed to
#    another net -> `¬ Correct` proved (Design.not_correct + decide); a short,
#    an FF feature, a CARRY4 feature -> fasm2lean2 refuses the FASM.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
LEAN=$(cd "$HERE/../../lean" && pwd)
FIX=$HERE/fixture
TMP=${TMPDIR:-/tmp}/fasm2lean2.$$; mkdir -p "$TMP"; trap 'rm -rf "$TMP"' EXIT
fail=0

echo "== 0. toolchain =="
for s in 1 2 3 4; do
    grep -q "sha256  9c732bc6303458df" "$FIX/link_arb_s$s.toolchain" && ! grep -q FAIL "$FIX/link_arb_s$s.toolchain" \
        && grep -q "fasm_audit PASS" "$FIX/link_arb_s$s.audit" \
        && echo "  seed $s: nextpnr 9c732bc6303458df, toolchain.sh ok, fasm_audit PASS" \
        || { echo "  seed $s: toolchain stamp / audit NOT ok"; fail=1; }
done

echo "== 1. FASM vs bitstream read-back, Lean data drift =="
for s in 1 2 3 4; do
    python3 "$HERE/fasm2lean2.py" "$FIX/link_arb_s$s.fasm" "$HERE/link_arb.xdc" --ns X --json "$TMP/a$s.json" \
        --out /dev/null 2> "$TMP/a$s.log" || { cat "$TMP/a$s.log"; fail=1; continue; }
    python3 "$HERE/gen.py" "$FIX/link_arb_s$s.fromBit.fasm" "$FIX/link_arb_s$s.bels" Formal.Net.FasmLink.S$s \
        "$TMP/S$s.lean" --json "$TMP/b$s.json" 2> "$TMP/b$s.log" || { cat "$TMP/b$s.log"; fail=1; continue; }
    if python3 - "$TMP/a$s.json" "$TMP/b$s.json" <<'EOF'
import json, sys
a, b = (json.load(open(f)) for f in sys.argv[1:])
key = lambda r: (r["inputs"], [(l["site"], l["lut"], l["init"], [p["src"] for p in l["pins"]]) for l in r["luts"]],
                 [(o["port"], o["src"]) for o in r["outs"]])
sys.exit(0 if key(a) == key(b) else 1)
EOF
    then echo "  seed $s: same netlist from FASM and from .bit  ($(grep '^fasm2lean:' "$TMP/b$s.log" | sed 's/fasm2lean: //'))"
    else echo "  seed $s: FASM and .bit DISAGREE"; fail=1; fi
    # the committed Lean names the fixture by a repo-relative path; so does the regenerated one
    sed -i "s|$TMP/S$s.lean.json||" "$TMP/S$s.lean"
    cmp -s "$TMP/S$s.lean" "$LEAN/Formal/Net/FasmLink/S$s.lean" \
        && echo "  seed $s: Formal/Net/FasmLink/S$s.lean up to date" \
        || { echo "  seed $s: Formal/Net/FasmLink/S$s.lean DRIFT (regenerate with gen.py)"; diff "$TMP/S$s.lean" "$LEAN/Formal/Net/FasmLink/S$s.lean" | head; fail=1; }
done

echo "== 2. composition vs yosys flattening =="
python3 "$HERE/compose.py" "$FIX/link_arb.synth.json" | sed 's/^/  /'
[ "${PIPESTATUS[0]}" -eq 0 ] || fail=1

echo "== 3. Lean =="
export PATH=$HOME/.elan/bin:$PATH
cd "$LEAN"; export LEAN_PATH=$PWD/.lake/build/lib/lean
O=.lake/build/lib/lean
mkdir -p $O/Formal/Net/FasmLink $O/Wip/C11c "$LEAN/Wip/C11c"
python3 ../scan.py Formal/Net/FasmLink/*.lean || { echo "  forbidden token"; fail=1; }
for dep in Formal/Cells/CElemTiming Formal/Cells/MuxTree Formal/Net/CoreLut Formal/Net/CoreLutPrelim Formal/Net/Fasm/Basic Formal/Net/Import/Netlist Formal/Net/Import/Cells Formal/Net/Import/PrelimSem Formal/Net/Import/Proofs; do
    [ -f $O/$dep.olean ] || { echo "  missing $dep.olean (build it first: see notes/C-11c-fasmlink.md)"; fail=1; }
done
for m in Basic LinkArb S1 S2 S3 S4 Proofs; do
    t0=$(date +%s)
    ../slot.sh lean -o $O/Formal/Net/FasmLink/$m.olean Formal/Net/FasmLink/$m.lean > "$TMP/$m.log" 2>&1 \
        && echo "  ok  Formal/Net/FasmLink/$m.lean  ($(( $(date +%s) - t0 )) s wall incl. slot wait)" \
        || { echo "  FAIL Formal/Net/FasmLink/$m.lean"; head -20 "$TMP/$m.log"; fail=1; }
done
cat > "$TMP/ax.lean" <<'EOF'
import Formal.Net.FasmLink.Proofs
open Formal.Net.FasmLink Formal.Net.FasmLink.LinkArb
#print axioms Design.check_sound
#print axioms Design.not_correct
#print axioms seed1_correct
#print axioms seed2_correct
#print axioms seed3_correct
#print axioms seed4_correct
#print axioms wrong_rho_caught
#print axioms grant_exclusion_s1
#print axioms grant_exclusion_s4
EOF
../slot.sh lean "$TMP/ax.lean" > "$TMP/ax.log" 2>&1
grep -v '^\[slot' "$TMP/ax.log" | sed 's/^/  /'
if grep -q "sorryAx\|error" "$TMP/ax.log" || grep "depends on axioms" "$TMP/ax.log" \
        | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' | grep -qv '^\(propext\|Quot.sound\|Classical.choice\)$'; then
    echo "  non-standard axiom"; fail=1
fi

echo "== 4. negative controls in the bits (seed 1) =="
python3 "$HERE/gen.py" "$FIX/link_arb_s1.fromBit.fasm" "$FIX/link_arb_s1.bels" X "$TMP/s1.lean" --json "$TMP/s1.json" 2>/dev/null
mut() {  # name kind expect(caught|refused)
    python3 "$HERE/mutate2.py" "$2" "$FIX/link_arb_s1.fromBit.fasm" "$TMP/s1.json" "$FIX/link_arb_s1.bels" \
        "$TMP/$1.fasm" 2> "$TMP/$1.mut" || { cat "$TMP/$1.mut"; fail=1; return; }
    local what; what=$(grep '^mutate2:' "$TMP/$1.mut" | sed 's/^mutate2: //' | cut -c1-120)
    if ! python3 "$HERE/gen.py" "$TMP/$1.fasm" "$FIX/link_arb_s1.bels" Wip.C11c.$1 "$LEAN/Wip/C11c/$1.lean" \
            --json "$TMP/$1.json" 2> "$TMP/$1.log"; then
        if [ "$3" = refused ]; then echo "  $1: refused by fasm2lean2: $(grep -v '^\s*$' "$TMP/$1.log" | tail -1 | sed 's/^ *//' | cut -c1-100)"
        else echo "  $1: fasm2lean2 refused it, expected a Lean disproof"; cat "$TMP/$1.log"; fail=1; fi
        return
    fi
    [ "$3" = refused ] && { echo "  $1: fasm2lean2 ACCEPTED it"; fail=1; return; }
    ../slot.sh lean -o "$O/Wip/C11c/$1.olean" "Wip/C11c/$1.lean" > "$TMP/$1.l1" 2>&1 || { cat "$TMP/$1.l1"; fail=1; return; }
    cat > "$LEAN/Wip/C11c/${1}Caught.lean" <<EOF
import Formal.Net.FasmLink.LinkArb
import Wip.C11c.$1
open Formal.Net.FasmLink
/-- negative control ($what): the defect in the bits is caught -/
theorem caught : ¬ (LinkArb.design Wip.C11c.$1.net Wip.C11c.$1.ports Wip.C11c.$1.rho).Correct :=
  Design.not_correct _ (by decide)
EOF
    if ../slot.sh lean "Wip/C11c/${1}Caught.lean" > "$TMP/$1.l2" 2>&1; then
        echo "  $1: caught (not Correct, proved by decide)  [$what]"
    else echo "  $1: NOT caught -- the import is blind to it"; head -5 "$TMP/$1.l2"; fail=1; fi
}
mut MutInit init caught
mut MutPips pips caught
mut MutShort short refused
mut MutFF ff refused
mut MutCarry carry refused

[ $fail -eq 0 ] && echo "fasm2lean2 check PASS" || { echo "fasm2lean2 check FAIL"; exit 1; }
