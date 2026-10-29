#!/usr/bin/env bash
# Probe C-11f end to end, from the committed fixtures (no routing needed):
#
#     formal/tools/fasm2lean3/check.sh            (Lean part: ~1-2 h of CPU when nothing is built)
#     formal/tools/fasm2lean3/check.sh --no-lean  (steps 0-2 and the Python half of 4: ~15 min)
#     formal/tools/fasm2lean3/route.sh SEED; python3 trim.py SEED   (re-route one seed)
#
# 0. every fixture seed was routed by the checked toolchain (nextpnr 9c732bc6303458df,
#    toolchain.sh ok), --freq 100 met, fasm_audit PASS.
# 1. per seed: the physical netlist fasm2lean3 extracts from the FASM READ BACK from
#    the .bit equals the one from nextpnr's FASM; gen3 pairs it with the yosys
#    netlist; check3.py (a Python mirror of Inst.check) passes every instance.
# 2. seed d: the committed Formal/Net/FasmDesign/GcdD/*.lean equal what gen3
#    regenerates from the fixtures (drift).
# 3. Lean: Basic + GcdD (Rho, C000..C042, All) build, formal/check.sh audit on
#    Basic.lean, GcdD/All.lean and FasmGcd.lean (axioms: propext, Classical.choice, Quot.sound).
# 4. negative controls injected in the BITS of seed d (mutate3.py): one INIT bit,
#    one re-pointed IMUX pip, one FF ZINI, one CLKINV -> check3 fails on exactly
#    that instance; the Lean files Wip/C11f/Mut*.lean prove `checkAll rho insts = false`.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
FORMAL=$(cd "$HERE/../.." && pwd); LEAN=$FORMAL/lean
FIX=$HERE/fixture
NOLEAN=0; [ "${1:-}" = "--no-lean" ] && NOLEAN=1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
fail=0
SEEDS=$(ls "$FIX" | sed -n 's/^gcd_hw_\(.*\)\.fromBit\.fasm\.xz$/\1/p' | sort)

echo "== 0. toolchain =="
for s in $SEEDS; do
    if grep -q "sha256  9c732bc6303458df" "$FIX/gcd_hw_$s.toolchain" && ! grep -q FAIL "$FIX/gcd_hw_$s.toolchain" \
        && grep -q "fasm_audit PASS" "$FIX/gcd_hw_$s.audit" && [ "$(grep -c 'PASS at 100.00 MHz' "$FIX/gcd_hw_$s.pnr")" = 4 ]; then
        echo "  seed $s: nextpnr 9c732bc6303458df, toolchain.sh ok, 4 clocks PASS at --freq 100, fasm_audit PASS"
    else echo "  seed $s: toolchain stamp / audit / freq NOT ok"; fail=1; fi
done

echo "== 1. bits -> physical netlist -> paired with yosys; Python mirror of the check =="
for s in $SEEDS; do
    xz -dc "$FIX/gcd_hw_$s.fromBit.fasm.xz" > "$TMP/gcd_hw_$s.fromBit.fasm"
    xz -dc "$FIX/gcd_hw_$s.fasm.xz" > "$TMP/gcd_hw_$s.fasm"
    xz -dc "$FIX/gcd_hw_$s.synth.json.xz" > "$TMP/gcd_hw_$s.json"
    xz -dc "$FIX/gcd_hw_$s.hint.json.xz" > "$TMP/gcd_hw_$s.routed.json"
    python3 "$HERE/fasm2lean3.py" "$TMP/gcd_hw_$s.fromBit.fasm" "$FIX/gcd_hw_$s.xdc" --json "$TMP/phys_$s.json" > "$TMP/x$s.log" 2>&1 \
        || { tail -5 "$TMP/x$s.log"; fail=1; continue; }
    python3 "$HERE/fasm2lean3.py" "$TMP/gcd_hw_$s.fasm" "$FIX/gcd_hw_$s.xdc" --json "$TMP/physn_$s.json" > "$TMP/y$s.log" 2>&1 \
        || { tail -5 "$TMP/y$s.log"; fail=1; continue; }
    if python3 - "$TMP/phys_$s.json" "$TMP/physn_$s.json" <<'EOF'
import json, sys
a, b = (json.load(open(f)) for f in sys.argv[1:])
key = lambda r: (sorted((c["name"], c["kind"], c["init"], sorted((k, json.dumps(v, sort_keys=True)) for k, v in c["conn"].items()), c["inv"]) for c in r["cells"]), sorted(r["outputs"].items()))
sys.exit(0 if key(a) == key(b) else 1)
EOF
    then echo "  seed $s: same physical netlist from nextpnr's FASM and from the .bit ($(grep -o "{'lut6_2.*" "$TMP/x$s.log"))"
    else echo "  seed $s: FASM and .bit DISAGREE"; fail=1; fi
    NS=GcdS$s; [ "$s" = d ] && NS=GcdD
    python3 "$HERE/gen3.py" "$TMP/phys_$s.json" "$TMP/gcd_hw_$s.json" "$TMP/gcd_hw_$s.routed.json" "$TMP/lean_$s" $NS \
        --report "$TMP/report_$s.json" > "$TMP/g$s.log" 2>&1 || { tail -5 "$TMP/g$s.log"; fail=1; continue; }
    echo "  seed $s: $(grep '^gen3: [0-9]' "$TMP/g$s.log" | sed 's/^gen3: //')"
    python3 "$HERE/check3.py" "$TMP/lean_$s" > "$TMP/c$s.log" 2>&1 && echo "  seed $s: $(tail -1 "$TMP/c$s.log")" \
        || { tail -5 "$TMP/c$s.log"; fail=1; }
done

echo "== 2. drift (seed d) =="
if diff -rq "$TMP/lean_d" "$LEAN/Formal/Net/FasmDesign/GcdD" > "$TMP/drift.log"; then
    echo "  Formal/Net/FasmDesign/GcdD/*.lean up to date"
else cat "$TMP/drift.log" | head; echo "  DRIFT (regenerate with gen3.py)"; fail=1; fi

if [ $NOLEAN = 0 ]; then
echo "== 3. Lean =="
export PATH=$HOME/.elan/bin:$PATH
( cd "$LEAN" && FORMAL_SLOT_CWD=$LEAN "$FORMAL/slot.sh" lake build Formal.Net.FasmGcd 2>&1 | grep -E "error|✖|Build completed" | head -20 )
( cd "$FORMAL" && ./check.sh Formal/Net/FasmDesign/Basic.lean Formal/Net/FasmDesign/GcdD/All.lean Formal/Net/FasmGcd.lean 2>&1 | tail -25 ) \
    | tee "$TMP/audit.log" | sed 's/^/  /'
grep -q "FAIL" "$TMP/audit.log" && fail=1
fi

echo "== 4. negative controls in the bits (seed d) =="
B=$HERE/build/mut; mkdir -p "$B"; cp "$TMP/gcd_hw_d.fromBit.fasm" "$B/in.fasm"
for spec in "init SLICE_X0Y63.ALUT C000" "pips SLICE_X0Y63.ALUT C000" "ffinit SLICE_X22Y62.ALUT C012" "clkinv SLICE_X22Y62.ALUT C012"; do
    set -- $spec; k=$1
    python3 "$HERE/mutate3.py" $k "$B/in.fasm" "$TMP/phys_d.json" $2 "$B/$k.fasm" 2> "$B/$k.mut.log" || { cat "$B/$k.mut.log"; fail=1; continue; }
    python3 "$HERE/fasm2lean3.py" "$B/$k.fasm" "$FIX/gcd_hw_d.xdc" --json "$B/$k.json" > "$B/$k.x.log" 2>&1 \
        || { echo "  $k: refused by fasm2lean3: $(tail -1 "$B/$k.x.log")"; continue; }
    python3 "$HERE/gen3.py" "$B/$k.json" "$TMP/gcd_hw_d.json" "$TMP/gcd_hw_d.routed.json" "$B/lean_$k" GcdDMut > "$B/$k.g.log" 2>&1 \
        || { echo "  $k: refused by gen3: $(tail -1 "$B/$k.g.log")"; continue; }
    python3 "$HERE/check3.py" "$B/lean_$k" > "$B/$k.c.log" 2>&1
    n=$(tail -1 "$B/$k.c.log" | sed -n 's/.*instances, \([0-9]*\) fail/\1/p')
    if [ "$n" = 1 ]; then echo "  $k: caught by check3 ($(cat "$B/$k.mut.log")): $(head -1 "$B/$k.c.log" | cut -c1-140)"
    else echo "  $k: NOT caught ($n failures)"; fail=1; fi
    "$HERE/mkmut.sh" $k $3 > /dev/null || fail=1
    if [ $NOLEAN = 0 ]; then
        N=Mut$(echo ${k^})
        ( cd "$LEAN" && FORMAL_SLOT_CWD=$LEAN "$FORMAL/slot.sh" lake env lean "Wip/C11f/$N.lean" > "$TMP/$N.out" 2>&1 ) \
            && echo "  $k: Lean proves checkAll rho insts = false (Wip/C11f/$N.lean)" \
            || { head -5 "$TMP/$N.out"; echo "  $k: Lean negative control FAILED"; fail=1; }
    fi
done

[ $fail = 0 ] && echo "fasm2lean3 check PASS" || echo "fasm2lean3 check FAIL"
exit $fail
