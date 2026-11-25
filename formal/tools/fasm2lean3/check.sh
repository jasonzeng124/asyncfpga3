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
# 2. every seed: the committed Formal/Net/FasmDesign/Gcd{D,2,3,4}/*.lean equal what gen3
#    regenerates from the fixtures (drift); Formal/Net/FasmRho{D,2,3,4}*.lean equal rhoinj.py's output (C-11g).
# 3. Lean: Basic + Gcd{D,2,3,4} (Rho, C000..C042, All; build.sh, one module at a time),
#    FasmGcd{,2,3,4}, FasmRho, FasmRho{D,2,3,4}; formal/check.sh audit on them
#    (axioms: propext, Classical.choice, Quot.sound).
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
    NS=Gcd$s; [ "$s" = d ] && NS=GcdD
    python3 "$HERE/gen3.py" "$TMP/phys_$s.json" "$TMP/gcd_hw_$s.json" "$TMP/gcd_hw_$s.routed.json" "$TMP/lean_$s" $NS \
        --report "$TMP/report_$s.json" > "$TMP/g$s.log" 2>&1 || { tail -5 "$TMP/g$s.log"; fail=1; continue; }
    echo "  seed $s: $(grep '^gen3: [0-9]' "$TMP/g$s.log" | sed 's/^gen3: //')"
    python3 "$HERE/check3.py" "$TMP/lean_$s" > "$TMP/c$s.log" 2>&1 && echo "  seed $s: $(tail -1 "$TMP/c$s.log")" \
        || { tail -5 "$TMP/c$s.log"; fail=1; }
done

echo "== 2. drift (every seed; rho certificates of seed d) =="
for s in $SEEDS; do
    NS=Gcd$s; [ "$s" = d ] && NS=GcdD
    if diff -rq "$TMP/lean_$s" "$LEAN/Formal/Net/FasmDesign/$NS" > "$TMP/drift.log"; then
        echo "  Formal/Net/FasmDesign/$NS/*.lean up to date"
    else head "$TMP/drift.log"; echo "  DRIFT in $NS (regenerate with gen3.py)"; fail=1; fi
done
for s in $SEEDS; do
    NS=Gcd$s; [ "$s" = d ] && NS=GcdD
    mkdir -p "$TMP/rho_$s"
    python3 "$HERE/rhoinj.py" "$TMP/lean_$s" $NS "$TMP/rho_$s" | sed 's/^/  /'
    for f in "$TMP"/rho_$s/*.lean; do
        cmp -s "$f" "$LEAN/Formal/Net/$(basename "$f")" || { echo "  DRIFT in $(basename "$f") (regenerate with rhoinj.py)"; fail=1; }
    done
done
echo "  Formal/Net/FasmRho{D,2,3,4}*.lean checked against rhoinj.py"

if [ $NOLEAN = 0 ]; then
echo "== 3. Lean =="
export PATH=$HOME/.elan/bin:$PATH
# one module at a time (build.sh), never a parallel chunk build
for s in $SEEDS; do NS=Gcd$s; [ "$s" = d ] && NS=GcdD; "$HERE/build.sh" $NS | tail -1 || fail=1; done
RHO=""; for s in D 2 3 4; do RHO="$RHO FasmRho${s}Inv FasmRho${s}Occ FasmRho${s}Mark FasmRho${s}Data FasmRho$s"; done
for m in FasmGcd FasmGcd2 FasmGcd3 FasmGcd4 $RHO; do
    ( cd "$LEAN" && FORMAL_SLOT_CWD=$LEAN flock "$HERE/build/.lean.lock" "$FORMAL/slot.sh" lake build Formal.Net.$m 2>&1 | grep -E "error|✖|Build completed" | head -5 )
done
( cd "$FORMAL" && ./check.sh Formal/Net/FasmDesign/Basic.lean Formal/Net/FasmDesign/GcdD/All.lean Formal/Net/FasmGcd.lean \
    Formal/Net/FasmDesign/Gcd2/All.lean Formal/Net/FasmGcd2.lean Formal/Net/FasmDesign/Gcd3/All.lean Formal/Net/FasmGcd3.lean \
    Formal/Net/FasmDesign/Gcd4/All.lean Formal/Net/FasmGcd4.lean Formal/Net/FasmRho.lean \
    Formal/Net/FasmRhoD.lean Formal/Net/FasmRho2.lean Formal/Net/FasmRho3.lean Formal/Net/FasmRho4.lean 2>&1 | tail -25 ) \
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
