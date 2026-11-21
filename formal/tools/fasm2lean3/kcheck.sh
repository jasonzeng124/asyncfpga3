#!/usr/bin/env bash
# Probe C-11g: the bitstream import of a STANDALONE compiled kernel (kroute.sh), from fixtures.
#     formal/tools/fasm2lean3/kcheck.sh KERNEL [--no-lean]
# 0. every fixture seed: nextpnr 9c732bc6303458df, toolchain.sh ok, fasm_audit PASS, flow.sh exit 0,
#    --freq 100 in pnr.log (the soak top has no clock: the frequency constrains nothing)
# 1. per seed: the physical netlist from the .bit read-back equals the one from nextpnr's FASM;
#    gen3 pairs it with the yosys netlist; check3 (Python mirror of Inst.check) passes every instance
# 2. drift: Formal/Net/FasmDesign/<Kernel><seed>/*.lean (gen3) and Formal/Net/FasmRho<Kernel><seed>*.lean
#    (rhoinj) equal their regeneration
# 3. Lean (unless --no-lean): build.sh per seed (one module at a time), the rho files, Fasm<Kernel><seed>.lean,
#    formal/check.sh audit
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
FORMAL=$(cd "$HERE/../.." && pwd); LEAN=$FORMAL/lean
FIX=$HERE/fixture
K=$1; KC=${K^}
NOLEAN=0; [ "${2:-}" = "--no-lean" ] && NOLEAN=1
TMP=$(mktemp -d); trap 'rm -rf "$TMP"' EXIT
fail=0
SEEDS=$(ls "$FIX" | sed -n "s/^${K}_\(.*\)\.fromBit\.fasm\.xz$/\1/p" | sort)
echo "== 0. toolchain =="
for s in $SEEDS; do
    if grep -q "sha256  9c732bc6303458df" "$FIX/${K}_$s.toolchain" && ! grep -q FAIL "$FIX/${K}_$s.toolchain" \
        && grep -q "fasm_audit PASS" "$FIX/${K}_$s.audit" && grep -q "flow.sh exit 0" "$FIX/${K}_$s.pnr" \
        && grep -q "target frequency 100.00 MHz" "$FIX/${K}_$s.pnr"; then
        echo "  seed $s: nextpnr 9c732bc6303458df, toolchain.sh ok, flow.sh gates ok, fasm_audit PASS, --freq 100"
    else echo "  seed $s: stamp NOT ok"; fail=1; fi
done
echo "== 1. bits -> physical netlist -> paired with yosys; Python mirror =="
for s in $SEEDS; do
    for x in fromBit.fasm fasm synth.json hint.json; do xz -dc "$FIX/${K}_$s.$x.xz" > "$TMP/$s.$x"; done
    python3 "$HERE/fasm2lean3.py" "$TMP/$s.fromBit.fasm" "$FIX/${K}_$s.xdc" --json "$TMP/phys_$s.json" > "$TMP/x$s.log" 2>&1 \
        || { tail -3 "$TMP/x$s.log"; fail=1; continue; }
    python3 "$HERE/fasm2lean3.py" "$TMP/$s.fasm" "$FIX/${K}_$s.xdc" --json "$TMP/physn_$s.json" > "$TMP/y$s.log" 2>&1 \
        || { tail -3 "$TMP/y$s.log"; fail=1; continue; }
    if python3 - "$TMP/phys_$s.json" "$TMP/physn_$s.json" <<'PY'
import json, sys
a, b = (json.load(open(f)) for f in sys.argv[1:])
key = lambda r: (sorted((c["name"], c["kind"], c["init"], sorted((k, json.dumps(v, sort_keys=True)) for k, v in c["conn"].items()), c["inv"]) for c in r["cells"]), sorted(r["outputs"].items()))
sys.exit(0 if key(a) == key(b) else 1)
PY
    then echo "  seed $s: same physical netlist from nextpnr's FASM and from the .bit ($(grep -o "{'lut6_2.*" "$TMP/x$s.log"))"
    else echo "  seed $s: FASM and .bit DISAGREE"; fail=1; fi
    python3 "$HERE/gen3.py" "$TMP/phys_$s.json" "$TMP/$s.synth.json" "$TMP/$s.hint.json" "$TMP/lean_$s" "$KC$s" \
        > "$TMP/g$s.log" 2>&1 || { tail -3 "$TMP/g$s.log"; fail=1; continue; }
    echo "  seed $s: $(grep '^gen3: [0-9]' "$TMP/g$s.log" | sed 's/^gen3: //')"
    python3 "$HERE/check3.py" "$TMP/lean_$s" > "$TMP/c$s.log" 2>&1 && echo "  seed $s: $(tail -1 "$TMP/c$s.log")" \
        || { tail -3 "$TMP/c$s.log"; fail=1; }
    mkdir -p "$TMP/rho_$s"; python3 "$HERE/rhoinj.py" "$TMP/lean_$s" "$KC$s" "$TMP/rho_$s" | sed 's/^/  /' || fail=1
done
echo "== 1b. negative controls in the bits (first seed, first lib LUT of chunk C001; Python mirror only) =="
s0=$(echo $SEEDS | cut -d' ' -f1)
site=$(grep -m1 -o '⟨"SLICE_X[0-9]*Y[0-9]*\.[A-D]LUT", .lut6_2' "$TMP/lean_$s0/C001.lean" | cut -d'"' -f2)
for k in init pips; do
    python3 "$HERE/mutate3.py" $k "$TMP/$s0.fromBit.fasm" "$TMP/phys_$s0.json" "$site" "$TMP/m_$k.fasm" > "$TMP/m_$k.log" 2>&1 || { cat "$TMP/m_$k.log"; fail=1; continue; }
    python3 "$HERE/fasm2lean3.py" "$TMP/m_$k.fasm" "$FIX/${K}_$s0.xdc" --json "$TMP/m_$k.json" > /dev/null 2>&1 \
        || { echo "  $k: refused by fasm2lean3"; continue; }
    python3 "$HERE/gen3.py" "$TMP/m_$k.json" "$TMP/$s0.synth.json" "$TMP/$s0.hint.json" "$TMP/mlean_$k" "${KC}Mut" > /dev/null 2>&1 \
        || { echo "  $k: refused by gen3"; continue; }
    python3 "$HERE/check3.py" "$TMP/mlean_$k" > "$TMP/mc_$k.log" 2>&1
    n=$(tail -1 "$TMP/mc_$k.log" | sed -n 's/.*instances, \([0-9]*\) fail/\1/p')
    if [ "$n" = 1 ] && grep -q "$site" "$TMP/mc_$k.log"; then echo "  $k: caught by check3 at $site ($(tail -1 "$TMP/m_$k.log"))"
    else echo "  $k: NOT caught at $site ($n failures)"; fail=1; fi
done
echo "== 2. drift =="
for s in $SEEDS; do
    diff -rq "$TMP/lean_$s" "$LEAN/Formal/Net/FasmDesign/$KC$s" > /dev/null && echo "  FasmDesign/$KC$s up to date" \
        || { echo "  DRIFT in FasmDesign/$KC$s"; fail=1; }
    for f in "$TMP"/rho_$s/*.lean; do
        cmp -s "$f" "$LEAN/Formal/Net/$(basename "$f")" || { echo "  DRIFT in $(basename "$f")"; fail=1; }
    done
done
if [ $NOLEAN = 0 ]; then
    echo "== 3. Lean =="
    export PATH=$HOME/.elan/bin:$PATH
    files=(Formal/Net/FasmDesign/Basic.lean Formal/Net/FasmRho.lean)
    for s in $SEEDS; do
        "$HERE/build.sh" "$KC$s" | tail -1 || fail=1
        for m in FasmRho$KC${s}Inv FasmRho$KC${s}Occ FasmRho$KC${s}Mark FasmRho$KC${s}Data FasmRho$KC$s Fasm$KC$s; do
            ( cd "$LEAN" && FORMAL_SLOT_CWD=$LEAN flock "$HERE/build/.lean.lock" "$FORMAL/slot.sh" lake build Formal.Net.$m 2>&1 \
                | grep -E "error|✖|Build completed" | head -3 )
        done
        files+=(Formal/Net/FasmDesign/$KC$s/All.lean Formal/Net/FasmRho$KC$s.lean Formal/Net/Fasm$KC$s.lean)
    done
    ( cd "$FORMAL" && flock "$HERE/build/.lean.lock" ./check.sh "${files[@]}" 2>&1 | tail -12 ) | tee "$TMP/audit.log" | sed 's/^/  /'
    grep -q "FAIL" "$TMP/audit.log" && fail=1
fi
[ $fail = 0 ] && echo "kcheck $K PASS" || echo "kcheck $K FAIL"
exit $fail
