#!/usr/bin/env bash
# F3 model checks.  Each testbench must PASS under GLS_FID and FAIL under the
# default prims.v model -- the failure with the mechanism disabled is the
# negative control, so a run where the default model passes is itself a FAIL.
#
#   cells/gls/fid/f3/run_f3.sh            unit testbenches (seconds)
#   cells/gls/fid/f3/run_f3.sh arbm WORK  + routed GLS of hw/arb_mtbf, WORK a
#                                          gen.py output dir (GLS_MODEL=fid)
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
GLS=$(cd "$HERE/../.." && pwd)
OUT=${F3_OUT:-$(mktemp -d)}
rc=0
for tb in tb_f3_lut tb_f3_meta tb_f3_follow tb_f3_carry tb_f3_latch tb_f3_ff; do
    for m in default fid; do
        defs="-DGLS_TRANSPORT_IC"; [ $m = fid ] && defs="$defs -DGLS_FID"
        # shellcheck disable=SC2086
        iverilog -gspecify -I"$GLS" $defs -o "$OUT/$tb.$m.vvp" "$HERE/$tb.v" "$GLS/prims.v" || { rc=1; continue; }
        vvp -n "$OUT/$tb.$m.vvp" > "$OUT/$tb.$m.log" 2>&1
        if grep -q "$tb PASS" "$OUT/$tb.$m.log"; then got=PASS; else got=FAIL; fi
        want=FAIL; [ $m = fid ] && want=PASS
        if [ $got = $want ]; then echo "ok    $tb [$m] $got (expected)"
        else echo "WRONG $tb [$m] $got, expected $want"; rc=1; fi
        grep -v VIOLATION "$OUT/$tb.$m.log" | grep -E "^ *([TCLFG][0-9]|A\.|B\.|  ok|  FAIL|   )" | sed 's/^/        /'
    done
done
# bd_arbiter near tie (research/data/fid/arbtie.md): with TLOOP 424 the fid
# model needs a server round trip S >= 1088 ps.  S = 1200 must be clean (and
# see resolver events); S = 600 must double-ack (the negative control: a
# server 490 ps too fast); the default model must fail (it has no resolver).
for arm in "fid 1200 PASS" "fid 600 FAIL" "default 1200 FAIL"; do
    read -r am aS aw <<< "$arm"
    defs="-DGLS_TRANSPORT_IC"; [ "$am" = fid ] && defs="$defs -DGLS_FID"
    # shellcheck disable=SC2086
    iverilog -gspecify -I"$GLS" $defs -Ptb_f3_arbtie.S="$aS" -o "$OUT/arbtie.$am.$aS.vvp" \
        "$HERE/tb_f3_arbtie.v" "$GLS/prims.v" || { rc=1; continue; }
    vvp -n "$OUT/arbtie.$am.$aS.vvp" +PASS_MAX=0 > "$OUT/arbtie.$am.$aS.log" 2>&1
    if grep -q "tb_f3_arbtie PASS" "$OUT/arbtie.$am.$aS.log"; then got=PASS; else got=FAIL; fi
    if [ $got = "$aw" ]; then echo "ok    tb_f3_arbtie [$am S=$aS] $got (expected)"
    else echo "WRONG tb_f3_arbtie [$am S=$aS] $got, expected $aw"; rc=1; fi
    grep "^SUM" "$OUT/arbtie.$am.$aS.log" | cut -d' ' -f2-7 | sed 's/^/        /'
done
# x semantics must not change: settled outputs of 3000 random x-laden vectors
for m in default fid; do
    defs="-DGLS_TRANSPORT_IC"; [ $m = fid ] && defs="$defs -DGLS_FID"
    # shellcheck disable=SC2086
    iverilog -gspecify -I"$GLS" $defs -o "$OUT/k.$m.vvp" "$HERE/tb_f3_kleene.v" "$GLS/prims.v" && \
        vvp -n "$OUT/k.$m.vvp" | grep -v finish > "$OUT/kleene.$m.out"
done
if cmp -s "$OUT/kleene.default.out" "$OUT/kleene.fid.out" && [ "$(wc -l < "$OUT/kleene.fid.out")" = 3000 ]; then
    echo "ok    tb_f3_kleene: 3000 settled x-laden vectors identical under both models"
else echo "WRONG tb_f3_kleene: settled values differ between models"; rc=1; fi
# the same for CARRY4 and SLICE_LATX (latch state carries across vectors)
for m in default fid; do
    defs="-DGLS_TRANSPORT_IC"; [ $m = fid ] && defs="$defs -DGLS_FID"
    # shellcheck disable=SC2086
    iverilog -gspecify -I"$GLS" $defs -o "$OUT/kc4.$m.vvp" "$HERE/tb_f3_kleene_c4.v" "$GLS/prims.v" && \
        vvp -n "$OUT/kc4.$m.vvp" | grep -v finish > "$OUT/kleene_c4.$m.out"
done
if cmp -s "$OUT/kleene_c4.default.out" "$OUT/kleene_c4.fid.out" && [ "$(wc -l < "$OUT/kleene_c4.fid.out")" = 3000 ]; then
    echo "ok    tb_f3_kleene_c4: 3000 settled x-laden CARRY4/latch vectors identical under both models"
else echo "WRONG tb_f3_kleene_c4: settled values differ between models"; rc=1; fi
# the same for SLICE_FFX and BUFGCTRL (S6), plus a negative control: a mutated
# fid flop (x on CE loads D) must differ, or the check could not fail
sed "s/end else if (ce) begin/end else if (ce !== 1'b0) begin/" "$GLS/prims.v" > "$OUT/prims_mut_ff.v"
for m in default fid mut; do
    defs="-DGLS_TRANSPORT_IC"; p="$GLS/prims.v"
    [ $m != default ] && defs="$defs -DGLS_FID"; [ $m = mut ] && p="$OUT/prims_mut_ff.v"
    # shellcheck disable=SC2086
    iverilog -gspecify -I"$GLS" $defs -o "$OUT/kff.$m.vvp" "$HERE/tb_f3_kleene_ff.v" "$p" && \
        vvp -n "$OUT/kff.$m.vvp" | grep -v finish > "$OUT/kleene_ff.$m.out"
done
nmut=$(diff "$OUT/kleene_ff.default.out" "$OUT/kleene_ff.mut.out" | grep -c "^<")
if cmp -s "$OUT/kleene_ff.default.out" "$OUT/kleene_ff.fid.out" && [ "$(wc -l < "$OUT/kleene_ff.fid.out")" = 3000 ]; then
    echo "ok    tb_f3_kleene_ff: 3000 settled x-laden SLICE_FFX/BUFGCTRL vectors identical under both models"
else echo "WRONG tb_f3_kleene_ff: settled values differ between models"; rc=1; fi
if cmp -s "$OUT/prims_mut_ff.v" "$GLS/prims.v" || [ "$nmut" -lt 1 ]; then
    echo "WRONG tb_f3_kleene_ff negative control: the mutated fid flop was not caught"; rc=1
else echo "ok    tb_f3_kleene_ff negative control: mutated fid flop (x CE loads D) differs on $nmut of 3000 lines"; fi
if [ "${1:-}" = arbm ]; then
    W=$2
    python3 "$HERE/gen_arbm_sig.py" "$W"
    iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I"$W" -I"$GLS" -o "$OUT/arbm.vvp" \
        "$HERE/tb_f3_arbm.v" "$W/netlist_baked.v" "$GLS/prims.v" 2>&1 | grep -v procedural
    for s in 1 2; do
        vvp -n "$OUT/arbm.vvp" +TEND=${TEND:-20000} +META_VERBOSE=1 +META_SEED=$s > "$OUT/arbm.s$s.log" 2>&1
        python3 "$HERE/meta_summary.py" "$W/names.map" "$OUT/arbm.s$s.log" | sed "s/^/  seed $s: /"
    done
fi
echo "logs in $OUT"
exit $rc
