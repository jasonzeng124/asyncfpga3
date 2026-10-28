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
for tb in tb_f3_lut tb_f3_meta; do
    for m in default fid; do
        defs="-DGLS_TRANSPORT_IC"; [ $m = fid ] && defs="$defs -DGLS_FID"
        # shellcheck disable=SC2086
        iverilog -gspecify -I"$GLS" $defs -o "$OUT/$tb.$m.vvp" "$HERE/$tb.v" "$GLS/prims.v" || { rc=1; continue; }
        vvp -n "$OUT/$tb.$m.vvp" > "$OUT/$tb.$m.log" 2>&1
        if grep -q "$tb PASS" "$OUT/$tb.$m.log"; then got=PASS; else got=FAIL; fi
        want=FAIL; [ $m = fid ] && want=PASS
        if [ $got = $want ]; then echo "ok    $tb [$m] $got (expected)"
        else echo "WRONG $tb [$m] $got, expected $want"; rc=1; fi
        grep -v VIOLATION "$OUT/$tb.$m.log" | grep -E "^ *(T[0-9]|A\.|B\.|  ok|  FAIL|   )" | sed 's/^/        /'
    done
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
