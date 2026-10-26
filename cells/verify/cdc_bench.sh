#!/usr/bin/env bash
# Does the bench FSM read the self-timed kernel through a synchroniser?
#
#     cells/verify/cdc_bench.sh [kernel ...]     (default: gcd; ~15 s each)
#
# Regression test for the August 2026 bench hang: gen_bench.py's 3-bit state
# register took a transition straight off o_req_latched/i_ack_latched, flops
# the kernel sets asynchronously, and on silicon `st` landed on a bitwise mix
# of two states (S_WAIT_ACK 011 -> S_RTZ 110, five times in eight board runs).
# Metastability cannot be simulated; the structure that permits it can be
# checked, and verify/cdc_fsm.py does that on the generated harness at gate
# level.
#
# Negative control, every run: the fix reverted in a copy -- i_ack_l_s and
# o_req_l_s wired to the async latches instead of the second synchroniser
# flop, which is the August code -- and a one-flop synchroniser.  Both must
# fail.
set -uo pipefail
cd "$(dirname "$0")/.."

TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
W=build/verify/cdc
mkdir -p "$W" build/gen
kernels=("$@")
[ ${#kernels[@]} -gt 0 ] || kernels=(gcd)

netlist() {   # netlist <harness.v> <kernel.v> <top> <out.json>
    "$TC/openxc7/bin/yosys" -q -p "
read_verilog -lib $2
read_verilog -lib rtl/*.v
read_verilog $1
hierarchy -top $3
proc; flatten; opt_clean; techmap; opt_clean
write_json $4
" > "$W/yosys.log" 2>&1 || { echo "SYNTH FAILED ($1)"; tail "$W/yosys.log"; return 1; }
}

fail=0
for k in "${kernels[@]}"; do
    top=${k}_bench_cdc
    python3 ../bdc/emit.py "../build/frontend/$k/comp/handshake_transformed.mlir" --no-top \
        -o "$W/${k}_kernel.v" > "$W/gen.log" 2>&1 &&
    python3 hw/gen_bench.py "$k" --top "$top" -o "$W/$top.v" >> "$W/gen.log" 2>&1 \
        || { echo "GENERATE FAILED ($k)"; cat "$W/gen.log"; fail=1; continue; }

    echo "== $k: the generated harness =="
    netlist "$W/$top.v" "$W/${k}_kernel.v" "${top}_bridge" "$W/$top.json" || { fail=1; continue; }
    python3 verify/cdc_fsm.py "$W/$top.json" || fail=1

    echo "== $k: negative controls =="
    for ctl in august onefl; do
        case $ctl in
            august) sed -e 's|^    wire i_ack_l_s = sync_i_ackl\[1\];|    wire i_ack_l_s = i_ack_latched;|' \
                        -e 's|^    wire o_req_l_s = sync_o_reql\[1\];|    wire o_req_l_s = o_req_latched;|' ;;
            onefl)  sed -e 's|^    wire o_req_l_s = sync_o_reql\[1\];|    wire o_req_l_s = sync_o_reql[0];|' ;;
        esac < "$W/$top.v" > "$W/${top}_$ctl.v"
        if cmp -s "$W/$top.v" "$W/${top}_$ctl.v"; then
            echo "  $ctl: the reversion did not apply -- gen_bench.py changed; update this control"
            fail=1; continue
        fi
        netlist "$W/${top}_$ctl.v" "$W/${k}_kernel.v" "${top}_bridge" "$W/${top}_$ctl.json" || { fail=1; continue; }
        if python3 verify/cdc_fsm.py "$W/${top}_$ctl.json" > "$W/${top}_$ctl.log"; then
            echo "  $ctl: PASSED -- the check is blind to this"; fail=1
        else
            echo "  $ctl: caught ($(grep -m1 'ASYNC INTO' "$W/${top}_$ctl.log" | sed 's/^ *//'))"
        fi
    done
done
[ $fail -eq 0 ] && echo "verify/cdc_bench PASS" || { echo "verify/cdc_bench FAIL"; exit 1; }
