#!/usr/bin/env bash
# rtl_bench.sh KERNEL VEC.hex EXP WORK [MEMEXP] -- the RTL run of the bench a route of KERNEL is built from: the same
# Verilog cells/hw/build_bench.sh generates (bdc/emit.py --no-top --host-mem, then gen_bench.py --top K_bench_gen; with
# BDC_AUTO=1 in the environment bdc/auto.py's rewrites first, as build_bench.sh does), the frozen cells (cells/rtl/)
# over cells/sim/bd_prims_sim.v's primitive models (cell arcs only, zero wire delay unless RTL_ROUTE_PS is set), driven
# by the gate's own PS model (cells/gls/ps/ps7_bench.v, through a bus-to-pin PS7 wrapper written here) with the gate's
# plusargs (FIXED mode, +FCLK_PS=12000, GATE_NRUNS runs per batch, +MEMDUMP=1 when MEMEXP is given), judged by the
# gate's own verdict code (extracted from research/tools/eventgraph/bench_gate.sh at run time, so the two cannot
# drift). Functional only: no route, no SDF, no bundling check beyond the RAM model's setup numbers.
# Prints one line: KERNEL rtl <verdict>   (or KERNEL rtl EMIT FAILED / COMPILE FAILED ...)
# Env: RTL_ROUTE_PS (default 0: bd_prims_sim's BD_ROUTE_PS, a uniform wire delay on every arc), GATE_NRUNS (2),
# RTL_TBATCH (ns per batch before HANG, default 400000), RTL_PLUSARGS (extra plusargs, e.g. +MEMCHECK=1).
# THE RAM BOUNDARY: bdc emits bd_mem's DCO as a 12-arc placeholder, which at cells/sim's 124 ps and zero wire delay is
# 1488 ps -- shorter than the RAM model's clock-to-out (2454 ps), so the acknowledge announces a word that does not exist
# yet and a load that captures its word (bdc_load_cap: every load on an arbitrated port) returns the previous one
# (research/data/suite/memorder.md).  A route must meet DCO >= clock-to-out (verify/tighten.py rule C), so here every
# DCO shorter than that at RTL_ROUTE_PS is raised for this run only, through gen_bench.py's BD_SZ_ macros (emit.log
# says which); RTL_KEEP_DCO=1 keeps the emitted value.
set -euo pipefail
K=$1; VEC=$(readlink -f "$2"); EXP=$(readlink -f "$3"); mkdir -p "$4"; W=$(cd "$4" && pwd); MEMEXP=${5:-}
[ -n "$MEMEXP" ] && MEMEXP=$(readlink -f "$MEMEXP")
[ -s "$EXP" ] || { echo "$1 rtl REFUSED: no expected values in $EXP (a run with nothing to compare is not a pass)"; exit 2; }
R=$(cd "$(dirname "$0")/../../.." && pwd)
MLIR=${RTL_MLIR:-$R/build/frontend/$K/comp/handshake_transformed.mlir}   # RTL_MLIR (opt-in): another handshake MLIR for K
[ -f "$MLIR" ] || { echo "$K rtl NO FIXTURE ($MLIR)"; exit 1; }
# gen_bench.py reads the kernel's delay parameters from cells/build/gen/ first: a stale kernel there would win
[ -e "$R/cells/build/gen/${K}_kernel_bench.v" ] && { echo "$K rtl REFUSED: $R/cells/build/gen/${K}_kernel_bench.v exists (gen_bench.py would read it, not this run's)"; exit 2; }
mkdir -p "$W/build/gen"; cd "$W"
M=$MLIR
if [ "${BDC_AUTO:-0}" = 1 ]; then python3 "$R/bdc/auto.py" "$MLIR" "$W/${K}_auto.mlir" > emit.log 2>&1 || { echo "$K rtl AUTO FAILED ($W/emit.log)"; exit 1; }; M=$W/${K}_auto.mlir; fi
python3 "$R/bdc/emit.py" "$M" --no-top --host-mem -o "build/gen/${K}_kernel_bench.v" >> emit.log 2>&1 \
  || { echo "$K rtl EMIT FAILED: $(grep -m1 -E 'Error|error' emit.log || tail -1 emit.log)"; exit 1; }
python3 "$R/cells/hw/gen_bench.py" "$K" --top "${K}_bench_gen" -o "build/gen/${K}_bench_gen.v" >> emit.log 2>&1 \
  || { echo "$K rtl GEN_BENCH FAILED: $(tail -1 emit.log)"; exit 1; }
# PS7 (the bus ports gen_bench.py's top uses) -> PS7_PS7 (ps7_bench.v's bit pins, cells/gls/ps/ps7_pins.py)
python3 - "$R/cells/gls/ps" > ps7_rtl.v <<'PY'
import re, sys
sys.path.insert(0, sys.argv[1]); import ps7_pins
def bus(p):
    m = re.fullmatch(r"([A-Z0-9]*?[A-Z])(\d+)", p)
    return (m.group(1), int(m.group(2))) if m and not p.startswith("MAXIGP0ACLK") else (p, None)
print("// written by research/tools/suite/rtl_bench.sh: the board's PS7 ports onto ps7_bench.v's PS7_PS7 pins")
print("`timescale 1ps/1ps")
print("module PS7 (input MAXIGP0ACLK, output MAXIGP0ARESETN, output MAXIGP0AWVALID, input MAXIGP0AWREADY,")
print("    output [31:0] MAXIGP0AWADDR, output [11:0] MAXIGP0AWID, output MAXIGP0WVALID, input MAXIGP0WREADY,")
print("    output [31:0] MAXIGP0WDATA, output [3:0] MAXIGP0WSTRB, input MAXIGP0BVALID, output MAXIGP0BREADY,")
print("    input [1:0] MAXIGP0BRESP, input [11:0] MAXIGP0BID, output MAXIGP0ARVALID, input MAXIGP0ARREADY,")
print("    output [31:0] MAXIGP0ARADDR, output [11:0] MAXIGP0ARID, input MAXIGP0RVALID, output MAXIGP0RREADY,")
print("    input [31:0] MAXIGP0RDATA, input [1:0] MAXIGP0RRESP, input MAXIGP0RLAST, input [11:0] MAXIGP0RID,")
print("    output [3:0] FCLKCLK, output [3:0] FCLKRESETN, input [3:0] FCLKCLKTRIGN);")
conn = []
for p in ps7_pins.OUTPUTS + ps7_pins.INPUTS:
    base, i = bus(p)
    conn.append(".%s(%s)" % (p, base if i is None else "%s[%d]" % (base, i)))
print("    PS7_PS7 u (" + ", ".join(conn) + ");")
print("endmodule")
print("module top; wire r, g; %s u (.led_red(r), .led_green(g)); endmodule" % (sys.argv[2] if len(sys.argv) > 2 else "BENCHTOP"))
PY
sed -i "s/BENCHTOP/${K}_bench_gen/" ps7_rtl.v
# DCO >= the RAM model's clock-to-out + 3 arcs at this RTL_ROUTE_PS (the header's RAM BOUNDARY), unless RTL_KEEP_DCO=1
DCO_DEFS=$(python3 - "$R/cells/sim/bd_prims_sim.v" "build/gen/${K}_kernel_bench.v" "${RTL_ROUTE_PS:-0}" "${RTL_KEEP_DCO:-0}" 2>> emit.log <<'PY'
import math, re, sys
tco = int(re.search(r"`define BD_RAM_TCO\s+(\d+)", open(sys.argv[1]).read()).group(1))
hop = 124 + int(sys.argv[3]); need = math.ceil((tco + 3 * hop) / hop)
low = [(n, int(v)) for n, v in re.findall(r"parameter\s+DELAY_(\w+_UCO)\s*=\s*(\d+)", open(sys.argv[2]).read()) if int(v) < need]
if low and sys.argv[4] != "1":
    sys.stderr.write("rtl_bench: %d DCO parameter(s) raised to %d for the RAM model's clock-to-out (%d ps at %d ps per arc)\n"
                     % (len(low), need, tco, hop))
    print(" ".join("-DBD_SZ_BRIDGE_I_UDUT_%s=%d" % (n.upper(), need) for n, _ in low))
elif low:
    sys.stderr.write("rtl_bench: RTL_KEEP_DCO=1: %d DCO parameter(s) shorter than the RAM model's clock-to-out kept\n" % len(low))
PY
)
iverilog -g2012 -gspecify -Wno-timescale -DBD_ROUTE_PS=${RTL_ROUTE_PS:-0} $DCO_DEFS -o rtl.vvp "$R/cells/sim/bd_prims_sim.v" \
    "$R"/cells/rtl/*.v "build/gen/${K}_kernel_bench.v" "build/gen/${K}_bench_gen.v" ps7_rtl.v \
    "$R/cells/gls/ps/ps7_bench.v" "$R/cells/gls/ps/tb_ps.v" > compile.log 2>&1 \
  || { echo "$K rtl COMPILE FAILED: $(grep -m1 -i error compile.log)"; exit 1; }
vvp -n rtl.vvp +FCLK_PS=12000 +MODE=1 +NRUNS=${GATE_NRUNS:-2} +VECFILE="$VEC" ${MEMEXP:+"+MEMDUMP=1"} \
    +TBATCH=${RTL_TBATCH:-400000} +TEND=200000000 ${RTL_PLUSARGS:-} > run.log 2>&1 || true
rm -f rtl.vvp
# the gate's verdict, verbatim (bench_gate.sh's inline python, between its `python3 - "$EXP" run.log` line and PY)
# (the call spans two lines since the runt monitor's arguments were added: everything up to the line with <<'PY' goes)
sed -n '/^python3 - "\$EXP" run.log/,/^PY$/p' "$R/research/tools/eventgraph/bench_gate.sh" | sed "0,/<<'PY'/d;\$d" > verdict.py
[ -s verdict.py ] || { echo "$K rtl NO VERDICT CODE (bench_gate.sh changed)"; exit 2; }
echo "$K rtl $(python3 verdict.py "$EXP" run.log "RTL (route ${RTL_ROUTE_PS:-0} ps/arc)" "$MEMEXP" "")"
