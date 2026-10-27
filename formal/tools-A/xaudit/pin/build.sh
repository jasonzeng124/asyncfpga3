#!/usr/bin/env bash
# Route ring3 / pipe3 (the xevents2 designs) on the xc7z010 and compute their prjxray
# per-arc delays, so that pinbands.py can give every LUT input pin its own band.
#
#     formal/tools-A/xaudit/pin/build.sh DESIGN SEED...     (DESIGN = ring3 | pipe3)
#
# Flow = formal/tools/fasm2lean/route.sh (cells/flow.sh's synth options; nextpnr
# --ignore-loops), with --freq 100 (CLAUDE.md: never the 12 MHz default) and a pinned
# --seed.  cells/verify/toolchain.sh runs first: if it fails nothing routed here is a
# result.  fasm_audit.py checks the routed JSON's pin record (X_ORIG_PORT) against the
# FASM, which is the record pinbands.py uses for the placer's pin permutation.
# Delays: origin/claude/research:cells/gls/fid/xray_delay.py (read with git show; it
# must be at $XRAY_DELAY), prjxray-db zynq7 of the toolchain.
# Scratch: /tmp/events2pin/build (large files; not for git).
set -euo pipefail
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
HERE=$(cd "$(dirname "$0")" && pwd)
REPO=$(cd "$HERE/../../../.." && pwd)
D=$1; shift
OUT=/tmp/events2pin/build; mkdir -p "$OUT"
XRAY_DELAY=${XRAY_DELAY:-/tmp/events2pin/xray_delay.py}
PRJ=$TC/openxc7-src/prjxray
case $D in
  ring3) cat > "$OUT/ring3.v" <<'EOF'
`default_nettype none
// tb_ring's control ring, N = 3, K = 1 (cells/tb/tb_ring.v), with the frozen cells.
module ring3 (input wire rst, output wire [2:0] c);
    bd_c2n_set u0 (.a(c[2]), .b(c[1]), .rst(rst), .q(c[0]));
    bd_c2n     u1 (.a(c[0]), .b(c[2]), .rst(rst), .q(c[1]));
    bd_c2n     u2 (.a(c[1]), .b(c[0]), .rst(rst), .q(c[2]));
endmodule
`default_nettype wire
EOF
    PORTS="rst c[0] c[1] c[2]" ;;
  pipe3) cat > "$OUT/pipe3.v" <<'EOF'
`default_nettype none
// bd_pipe W=2 N=3 with its defaults (formal/tools-A/xaudit/mkdesign.py's pipe3).
module pipe3 (input wire rst, input wire req_in, output wire ack_in, input wire [1:0] data_in,
              output wire req_out, input wire ack_out, output wire [1:0] data_out);
    bd_pipe #(.W(2), .N(3)) u (.rst(rst), .req_in(req_in), .ack_in(ack_in), .data_in(data_in),
        .req_out(req_out), .ack_out(ack_out), .data_out(data_out));
endmodule
`default_nettype wire
EOF
    PORTS="rst req_in ack_in data_in[0] data_in[1] req_out ack_out data_out[0] data_out[1]" ;;
  *) echo "unknown design $D"; exit 2 ;;
esac
PINS=(B19 A20 C20 B20 D19 D20 E18 E19 F16 F17)
X="$OUT/$D.xdc"; : > "$X"; i=0
for p in $PORTS; do
  echo "set_property PACKAGE_PIN ${PINS[$i]} [get_ports {$p}]" >> "$X"
  echo "set_property IOSTANDARD LVCMOS33 [get_ports {$p}]" >> "$X"
  i=$((i + 1))
done
"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $REPO/cells/rtl/bd_ce.v $REPO/cells/rtl/bd_latch.v $REPO/cells/rtl/bd_link.v $OUT/$D.v
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -noclkbuf -top $D
write_json $OUT/$D.json
" > "$OUT/$D.yosys.log" 2>&1 || { tail -20 "$OUT/$D.yosys.log"; exit 1; }
for SEED in "$@"; do
  B=$OUT/${D}_s$SEED
  "$REPO/cells/verify/toolchain.sh" > "$B.toolchain" 2>&1 \
      || { cat "$B.toolchain"; echo "toolchain.sh FAILED: nothing routed here is a result"; exit 1; }
  "$TC/openxc7/bin/nextpnr-xilinx" --chipdb "$TC/openxc7/xc7z010clg400.bin" \
      --xdc "$X" --ignore-loops --seed "$SEED" --freq 100 \
      --json "$OUT/$D.json" --write "$B"_routed.json --sdf "$B.sdf" --fasm "$B.fasm" \
      > "$B.pnr.log" 2>&1 || { tail -30 "$B.pnr.log"; exit 1; }
  python3 "$REPO/cells/verify/fasm_audit.py" "$B"_routed.json "$B.fasm" --synth "$OUT/$D.json" > "$B.audit" 2>&1 \
      || { cat "$B.audit"; echo "fasm_audit FAILED"; exit 1; }
  PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python${PYLIB:+:$PYLIB}" python3 "$XRAY_DELAY" \
      --routed "$B"_routed.json --sdf "$B.sdf" --out "$B.xray.sdf" --arcs "$B.arcs.tsv" > "$B.xray.log" 2>&1 \
      || { tail -20 "$B.xray.log"; echo "xray_delay FAILED"; exit 1; }
  echo "$D seed $SEED: routed, nextpnr $(grep -m1 sha256 "$B.toolchain" | awk '{print $2}'), $(tail -1 "$B.audit"), $(head -1 "$B.xray.log")"
done
