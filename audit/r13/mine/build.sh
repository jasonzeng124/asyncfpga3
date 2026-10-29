#!/bin/bash
# auditor r13: synth + route mine.v (or $1) the way cells/verify/fasm/check.sh routes probe.v
set -u
TC=${TC:-/root/audit-tc}; D=$(cd $(dirname $0) && pwd); NAME=${1:-mine}; OUT=$HOME/r13work/routes/$NAME; mkdir -p $OUT
cat > $OUT/x.xdc <<'X'
set_property PACKAGE_PIN U18 [get_ports clk]
set_property IOSTANDARD LVCMOS33 [get_ports clk]
set_property PACKAGE_PIN W13 [get_ports din]
set_property IOSTANDARD LVCMOS33 [get_ports din]
set_property PACKAGE_PIN W14 [get_ports dout]
set_property IOSTANDARD LVCMOS33 [get_ports dout]
X
$TC/openxc7/bin/yosys -p "read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $D/$NAME.v
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -top $NAME
write_json $OUT/$NAME.json" > $OUT/yosys.log 2>&1 || { echo SYNTH FAIL; exit 1; }
$TC/openxc7/bin/nextpnr-xilinx --chipdb $TC/openxc7/xc7z010clg400.bin --xdc $OUT/x.xdc --seed 1 --freq 50 \
  --json $OUT/$NAME.json --write $OUT/${NAME}_routed.json --fasm $OUT/$NAME.fasm --sdf $OUT/$NAME.sdf > $OUT/pnr.log 2>&1 || { echo PNR FAIL; tail $OUT/pnr.log; exit 1; }
echo built $OUT
