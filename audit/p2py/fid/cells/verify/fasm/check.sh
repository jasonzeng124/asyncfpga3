#!/usr/bin/env bash
# Does the installed nextpnr write the bits the netlist asks for?
#
#     cells/verify/fasm/check.sh          (~15 s: one synth, one tiny route)
#
# Regression test for the three August 2026 bitstream bugs in patches/:
# lut-pinmap (131 gcd_hw LUTs written as another function), dsp-constpins
# (INMODE etc. left at the tile default, A gated to zero) and dsp-areg
# (AREG=1 written as AREG=2).  Each was invisible to the netlist, the SDF and
# every simulation, and toolchain.sh's fingerprints only say a patch is
# present -- the dsp-areg one ("ZAREG_2_ACASCREG_1") is in the unpatched
# source too and cannot fail.  This routes probe.v, which carries every
# encoding those bugs got wrong, and reads the FASM back against the netlist
# with verify/fasm_audit.py.
#
# Then the negative control, every run: the same FASM rewritten the way the
# unpatched writer at bfdeaf7c would have written it, one bug at a time
# (fasm_audit.py --write-unpatched), must FAIL the audit.  An emulation, not
# an unpatched binary -- there is none to run -- written line for line from
# the unpatched fasm.cc / pack_dsp_xc7.cc.
set -uo pipefail

TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
CELLS=$(cd "$(dirname "$0")/../.." && pwd)
SRC=$CELLS/verify/fasm
WORK=$CELLS/build/verify/fasm
AUDIT="python3 $CELLS/verify/fasm_audit.py"
mkdir -p "$WORK"

cat > "$WORK/probe.xdc" <<'EOF'
set_property PACKAGE_PIN U18 [get_ports clk]
set_property IOSTANDARD LVCMOS33 [get_ports clk]
set_property PACKAGE_PIN W13 [get_ports din]
set_property IOSTANDARD LVCMOS33 [get_ports din]
set_property PACKAGE_PIN W14 [get_ports dout]
set_property IOSTANDARD LVCMOS33 [get_ports dout]
EOF

"$TC/openxc7/bin/yosys" -p "
read_verilog -lib -specify $TC/openxc7/share/yosys/xilinx/cells_sim.v
read_verilog $SRC/probe.v
synth_xilinx -family xc7 -flatten -nosrl -nolutram -nobram -top fasm_probe
write_json $WORK/probe.json
" > "$WORK/yosys.log" 2>&1 || { echo "SYNTH FAILED"; tail -20 "$WORK/yosys.log"; exit 1; }

"$TC/openxc7/bin/nextpnr-xilinx" --chipdb "$TC/openxc7/xc7z010clg400.bin" \
    --xdc "$WORK/probe.xdc" --seed 1 --freq 50 \
    --json "$WORK/probe.json" --write "$WORK/probe_routed.json" \
    --fasm "$WORK/probe.fasm" > "$WORK/pnr.log" 2>&1 \
    || { echo "PNR FAILED"; tail -20 "$WORK/pnr.log"; exit 1; }

echo "== the installed nextpnr =="
# --min-*: the probe must actually exercise each bug, or a pass means nothing.
$AUDIT "$WORK/probe_routed.json" "$WORK/probe.fasm" --synth "$WORK/probe.json" \
    --min-runtogether 8 --min-dsp 3 || { echo "verify/fasm FAIL"; exit 1; }

echo "== negative controls: what each unpatched writer would have written =="
fail=0
for kind in pinmap areg constpins-packer constpins-inv; do
    $AUDIT "$WORK/probe_routed.json" "$WORK/probe.fasm" \
        --write-unpatched "$kind" "$WORK/unpatched_$kind.fasm" > /dev/null
    if $AUDIT "$WORK/probe_routed.json" "$WORK/unpatched_$kind.fasm" \
            --synth "$WORK/probe.json" > "$WORK/unpatched_$kind.log" 2>&1; then
        echo "  $kind: audit PASSED an unpatched FASM -- this check is blind"
        fail=1
    else
        echo "  $kind: caught ($(grep -c MISMATCH "$WORK/unpatched_$kind.log") mismatch(es))"
    fi
done
[ $fail -eq 0 ] || { echo "verify/fasm FAIL"; exit 1; }
echo "verify/fasm PASS -- the bitstream encodes the netlist, and the audit can tell when it does not"
