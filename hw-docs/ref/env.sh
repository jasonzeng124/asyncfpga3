# source this: . ref/env.sh [ice40|xc7|both]   (default: ice40)
#
# The open FPGA toolchain is built from source under ~/dev2/lib/fpgatoolchain
# and is NOT on the default PATH. openXC7 ships its own yosys (with
# synth_xilinx) -- distinct from the ice40 one, so "both" puts openXC7 first
# and leaves the ice40 tools reachable via $YOSYS / $NEXTPNR.

TC="${TC:-$HOME/dev2/lib/fpgatoolchain}"
_mode="${1:-ice40}"

case "$_mode" in
  ice40|both)
    export YOSYS="$TC/yosys/build/yosys"
    export NEXTPNR="$TC/nextpnr/build/nextpnr-ice40"   # getCellDelay-patched
    export ICEPACK="$TC/icestorm/icepack/icepack"
    export PATH="$TC/icestorm/icepack:$TC/icestorm/icetime:$PATH"
    ;;
esac

case "$_mode" in
  xc7|both)
    . "$TC/openxc7/export.sh"          # PATH, PYTHONPATH, NEXTPNR_XILINX_PYTHON_DIR, PRJXRAY_DB_DIR
    export CHIPDB="$TC/openxc7/xc7z010clg400.bin"
    export PART="xc7z010clg400-1"
    export PRJXRAY_SRC="$TC/openxc7-src/prjxray"
    ;;
esac

# Vivado Lab: hw_server + xsdb (NOT xsct in this install)
export VIVADO_LAB="$HOME/dev2/lib/vivado/2026.1/Vivado_Lab/bin"
export XSDB="$VIVADO_LAB/xsdb"
export HW_SERVER="$VIVADO_LAB/hw_server"

# JTAG
export OPENFPGALOADER="$HOME/dev2/lib/jtag/openFPGALoader/build/openFPGALoader"
export FX2_FW="$HOME/dev2/lib/jtag/fw/xusb_xp2.hex"

unset _mode
