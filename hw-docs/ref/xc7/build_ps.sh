#!/usr/bin/env bash
# PS7/AXI-wrapped bitstream build for the EBAZ4205 (xc7z010clg400-1):
#   build_ps.sh <design.v> <wrapper.v> <top> <xdc> <outdir>
#   boards/xc7/build_ps.sh build/m3/fib/fib.v boards/xc7/zynq/fib_ps_top.v \
#     fib_ps_top boards/xc7/zynq/ebaz4205.xdc build/fib_ps
#
# Sibling to run_flow.sh, NOT a bend of it (see QUESTIONS.md Q6): run_flow.sh
# is built for a bare clockless core (no clock, no hard macros, an auto-XDC
# that explicitly disclaims ever touching hardware, and a signoff step keyed
# to the async sidecar's own hlatch/merge structural shape). A PS7/AXI
# wrapper is a genuinely different artifact -- a real synchronous AXI FSM
# clocked off FCLK0, the PS7/BUFG hard macros, and only 2 real package pins
# (the AXI/PS7 wiring is internal fabric-to-hard-macro routing, never
# touches a pin) -- so this is a separate script reusing what actually
# carries over: the SB_LUT4 blackbox trick, the LUT4/loop_breaker techmap
# steps (the wrapper still `includes the design, which still uses the
# library), the LUT-map SAT equivalence check, and the dedup-lut-inputs
# gate. It does NOT reuse run_flow.sh's auto-XDC (a real, checked-in XDC is
# required instead) or its async timing-signoff step (see the note at the
# bottom of this file for why that's skipped here, not silently dropped).
#
# PS7/BUFG need NO special blackbox declaration: unlike this project's
# SB_LUT4 (an ICE40 primitive reused on a Xilinx flow, hence the explicit
# `read_verilog -lib +/ice40/cells_sim.v`), PS7/BUFG are native Xilinx
# primitives synth_xilinx already knows about -- confirmed empirically
# before writing this file (a minimal PS7+BUFG-only module through this
# project's own yosys with `-family xc7` leaves them as opaque cells with
# zero extra help; see QUESTIONS.md Q6).
set -euo pipefail

if [ $# -ne 5 ]; then
  echo "usage: $0 <design.v> <wrapper.v> <top> <xdc> <outdir>" >&2
  exit 2
fi

DESIGN="$(readlink -f "$1")"
WRAPPER="$(readlink -f "$2")"
TOP="$3"
XDC="$(readlink -f "$4")"
OUTDIR="$(mkdir -p "$5" && readlink -f "$5")"

# Guard against the exact mistake this project already made once this
# session: hlsc's default guardband (6/5, margin 3) is the ice40 model
# and FAILS xc7 signoff (request-line delays are ~half what xc7 routing
# needs, boards/xc7/README.md) -- a design built without --depth-scale
# 12/5 --margin 8 can still PASS a few golden vectors on real hardware
# by routing luck (STATUS.md's F16 case), which is not the same as
# being signed off. hlsc stamps the margin into the generated file's
# header; refuse to build hardware from anything under 8 here.
design_margin="$(grep -m1 -oP '(?<=margin=)\d+' "$DESIGN" || echo 0)"
if [ "$design_margin" -lt 8 ]; then
  echo "ERROR: $DESIGN was built with margin=$design_margin (need >=8," \
       "i.e. --depth-scale 12/5 --margin 8 -- boards/xc7/README.md)." >&2
  echo "       Rebuild it with those flags before flashing hardware." >&2
  exit 1
fi

BOARD_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(readlink -f "$BOARD_DIR/../..")"
RTL="$ROOT/rtl"

TOOLCHAIN="${TOOLCHAIN:-$HOME/dev2/lib/fpgatoolchain}"
YOSYS="${YOSYS:-$TOOLCHAIN/yosys/build/yosys}"
NEXTPNR="${NEXTPNR:-$TOOLCHAIN/openxc7/bin/nextpnr-xilinx}"
CHIPDB="${CHIPDB:-$TOOLCHAIN/openxc7/xc7z010clg400.bin}"
PART="${PART:-xc7z010clg400-1}"
PRJXRAY_DB="${PRJXRAY_DB:-$TOOLCHAIN/openxc7/share/nextpnr/prjxray-db/zynq7}"
PRJXRAY_SRC="${PRJXRAY_SRC:-$TOOLCHAIN/openxc7-src/prjxray}"
FASM2FRAMES="$PRJXRAY_SRC/utils/fasm2frames.py"
FRAMES2BIT="${FRAMES2BIT:-$TOOLCHAIN/openxc7/bin/xc7frames2bit}"
SEED="${SEED:-1}"

echo "== xc7 PS build: design=$DESIGN wrapper=$WRAPPER top=$TOP outdir=$OUTDIR part=$PART"

# ---------------------------------------------------------------------------
# Step 0: SB_LUT4 -> LUT4 init-bit equivalence check (mandatory, every run,
# same as run_flow.sh -- the wrapper still pulls in the library via the
# design it wraps).
# ---------------------------------------------------------------------------
echo "== LUT map equivalence check"
YOSYS="$YOSYS" "$BOARD_DIR/check_lut_map.sh" "$OUTDIR/lutcheck"

# ---------------------------------------------------------------------------
# Step 1: synth. Same recipe as synth.ys (ice40 cells_sim.v as blackbox for
# SB_LUT4, -nosrl -nolutram -nobram to forbid inference paths that could
# only misfire on the design's OWN behavioral memory-shaped code -- PS7/BUFG
# are explicit hard-macro instances, not inference candidates, so these
# flags don't touch them), but reading BOTH the design and the wrapper, and
# rooting hierarchy at the wrapper's top instead of the bare core.
# ---------------------------------------------------------------------------
JSON="$OUTDIR/$TOP.json"
echo "== yosys"
"$YOSYS" -q -l "$OUTDIR/yosys.log" -p "
  read_verilog -lib +/ice40/cells_sim.v
  read_verilog -DSYNTHESIS -sv -I $RTL $RTL/async.sv
  read_verilog -DSYNTHESIS -sv -I $RTL $DESIGN
  read_verilog -DSYNTHESIS -sv -I $RTL $WRAPPER
  hierarchy -top $TOP
  setattr -mod -unset keep_hierarchy
  synth_xilinx -family xc7 -top $TOP -flatten -nodsp -nosrl -nolutram -nobram
  scc
  select -clear
  tee -o $OUTDIR/core.stat stat
  techmap -map $BOARD_DIR/sb_lut4_map.v
  select -assert-none t:SB_LUT4
  tee -o $OUTDIR/mapped.stat stat
  techmap -map $BOARD_DIR/loop_breaker_dissolve.v
  select -assert-none t:loop_breaker
  delete t:\$scopeinfo
  tee -o $OUTDIR/final.stat stat
  write_json $JSON
"

# ---------------------------------------------------------------------------
# Step 1b: fold duplicated LUT input nets before P&R (same hazard, same
# fix, as run_flow.sh -- see dedup_lut_inputs_xc7.py's header).
# ---------------------------------------------------------------------------
echo "== dedup-lut-inputs (pre-P&R fold)"
python3 "$BOARD_DIR/dedup_lut_inputs_xc7.py" "$JSON"

# ---------------------------------------------------------------------------
# Step 2: place and route against the REAL board XDC (led_red/led_green
# only -- everything else rides M_AXI_GP0 through the PS7 hard macro's own
# internal routing, never a package pin). --ignore-loops is still required
# (the wrapped core is still full of intentional combinational loops).
# ---------------------------------------------------------------------------
echo "== nextpnr-xilinx --ignore-loops"
"$NEXTPNR" --chipdb "$CHIPDB" --xdc "$XDC" --ignore-loops \
  --json "$JSON" --write "$OUTDIR/${TOP}_routed.json" \
  --fasm "$OUTDIR/$TOP.fasm" --seed "$SEED" \
  -l "$OUTDIR/nextpnr.log" -q \
  || { tail -40 "$OUTDIR/nextpnr.log"; exit 1; }
grep -E 'SLICE_LUTX:|SLICE_FFX:|BUFGCTRL:|PS7:|Routing complete' "$OUTDIR/nextpnr.log" | sed 's/^/  /' || true

# ---------------------------------------------------------------------------
# Step 2b: post-route dedup-lut-inputs gate (same as run_flow.sh).
# ---------------------------------------------------------------------------
echo "== dedup-lut-inputs (post-route check)"
python3 "$BOARD_DIR/dedup_lut_inputs_xc7.py" --check "$OUTDIR/${TOP}_routed.json"

# ---------------------------------------------------------------------------
# Step 3: FASM -> frames -> bitstream.
# ---------------------------------------------------------------------------
HAVE_BIT="no"
if [ -f "$FASM2FRAMES" ] && [ -x "$FRAMES2BIT" ]; then
  echo "== fasm2frames + xc7frames2bit"
  PYTHONPATH="$PRJXRAY_SRC:$TOOLCHAIN/openxc7/lib/python${PYTHONPATH:+:$PYTHONPATH}" \
    python3 "$FASM2FRAMES" --db-root "$PRJXRAY_DB" --part "$PART" \
    "$OUTDIR/$TOP.fasm" "$OUTDIR/$TOP.frames" 2> >(grep -v -e '^ *$' -e Warning -e antlr -e 'pip ' -e warn >&2 || true)
  "$FRAMES2BIT" --part_file "$PRJXRAY_DB/$PART/part.yaml" --part_name "$PART" \
    --frm_file "$OUTDIR/$TOP.frames" --output_file "$OUTDIR/$TOP.bit"
  HAVE_BIT="yes"
  echo "  bitstream: $OUTDIR/$TOP.bit ($(stat -c%s "$OUTDIR/$TOP.bit") bytes)"
else
  echo "WARNING: prjxray frame tools not found ($FASM2FRAMES / $FRAMES2BIT);"
  echo "         stopping at routed FASM."
fi

# ---------------------------------------------------------------------------
# Step 4: structural sanity (library-invariant counts only -- same checks
# as run_flow.sh's step 5, points 1-4: loop_breaker/SB_LUT4 bookkeeping,
# the 1:1 SB_LUT4->LUT4 retarget, breaker dissolution, and the "yosys never
# saw a real loop" check. These are about the LIBRARY's own structure and
# hold regardless of the extra PS7/BUFG/AXI-FSM cells around it, so they
# stay meaningful here. Point 5 (sidecar sum-T check) and the ice40-style
# exact structural signoff do NOT apply -- those assume the top-level
# module's ports ARE the async sidecar's r_i/a_i/d_i/r_o/a_o/d_o/rst
# bundle, which fib_ps_top's ports (led_red/led_green) are not.
# ---------------------------------------------------------------------------
python3 - "$OUTDIR" <<'PYEOF'
import re, sys
outdir = sys.argv[1]
fails = []

def counts(stat_file):
    c = {}
    for line in open(stat_file):
        m = re.match(r"\s*(\d+)\s+(\S+)\s*$", line)
        if m:
            c[m.group(2)] = c.get(m.group(2), 0) + int(m.group(1))
    return c

core = counts(f"{outdir}/core.stat")
mapped = counts(f"{outdir}/mapped.stat")
final = counts(f"{outdir}/final.stat")
lb = core.get("loop_breaker", 0)
sb = core.get("SB_LUT4", 0)
lut_types = ["LUT1", "LUT2", "LUT3", "LUT4", "LUT5", "LUT6"]

if lb == 0 or lb % 5 != 0:
    fails.append(f"loop_breaker count {lb} is not a positive multiple of 5")
lib_luts = lb // 5
if sb != lib_luts:
    fails.append(f"SB_LUT4 count {sb} != loop_breaker/5 = {lib_luts}")
if mapped.get("SB_LUT4", 0) != 0:
    fails.append(f"{mapped.get('SB_LUT4')} SB_LUT4 survived the retarget")
if mapped.get("LUT4", 0) != core.get("LUT4", 0) + sb:
    fails.append(f"LUT4 after retarget {mapped.get('LUT4', 0)} != datapath {core.get('LUT4', 0)} + library {sb}")
for t in lut_types:
    if t == "LUT4":
        continue
    if mapped.get(t, 0) != core.get(t, 0):
        fails.append(f"{t} changed across retarget: {core.get(t, 0)} -> {mapped.get(t, 0)}")
if final.get("loop_breaker", 0) != 0:
    fails.append(f"{final.get('loop_breaker', 0)} loop_breaker cells survived")
ylog = open(f"{outdir}/yosys.log").read()
for m in re.finditer(r"Found (\d+) SCCs", ylog):
    if int(m.group(1)) != 0:
        fails.append(f"yosys detected combinational loops: '{m.group(0)}'")

if fails:
    print("result: FAIL")
    for f in fails:
        print(f"  ! {f}")
    sys.exit(1)
print(f"structural sanity: PASS (library LUTs={lib_luts}, "
      f"PS7={final.get('PS7', 0)}, BUFG={final.get('BUFG', 0)})")
PYEOF

if [ "$HAVE_BIT" = "yes" ]; then
  echo "== done: $OUTDIR/$TOP.bit"
else
  echo "== done (FASM only): $OUTDIR/$TOP.fasm"
fi
