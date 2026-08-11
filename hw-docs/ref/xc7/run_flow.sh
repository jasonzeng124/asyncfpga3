#!/usr/bin/env bash
# Xilinx 7-series (openXC7) flow for async (clockless) bundled-data designs:
#   run_flow.sh <design.v> <top> <outdir>
# Produces <outdir>/<top>.fasm (routed) and, when the prjxray frame tools are
# available, <outdir>/<top>.frames + <outdir>/<top>.bit, plus a sanity
# report, with the deliberate combinational feedback structures verified
# intact. Target: xc7z010clg400-1 (EBAZ4205). See boards/xc7/README.md.
set -euo pipefail

if [ $# -ne 3 ]; then
  echo "usage: $0 <design.v> <top> <outdir>" >&2
  exit 2
fi

DESIGN="$(readlink -f "$1")"
TOP="$2"
OUTDIR="$(mkdir -p "$3" && readlink -f "$3")"

BOARD_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT="$(readlink -f "$BOARD_DIR/../..")"
RTL="$ROOT/rtl"

# Tool locations (override via env if needed).
TOOLCHAIN="${TOOLCHAIN:-$HOME/dev2/lib/fpgatoolchain}"
YOSYS="${YOSYS:-$TOOLCHAIN/yosys/build/yosys}"
# NOTE: use the non-.bak nextpnr-xilinx -- it is the newer build (same
# version string as the .bak but later mtime) carrying the owner's
# timing-model fix (06-field-notes.md).
NEXTPNR="${NEXTPNR:-$TOOLCHAIN/openxc7/bin/nextpnr-xilinx}"
CHIPDB="${CHIPDB:-$TOOLCHAIN/openxc7/xc7z010clg400.bin}"
PART="${PART:-xc7z010clg400-1}"
PRJXRAY_DB="${PRJXRAY_DB:-$TOOLCHAIN/openxc7/share/nextpnr/prjxray-db/zynq7}"
# Optional placement-seed override (nextpnr's own default if unset). Timing
# signoff is placement-scatter-sensitive by nature (F16, QUESTIONS.md Q16):
# any netlist change re-rolls every routed delay, so a thin margin on one
# seed carries no principled meaning and per-design --seed iteration is an
# accepted engineering cost here, same as --depth-scale/--margin already
# are (D19/D20). Empty by default so every existing invocation is unaffected.
NEXTPNR_SEED="${NEXTPNR_SEED:-}"
# fasm2frames.py needs the prjxray source tree on PYTHONPATH (for `prjxray`
# and `utils`) plus the `fasm` python module from openxc7/lib/python. The
# `fasm2frames` wrapper installed in ~/.local/bin is broken (missing `utils`
# module); invoke the script directly.
PRJXRAY_SRC="${PRJXRAY_SRC:-$TOOLCHAIN/openxc7-src/prjxray}"
FASM2FRAMES="$PRJXRAY_SRC/utils/fasm2frames.py"
FRAMES2BIT="${FRAMES2BIT:-$TOOLCHAIN/openxc7/bin/xc7frames2bit}"

echo "== xc7 flow: design=$DESIGN top=$TOP outdir=$OUTDIR part=$PART"

# ---------------------------------------------------------------------------
# Step 0: SB_LUT4 -> LUT4 init-bit equivalence check (mandatory, every run).
# Silent truth-table corruption from a wrong init permutation is the failure
# mode that costs weeks on hardware; ~1 min of SAT per build is cheap
# insurance that sb_lut4_map.v is still correct for this yosys.
# ---------------------------------------------------------------------------
echo "== LUT map equivalence check"
YOSYS="$YOSYS" "$BOARD_DIR/check_lut_map.sh" "$OUTDIR/lutcheck"

# ---------------------------------------------------------------------------
# Step 1: compose synth.gen.ys from the template and run yosys.
# No IO shim (unlike ice40): xc7z010clg400 has 100 PL IO pads in banks 34/35
# and addmul-class designs fit directly. The XDC generator in step 2 errors
# out with a clear message if a design ever exceeds the pad count.
# ---------------------------------------------------------------------------
JSON="$OUTDIR/$TOP.json"
sed -e "s|@RTL_DIR@|$RTL|g" \
    -e "s|@DESIGN@|$DESIGN|g" \
    -e "s|@TOP@|$TOP|g" \
    -e "s|@OUTDIR@|$OUTDIR|g" \
    -e "s|@BOARD_DIR@|$BOARD_DIR|g" \
    -e "s|@JSON@|$JSON|g" \
    "$BOARD_DIR/synth.ys" > "$OUTDIR/synth.gen.ys"

echo "== yosys"
"$YOSYS" -q -l "$OUTDIR/yosys.log" -s "$OUTDIR/synth.gen.ys"

# ---------------------------------------------------------------------------
# Step 1b: fold duplicated LUT input nets before P&R. nextpnr-xilinx's
# fixupPlacement() merges same-net LUT pins on fractured slices and mangles
# the FASM writer's X_ORIG_PORT_A* attribute, silently zeroing the INIT rows
# for the merged pin's terms -- a dead cell on real hardware invisible to
# every sim/audit run on the logical netlist (bench-debugged on silicon,
# async-hls-v2 EBAZ4205 knapsack bring-up, 2026-07-21). This project's every
# delay-chain stage[0] hits it by construction (.i0(path[0]) and .i1(i) are
# the same net on the first hop); see dedup_lut_inputs_xc7.py's header.
# ---------------------------------------------------------------------------
echo "== dedup-lut-inputs (pre-P&R fold)"
python3 "$BOARD_DIR/dedup_lut_inputs_xc7.py" "$JSON"

# ---------------------------------------------------------------------------
# Step 2: auto-generate the XDC. nextpnr-xilinx hard-errors on any pad
# without an IOSTANDARD, and its XDC parser did not accept a portless/
# wildcard [get_ports] form (tested), so every port bit gets an explicit
# PACKAGE_PIN + IOSTANDARD from the prjxray package_pins.csv (PL banks 34/35
# only; banks 0/500/501/502 are config/PS pins). Pin choice is arbitrary --
# this bitstream never touches hardware.
# ---------------------------------------------------------------------------
XDC="$OUTDIR/$TOP.gen.xdc"
python3 - "$JSON" "$TOP" "$PRJXRAY_DB/$PART/package_pins.csv" "$XDC" <<'PYEOF'
import csv, json, sys
json_path, top, pins_csv, xdc_path = sys.argv[1:5]
ports = json.load(open(json_path))["modules"][top]["ports"]
bits = []
for name, p in ports.items():
    n = len(p["bits"])
    bits += [name] if n == 1 else [f"{name}[{i}]" for i in range(n)]
pins = [r["pin"] for r in csv.DictReader(open(pins_csv))
        if r["bank"] in ("34", "35")]
if len(bits) > len(pins):
    sys.exit(f"{len(bits)} port bits > {len(pins)} PL pads; an IO shim like "
             "boards/ice40's would be needed -- see README.md")
with open(xdc_path, "w") as f:
    for b, pin in zip(bits, pins):
        f.write(f"set_property PACKAGE_PIN {pin} [get_ports {{{b}}}]\n")
        f.write(f"set_property IOSTANDARD LVCMOS33 [get_ports {{{b}}}]\n")
print(f"XDC: {len(bits)} port bits on {len(pins)} available PL pads",
      file=sys.stderr)
PYEOF

# ---------------------------------------------------------------------------
# Step 3: place and route. --ignore-loops is REQUIRED: the netlist is full of
# intentional combinational loops and nextpnr's timing-graph construction
# would otherwise abort. "No clocks found in design" warnings are expected
# and correct. nextpnr's timing/Fmax output is meaningless for clockless
# logic -- ignore it (custom signoff via the nextpnr Python API per-cell
# delay hooks is a separate milestone; see README.md).
# ---------------------------------------------------------------------------
echo "== nextpnr-xilinx --ignore-loops"
# --post-route timing_dump.py: writes the routed pin-level delay graph
# ($TOP.graph.json) via the owner's getCellDelay/getRouteDelayPs
# pybindings -- the xc7 signoff data source (stock nextpnr-xilinx has no
# --sdf, Q7b). PNR_SYNTH_JSON must be the SAME pre-place JSON passed to
# --json (logical-pin resolution against LUT fracturing; see the dump's
# header).
SEED_ARGS=()
if [ -n "$NEXTPNR_SEED" ]; then
  SEED_ARGS=(--seed "$NEXTPNR_SEED")
fi
PNR_SYNTH_JSON="$JSON" PNR_GRAPH_OUT="$OUTDIR/$TOP.graph.json" \
"$NEXTPNR" --chipdb "$CHIPDB" --xdc "$XDC" --ignore-loops \
  --json "$JSON" --write "$OUTDIR/${TOP}_routed.json" \
  --fasm "$OUTDIR/$TOP.fasm" -l "$OUTDIR/nextpnr.log" -q \
  "${SEED_ARGS[@]}" \
  --post-route "$BOARD_DIR/timing_dump.py"

# ---------------------------------------------------------------------------
# Step 3b: post-route dedup-lut-inputs gate. Fails the flow (nonzero exit)
# if nextpnr merged any LUT pins carrying a LIVE (non-constant) net -- i.e.
# the pre-P&R fold above missed a case, or nextpnr found a NEW fractured-
# slice merge the fold didn't anticipate. A design that fails this check is
# not a deliverable: it may be silently wrong on real hardware while every
# other gate above stays green.
# ---------------------------------------------------------------------------
echo "== dedup-lut-inputs (post-route check)"
python3 "$BOARD_DIR/dedup_lut_inputs_xc7.py" --check "$OUTDIR/${TOP}_routed.json"

# ---------------------------------------------------------------------------
# Step 4: FASM -> frames -> bitstream (skipped, with a warning, if the
# prjxray tools are absent; the routed FASM is the flow's primary artifact).
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
else
  echo "WARNING: prjxray frame tools not found ($FASM2FRAMES / $FRAMES2BIT);"
  echo "         stopping at routed FASM."
fi

# ---------------------------------------------------------------------------
# Step 5: sanity checks + report.
# ---------------------------------------------------------------------------
TIMING_JSON="${DESIGN%.v}.timing.json"
python3 - "$OUTDIR" "$TOP" "$HAVE_BIT" "$TIMING_JSON" <<'PYEOF'
import json, os, re, sys

outdir, top, have_bit, timing_path = \
    sys.argv[1], sys.argv[2], sys.argv[3] == "yes", sys.argv[4]
fails, notes = [], []

def counts(stat_file):
    c = {}
    for line in open(stat_file):
        m = re.match(r"\s*(\d+)\s+(\S+)\s*$", line)
        if m:
            c[m.group(2)] = c.get(m.group(2), 0) + int(m.group(1))
    return c

core = counts(f"{outdir}/core.stat")     # post synth_xilinx
mapped = counts(f"{outdir}/mapped.stat") # post SB_LUT4->LUT4 techmap
final = counts(f"{outdir}/final.stat")   # post loop_breaker dissolution

lb = core.get("loop_breaker", 0)
sb = core.get("SB_LUT4", 0)
lut_types = ["LUT1", "LUT2", "LUT3", "LUT4", "LUT5", "LUT6",
             "MUXF7", "MUXF8", "CARRY4", "IBUF", "OBUF"]

# 1. loop_breaker bookkeeping: every library lut has exactly 5 breakers and
#    exactly one SB_LUT4 (on xc7 the library/datapath cell types are
#    disjoint pre-map, so this is an exact check, stronger than ice40's).
if lb == 0 or lb % 5 != 0:
    fails.append(f"loop_breaker count {lb} is not a positive multiple of 5")
lib_luts = lb // 5
if sb != lib_luts:
    fails.append(f"SB_LUT4 count {sb} != loop_breaker/5 = {lib_luts}")

# 2. SB_LUT4 -> LUT4 retarget must be exactly 1:1 and touch nothing else.
if mapped.get("SB_LUT4", 0) != 0:
    fails.append(f"{mapped.get('SB_LUT4')} SB_LUT4 survived the retarget")
if mapped.get("LUT4", 0) != core.get("LUT4", 0) + sb:
    fails.append(f"LUT4 after retarget {mapped.get('LUT4', 0)} != "
                 f"datapath {core.get('LUT4', 0)} + library {sb}")
for t in lut_types:
    if t == "LUT4":
        continue
    if mapped.get(t, 0) != core.get(t, 0):
        fails.append(f"{t} changed across retarget: "
                     f"{core.get(t, 0)} -> {mapped.get(t, 0)}")
if mapped.get("loop_breaker", 0) != lb:
    fails.append("loop_breaker count changed across retarget")

# 3. breaker dissolution must not change any real cell count, and no breaker
#    may survive into the JSON.
for t in lut_types:
    if final.get(t, 0) != mapped.get(t, 0):
        fails.append(f"{t} changed across dissolution: "
                     f"{mapped.get(t, 0)} -> {final.get(t, 0)}")
if final.get("loop_breaker", 0) != 0:
    fails.append(f"{final['loop_breaker']} loop_breaker cells survived")

# 4. yosys must never have seen (let alone broken) the feedback loops.
#    (synth_xilinx's pass list logs no "Found N SCCs" lines at all with the
#    blackboxes in place -- but check any that do appear are 0.)
ylog = open(f"{outdir}/yosys.log").read()
for m in re.finditer(r"Found (\d+) SCCs", ylog):
    if int(m.group(1)) != 0:
        fails.append(f"yosys detected combinational loops: '{m.group(0)}'")
bad_lines = [l for l in ylog.splitlines()
             if re.search(r"break", l, re.I) and "breaker" not in l
             and not l.startswith("Generating RTLIL representation")]
if bad_lines:
    fails.append("suspicious 'break' lines in yosys.log: " + "; ".join(bad_lines[:5]))
scc_cells = [t for t in final if "SCC_BREAKER" in t.upper()]
if scc_cells:
    fails.append(f"abc9 SCC breaker cells in final netlist: {scc_cells}")
removed = re.findall(r"Removed a total of (\d+) cells", ylog)
notes.append(f"opt cell removals during datapath lowering: {removed} "
             "(datapath $-cells only; library counts proven intact above)")

# 5. rough consistency vs the compiler's timing sidecar. The M3 backend
#    renamed "stages" to "elements" (hlatch/merge_delay, and from M6 also
#    ram1rw/statevar kinds); the exact per-element structural check lives in
#    the ice40 timing-signoff step (xc7 signoff pending Q7/Q13 — no working
#    --sdf path confirmed yet). Here: sum-T sanity only, same as ice40.
if os.path.exists(timing_path):
    t = json.load(open(timing_path))
    elems = t.get("elements", t.get("stages", []))
    sum_t = sum(s["T"] for s in elems)
    if sum_t > lib_luts:
        fails.append(f"delay-chain LUTs (sum T={sum_t}) exceed library LUTs {lib_luts}")
    else:
        notes.append(f"sidecar: {len(elems)} timing elements, sum T={sum_t} "
                     f"delay LUTs <= {lib_luts} library LUTs (exact structural "
                     "check is the ice40 signoff step; xc7 signoff pending)")
else:
    notes.append(f"no timing sidecar at {timing_path}; skipped consistency check")

# 6. LUT-map equivalence check evidence (step 0 aborts the flow on failure;
#    record the proof count here).
try:
    eqlog = open(f"{outdir}/lutcheck/check.log").read()
    n_ok = eqlog.count("SAT proof finished - no model found: SUCCESS")
    notes.append(f"SB_LUT4->LUT4 map: {n_ok} SAT proofs (12 init miters + "
                 "16 anchor proofs) in lutcheck/")
    if n_ok < 28:
        fails.append(f"only {n_ok} SAT proofs in lutcheck/check.log (expect 28)")
except FileNotFoundError:
    fails.append("missing lutcheck/check.log")

# 7. nextpnr / bitstream results.
plog = open(f"{outdir}/nextpnr.log").read()
if "Routing complete" not in plog:
    fails.append("nextpnr did not report 'Routing complete'")
if re.search(r"^ERROR", plog, re.M):
    fails.append("ERROR lines in nextpnr.log")
util = {m.group(1): (int(m.group(2)), int(m.group(3)))
        for m in re.finditer(r"(\S+):\s+(\d+)/\s*(\d+)\s+\d+%", plog)}
fasm_path = f"{outdir}/{top}.fasm"
if not (os.path.exists(fasm_path) and os.path.getsize(fasm_path) > 0):
    fails.append("missing/empty .fasm")
if have_bit:
    bit_path = f"{outdir}/{top}.bit"
    if not (os.path.exists(bit_path) and os.path.getsize(bit_path) > 0):
        fails.append("missing/empty .bit")
    bit_note = f"{bit_path} ({os.path.getsize(bit_path)} bytes)" \
        if os.path.exists(bit_path) else "MISSING"
else:
    bit_note = "not built (prjxray frame tools unavailable)"

slice_lut = util.get("SLICE_LUTX", ("?", "?"))
inbuf = util.get("IOB33_INBUF_EN", ("?", "?"))
outbuf = util.get("IOB33_OUTBUF", ("?", "?"))

def row(t):
    return (f"{t:<12}: core {core.get(t, 0):>4}  mapped {mapped.get(t, 0):>4}  "
            f"final {final.get(t, 0):>4}")
table = "\n".join(row(t) for t in
                  ["SB_LUT4", "loop_breaker"] + lut_types
                  if core.get(t, 0) or mapped.get(t, 0) or final.get(t, 0))

report = f"""xc7 (openXC7) async flow sanity report
======================================
design top          : {top}   part: xc7z010clg400-1
library LUTs        : {lib_luts} SB_LUT4 -> LUT4 (= loop_breaker/5 = {lb}/5)
datapath cells      : mapped by synth_xilinx (see table)
loop_breaker post   : {final.get("loop_breaker", 0)}
cell counts by stage (core = post synth_xilinx, mapped = post SB_LUT4->LUT4,
                      final = post breaker dissolution):
{table}
SLICE_LUTX placed   : {slice_lut[0]}/{slice_lut[1]}   (post-PnR packing)
IOB33 in/out placed : {inbuf[0]}/{inbuf[1]} in, {outbuf[0]}/{outbuf[1]} out
bitstream           : {bit_note}
notes:
""" + "".join(f"  - {n}\n" for n in notes)
report += "result: " + ("FAIL\n" + "".join(f"  ! {f}\n" for f in fails) if fails else "PASS\n")
open(f"{outdir}/sanity_report.txt", "w").write(report)
print(report)
sys.exit(1 if fails else 0)
PYEOF

# ---------------------------------------------------------------------------
# Step 6: bundled-data timing signoff (gate) -- same tool, tracer, and Q9
# ratio policy as the ice40 flow's step 5, fed by the routed graph the
# --post-route dump wrote instead of an SDF. A design that fails signoff
# is not a deliverable. SIGNOFF_POLICY=zero for the plain >= 0 debug gate.
# ---------------------------------------------------------------------------
if [ -f "$TIMING_JSON" ] && [ -f "$OUTDIR/$TOP.graph.json" ]; then
  echo "== timing signoff (routed graph via nextpnr pybindings)"
  python3 "$ROOT/tools/timing_signoff.py" \
    --graph-json "$OUTDIR/$TOP.graph.json" --sidecar "$TIMING_JSON" \
    --policy "${SIGNOFF_POLICY:-ratio}" \
    --report "$OUTDIR/signoff_report.txt"
else
  echo "== WARNING: no sidecar/graph -- SIGNOFF SKIPPED" >&2
fi

if [ "$HAVE_BIT" = "yes" ]; then
  echo "== done: $OUTDIR/$TOP.bit"
else
  echo "== done (FASM only): $OUTDIR/$TOP.fasm"
fi
