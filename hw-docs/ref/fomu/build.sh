#!/bin/bash
# fomu/build.sh -- build+PNR the fomu_top self-test harness (wraps a
# compiled async-hls core, default `gcd`) for a real Fomu PVT
# (iCE40UP5K-UWG30) and produce a flash-ready .dfu file.
#
# usage: fomu/build.sh [core-verilog-dir] [core-name]
#   default: build/gcd_tight_pass2  gcd      (the tightened pass-2 build
#            from tests/pnr_tighten.sh -- run that first if it doesn't
#            exist yet)
#
# This does NOT flash anything -- dfu-util -w -D needs real USB access
# to the device, which this environment may not have. It stops after
# producing fomu/build/fomu.dfu and prints the exact flash command to
# run wherever the Fomu is actually reachable.
set -eu
cd "$(dirname "$0")/.."

coredir="${1:-build/gcd_tight_pass2}"
corename="${2:-gcd}"
topfile="${TOPFILE:-fomu/fomu_top.sv}"
topmod="${TOPMOD:-fomu_top}"
out="${OUT:-fomu/build}"
YOSYS="${YOSYS:-yosys}"
NEXTPNR="${NEXTPNR:-nextpnr-ice40}"

[ -f "$coredir/$corename.v" ] || {
  echo "missing $coredir/$corename.v -- run tests/pnr_tighten.sh $corename first"
  exit 1
}

mkdir -p "$out"

usb_srcs=""
case "$topmod" in fomu_uart_*) usb_srcs="read_verilog -sv $(echo fomu/usb/*.v)";; esac

echo "== synth ($topmod wrapping $coredir/$corename.v) =="
"$YOSYS" -q -p "
  read_verilog -DASYNC_SYNTH_ICE40 -I rtl $coredir/$corename.v
  read_verilog -sv $topfile
  $usb_srcs
  hierarchy -top $topmod
  synth_ice40 -top $topmod ${ABC9:+-abc9}
  write_json $out/fomu_audit.json
  techmap -map tests/loopbreaker_resolve.v
  opt_clean
  stat
  write_json $out/fomu.json
"

echo "-- structural audit (informational -- fomu_top's own sync glue"
echo "   isn't part of the async bundling model, only $corename's core is) --"
python3 tests/audit_bundling.py "$out/fomu_audit.json" || true

echo "== place & route (up5k / uwg30) =="
# --timing-allow-fail: the harness's clocked glue (i_req_r -> ... -> done/
# pass) makes one big register-to-register combinational cone that
# routes straight through the whole clockless gcd core. nextpnr times
# that as ordinary sync logic and (correctly, but irrelevantly) fails to
# close it at its default frequency guess -- this is a one-shot self
# test, not a pipelined design, so frequency closure across that cone
# doesn't matter. Same reasoning as --ignore-loops elsewhere in this
# project: real timing signoff is the bundling audit, not classic STA.
"$NEXTPNR" --up5k --package uwg30 --pcf fomu/fomu_pvt.pcf \
  --json "$out/fomu.json" --asc "$out/fomu.asc" --ignore-loops \
  --freq 48 --timing-allow-fail --opt-timing ${SEED:+--seed "$SEED"} ${TW:+--placer-heap-timingweight "$TW"} ${NPG:+--no-promote-globals} \
  > "$out/pnr.log" 2>&1 || { tail -30 "$out/pnr.log"; exit 1; }
grep -E '(ICESTORM_LC|SB_IO):.*%' "$out/pnr.log" | sed 's/Info: */  /'

echo "== post-route checks (async bundling audit + sync 48MHz closure --"
echo "   requires the local getCellDelay-patched nextpnr) =="
PNR_TIMING_OUT="$out/timing.json" SYNC_TIMING_OUT="$out/sync_timing.json" \
  "$NEXTPNR" --up5k --package uwg30 --pcf fomu/fomu_pvt.pcf \
  --json "$out/fomu.json" --ignore-loops --freq 48 --timing-allow-fail --opt-timing \
  ${SEED:+--seed "$SEED"} ${TW:+--placer-heap-timingweight "$TW"} ${NPG:+--no-promote-globals} \
  --post-route fomu/postroute_checks.py \
  > "$out/postroute.log" 2>&1 || { tail -40 "$out/postroute.log"; exit 1; }
grep -E 'postroute|synccheck' "$out/postroute.log" | sed 's/^/  /'

echo "== bitstream =="
icepack "$out/fomu.asc" "$out/fomu.bin"
cp "$out/fomu.bin" "$out/fomu.dfu"
dfu-suffix -v 1209 -p 70b1 -a "$out/fomu.dfu"
echo "  wrote $out/fomu.dfu ($(stat -c%s "$out/fomu.dfu") bytes)"

echo
echo "== flash (run wherever the Fomu is actually reachable over USB) =="
echo "  dfu-util -w -D $out/fomu.dfu"
