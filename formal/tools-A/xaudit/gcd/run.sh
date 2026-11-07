#!/usr/bin/env bash
# Reproduce formal/notes/A-xaudit-gcd.md: gcd_hw R5 routed -> xaudit.  Not run by any gate.
#
#   W=/tmp/gcdwt  (a detached worktree of this repo; builds never touch the main tree)
#   S=/tmp/gcdx   (scratch: prjxray arcs, nets, bands, runs)
#
# 0. toolchain: TC=~/dev2/lib/fpgatoolchain bash cells/verify/toolchain.sh   (nextpnr sha256 9c732bc6303458df)
#    runtime libs needed by the restored binaries (apt): libtcl8.6 libboost-python1.83.0
#    libboost-filesystem1.83.0 libboost-program-options1.83.0.  The bitstream step (fasm2frames)
#    needs python textx and was NOT run: nothing here needs a bitstream.
# 1. build (BOARD-QUEUE #2 command, R5 sizes), seeds d 3 4 5, from $W/cells, with the Dynamatic
#    frontend restored from cloud/fixtures (cp -r cloud/fixtures/frontend/* build/frontend/):
#      [NEXTPNR_SEED=N] BD_SIZES=../research/data/gcd_hw_sizes_R5.vh \
#        BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw
# 2. prjxray per-arc delays (research branch tool, read with git show into $S):
#      git show origin/claude/research:cells/gls/fid/xray_delay.py > $S/xray_delay.py
#      PYTHONPATH=$TC/openxc7-src/prjxray:<simplejson shim>:<intervaltree> \
#      XRAY_DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7 python3 $S/xray_delay.py \
#        --routed gcd_hw_routed.json --sdf gcd_hw.sdf --out xray.sdf --arcs arcs.tsv
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
S=${S:-/tmp/gcdx}
X=${XAUDIT:-$HERE/../../../lean/.lake/build/bin/xaudit}
SEED=${SEED:-d}
ROUTED=${ROUTED:-/tmp/gcdwt/out/$SEED/gcd_hw_routed.json}
cd "$S"
# 3. netlist + bands (the netlist is the same for every corner; only the bands change)
for c in slow fast indep; do
  python3 -I "$HERE/../routed2x.py" "$ROUTED" --xray-arcs $SEED/arcs.tsv --corner $c \
    --out $SEED/net.json --bands $SEED/$c.bands.json --report $SEED/routed2x_$c.txt
done
for w in 0 0.02 0.05; do
  python3 -I "$HERE/../routed2x.py" "$ROUTED" --xray-arcs $SEED/arcs.tsv --corner slowmax --widen $w \
    --out $SEED/net.json --bands $SEED/smax_w$w.bands.json
done
# 4. xaudit (timed engine, every LUT node printed), vector 1, 20 ns reset
mkdir -p runs
x() { out=$1; shift; "$X" "$@" > runs/$out.out || true; python3 -I "$HERE/analyze.py" runs/$out.out > runs/$out.summary.txt; }
x ${SEED}_slow_v1   $SEED/net.json --bands $SEED/slow.bands.json  --stim "$HERE/inputs/v1_100ns.stim.json" --timed-only --all
x ${SEED}_fast_v1   $SEED/net.json --bands $SEED/fast.bands.json  --stim "$HERE/inputs/v1_70ns.stim.json"  --timed-only --all
x ${SEED}_smax0_v1  $SEED/net.json --bands $SEED/smax_w0.bands.json    --stim "$HERE/inputs/v1_100ns.stim.json" --timed-only --all
x ${SEED}_smaxw02_v1 $SEED/net.json --bands $SEED/smax_w0.02.bands.json --stim "$HERE/inputs/v1_100ns.stim.json" --timed-only --all
x ${SEED}_smaxw05_v1 $SEED/net.json --bands $SEED/smax_w0.05.bands.json --stim "$HERE/inputs/v1_100ns.stim.json" --timed-only --all
# 5. static own-feedback race check, every corner
for c in slow fast indep; do python3 -I "$HERE/fbrace.py" $SEED/net.json $SEED/$c.bands.json; done
# 6. concrete cross-check samples (see csim.py): e.g.
#   python3 -I csim.py NET BANDS --stim S --mode ends --seed K --strobe rig_lap --bus rig_res_data --stop-after 3 --sig sig.json
