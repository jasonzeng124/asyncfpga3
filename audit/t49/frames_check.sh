#!/usr/bin/env bash
# T49: does the committed H_RUNT rig bit (research/board/runt/runt_top.bit) carry exactly the committed FASM?
# Own read-back (prjxray bit2fasm via bitread) -> FASM; both FASMs assembled to sparse frames with prjxray fasm2frames
# against the toolchain's prjxray-db; the two frame files must be identical. Plus the own 5FF/5FFMUX scan (t43).
set -eu
W=/root/t49; R=${1:-/root/wt-r34}; mkdir -p $W; cd $W
cp $R/research/board/runt/runt_top.bit .; xz -dc $R/research/board/runt/runt_top.fasm.xz > committed.fasm
source /root/audit-tc/openxc7/export.sh; export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:$PYTHONPATH; DB=$PRJXRAY_DB_DIR/zynq7
python3 /root/audit-tc/openxc7-src/prjxray/utils/bit2fasm.py --db-root $DB --part xc7z010clg400-1 --bitread $(which bitread) runt_top.bit > readback.fasm
for f in committed readback; do python3 /root/audit-tc/openxc7-src/prjxray/utils/fasm2frames.py --db-root $DB --part xc7z010clg400-1 --sparse $f.fasm $f.frm; done
cmp committed.frm readback.frm && echo FRAMES IDENTICAL
python3 -I /home/user/asyncfpga3/audit/t43/scan_5ff_own.py committed.fasm
