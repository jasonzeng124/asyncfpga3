#!/usr/bin/env bash
# T160: research f7573b807 turns the md5-keyed rewrites off by default; items 39-41 commands add BDC_AUTO_REWRITES=1
# ("rebuilds the same routes"). Own check: auto.py + emit.py --no-top at 312abcc32 (farm flow v3) vs research head with
# and without BDC_AUTO_REWRITES=1, on the four board kernels; md5 of the netlist without its header line (input path).
for K in collatz collatz64 xorshift ipow; do M=/root/wt-r91/build/frontend/$K/comp/handshake_transformed.mlir
 (cd /root/wt-r91 && python3 bdc/auto.py $M /root/t160/${K}_old.mlir && BDC_AUTO=1 python3 bdc/emit.py /root/t160/${K}_old.mlir --no-top -o /root/t160/${K}_old.v) >/dev/null 2>&1
 (cd /root/wt-rhead && BDC_AUTO_REWRITES=1 python3 bdc/auto.py $M /root/t160/${K}_rw.mlir && BDC_AUTO=1 BDC_AUTO_REWRITES=1 python3 bdc/emit.py /root/t160/${K}_rw.mlir --no-top -o /root/t160/${K}_newrw.v) >/dev/null 2>&1
 (cd /root/wt-rhead && python3 bdc/auto.py $M /root/t160/${K}_def.mlir && BDC_AUTO=1 python3 bdc/emit.py /root/t160/${K}_def.mlir --no-top -o /root/t160/${K}_newdef.v) >/dev/null 2>&1
 echo "$K 312abcc32=$(tail -n +2 /root/t160/${K}_old.v|md5sum|cut -c1-8) head+RW=$(tail -n +2 /root/t160/${K}_newrw.v|md5sum|cut -c1-8) head-default=$(tail -n +2 /root/t160/${K}_newdef.v|md5sum|cut -c1-8)"; done
