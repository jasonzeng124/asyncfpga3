#!/usr/bin/env bash
# Run check_unit.py on all 20 bdc_fused units of THE target (untrusted Python).
cd /tmp/claude-0/dp
for u in uori0 uori1 uori2 uori3 uori4 ucmpi0 ucmpi1 ucmpi2 ucmpi3 ucmpi8 ucmpi10 uaddi0 uselect0 uselect1 ushli0 ushrsi0 ushrsi1 ushrsi2 ushrsi3 ushrsi4; do
  echo "=== $u"; python3 check_unit.py ps.json ps.routed.json net.json $u | grep -v "^input map"
done
