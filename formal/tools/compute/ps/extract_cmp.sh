#!/usr/bin/env bash
# Extract the 20 bdc_fused units from THE target's (gcd_ps e6bb4aec) yosys synthesis and compare
# with the committed Formal/Gen/Compute/GcdD/*.lean (gcd_hw route d). Untrusted Python.
R=/home/user/asyncfpga3/formal
for u in uori0 uori1 uori2 uori3 uori4 ucmpi0 ucmpi1 ucmpi2 ucmpi3 ucmpi8 ucmpi10 uaddi0 uselect0 uselect1 ushli0 ushrsi0 ushrsi1 ushrsi2 ushrsi3 ushrsi4; do
  U="$(echo "${u:0:1}" | tr a-z A-Z)${u:1}"
  python3 $R/tools/compute/extract.py /tmp/claude-0/dp/ps.json "$u" "Formal.Gen.Compute.GcdD.$U" extract/$U.lean >/dev/null || { echo "$U EXTRACT FAIL"; continue; }
  cmp -s extract/$U.lean $R/lean/Formal/Gen/Compute/GcdD/$U.lean && echo "$U identical" || echo "$U DIFFERS"
done
