#!/bin/bash
# lengthen.sh WORK ROUTED_JSON CELL DELTA_PS OUT VECFILE -- the self-check's second half (PROGRAM.md FIRST item, step 3):
# copy WORK's netlist_baked.v with every pin->output arc of the ONE cell whose routed-JSON name is CELL raised by
# DELTA_PS, rebuild the bench sim (the same flags build_ps.sh uses), run one 256-round vector twice and print
# latmin (12 ns cycles).  A delay element on the critical cycle must raise the iteration time; one off it must not.
set -euo pipefail
W=$1; RJ=$2; CELL=$3; D=$4; O=$5; G=$(cd "$(dirname "$0")/../../../cells/gls" && pwd)
mkdir -p "$O"
python3 - "$W" "$RJ" "$CELL" "$D" "$O" <<'PY'
import sys, re, json
W, RJ, CELL, D, O = sys.argv[1], sys.argv[2], sys.argv[3], int(sys.argv[4]), sys.argv[5]
j = json.load(open(RJ)); m = j["modules"]; top = [k for k in m if m[k].get("attributes", {}).get("top")] or list(m)
bel = m[top[0]]["cells"][CELL]["attributes"]["NEXTPNR_BEL"]
c = [l.split()[0] for l in open(W + "/names.map") if l.split()[1:2] == [bel.replace("5LUT", "6LUT")]]
assert len(c) == 1, (bel, c)
n = 0; out = []
for line in open(W + "/netlist_baked.v"):
    if re.search(r"\)\s+%s\s*\(" % c[0], line):
        def bump(mm):
            global n; n += 1; return ".%s(%d)" % (mm.group(1), int(mm.group(2)) + D)
        line = re.sub(r"\.(TA\dO[56]|TI0O|TD[01]OUT|TS0OUT)\((\d+)\)", bump, line)
        print("cell", c[0], bel, "arcs raised:", n, line.strip()[:200])
    out.append(line)
assert n > 0
open(O + "/netlist_baked.v", "w").writelines(out)
PY
cd "$O"
iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I"$G" -I. -o run.vvp "$G/ps/tb_ps.v" netlist_baked.v "$G/prims.v" "$G/ps/ps7_bench.v" 2>&1 | grep -v 'procedural continuous' || true
vvp run.vvp +FCLK_PS=12000 +MODE=1 +NRUNS=2 +VECFILE="$6" +TBATCH=1200000 +TEND=3000000 > run.log 2>&1 || true
rm -f run.vvp
grep -o "latmin=[0-9]* latmax=[0-9]* .*odata=[0-9a-f]*" run.log | sed 's/sig=[0-9a-f]* //' || echo "NO BENCHRES"
