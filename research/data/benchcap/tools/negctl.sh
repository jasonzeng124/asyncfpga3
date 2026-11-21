#!/usr/bin/env bash
# negctl.sh SRC_PNR_DIR OUT_ROUTE_DIR DELTA_PS -- the negative control's route: SRC's pnr/ (soak_xray.sdf, soak_routed.json,
# sizes.vh) with ONE arc lengthened by DELTA_PS (all of min:typ:max, rise and fall): isprime it 5's umux13 data LUT
# $23629/O6 -> $24110/A4, the LUT in front of the bench flop result_hold[0]'s D.  Then, e.g.:
#   CA_BENCHCAP=1 ca_run.sh REPO OUT_ROUTE_DIR/seed1 0.20 OUT --no-size ; grep umux13 OUT/report.txt
set -euo pipefail
SRC=$1; O=$2/seed1/pnr; D=$3; mkdir -p "$O"
ln -sfn "$(readlink -f "$SRC/soak_routed.json")" "$O/soak_routed.json"; cp "$SRC/sizes.vh" "$O/sizes.vh"
python3 - "$SRC/soak_xray.sdf" "$O/soak_xray.sdf" "$D" <<'PY'
import re, sys
src, dst, d = sys.argv[1], sys.argv[2], int(sys.argv[3])
key = (r"bridge_i.udut.umux13.\$abc\$23623\$auto\$blifparse.cc\:557\:parse_blif\$23629/O6 "
       r"\$abc\$23630\$auto\$blifparse.cc\:557\:parse_blif\$24110/A4 ")
n = 0
with open(src) as f, open(dst, "w") as g:
    for ln in f:
        if "(INTERCONNECT " + key in ln:
            ln = re.sub(r"\((\d+):(\d+):(\d+)\)", lambda m: "(%d:%d:%d)" % tuple(int(x) + d for x in m.groups()), ln); n += 1
        g.write(ln)
assert n == 1, n
PY
