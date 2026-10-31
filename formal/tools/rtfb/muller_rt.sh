#!/usr/bin/env bash
# Probe C-10f / C-10f2: RT_FB for every C-element of a routed Muller pipeline seed
# (route first with route_muller.sh), on the FASM READ BACK from the bits.
#   1. 11b's fasm2lean + 10d's rt_all.py (both unchanged): the C-10f numbers (no OUTMUX hop),
#      report build/muller/muller<N>_s<SEED>.rt.txt -- cross-check only since C-10f2
#   2. rtfb_design.py with RTFB_NO_HOP=1: must give the same failing counts as (1)
#   3. rtfb_design.py with the driver-side OUTMUX hop (C-10f2): report .rtd.txt and, with --lean,
#      the Lean data Formal/Timing/RtFbM<N>S<SEED>.lean (every C-element: --lean-all)
#     formal/tools/rtfb/muller_rt.sh SEED [N] [--lean]
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); REPO=$(cd "$HERE/../../.." && pwd)
F2L=$REPO/formal/tools/fasm2lean; R2L=$REPO/formal/tools/routed2lean
SEED=$1; N=${2:-64}; B=$HERE/build/muller/muller${N}_s$SEED
python3 "$F2L/fasm2lean.py" "$B.fromBit.fasm" "$R2L/pipe/muller_pipe.xdc" --ns X --json "$B.f2l.json" \
    --out /dev/null 2> "$B.f2l.log"
python3 -I "$R2L/rt_all.py" "$B.f2l.json" --ns X --sdf "$B.sdf" --routed "$B"_routed.json \
    --out /dev/null --report "$B.rt.txt" > /dev/null
RTFB_NO_HOP=1 python3 -I "$HERE/rtfb_design.py" "$B.fromBit.fasm" --routed "$B"_routed.json --sdf "$B.sdf" \
    --report "$B.rtd0.txt" > /dev/null
LEAN=(); [ "${3:-}" = --lean ] && LEAN=(--lean-all --ns RtFbM${N}S$SEED --lean "$REPO/formal/lean/Formal/Timing/RtFbM${N}S$SEED.lean")
python3 -I "$HERE/rtfb_design.py" "$B.fromBit.fasm" --routed "$B"_routed.json --sdf "$B.sdf" \
    --report "$B.rtd.txt" --json "$B.rtd.json" "${LEAN[@]}" > /dev/null
# (2) == (1): failing counts per variant
python3 -I - "$B.rt.txt" "$B.rtd0.txt" <<'PY'
import re, sys
V = ["indep", "fast", "slow", "fastE", "slowE", "sdf"]
def rt(p):  # rt_all.py report: one row per C-element, slack columns named by variant
    hdr, n = None, {v: 0 for v in V}
    for line in open(p):
        f = line.split()
        if f and f[0] == "LUT": hdr = f; continue
        if hdr and f and f[0].startswith("SLICE"):
            d = dict(zip(hdr, f))
            for v in V:
                n[v] += int(d[v]) < 0
    return n
def rtd(p):
    t = open(p).read()
    return {v: int(re.search(r"^%s\s+failing (\d+)/" % v, t, re.M).group(1)) for v in V}
a, b = rt(sys.argv[1]), rtd(sys.argv[2])
print("rt_all (C-10f) %s | rtfb_design NO_HOP %s | %s" % (a, b, "AGREE" if a == b else "DISAGREE"))
PY
grep -E '^(indep|fast|slow|fastE|slowE|sdf) +failing' "$B.rtd.txt" | tr '\n' ';'; echo
