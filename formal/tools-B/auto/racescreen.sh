#!/usr/bin/env bash
# formal/tools-B/auto/racescreen.sh K HWDIR OUT [GENDIR]   (shard B, 2026-11-20; UNTRUSTED simulation and extraction,
# bound logic in Lean: SteerSettle + SettleAll / ForceTree + ChainHold + CtlChain.hold_mem)
#
# The steer races of one built route, from its BITS:
#   1. HWDIR/K_bench_gen.bit read back (prjxray bit2fasm) and decoded (formal's decoder), 2 + 2 draws of research's model
#      as a sanity run (suite/task.sh PREBUILT=HWDIR);
#   2. steersafe.py --auto: every steer LUT (ucond_br*): the condition (a compare with a join, a one-channel compare, or
#      a link latch) settles before the request reaches the steer, for every delay of the prjxray band up to kappa_lo
#      (FOR-RESEARCH B20-B22);
#   3. ctlsweep.sh: the latch-fed steer race of B21 (link latch opening on ctl's rise vs the request through the link's
#      rdly and the steer's join): its race-only adversary, kappa 0 .. 0.20, both corners;
#   5. outsafe.py: the output capture's kappa_lo (B16).
#   6. weaksweep.sh (2026-11-21): the weakest steer's race-only adversary (its condition cone slow, its request walk
#      fast), kappa 0 .. 0.20, both corners: the first kappa with a wrong answer or no verdict (the bound must sit below).
#   4. trim/xtol.sh: the weakest steer's path-error tolerance at research's bands (chains 0.20, rest 0.31, CARRY 1.0):
#      condition side +x, request side -x, the first x with storage pulses and the first that fails.
# Needs: $TC (the toolchain, cells/verify/toolchain.sh passing), $RS (a research checkout: vectors, oracles; and
# GENDIR = its cells/build/gen with this build's K_bench_gen.v / K_kernel_bench.v unless HWDIR/gen has them), g++.
# HWDIR is what build_bench.sh leaves in cells/build/hw/K_bench_gen (or a trimmed copy: K_bench_gen.bit made from the
# trimmed FASM). Prints one summary line; details in OUT/.
set -uo pipefail
# DRAW_DOUT (2026-11-21, B31): the host samples out0's data this long after out0's request. Research's PS bench reads it
# through a 2-flop synchroniser at FCLK 12 ns, >= ~24 ns after the request, and CA_BENCHCAP flows (suite13t, v10, v11)
# size out0 for that; simx's own default (3 ns) turns those routes into false failures (flow v10 divmodu s1: garbage
# results at 3 ns, PASS at 23 ns). Default here now 23000; set DRAW_DOUT=3000 for the old, stricter host.
export DRAW_DOUT=${DRAW_DOUT:-23000}
K=$1; HW=$(readlink -f "$2"); O=$3; GD=${4:-${RS:-/home/user/rs}/cells/build/gen}; H=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$O"; O=$(readlink -f "$O")
if [ ! -d "$HW/gen" ]; then mkdir -p "$HW/gen"; cp "$GD/${K}_bench_gen.v" "$GD/${K}_kernel_bench.v" "$HW/gen/"; fi
PREBUILT=$HW bash "$H/suite/task.sh" "$K" 1 /dev/null - "$O/j" 2 > /dev/null 2>&1
[ -f "$O/j/w/m/net.json" ] || { echo "$K: decode failed (see $O/j/summary.txt)"; exit 1; }
python3 "$H/steersafe.py" "$O/j/w/m" --auto > "$O/j/steersafe.txt" 2>&1
ss=$(grep -o '^steers.*' "$O/j/steersafe.txt"); w=$(head -1 "$O/j/steersafe.txt" | cut -c1-28 | tr -s ' ')
cs=$(bash "$H/ctlsweep.sh" "$O/j" "$K" 2>&1 | grep -o 'steer .*')
xt=$(bash "$H/trim/xtol.sh" "$O/j" "$K" 2>&1 | grep -o 'first pulses.*')
dr=$(grep -o 'PASS [0-9]* FAIL [0-9]*' "$O/j/summary.txt" | tr '\n' ' ')
oc=$(timeout 2400 python3 "$H/outsafe.py" "$O/j/w/m" 2>&1 | tee "$O/j/outsafe.txt" | grep -o 'kappa_lo -\?[0-9.]*' | awk '{print $2}' | sort -g | head -1)
ws=$(timeout 3000 bash "$H/weaksweep.sh" "$O/j" "$K" 2>&1 | grep -o 'adversary first failure.*' | sed 's/adversary first failure: //')
echo "$K | draws $dr| $ss (weakest $w) | latch-fed race: ${cs:-none} | weakest steer at research's bands: $xt | output capture kappa_lo ${oc:-none} | weakest steer's race-only adversary: first failure ${ws:-not run}" | tee "$O/racescreen.txt"
