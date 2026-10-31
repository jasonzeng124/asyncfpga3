#!/usr/bin/env bash
# Probe XInert: gcd_hw seed d (formal/notes/A-xaudit-gcd.md inputs) under xaudit --inertial.
#   XAUDIT=<binary> W=<dir with net_d.json, bands_d_<corner>.json: the E8Mux-corrected (OUTMUX hop, --inverted hull) seed-d files, see notes/A-xinert.md> \
#     ./run_gcd.sh check            # every (corner, rho) in check mode: refusal counts only (no simulation)
#     ./run_gcd.sh widen CORNER VAR # one simulation, VAR in rho0 rho15 rho50 dlut dall
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
X="${XAUDIT:?binary}"; W="${W:?scratch dir}"
G="$HERE/../gcd"
R="$HERE/results/gcd"; mkdir -p "$R"
var() { case $1 in rho0) echo "--rho 0";; rho15) echo "--rho 15";; rho50) echo "--rho 50";;
  dlut) echo "--rho-lut delay --rho-route 0";; dall) echo "--rho delay";; esac; }
stim() { case $1 in fast) echo "$G/inputs/v1_70ns.stim.json";; *) echo "$G/inputs/v1_100ns.stim.json";; esac; }
if [ "$1" = check ]; then
  for c in ${CORNERS:-slow fast gb smax_w0 smax_w0.02}; do for v in rho15 rho50 dlut dall; do
    "$X" "$W/net_d.json" --bands "$W/bands_d_$c.json" --stim "$HERE/designs/gcd_1step.stim.json" --timed-only \
      --inertial check $(var $v) > "$R/d_${c}__$v.check.txt"; e=$?
    echo "$c $v: exit $e $(grep -o 'check REFUSED: [0-9]* gates.*max widening needed [0-9]* steps' "$R/d_${c}__$v.check.txt")$(grep -o 'check: rho.*' "$R/d_${c}__$v.check.txt")"
  done; done | tee "$R/check_summary.txt"
else
  c=$2; v=$3; o="$W/d_${c}__$v.out"
  python3 -I -c 'import resource,subprocess,sys,time
t=time.time(); r=subprocess.run(sys.argv[3:],stdout=open(sys.argv[2],"w"))
print("exit",r.returncode,"wall_s",round(time.time()-t,1),"peak_rss_kB",resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,file=open(sys.argv[1],"w"))' \
    "$R/d_${c}__$v.time" "$o" "$X" "$W/net_d.json" --bands "$W/bands_d_$c.json" --stim "$(stim $c)" \
      --timed-only --all --inertial widen $(var $v)
  grep -E '^(inertial|  widened)' "$o" > "$R/d_${c}__$v.header.txt"
  python3 -I "$G/analyze.py" "$o" > "$R/d_${c}__$v.summary.txt"
  xz -kf "$o"; cp "$o.xz" "$R/"
fi
