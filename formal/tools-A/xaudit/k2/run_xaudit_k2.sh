#!/usr/bin/env bash
# Probe K2: the verified X/hazard audit `xaudit` (timed engine, every node printed) on the routed
# collatz_hw, vector 1 (n = 2, answer 1), as gcd/run.sh does for gcd_hw.
#   corners: slow (horizon 220 ns), fast (120 ns), slowmax w = 0 / 0.02 / 0.05 (220 ns)
#   + the static own-feedback race check (gcd/fbrace.py) at slow / fast / indep.
# Concrete latency of vector 1 (gcd/csim.py, every element at its band's hi, seed d): rig_lap
# rises at 181.1 ns slow, 89.2 ns fast; rig_res_data = 0x1.
# Inputs $OUT/<seed>/{net.json,<corner>.bands.json} (bands_k2.sh).  Reports: k2/results/xa_*.
# XA: the compiled lake exe if present, else `lean --run Formal/Core/XAudit/Main.lean`; slot.sh.
set -u
K2="$(cd "$(dirname "$0")" && pwd)"
X="$K2/.."
LEAN="$(cd "$K2/../../../lean" && pwd)"
OUT=${OUT:-$HOME/k2out}
R=${R:-$K2/results}
SEED=${SEED:-d}
D=$OUT/$SEED
mkdir -p "$R" "$D/runs"
export PATH=$HOME/.elan/bin:$PATH
xa() {  # xa TIMEFILE args...
  local tf=$1; shift
  if [ -x "${XAUDIT:-$LEAN/.lake/build/bin/xaudit}" ]; then
    FORMAL_SLOT_CWD=$LEAN "$LEAN/../slot.sh" /usr/bin/time -v -o $tf "${XAUDIT:-$LEAN/.lake/build/bin/xaudit}" "$@"
  else
    FORMAL_SLOT_CWD=$LEAN "$LEAN/../slot.sh" /usr/bin/time -v -o $tf lake env sh -c 'LEAN_PATH="$0:$LEAN_PATH" exec lean --run Formal/Core/XAudit/Main.lean "$@"' "${XAUDIT_OLEAN:-$HOME/k2olean}" "$@"
  fi
}
for w in 0 0.02 0.05; do
  [ -e $D/smax_w$w.bands.json ] || python3 -I "$X/routed2x.py" $D/collatz_hw_routed.json --xray-arcs $D/arcs.tsv \
      --corner slowmax --widen $w --out $D/net.json --bands $D/smax_w$w.bands.json > /dev/null
done
run() {  # name bands stim
  local t0=$(date +%s)
  xa $D/runs/$1.time $D/net.json --bands $2 --stim $3 --timed-only --all > $D/runs/$1.out 2>&1
  python3 -I "$X/gcd/analyze.py" $D/runs/$1.out > "$R/xa_${SEED}_$1.summary.txt" 2>&1
  echo "$1: $(( $(date +%s) - t0 )) s, peak RSS $(awk '/Maximum resident/{print $6}' $D/runs/$1.time) kB" >> "$R/xa_${SEED}_$1.summary.txt"
  echo "== $1"; tail -12 "$R/xa_${SEED}_$1.summary.txt"
}
for job in ${JOBS:-slow fast smax0 smaxw02 smaxw05}; do
  case $job in
    slow)    run slow    $D/slow.bands.json        $K2/v1_220ns.stim.json ;;
    fast)    run fast    $D/fast.bands.json        $K2/v1_120ns.stim.json ;;
    smax0)   run smax0   $D/smax_w0.bands.json     $K2/v1_220ns.stim.json ;;
    smaxw02) run smaxw02 $D/smax_w0.02.bands.json  $K2/v1_220ns.stim.json ;;
    smaxw05) run smaxw05 $D/smax_w0.05.bands.json  $K2/v1_220ns.stim.json ;;
  esac
done
for c in slow fast indep; do
  echo "== fbrace $c"; python3 -I "$X/gcd/fbrace.py" $D/net.json $D/$c.bands.json 2>&1 | tail -6
done | tee "$R/fbrace_${SEED}.txt"
