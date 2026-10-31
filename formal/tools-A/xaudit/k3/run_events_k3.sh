#!/usr/bin/env bash
# Probe K3: xevents8 (Events8.design_verdict8) and, for comparison, xevents5 (Events6.design_verdict)
# on a routed <k>_hw.  Per seed x corner:
#   events4/skel.py  -> events8/cert8.py (UNTRUSTED) -> xevents8   (lean --run Events8Main.lean)
#                    -> events6/cert6.py (UNTRUSTED) -> xevents5   (lean --run Events5Main.lean)
#   events5/ana5.py (untrusted Python analysis, comparison only)
# Lean runs on the private overlay $XAUDIT_OLEAN (k3/mk_k3.sh), through formal/slot.sh, at most $J (2)
# at once (parallel runs gave empty outputs before), --fuel 256 (any fuel is sound; 64 is too short
# for collatz's pin paths).
# Negative controls on seed $NS (default d) slow, each MUST be rejected:
#   NEG-fb5000 : +5000 ps on both bounds of ucontrol_merge0.uarb1.ua2's own-feedback arc (negctl_k2.py)
#   NEG-recog  : certificate edit, one real node's feedback input claimed to be its reset input
#   NEGentry   : +GPS ps (60000) on both bounds of the first umux guarded pin's arc -> that guard residual
#   NEGexit    : +GPS ps on the upper bound of that stage's guard-pin arc             -> that guard residual
#   (gcd's neg8.sh used +5000 / +18000; on ipow d +5000 on umux3.uya pin1 left it CLEAN -- the ENTRY
#    margin includes the S->D walk dW, many ns -- so the defect is now larger than any transaction walk)
#   NEGnoguard : cert8.py --no-guard                                             -> every guard residual
#   k3/run_events_k3.sh <kernel>     SEEDS="d 3 4 5" CORNERS="slow fast indep gb" CHK="8 5" NEG=1
# Inputs $OUT/<seed>/{net.json,<corner>.bands.json} (bands_k3.sh).  Outputs $R/{xe8,xe5,cert8,cert6,ana5}_<seed>_<corner>.txt
set -u
K3="$(cd "$(dirname "$0")" && pwd)"; X="$K3/.."
LEAN="$(cd "$K3/../../../lean" && pwd)"
K=$1; OUT=${OUT:-$HOME/k3out/$K}; R=${R:-$K3/out/$K}; J=${J:-2}; NS=${NS:-d}
OL=${XAUDIT_OLEAN:-$HOME/k3olean}
mkdir -p "$R"
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 PATH=$HOME/.elan/bin:$PATH
xe() {  # main skel bands cert out
  FORMAL_SLOT_CWD=$LEAN "$LEAN/../slot.sh" lake env sh -c \
    'LEAN_PATH="$0:$LEAN_PATH" exec lean --run "$@"' "$OL" \
    "Formal/Core/XAudit/Events$1Main.lean" "$2" "$3" "$4" --fuel ${FUEL:-256} 2>&1 | grep -v '^\[slot\]' > "$5"
}
rows=()
for s in ${SEEDS:-d 3 4 5}; do
  [ "$s" = none ] && continue
  D=$OUT/$s
  for c in ${CORNERS:-slow fast indep gb}; do
    python3 "$X/events4/skel.py" $D/net.json $D/$c.bands.json $D/skel.json $D/skel_$c.bands.json > "$R/skel_${s}_$c.txt"
    for x in ${CHK:-8 5}; do
      if [ $x = 8 ]; then python3 "$X/events8/cert8.py" $D/skel.json $D/skel_$c.bands.json $D/cert8_$c.json > "$R/cert8_${s}_$c.txt" 2>&1
                          rows+=("8 $D/skel.json $D/skel_$c.bands.json $D/cert8_$c.json $R/xe8_${s}_$c.txt")
      else python3 "$X/events6/cert6.py" $D/skel.json $D/skel_$c.bands.json $D/cert6_$c.json > "$R/cert6_${s}_$c.txt" 2>&1
           rows+=("5 $D/skel.json $D/skel_$c.bands.json $D/cert6_$c.json $R/xe5_${s}_$c.txt"); fi
    done
    python3 "$X/events5/ana5.py" $D/skel.json $D/skel_$c.bands.json --label ${s}_$c > "$R/ana5_${s}_$c.txt" 2>&1
  done
done
if [ "${NEG:-1}" = 1 ]; then
  D=$OUT/$NS; N=$R/neg.txt; : > $N
  python3 "$X/k2/negctl_k2.py" $D/skel.json $D/skel_slow.bands.json $D/skel_slow_NEGfb5000.bands.json \
      urig.udut.ucontrol_merge0.uarb1.ua2.u 5000 >> $N
  python3 "$X/events8/cert8.py" $D/skel.json $D/skel_slow_NEGfb5000.bands.json $D/cert8_NEGfb5000.json >> $N 2>&1
  rows+=("8 $D/skel.json $D/skel_slow_NEGfb5000.bands.json $D/cert8_NEGfb5000.json $R/xe8_${NS}_slow_NEGfb5000.txt")
  python3 -I - $D/cert8_slow.json $D/cert8_NEGrecog.json >> $N <<'PY'
import json, sys
c = json.load(open(sys.argv[1]))
n = next(x for x in c["nodes"] if not x["virt"] and not x["mg"])
n["qi"] = n["ri"]
print("NEG-recog:", n["name"])
json.dump(c, open(sys.argv[2], "w"))
PY
  rows+=("8 $D/skel.json $D/skel_slow.bands.json $D/cert8_NEGrecog.json $R/xe8_${NS}_slow_NEGrecog.txt")
  python3 -I - $D/cert8_slow.json $D/skel_slow.bands.json $D ${GPS:-60000} >> $N <<'PY'
import json, sys
c = json.load(open(sys.argv[1])); src, od, G = sys.argv[2], sys.argv[3], int(sys.argv[4])
k = next(k for k in c["guards"] if "umux" in c["nodes"][int(k.split("/")[0])]["name"])
j, p = map(int, k.split("/")); n = c["nodes"][j]
gd = n["pins"][p]["paths"][0][0][0]; gg = n["pins"][n["pins"][p]["gp"]]["paths"][0][0][0]
open(f"{od}/NEG_guard_target.txt", "w").write(f"{n['name']} pin{p}\n")
for tag, arc, dlo, dhi in (("NEGentry", gd, G, G), ("NEGexit", gg, 0, G)):
    b = json.load(open(src)); lo, hi = b["arcs"][arc]; b["arcs"][arc] = [lo + dlo, hi + dhi]
    print(f"{tag}: guard {k} = {n['name']} pin{p}: {arc} {lo},{hi} -> {lo+dlo},{hi+dhi}")
    json.dump(b, open(f"{od}/skel_slow_{tag}.bands.json", "w"))
PY
  for t in NEGentry NEGexit; do
    python3 "$X/events8/cert8.py" $D/skel.json $D/skel_slow_$t.bands.json $D/cert8_$t.json >> $N 2>&1
    rows+=("8 $D/skel.json $D/skel_slow_$t.bands.json $D/cert8_$t.json $R/xe8_${NS}_slow_$t.txt")
  done
  python3 "$X/events8/cert8.py" $D/skel.json $D/skel_slow.bands.json $D/cert8_NEGnoguard.json --no-guard >> $N 2>&1
  rows+=("8 $D/skel.json $D/skel_slow.bands.json $D/cert8_NEGnoguard.json $R/xe8_${NS}_slow_NEGnoguard.txt")
fi
for r in "${rows[@]}"; do
  xe $r &
  while [ "$(jobs -rp | wc -l)" -ge $J ]; do sleep 1; done
done
wait
for r in "${rows[@]}"; do set -- $r; t=$(basename $5 .txt)
  echo "$t: $(grep -h 'guarded pins' $5 | cut -c1-90) | $(tail -1 $5 | cut -c1-70)"; done
