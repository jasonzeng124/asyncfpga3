#!/usr/bin/env bash
# Probe K3: the cells/ post-route audits on each routed <k>_hw (as K2 ran them on collatz_hw):
#   verify/tighten.py SDF --osc dhk --osc invhk   (rules A, H, I, F, B, C, D; D is a one-sided SCREEN)
#   verify/skew.py SDF                            (rule E, the measurement rule D defers to)
#   verify/arb_fork.py SDF                        (arbiter A0 before the grant it unlocks)
#   k3/audit_k3.sh <kernel> [seed ...]  -> $OUT/<seed>/audit_{tighten,skew,arbfork}.txt + one line per seed
set -u
K=$1; shift; SRC=${SRC:-$HOME/k3src_$K}; OUT=${OUT:-$HOME/k3out/$K}
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
cd "$SRC/cells"
for s in "${@:-d}"; do
  D=$OUT/$s; S=$D/${K}_hw.sdf
  python3 verify/tighten.py $S --osc dhk --osc invhk > $D/audit_tighten.txt 2>&1; rt=$?
  python3 verify/skew.py $S > $D/audit_skew.txt 2>&1; re=$?
  python3 verify/arb_fork.py $S > $D/audit_arbfork.txt 2>&1; ra=$?
  cnt() { awk -v r="$1" '/^[A-Z]\. /{sec=substr($1,1,1)} sec==r && /VIOLATION/{n++} END{print n+0}' $D/audit_tighten.txt; }
  echo "$s tighten rc=$rt A=$(cnt A) H=$(cnt H) I=$(cnt I) F=$(cnt F) B=$(cnt B) C=$(cnt C) D=$(cnt D) (screen) |" \
       "E rc=$re $(grep -o '[0-9]* select gates, [0-9]* measured, [0-9]* violated' $D/audit_skew.txt) |" \
       "arb_fork rc=$ra $(grep -c '^  ok' $D/audit_arbfork.txt) ok $(grep -cE '^  (FAIL|VIOL|bad)' $D/audit_arbfork.txt) bad |" \
       "nextpnr $(grep -m1 -o 'nextpnr [0-9a-f]*' $D/audit_tighten.txt)"
done
