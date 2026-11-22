#!/usr/bin/env bash
# ca_fast_e2e.sh ROUTE_CA_DIR OUT [CORNERS] -- the sizing rule exactly as auto_size.sh runs it (corner_audit.py
# CA_SIZERULE=1 CA_JOINAWARE=1 BD_SKEW_STEER_SELF=1 BD_SKEW_AND_JOIN=1, one --band per corner, chains at 0.20), twice
# per corner: as before and with CA_FAST=1, and every output compared (sizes.vh, lines.tsv, negative_sized.tsv,
# report.txt, verify.txt, the three audit logs; the run's own output directory is the only text allowed to differ).
# ROUTE_CA_DIR is an auto_size.sh rule directory ($RUNS/ca/NAME_I, with seed1/pnr/{soak_xray.sdf, soak_routed.json,
# sizes.vh}).  Writes OUT/{old,new}_<corner>/ and OUT/summary.txt (wall and cpu seconds per run, IDENTICAL or the
# diff).  CA_JOBS (environment) is passed to both; E2E_PAR=1 runs old and new of a corner side by side;
# CA_OLD_TOOLS=<dir> runs the old side from another checkout's research/tools (the commit before CA_FAST).
# Both sides run with PYTHONHASHSEED=${E2E_HASHSEED:-1}: the rule iterates Python sets of pin names in places
# (find_chains' chain order, hence lines.tsv's order among lines of equal length and the greedy shrink's order
# among them), so two runs of the OLD rule with different hash seeds can already differ there.
set -uo pipefail
RD=$1; O=$2; CS=${3:-0.20 0.31}
R=$(cd "$(dirname "$0")/../../.." && pwd)
mkdir -p "$O"; : > "$O/summary.txt"
run() {   # run MODE CORNER
  local m=$1 c=$2 d="$O/$1_$2"; rm -rf "$d"
  local fast="" ca="${CA_OLD_TOOLS:-$R/research/tools}/corner_audit.py"
  [ "$m" = new ] && fast=1 && ca="$R/research/tools/corner_audit.py"
  /usr/bin/time -f "%e %U %S" -o "$d.time" env PYTHONHASHSEED=${E2E_HASHSEED:-1} CA_FAST=$fast CA_SIZERULE=1 CA_JOINAWARE=1 BD_SKEW_STEER_SELF=1 \
    BD_SKEW_AND_JOIN=1 python3 "$ca" "$RD/seed1" --prefix bridge_i.udut. --band "$c" \
    --inst-rx '\.chain\.g\[\d+\]\.u$:0.20' --out "$d" > "$d.txt" 2>&1
}
for c in $CS; do
  if [ "${E2E_PAR:-}" = 1 ]; then run old "$c" & run new "$c"; wait; else run old "$c"; run new "$c"; fi
  bad=0; diffs=""
  for f in sizes.vh lines.tsv negative_sized.tsv report.txt verify.txt tighten.log skew.log arb_fork.log; do
    if [ ! -s "$O/old_$c/$f" ] || [ ! -s "$O/new_$c/$f" ]; then bad=1; diffs="$diffs $f(missing)"; continue; fi
    if ! cmp -s <(sed "s#$O/old_$c#OUT#g" "$O/old_$c/$f") <(sed "s#$O/new_$c#OUT#g" "$O/new_$c/$f"); then
      bad=1; diffs="$diffs $f"; fi
  done
  if ! cmp -s <(sed "s#$O/old_$c#OUT#g" "$O/old_$c.txt") <(sed "s#$O/new_$c#OUT#g" "$O/new_$c.txt"); then
    bad=1; diffs="$diffs stdout"; fi
  wo=0 uo=0 so=0 wn=0 un=0 sn=0
  [ -s "$O/old_$c.time" ] && [ -s "$O/new_$c.time" ] || { bad=1; diffs="$diffs time(missing)"; }
  read -r wo uo so < <(tail -1 "$O/old_$c.time"); read -r wn un sn < <(tail -1 "$O/new_$c.time")
  printf "%s corner %s  old %.0f s wall %.0f s cpu  new %.0f s wall %.0f s cpu  %s  %s\n" "$RD" "$c" "$wo" \
    "$(echo "$uo + $so" | bc)" "$wn" "$(echo "$un + $sn" | bc)" "$([ $bad = 0 ] && echo IDENTICAL || echo "DIFFERENT:$diffs")" \
    "$(grep -h '^proposal' "$O/new_$c.txt" | cut -c1-90)" | tee -a "$O/summary.txt"
done
