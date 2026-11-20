#!/usr/bin/env bash
# trim_shrink.sh HWDIR KERNEL TRIMREC VEC EXP OUT "DRAWKEYS" K... -- how far a trimmed route sits from the first trim that
# fails (PROGRAM "The board decides": "Sizes may be chosen by this simulation ... say how far the choice sits from the
# first size that fails").  HWDIR is a route the flow's trim step (auto_size.sh AUTO_TRIM=1) left trimmed, with its
# untrimmed copies (D_routed.untrimmed.json / D.untrimmed.fasm); TRIMREC its record (trim_I.txt: MACRO=LEN, the lengths
# the rule's trim mode chose).  For each K: every line of TRIMREC shortened K more elements (to >= 1; a line already at
# 1 stays), applied by trim_lines.py to a COPY of the route (the route itself is not touched), its bitstream, and one
# bench_gate.sh run per draw key in DRAWKEYS ("10101 10102 ..."; the same delay-model points the route was judged on).
# Writes OUT/kK/{trims.txt, draw_*.txt} and prints one line per K: K, lines shortened, ps the critical lines lost is not
# computed here (the event graph is not re-run), and the draws' verdicts.  VEC / EXP: the kernel's gate vectors and the
# expected values (suite_one.sh's exp.txt; GATE_MEMEXP in the environment for a memory kernel).
set -uo pipefail
HW=$(cd "$1" && pwd); K=$2; REC=$(readlink -f "$3"); VEC=$(readlink -f "$4"); EXP=$(readlink -f "$5"); OUT=$(mkdir -p "$6" && cd "$6" && pwd)
KEYS=$7; shift 7
R=$(cd "$(dirname "$0")/../../.." && pwd); D=${K}_bench_gen
P=xc7z010clg400-1; TCD=${TC:-$HOME/dev2/lib/fpgatoolchain}; DB=$TCD/openxc7/share/nextpnr/prjxray-db/zynq7; PX=$TCD/openxc7-src/prjxray
[ -f "$HW/${D}_routed.untrimmed.json" ] && [ -f "$HW/$D.untrimmed.fasm" ] || { echo "no untrimmed copies in $HW"; exit 1; }
for k in "$@"; do
  W=$OUT/k$k; rm -rf "$W"; mkdir -p "$W/hw"
  # the route copy: every file the gate reads, the trimmed lines K shorter (from the UNTRIMMED copies)
  for f in "$HW"/*; do case $f in *.untrimmed.*|*.prev.*) ;; *) [ -f "$f" ] && ln -s "$f" "$W/hw/";; esac; done
  rm -f "$W/hw/${D}_routed.json" "$W/hw/$D.fasm" "$W/hw/$D.bit"
  # every trimmable line (trim_lines.py --list on the untrimmed route), from its current length (TRIMREC's, else as
  # built) K shorter, to >= 1: the trims the rule chose and the lines it kept at their built length alike
  args=$(python3 "$R/research/tools/auto/trim_lines.py" --list "$HW/${D}_routed.untrimmed.json" | \
    awk -F'\t' -v k="$k" -v rec="$REC" 'BEGIN { while ((getline l < rec) > 0) { split(l, a, "="); cur[a[1]] = a[2] } }
      $2 == "trimmable" { c = ($1 in cur) ? cur[$1] : $3; n = c - k; if (n < 1) n = 1; if (n < $3) printf "%s=%d ", $1, n }')
  echo "$args" | tr ' ' '\n' | grep . > "$W/trims.txt"
  python3 "$R/research/tools/auto/trim_lines.py" --partial "$HW/${D}_routed.untrimmed.json" "$HW/$D.untrimmed.fasm" \
    "$W/hw/${D}_routed.json" "$W/hw/$D.fasm" $args > "$W/trim.log" 2>&1 || { echo "k=$k trim_lines FAILED"; continue; }
  PYTHONPATH="$PX:$TCD/openxc7/lib/python${PYTHONPATH:+:$PYTHONPATH}" python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$P" \
    "$W/hw/$D.fasm" > "$W/hw/$D.frames" 2> "$W/frames.log" && "$TCD/openxc7/bin/xc7frames2bit" --part_file "$DB/$P/part.yaml" \
    --part_name "$P" --frm_file "$W/hw/$D.frames" --output_file "$W/hw/$D.bit" > "$W/bit.log" 2>&1 || { echo "k=$k bitstream FAILED"; continue; }
  v=""
  for key in $KEYS; do   # the draws of one K at once (each has its own work directory; compiles go through compile_slot.sh)
    ( mkdir -p "$W/d$key"; [ -n "${XRAY:-}" ] && cp "$XRAY" "$W/d$key/xray.sdf"   # XRAY: the route's prjxray SDF (same route)
      g=$(GATE_RUNTS=${GATE_RUNTS-1} "$R/research/tools/eventgraph/bench_gate.sh" "$W/hw" "$D" "$W/d$key" "$VEC" "$EXP" "draw:$key" 2>&1 | tail -1)
      echo "draw $key :: $g" > "$W/draw_$key.txt"; rm -rf "$W/d$key/draw_$key" ) &
  done; wait
  for key in $KEYS; do v="$v $key:$(sed 's/.*:: //' "$W/draw_$key.txt" | awk '{print $1, $2}')"; done
  echo "k=$k lines=$(grep -c '^trim ' "$W/trim.log") refused=$(grep -c '^REFUSED' "$W/trim.log") |$v"
done
