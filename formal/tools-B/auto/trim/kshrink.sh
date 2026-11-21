#!/usr/bin/env bash
# tools-B/auto/trim/kshrink.sh UNTRIMMED_DIR K SEED RECORD OUT "KS"  (shard B, UNTRUSTED): research's trim_shrink.sh margin
# study judged by formal: for each k in KS, every trimmable line (trim_lines.py --list) k elements below its length in
# RECORD (else as built), >= 1; trimtask.sh (bits, 8 + 8 draws), then steersafe.py --auto (structural bounds) and
# ctlsweep.sh (B21's race adversary). One line per k.
set -uo pipefail
U=$(readlink -f "$1"); K=$2; S=$3; REC=$(readlink -f "$4"); O=$5; KS=$6; H=$(cd "$(dirname "$0")/.." && pwd); RST=${RSTRIM:-/home/user/rs}
mkdir -p "$O"
for k in $KS; do
  args=$(python3 "$RST/research/tools/auto/trim_lines.py" --list "$U/${K}_bench_gen_routed.json" | \
    awk -F'\t' -v k="$k" -v rec="$REC" 'BEGIN { while ((getline l < rec) > 0) { split(l, a, "="); cur[a[1]] = a[2] } }
      $2 == "trimmable" { c = ($1 in cur) ? cur[$1] : $3; n = c - k; if (n < 1) n = 1; if (n < $3) printf "%s=%d ", $1, n }')
  W=$O/k$k; RSTRIM=$RST bash "$H/trim/trimtask.sh" "$U" "$K" "$S" "$W" 8 $args > /dev/null 2>&1
  st=$(timeout 2400 python3 "$H/steersafe.py" "$W/j/w/m" --auto 2>&1 | tee "$W/j/steersafe.txt" | grep -o 'min kappa_lo .*')
  wk=$(head -1 "$W/j/steersafe.txt" | grep -o '^[^ ]*\|slack [-+0-9]* / [-+0-9]*' | head -2 | tr '\n' ' ')
  cs=$(bash "$H/ctlsweep.sh" "$W/j" "$K" 2>&1 | grep -o 'ctl slack.*')
  echo "k=$k lines $(echo $args | wc -w) | draws $(grep -o 'PASS [0-9]* FAIL [0-9]* UNDECIDED [0-9]*' $W/j/summary.txt | tr '\n' ' ') | steers $st (weakest $wk) | ctl $cs"
  rm -rf $W/j/d1*/simx $W/j/d1*/net.simx $W/hw/*.frames
done
