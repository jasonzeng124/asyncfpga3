#!/usr/bin/env bash
# "Sizes and route are a pair" -- hw/tighten_loop.sh says so and rejects builds
# where the pairing does not hold.  How OFTEN does it not hold?  Rebuild the
# converged, board-validated xorshift with its own shipped sizes, changing
# nothing but the PnR seed, and count rule A violations each time.
set -u
cd /home/jayjay/dev2/proj/asyncfpga3/cells
D=/home/jayjay/.claude/jobs/4181ab68/tmp/shmoo
SZ=build/validated/xorshift_bench_gen/xorshift_bench_gen_sizes.vh
printf 'seed\tnviol\tworst_cell\tworst_margin\tworst_slack\tviolators\n' > "$D/stability.tsv"
for s in 1 2 3 4 5 6 7 8; do
    if ! BD_SIZES="$SZ" BD_SIZES_GATE=0 NEXTPNR_SEED=$s timeout 2400 \
         hw/build_bench.sh xorshift > "$D/logs/stab_$s.log" 2>&1; then
        echo "seed $s: BUILD FAILED"; printf '%s\tBUILDFAIL\n' "$s" >> "$D/stability.tsv"; continue
    fi
    python3 verify/tighten.py build/hw/xorshift_bench_gen/xorshift_bench_gen.sdf \
        > "$D/logs/stab_tighten_$s.log" 2>&1 || true
    python3 - "$D/logs/stab_tighten_$s.log" "$s" >> "$D/stability.tsv" <<'PY'
import re, sys
t = open(sys.argv[1]).read()
a = t.split("\nA. ", 1)[1].split("\nB. ", 1)[0]
rows = []
for m in re.finditer(r"^  (\S+)\s+(\d+) links\s+(\d+) ps\s+req\s+(-?\d+)\s+peak\s+(-?\d+)\s+guard\s+(\d+)\s+margin\s+(-?\d+)(.*)$", a, re.M):
    c, li, ch, rq, pk, g, mg, tl = m.groups()
    rows.append((c.split(".")[-1], int(g), int(mg), "VIOLATION" in tl))
w = min(rows, key=lambda r: r[2])
v = [r[0] for r in rows if r[3]]
print("\t".join([sys.argv[2], str(len(v)), w[0], str(w[2]), str(w[2]+w[1]),
                 ",".join(v) if v else "-"]))
PY
    tail -1 "$D/stability.tsv" | sed 's/^/  seed /'
done
echo "=== STABILITY DONE ==="
column -t "$D/stability.tsv"
