#!/usr/bin/env bash
# tools-B/auto/decode.sh DIR KERNEL  (shard B, UNTRUSTED): formal's decode of a research bench build whose files are in DIR
# (K_bench_gen.{fasm,json,sdf}, K_bench_gen_routed.json, K_bench_gen.v, K_kernel_bench.v) into DIR/m: C's run.sh for the
# decode (RC_TREE=1 arcs, DSP sites), then this directory's boundary_bench.py (C's + constant output bits) + bnd_const.py,
# A's mk_bnd_sim.py and arbs.py. Prints the md5s.
set -uo pipefail
D=$1; K=$2; H=$(cd "$(dirname "$0")" && pwd); F=$(cd "$H/../.." && pwd); A=$F/tools-A/target; O=$D/m
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
[ -f "$O/net.json" ] || JOBS=1 DRAWS=0 KERNEL=$K PAIRS="1,1" SYNTH=$D/${K}_bench_gen.json ROUTED=$D/${K}_bench_gen_routed.json \
  KV=$D/${K}_kernel_bench.v BV=$D/${K}_bench_gen.v bash "$F/tools/margin/run.sh" "$D/${K}_bench_gen.fasm" "$O" > "$D/decode.txt" 2>&1
[ -f "$O/net.json" ] || { echo "decode failed: $D/decode.txt"; exit 1; }
python3 "$H/boundary_bench.py" "$O/synth.json" "$O/routed.json" "$O/net.json" "$D/${K}_kernel_bench.v" "$D/${K}_bench_gen.v" "$O/bnd_bench.json" | tail -3
python3 "$A/mk_bnd_sim.py" "$O/bnd_bench.json" "$O/bnd.json"
python3 "$H/bnd_const.py" "$O/bnd.json" "$O/net.json"
python3 "$A/arbs.py" "$O/routed.json" "$O/d0.json" "$O/net.json" "$O/arbs.json" 2>&1 | head -1; [ -s "$O/arbs.json" ] || echo "[]" > "$O/arbs.json"
grep -E "dsp_gates --check|mismatches" "$D/decode.txt" | tail -1
(cd "$O" && md5sum fromBit.fasm net.json bnd.json) | tee "$O/md5.txt"
