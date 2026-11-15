#!/usr/bin/env bash
# formal/tools/margin/run.sh BUILD.fasm OUT/   (shard C, v0, UNTRUSTED search; method in margin.py, races.py, rank.py)
#
# The kappa margin of a routed build at g = 1, corner 0, with H_RUNT(20) (and without, W0=1): every single-pin
# race of a control storage node that the adversary sweep can make fail, its failing kappa, kappa* and a witness.
# BUILD.fasm: the read-back (fromBit) FASM, plain/.xz/.gz. Next to it (or via env) the build's XDC, yosys JSON and
# nextpnr routed JSON (for the boundary names): XDC=, SYNTH=, ROUTED=. v0 knows only the gcd_ps kernel boundary.
# Knobs (env): JOBS (8), TOP (0 = every active candidate), KHI (0.45), KLO (0.20), W0 (1: also without H_RUNT),
#   ONLY (file of node:pin keys: sweep only these), SHARD (K/N: every N-th candidate from K, for farm tasks), PAIRS ("0x49e9c618,0x35bf992e 1071,462"), LATCH (0; 1 = also latch-like storage nodes), TC (prjxray-db root).
set -euo pipefail
B=$1; O=$2; mkdir -p "$O"; O=$(cd "$O" && pwd)
H=$(cd "$(dirname "$0")" && pwd); F=$(cd "$H/../.." && pwd); R=$(cd "$F/.." && pwd)
JOBS=${JOBS:-8}; TOP=${TOP:-0}; KHI=${KHI:-0.45}; KLO=${KLO:-0.20}; W0=${W0:-1}; LATCH=${LATCH:-0}
PAIRS=${PAIRS:-"0x49e9c618,0x35bf992e 1071,462"}; KERNEL=${KERNEL:-gcd}
log() { echo "$(date +%H:%M:%S) $*" | tee -a "$O/run.log"; }
cat_any() { case "$1" in *.xz) xz -dc "$1";; *.gz) gzip -dc "$1";; *) cat "$1";; esac; }
pick() { for f in "$@"; do [ -f "$f" ] && { echo "$f"; return; }; done; echo ""; }
base=${B%.xz}; base=${base%.gz}; base=${base%.fasm}; base=${base%.fromBit}
XDC=${XDC:-$(pick "$base.xdc")}; SYNTH=${SYNTH:-$(pick "$base.json" "$base.json.xz")}
ROUTED=${ROUTED:-$(pick "$base.routed.json" "$base.routed.json.xz")}
# Bench builds (research's kernel benches): give BND= (tools-A/target boundary_bench.py + mk_bnd_sim.py output) and
# KERNEL= (collatz | collatz64 | xorshift; vectors in PAIRS as "a,b", one-operand kernels "n,n"); XDC/SYNTH/ROUTED unused.
# Or, for a bench build straight from research's build tree: KV= (build/gen/K_kernel_bench.v), BV= (build/gen/K_bench_gen.v),
# SYNTH= and ROUTED= (build/hw/K_bench_gen/K_bench_gen{,_routed}.json): the boundary is made by tools-A boundary_bench.py.
if [ -z "${BND:-}" ] && [ -n "${KV:-}" ]; then
  [ -n "$SYNTH" ] && [ -n "$ROUTED" ] && [ -n "${BV:-}" ] || { echo "bench mode needs KV, BV, SYNTH, ROUTED" >&2; exit 1; }
  BENCH=1
fi
if [ -z "${BND:-}" ] && [ -z "${BENCH:-}" ]; then
  [ -n "$XDC" ] && [ -n "$SYNTH" ] && [ -n "$ROUTED" ] || { echo "need XDC, SYNTH, ROUTED next to $B or in env (or BND=)" >&2; exit 1; }
fi

# prjxray-db: $TC, else unpack zynq7 from the repo's toolchain-cache branch (read-only git: cat-file only)
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
if [ ! -d "$TC/openxc7/share/nextpnr/prjxray-db/zynq7" ]; then
  TC=${MARGIN_TC:-/tmp/margin-tc}
  if [ ! -d "$TC/openxc7/share/nextpnr/prjxray-db/zynq7" ]; then
    KEY=$(bash "$R/cloud/toolchain-cache.sh" key); ref=origin/toolchain-cache/$KEY
    log "prjxray-db: unpacking zynq7 from $ref into $TC"
    mkdir -p "$TC"
    for p in $(git -C "$R" ls-tree --name-only "$ref" | grep '^part-' | sort); do git -C "$R" cat-file blob "$ref:$p"; done |
      $(for p in python3 python3.13 /usr/local/bin/python3; do $p -c 'import zstandard' 2>/dev/null && { echo $p; break; }; done || echo python3) -c '
import sys, tarfile
try:
    import zstandard; d = zstandard.ZstdDecompressor().stream_reader(sys.stdin.buffer)
except ImportError:
    import subprocess; d = subprocess.Popen(["zstd", "-dc"], stdin=sys.stdin.buffer, stdout=subprocess.PIPE).stdout
t = tarfile.open(fileobj=d, mode="r|")
for m in t:
    if "prjxray-db/zynq7" in m.name: t.extract(m, sys.argv[1])
' "$TC"
  fi
fi
export TC

# 1. decode (reused if OUT/net.json exists)
A=$F/tools-A/target
if [ ! -f "$O/net.json" ]; then
  log "decode"
  cat_any "$B" > "$O/fromBit.fasm"
  [ -z "${BND:-}" ] && [ -z "${BENCH:-}" ] && { cat_any "$SYNTH" > "$O/synth.json"; cat_any "$ROUTED" > "$O/routed.json"; }
  if [ -n "${BENCH:-}" ]; then
    : > "$O/empty.xdc"
    python3 "$A/decode_base.py" "$O/fromBit.fasm" "$O/empty.xdc" --json "$O/d0.json" 2>&1 | tail -1 | tee -a "$O/run.log"
    python3 "$A/build_net.py" "$O/d0.json" "$O/fromBit.fasm" - "$O/net.json" > /dev/null
    cat_any "$SYNTH" > "$O/synth.json"; cat_any "$ROUTED" > "$O/routed.json"
    python3 "$H/boundary_bench.py" "$O/synth.json" "$O/routed.json" "$O/net.json" "$KV" "$BV" "$O/bnd_bench.json" | tail -1 | tee -a "$O/run.log"
    python3 "$A/mk_bnd_sim.py" "$O/bnd_bench.json" "$O/bnd.json" | tee -a "$O/run.log"
    python3 "$A/arbs.py" "$O/routed.json" "$O/d0.json" "$O/net.json" "$O/arbs.json" 2>&1 | head -1 | tee -a "$O/run.log" ||
      echo "[]" > "$O/arbs.json"
    [ -s "$O/arbs.json" ] || echo "[]" > "$O/arbs.json"
  elif [ -n "${BND:-}" ]; then
    : > "$O/empty.xdc"
    python3 "$A/decode_base.py" "$O/fromBit.fasm" "$O/empty.xdc" --json "$O/d0.json" 2>&1 | tail -1 | tee -a "$O/run.log"
    python3 "$A/build_net.py" "$O/d0.json" "$O/fromBit.fasm" - "$O/net.json" > /dev/null
    cp "$BND" "$O/bnd.json"; echo "[]" > "$O/arbs.json"   # bench arbiters not named yet: no ArbOK flag
  else
    python3 "$A/decode_base.py" "$O/fromBit.fasm" "$XDC" --json "$O/d0.json" 2>&1 | tail -1 | tee -a "$O/run.log"
    python3 "$A/build_net.py" "$O/d0.json" "$O/fromBit.fasm" - "$O/net.json" > /dev/null
    python3 "$A/boundary_ps.py" "$O/synth.json" "$O/routed.json" "$O/net.json" "$O/bnd.json" | tail -1 | tee -a "$O/run.log"
    python3 "$A/arbs.py" "$O/routed.json" "$O/d0.json" "$O/net.json" "$O/arbs.json" | head -1 | tee -a "$O/run.log"
  fi
fi
(cd "$O" && md5sum fromBit.fasm net.json bnd.json arbs.json 2>/dev/null) | tee "$O/md5.txt" || true

# 2. candidates (storage gate x live pin), 3. reference run at KHI (dump) and dynamic rank
log "candidates"
python3 "$H/races.py" "$O/net.json" "$O/bnd.json" "$O/races.json" $([ "$LATCH" = 1 ] && echo --latch) 2>&1 | tee -a "$O/run.log"
if [ ! -f "$O/ref_dump.json" ]; then
  log "reference run kappa $KHI"
  echo '{"S": [], "F": []}' > "$O/empty.json"
  KDEN=100 python3 "$F/tools/huff/simadv.py" "$O/net.json" "$O/bnd.json" --pairs $PAIRS --kernel "$KERNEL" --corner 0 --kappa "$KHI" \
    --classes "$O/empty.json" --cdefault F --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq \
    --tmax "${TFULL:-5000000}" --w 20 --dump "$O/ref_dump.json" 2>&1 | grep -E "RESULT|events" | tee -a "$O/run.log"
fi
python3 "$H/rank.py" "$O/net.json" "$O/races.json" "$KHI" "$O/ranked.json" "$O/ref_dump.json"
# 4. sweep + bisection + report
log "sweep"
python3 "$H/margin.py" "$O/net.json" "$O/bnd.json" "$O/ranked.json" "$O" --jobs "$JOBS" --top "$TOP" --khi "$KHI" \
  --klo "$KLO" --tfull "${TFULL:-5000000}" --pairs $PAIRS --kernel "$KERNEL" --w 20 $([ "$W0" = 1 ] && echo --w0) --arbs "$O/arbs.json" $([ -n "${ONLY:-}" ] && echo --only $(cat "$ONLY")) $([ -n "${SHARD:-}" ] && echo --shard "$SHARD")
log "check every failing row"; python3 "$H/checkrows.py" "$O" > /dev/null 2>&1 || true
[ -f "$O/routed.json" ] && python3 "$H/names.py" "$O" > /dev/null 2>&1 || true
log "done: $O/names.txt $O/kappa_hi.txt $O/checked.txt $O/margins.txt"
