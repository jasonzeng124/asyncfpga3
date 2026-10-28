#!/usr/bin/env bash
# A/B the region-fusion flag on real silicon, same session, same board.
#
#   hw/fold_ab.sh [kernel]           default: xorshift
#
# Everything about fusion's payoff so far has been a projection: LUT counts
# from yosys, ring-stage counts from the MLIR, and my own arithmetic scaling
# a measured iteration time by a ratio of delay-chain sums.  None of that is
# the number anyone cares about, which is how long an iteration takes on the
# part.
#
# So build the kernel twice -- BDC_OP_FUSION off, then on -- and run both
# through the same bench harness in the same session.  Building both here
# rather than reusing the existing off-baseline is deliberate: placement is
# deterministic per binary but not stable across builds, and the rings in
# hw/ro_link_ps.v showed +/-15% between routes of the same design.  A
# before/after where the "before" came from a different route on a different
# day is measuring two things at once.
set -eu
cd "$(dirname "$0")/.."

K=${1:-xorshift}
OUT=build/hw/fold_ab/$K
mkdir -p "$OUT"
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}

for f in 0 1; do
    tag=$([ "$f" = 0 ] && echo off || echo on)
    echo "==== BDC_OP_FUSION=$f ($tag) ===="
    BDC_OP_FUSION=$f ./hw/build_bench.sh "$K" > "$OUT/build_$tag.log" 2>&1 || {
        echo "  BUILD FAILED (see $OUT/build_$tag.log)"; continue; }
    BIT=build/hw/${K}_bench_gen/${K}_bench_gen.bit
    [ -e "$BIT" ] || { echo "  no bitstream"; continue; }
    cp "$BIT" "$OUT/${K}_$tag.bit"

    # The matched-delay total is the quantity the projections were built on,
    # so record it beside the measurement rather than re-deriving it later
    # from a build that may have moved.
    python3 verify/tighten.py "build/hw/${K}_bench_gen/${K}_bench_gen.sdf" \
        > "$OUT/tighten_$tag.log" 2>&1 || true
    python3 - "$OUT/tighten_$tag.log" "$tag" <<'PY'
import re, sys
rows = re.findall(r"^  (\S+)\s+(\d+) links\s+(\d+) ps\s+req\s+(\d+)\s+peak\s+(\d+)"
                  r"\s+guard\s+(\d+)\s+margin", open(sys.argv[1]).read(), re.M)
if rows:
    tc = sum(int(r[2]) for r in rows)
    tpg = sum(int(r[4]) + int(r[5]) for r in rows)
    print(f"  {sys.argv[2]}: {len(rows)} delay-bearing cells, "
          f"chain {tc/1000:.1f} ns, peak+guard {tpg/1000:.1f} ns")
PY

    # Four positional args, same as hw/run_all_bench.sh passes: bitfile,
    # label, uniform-vector count, FPGA0_CLK_CTRL.  The tcl reads all four by
    # index and does not default them.  And it goes through hw/board.sh
    # because there is one board and one JTAG cable.
    hw/board.sh "$XSDB" hw/xsdb_bench_gen.tcl "$BIT" "${K}_fold_$tag" \
        "${N_UNIFORM:-3000}" "${CLK_CTRL:-0x00100A00}" \
        > "$OUT/run_$tag.log" 2>&1 || true
    grep -E "BENCH|per iter|median" "$OUT/run_$tag.log" | tail -4 | sed 's/^/  /' || \
        tail -3 "$OUT/run_$tag.log" | sed 's/^/  /'
done
