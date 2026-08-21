#!/usr/bin/env bash
# rloc_sweep.sh -- does RLOC_GROUP relative placement actually buy anything?
#
# Re-places ONE post-synthesis netlist three ways -- unclustered, v1 (a link's
# C node beside one of its own latch LUTs) and v2 (v1 plus the consuming
# bd_mux's two joins) -- over several placer seeds, and measures each route.
#
# Everything except the attribute is held fixed: same synthesis output, same
# nextpnr binary, same xdc, same seed.  The baseline is the identical JSON put
# through the identical rewriter with --variant none, so a difference in the
# numbers can only come from the attribute.  That matters more than usual here
# because the toolchain source tree carries three other in-progress patches;
# comparing against a bitstream built yesterday would be comparing binaries.
#
# WHY SEEDS.  A single route decides nothing.  Measured here, the unclustered
# gcd_ps netlist reports 0, 6, 5 and 3 rule-E violations on seeds default,
# 1, 2 and 3 -- build-to-build placement noise is larger than any one route's
# margin, which is exactly why per-link delay padding never converged
# (verify/converge.sh).  A remedy has to hold across seeds or it is luck.
#
#   usage: rloc_sweep.sh [design ...]          default: gcd_ps ipow_ps
#   env:   SEEDS="dflt 1 2 3"   NEXTPNR=<binary>   OUT=<dir>
#
# Needs cells/build/hw/<design>/<design>.json to exist (./hw/build_hw.sh
# <design> writes it).  It reads that file and never writes into build/hw.
set -u
cd "$(dirname "$0")/.." || exit 2

TC=${TC:-/home/jayjay/dev2/lib/fpgatoolchain}
NEXTPNR=${NEXTPNR:-$TC/openxc7-src/nextpnr-xilinx/build/nextpnr-xilinx}
CHIPDB=${CHIPDB:-$TC/openxc7/xc7z010clg400.bin}
OUT=${OUT:-build/rloc}
SEEDS=${SEEDS:-"dflt 1 2 3"}
DESIGNS=${*:-"gcd_ps ipow_ps"}

[ -x "$NEXTPNR" ] || { echo "no nextpnr at $NEXTPNR" >&2; exit 2; }
mkdir -p "$OUT"

for d in $DESIGNS; do
    src=build/hw/$d/$d.json
    [ -f "$src" ] || { echo "missing $src -- run ./hw/build_hw.sh $d" >&2; exit 2; }
    # Copy once.  Another agent rebuilding build/hw mid-sweep would otherwise
    # put two different netlists into one before/after comparison.
    cp "$src" "$OUT/$d.src.json"
    for v in none v1 v2; do
        n=$v; [ "$v" = none ] && n=base
        python3 hw/rloc_stamp.py "$OUT/$d.src.json" "$OUT/$d.$n.json" \
            --variant "$v" --report
    done
done

for s in $SEEDS; do
    for d in $DESIGNS; do
        for v in base v1 v2; do
            o=$OUT/$([ "$s" = dflt ] && echo "" || echo "seed$s/")$d.$v
            mkdir -p "$o"
            cat > "$o/$d.xdc" <<'XDC'
set_property PACKAGE_PIN W14 [get_ports led_red]
set_property IOSTANDARD LVCMOS33 [get_ports led_red]
set_property PACKAGE_PIN W13 [get_ports led_green]
set_property IOSTANDARD LVCMOS33 [get_ports led_green]
XDC
            seedarg=""; [ "$s" = dflt ] || seedarg="--seed $s"
            t0=$(date +%s)
            # shellcheck disable=SC2086
            "$NEXTPNR" --chipdb "$CHIPDB" --xdc "$o/$d.xdc" --ignore-loops \
                $seedarg --json "$OUT/$d.$v.json" \
                --write "$o/${d}_routed.json" --sdf "$o/$d.sdf" \
                --fasm "$o/$d.fasm" > "$o/pnr.log" 2>&1
            rc=$?
            echo "$d $v seed=$s rc=$rc wall=$(( $(date +%s) - t0 ))s" \
                | tee "$o/wall.txt"
            [ $rc -eq 0 ] || continue
            python3 verify/skew.py "$o/$d.sdf" -v > "$o/skew.txt" 2>&1
        done
    done
done

echo
python3 - "$OUT" $DESIGNS <<'PY'
import re, sys, pathlib
out = pathlib.Path(sys.argv[1])
for d in sys.argv[2:]:
    print(f"=== {d}   verify/skew.py rule E, guarded margin in ps")
    print(f"{'seed':>5} {'variant':>7} {'gates':>6} {'viol':>5} {'worst':>7} "
          f"{'p10':>7} {'LUTsites':>9} {'CLBtiles':>9} {'wall':>6}")
    for s in ["dflt", "1", "2", "3"]:
        for v in ["base", "v1", "v2"]:
            o = out / (f"{d}.{v}" if s == "dflt" else f"seed{s}/{d}.{v}")
            if not (o / "skew.txt").exists():
                continue
            g = sorted(int(m.group(2)) for m in re.finditer(
                r"margin ([+-]\d+) ps raw, ([+-]\d+) ps guarded",
                (o / "skew.txt").read_text()))
            f = (o / f"{d}.fasm").read_text()
            tiles = len(set(re.findall(r"^CLB[A-Z_]+_X\d+Y\d+", f, re.M)))
            w = re.search(r"wall=(\d+)s", (o / "wall.txt").read_text()).group(1)
            n = len(g)
            print(f"{s:>5} {v:>7} {n:>6} {sum(1 for x in g if x <= 0):>5} "
                  f"{g[0]:>7} {g[int(.1 * (n - 1))]:>7} "
                  f"{f.count('LUT.INIT'):>9} {tiles:>9} {w + 's':>6}")
    print()
PY
python3 verify/rloc_dist.py "$OUT"/*.base/*.sdf "$OUT"/*.v1/*.sdf "$OUT"/*.v2/*.sdf
