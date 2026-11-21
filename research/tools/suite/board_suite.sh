#!/usr/bin/env bash
# board_suite.sh SPECDIR [K...] -- the automatic flow's suite on the board, one self-judging loop.
# For each kernel's spec in SPECDIR (research/tools/suite/mk_board_specs.py; every kernel there, or the K named):
#   1. research/tools/suite/board_rebuild.sh: the route rebuilt byte for byte (sdf and trimmed fasm checked) and its
#      bit put in cells/build/hw/K_bench_gen/;
#   2. the expected results derived from the C exactly as research/tools/suite/suite_one.sh derives them for the GLS
#      gate: its own choice of vector file and oracle (its "case $K in ... esac" block is read from suite_one.sh and
#      evaluated here, so the two cannot drift), oracle_mem.sh with ORACLE_RUNS=2 for a vector file with arrays;
#   3. the vectors on the board: cells/hw/xsdb_bench_vec.tcl (FIXED, 2 runs per call, FCLK0 83.33 MHz as the gate;
#      arrays dumped after each call for a memory kernel), under cells/hw/board.sh's lock;
#   4. research/tools/suite/board_vec_judge.py: the gate's rules against the C (arrays too, for a memory kernel).
# One line per kernel ("K: PASS k/n", "K: FAIL ...", "K: NOT RUN (why)"); last line "board_suite: P of N kernels PASS".
# Exit 0 only if every kernel named passed. Work files: ${BQ_OUT:-$HOME/runs/bq_suite}/K/ (rebuild.txt, exp.txt,
# memexp.txt, board.log, judge.txt); routes built under ${BQ_RUNS:-$HOME/runs/bq}.
# Needs: $TC (cells/verify/toolchain.sh passing), gcc (the oracles), xsdb ($XSDB) and the board.
# BQ_MOCK=1 (no board; cells/hw/test_bench_vec.sh's mock bench answers with the oracle's own values) and
# BQ_SKIP_REBUILD=1 test the loop's plumbing without a board or a toolchain.
set -uo pipefail
R=$(cd "$(dirname "$0")/../../.." && pwd)
SD=$(readlink -f "${1:?usage: board_suite.sh SPECDIR [K...]}"); shift
XSDB=${XSDB:-/home/jayjay/dev2/lib/vivado/2026.1/Vivado_Lab/bin/xsdb}
OUT=${BQ_OUT:-$HOME/runs/bq_suite}; mkdir -p "$OUT"
if [ $# -gt 0 ]; then KS=("$@"); else KS=($(ls "$SD"/*.spec | xargs -n1 basename | sed 's/\.spec$//')); fi
CASE=$(sed -n '/^case \$K in$/,/^esac$/p' "$R/research/tools/suite/suite_one.sh")
[ -n "$CASE" ] || { echo "board_suite: no vector / oracle block in suite_one.sh"; exit 2; }
np=0; n=0
for K in "${KS[@]}"; do
  n=$((n + 1)); O=$OUT/$K; rm -rf "$O"; mkdir -p "$O"
  if [ ! -f "$SD/$K.spec" ]; then echo "$K: NOT RUN (no spec $SD/$K.spec)"; continue; fi
  if [ "${BQ_SKIP_REBUILD:-0}" != 1 ]; then
    "$R/research/tools/suite/board_rebuild.sh" "$SD/$K.spec" > "$O/rebuild.txt" 2>&1 ||
      { echo "$K: NOT RUN (rebuild: $(tail -1 "$O/rebuild.txt"))"; continue; }
  fi
  V=""; OR=""; PV=""; eval "$CASE"
  [ -n "$V" ] && [ -f "$R/$V" ] || { echo "$K: NOT RUN (no vector file '$V')"; continue; }
  MEMV=0; head -1 "$R/$V" | grep -q '^// benchvec' && MEMV=1
  if [ "$MEMV" = 1 ]; then
    ( cd "$R" && ORACLE_RUNS=2 ORACLE_MEMOUT="$O/memexp.txt" research/tools/suite/oracle_mem.sh "$K" "$V" ) \
      > "$O/exp.txt" 2> "$O/oracle.err" || { echo "$K: NOT RUN (oracle: $(head -1 "$O/oracle.err"))"; continue; }
  else
    ( cd "$R" && $OR < "$V" ) > "$O/exp.txt" 2> "$O/oracle.err" || { echo "$K: NOT RUN (oracle: $(head -1 "$O/oracle.err"))"; continue; }
    [ "$(grep -c . "$O/exp.txt")" = "$(grep -c . "$R/$V")" ] || { echo "$K: NOT RUN (oracle: line count)"; continue; }
  fi
  BIT=build/hw/${K}_bench_gen/${K}_bench_gen.bit
  if [ "${BQ_MOCK:-0}" = 1 ]; then
    lay=0; mi=""
    if [ "$MEMV" = 1 ]; then   # the mock bench describes itself from the file's header (words, mems) and comment
      read -r w m < <(head -1 "$R/$V" | sed -n 's/^\/\/ benchvec words=\([0-9]*\) mems=\([0-9]*\).*/\1 \2/p')
      lay=$(( (m << 24) | (w << 16) | 0xB5C2 ))
      mi=$(sed -n '2s/.*memories \(.*\); seed.*/\1/p' "$R/$V" | grep -o '\[[0-9]*\] [iu][0-9]*' | sed 's/\[\([0-9]*\)\] [iu]\([0-9]*\)/\1:\2/' | paste -sd,)
    fi
    ( cd "$R/cells" && MOCK_EXP="$O/exp.txt" MOCK_LAYOUT=$lay MOCK_MEMINFO="$mi" \
        tclsh hw/mock_xsdb_vec.tcl hw/xsdb_bench_vec.tcl "$BIT" "$R/$V" 2 0x00100C00 "$MEMV" 0 ) > "$O/board.log" 2>&1
  else
    ( cd "$R/cells" && hw/board.sh "$XSDB" hw/xsdb_bench_vec.tcl "$BIT" "$R/$V" 2 0x00100C00 "$MEMV" 0 ) > "$O/board.log" 2>&1
  fi
  python3 "$R/research/tools/suite/board_vec_judge.py" "$O/exp.txt" "$O/board.log" \
    $([ "$MEMV" = 1 ] && echo "$O/memexp.txt") > "$O/judge.txt" 2>&1
  rc=$?
  echo "$K: $(head -1 "$O/judge.txt")"
  [ "$rc" = 0 ] && np=$((np + 1))
done
echo "board_suite: $np of $n kernels PASS"
[ "$np" = "$n" ]
