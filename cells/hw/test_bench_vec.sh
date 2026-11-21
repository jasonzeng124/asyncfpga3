#!/usr/bin/env bash
# test_bench_vec.sh -- hw/xsdb_bench_vec.tcl under tclsh against hw/mock_xsdb_vec.tcl (no board): the vector files are
# read as $readmemh reads them, every call's stimulus (operand words, every memory word) is written as the GLS host
# writes it, the BENCHRES lines are judged by research/tools/suite/board_vec_judge.py, and the judge FAILS what it must.
#   cells/hw/test_bench_vec.sh            prints one line per check and "test_bench_vec: N / N OK"; exit 0 only if all
set -uo pipefail
cd "$(dirname "$0")/.."                       # cells/
R=..; T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
J="python3 $R/research/tools/suite/board_vec_judge.py"
n=0; okc=0
check() { n=$((n + 1)); if [ "$2" = "$3" ]; then okc=$((okc + 1)); echo "ok   $1"; else echo "FAIL $1 (got $2, want $3)"; fi; }
mock() { tclsh hw/mock_xsdb_vec.tcl hw/xsdb_bench_vec.tcl "$@"; }

# 1. two-word vectors (the collatz gate vectors) with their C-derived expected results
V=$R/research/data/eventgraph/gate/col18.hex; E=$R/research/data/eventgraph/gate/col18.exp
MOCK_EXP=$E MOCK_LOG=$T/w1.log mock bit.bit $V > $T/r1.log 2>&1
$J $E $T/r1.log > $T/j1.txt; rc=$?; check "v1: judge passes a right run ($(cat $T/j1.txt))" $rc 0
python3 - "$V" "$T/w1.log" > $T/s1.txt <<'PY'
import re, sys
words = [int(t, 16) for l in open(sys.argv[1]) for t in l.split("//")[0].split()]
calls = [words[i:i + 2] for i in range(0, len(words), 2)]
cur, seen, bad = {}, [], 0
for l in open(sys.argv[2]):
    f = l.split()
    if f[0] == "W":
        cur[int(f[1], 16)] = int(f[2], 16)
    elif f[0] == "START":
        j = int(f[1]); seen.append(j)
        if [cur.get(0x08), cur.get(0x0C)] != calls[j] or cur.get(0x14) != 2:
            bad += 1
print("calls %d started %d stimulus-mismatch %d" % (len(calls), len(seen), bad))
PY
check "v1: every call started once with the file's operands, NRUNS 2 ($(cat $T/s1.txt))" "$(cat $T/s1.txt)" "calls 17 started 17 stimulus-mismatch 0"
MOCK_EXP=$E MOCK_CORRUPT=5 mock bit.bit $V > $T/r2.log 2>&1
$J $E $T/r2.log > $T/j2.txt; rc=$?; check "v1 negative: one wrong result fails ($(cat $T/j2.txt))" $rc 1
MOCK_EXP=$E MOCK_HANG=3 mock bit.bit $V > $T/r3.log 2>&1
$J $E $T/r3.log > $T/j3.txt; rc=$?; check "v1 negative: one call not done fails ($(cat $T/j3.txt))" $rc 1
head -n 5 $T/r1.log | grep -v BENCHSUMMARY > $T/r4.log
$J $E $T/r4.log > $T/j4.txt; rc=$?; check "a run that stopped early is not judged ($(cat $T/j4.txt))" $rc 2

# 2. v2 vectors with a memory (binary_search: 1 operand word, a[101] i32); the "kernel" returns a made-up oracle
V2=$R/research/data/suite/vec/binary_search.hex
nw=$(grep -v '^ *//' $V2 | wc -w); nc=$((nw / 102))
python3 -c "import sys; [print('%08x' % (0x1000 + i)) for i in range($nc)]" > $T/e2.txt
LAY=$(( (1 << 24) | (1 << 16) | 0xB5C2 ))
MOCK_EXP=$T/e2.txt MOCK_LOG=$T/w5.log MOCK_LAYOUT=$LAY MOCK_MEMINFO=101:32 mock bit.bit $V2 2 0x00100C00 1 1 > $T/r5.log 2>&1
$J $T/e2.txt $T/r5.log > $T/j5.txt; rc=$?; check "v2: judge passes ($nc calls; $(cat $T/j5.txt))" $rc 0
python3 - "$V2" "$T/w5.log" "$T/r5.log" > $T/s5.txt <<'PY'
import sys
words = [int(t, 16) for l in open(sys.argv[1]) for t in l.split("//")[0].split()]
calls = [words[i:i + 102] for i in range(0, len(words), 102)]
cur, fill, bad, nst = {}, [], 0, 0
for l in open(sys.argv[2]):
    f = l.split()
    if f[0] == "W":
        a, v = int(f[1], 16), int(f[2], 16)
        cur[a] = v
        if a == 0x8C: fill = []          # MEMSTAT clear: once per call, before its fill (the read-back re-selects with 0x80)
        if a == 0x84: fill.append(v)
    elif f[0] == "START":
        j = int(f[1]); nst += 1
        if cur.get(0x08) != calls[j][0] or fill != calls[j][1:]:
            bad += 1
dump = {}
for l in open(sys.argv[3]):
    if l.startswith("BENCHMEM ") and "data=" in l:
        d = dict(x.split("=", 1) for x in l.split()[1:])
        dump[int(d["batch"])] = [int(x, 16) for x in d["data"].split(",")]
dbad = sum(1 for j, c in enumerate(calls) if dump.get(j) != c[1:])
chk = [l for l in open(sys.argv[3]) if l.startswith("BENCHMEMCHK") and "bad=0" not in l]
print("calls %d started %d stimulus-mismatch %d memdump-mismatch %d memchk-bad %d" % (len(calls), nst, bad, dbad, len(chk)))
PY
check "v2: operand + all 101 array words per call, read back and dumped as written ($(cat $T/s5.txt))" "$(cat $T/s5.txt)" "calls $nc started $nc stimulus-mismatch 0 memdump-mismatch 0 memchk-bad 0"
MOCK_EXP=$T/e2.txt MOCK_LAYOUT=$(( (2 << 24) | (1 << 16) | 0xB5C2 )) MOCK_MEMINFO=101:32,4:32 mock bit.bit $V2 > $T/r6.log 2>&1
grep -q "LAYOUT MISMATCH" $T/r6.log; rc=$?; check "v2 negative: a bench whose LAYOUT disagrees with the file is refused" $rc 0
$J $T/e2.txt $T/r6.log > /dev/null; rc=$?; check "  ... and that run is not judged" $rc 2
echo "test_bench_vec: $okc / $n OK"
[ "$okc" = "$n" ]
