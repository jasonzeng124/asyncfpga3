#!/usr/bin/env bash
# trimcheck.sh UNTRIMMED.fasm TRIMMED.fasm WORKDIR [TRIM_RECORD]   (shard A, 2026-11-20; untrusted Python)
# Research's post-route trim (research/tools/auto/trim_lines.py) shortens a routed delay line by giving one element the
# INIT that passes the line's side input. This checks, from the bits alone:
#  1. the two FASMs differ ONLY in LUT INIT lines (no pip, no other feature): placement and routing are unchanged;
#  2. each changed LUT read two pins before (the chain AND / OR of predecessor and side) and passes exactly one of
#     them afterwards, uninverted, on O6 and O5 (lutdep.py);
#  3. in the netlist decoded from the TRIMMED bits (tools-A/target/make_net_fasm.sh: prjxray-db, round trip invented 0),
#     the kept pin is the line's side input: the source it reads also feeds a LUT that drives the entry, i.e. the dead
#     predecessor reads the same source; and the live line from the entry onwards has N elements (chainck.py).
#     Compare those lengths with TRIM_RECORD (MACRO=LEN): the bits carry no macro names, so the match is by multiset
#     (a macro can hold several chains).
# Needs $TC with openxc7's prjxray-db (cloud/toolchain-cache.sh fetch).
set -euo pipefail
U=$1; T=$2; W=$3; R=${4:-}
HERE=$(cd "$(dirname "$0")" && pwd); mkdir -p "$W"
other=$(diff <(sort "$U") <(sort "$T") | grep '^[<>]' | grep -v '\.INIT\[' || true)
[ -z "$other" ] && echo "1. only LUT INIT lines differ" || { echo "1. FAIL: non-INIT differences:"; echo "$other" | head; }
python3 "$HERE/lutdep.py" "$U" "$T" | tee "$W/lutdep.txt" | tail -1
sites=$(diff <(sort "$U") <(sort "$T") | grep '^>' | grep '\.INIT\[' | sed 's/^> //; s/\.INIT\[.*//' | sort -u || true)
"$HERE/../target/make_net_fasm.sh" "$T" "$W/net" > "$W/decode.txt" 2>&1; grep roundtrip: "$W/decode.txt"
python3 "$HERE/chainck.py" "$W/net/net.json" $sites | tee "$W/chains.txt"
echo "live lengths from the bits: $(grep -o 'from entry = [0-9]*' "$W/chains.txt" | awk '{print $4}' | sort -n | tr '\n' ' ')"
if [ -n "$R" ]; then
  echo "trim record lengths:         $(cut -d= -f2 "$R" | sort -n | tr '\n' ' ')"
  bl=$(grep -o 'from entry = [0-9]*' "$W/chains.txt" | awk '{print $4}' | sort -n | tr '\n' ' '); rl=$(cut -d= -f2 "$R" | sort -n | tr '\n' ' ')
  if [ "$(echo $bl | wc -w)" = "$(echo $rl | wc -w)" ]; then
    [ "$bl" = "$rl" ] || { echo "FAIL: live lengths from the bits differ from the record"; exit 2; }
  else echo "(lengths not compared one to one: $(echo $bl | wc -w) chains for $(echo $rl | wc -w) macros; a macro can hold several chains)"; fi
fi
grep -q "feeds the entry (dead predecessor): NO" "$W/chains.txt" && { echo "FAIL: a kept pin is not the side input"; exit 2; }
[ -z "$other" ] || exit 2
grep -q "not as expected: 0" "$W/lutdep.txt" || exit 2
echo "OK"
