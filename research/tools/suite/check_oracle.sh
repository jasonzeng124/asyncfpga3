#!/usr/bin/env bash
# check_oracle.sh -- the suite oracle's own checks; run after any change to research/tools/suite/oracle.sh.
#   1. it reproduces two expected-value files of the original kernels' gates byte for byte (those kernels have no bench
#      mask): research/data/eventgraph/gate/ipow17.exp (two i32 arguments) and research/data/alltable/isp17.exp (one);
#   2. negative control for 1: the ipow17 vectors with their two words swapped must NOT reproduce ipow17.exp, so a
#      mapping that got the argument order wrong would have failed check 1;
#   3. the i64 word order (low word first, then high): fold64 through the oracle on "lo hi" equals fold64 called
#      directly on (hi << 32 | lo), and differs from it with the words swapped;
#   4. refusals (exit 2): a kernel the bench masks (collatz) and a memory kernel (memsum).
# Prints one line per check and "check_oracle: PASS" or "check_oracle: FAIL".
set -uo pipefail
R=$(cd "$(dirname "$0")/../../.." && pwd); O=$R/research/tools/suite/oracle.sh; T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
bad=0; ok() { echo "ok    $*"; }; no() { echo "FAIL  $*"; bad=1; }
for p in "ipow research/data/eventgraph/gate/ipow17" "isprime research/data/alltable/isp17"; do
  set -- $p
  "$O" "$1" < "$R/$2.hex" > "$T/$1.exp" && cmp -s "$T/$1.exp" "$R/$2.exp" && ok "$1 reproduces $2.exp byte for byte" \
    || no "$1 does not reproduce $2.exp"
done
awk '{print $2, $1}' "$R/research/data/eventgraph/gate/ipow17.hex" | "$O" ipow > "$T/swap.exp"
cmp -s "$T/swap.exp" "$R/research/data/eventgraph/gate/ipow17.exp" && no "negative control: swapped ipow words still match" \
  || ok "negative control: ipow17 with its words swapped does not match ipow17.exp"
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
sed 's/^int main(void)/int main_unused(void)/' "$R/kernels/fold64/fold64.c" > "$T/k.c"
cat > "$T/d.c" <<'C'
#include <stdio.h>
#include "fold64.h"
int main(void) {
  static const unsigned long long v[] = {0x1122334455667788ull, 0x80000000000000ffull, 0x00000001fffffff0ull};
  for (int i = 0; i < 3; i++) printf("%08x\n", (unsigned)fold64((in_int_t)v[i]));
  return 0;
}
C
gcc -O1 -fwrapv -I"$T" -I"$R/kernels/fold64" "$T/d.c" "$T/k.c" -o "$T/direct" && "$T/direct" > "$T/direct.exp"
printf '55667788 11223344\n000000ff 80000000\nfffffff0 00000001\n' | "$O" fold64 > "$T/lohi.exp"
printf '11223344 55667788\n80000000 000000ff\n00000001 fffffff0\n' | "$O" fold64 > "$T/hilo.exp"
cmp -s "$T/lohi.exp" "$T/direct.exp" && ok "i64: fold64 on 'lo hi' equals the direct call on hi:lo" || no "i64 word order"
cmp -s "$T/hilo.exp" "$T/direct.exp" && no "i64 negative control: swapped words still match" \
  || ok "i64 negative control: 'hi lo' does not match"
for k in collatz memsum; do
  echo "00000001 00000002" | "$O" $k > /dev/null 2>&1; rc=$?
  [ $rc = 2 ] && ok "$k refused (exit 2)" || no "$k not refused (exit $rc)"
done
[ $bad = 0 ] && echo "check_oracle: PASS" || { echo "check_oracle: FAIL"; exit 1; }
