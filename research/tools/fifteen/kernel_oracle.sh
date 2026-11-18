#!/usr/bin/env bash
# kernel_oracle.sh {collatz|collatz64|xorshift|ipow|isprime|gcd} < VEC.hex > VEC.exp -- the gate oracle compiled from kernels/<k>/<k>.c itself
# (CALL_KERNEL stubbed, main renamed). VEC lines are two hex words: collatz reads the first, collatz64 second:first,
# xorshift / ipow take (first, second) as their two arguments; isprime reads the first (no bench mask; 2026-11-17).
# Reproduces col13 / c6414 / xor17 / ipow17 .exp exactly (checked 2026-11-16); produced col14 / c6415 / xor19.
set -euo pipefail
K=$1; R=$(cd "$(dirname "$0")/../../.." && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
# A kernel not in kernels/ is read from Dynamatic's integration tests (gcd), as data: nothing there is edited.
S=$R/kernels/$K; [ -d "$S" ] || S=$R/dynamatic/integration-test/$K
sed 's/^int main(void)/int main_unused(void)/' "$S/$K.c" > "$T/k.c"
# The bench masks operands before the kernel sees them (cells/hw/gen_bench.py DOMAIN_RESTRICTIONS): collatz n & 0xFFFF,
# collatz64 high word 0, xorshift rounds & 0xFFF. The oracle applies the same masks, so a vector outside the domain gets
# the answer the bench will actually produce (2026-11-17: three collatz vectors above the mask looked like kernel errors).
case $K in collatz64) ARG='(in_int_t)lo';; collatz) ARG='(in_int_t)(lo & 0xFFFFu)';; xorshift) ARG='(in_int_t)lo, (in_int_t)(hi & 0xFFFu)';; isprime) ARG='(in_int_t)lo';; *) ARG='(in_int_t)lo, (in_int_t)hi';; esac
cat > "$T/d.c" <<C
#include <stdio.h>
#include "$K.h"
int main(void){ unsigned lo,hi; while(scanf("%x %x",&lo,&hi)==2) printf("%08x\n",(unsigned)$K($ARG)); return 0; }
C
gcc -O1 -fwrapv -I"$T" -I"$S" "$T/d.c" "$T/k.c" -o "$T/o"; "$T/o"
