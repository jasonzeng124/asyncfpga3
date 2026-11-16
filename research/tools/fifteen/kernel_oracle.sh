#!/usr/bin/env bash
# kernel_oracle.sh {collatz|collatz64|xorshift|ipow} < VEC.hex > VEC.exp -- the gate oracle compiled from kernels/<k>/<k>.c itself
# (CALL_KERNEL stubbed, main renamed). VEC lines are two hex words: collatz reads the first, collatz64 second:first,
# xorshift / ipow take (first, second) as their two arguments.
# Reproduces col13 / c6414 / xor17 / ipow17 .exp exactly (checked 2026-11-16); produced col14 / c6415 / xor19.
set -euo pipefail
K=$1; R=$(cd "$(dirname "$0")/../../.." && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
sed 's/^int main(void)/int main_unused(void)/' "$R/kernels/$K/$K.c" > "$T/k.c"
case $K in collatz64) ARG='(in_int_t)(((unsigned long long)hi<<32)|lo)';; collatz) ARG='(in_int_t)lo';; *) ARG='(in_int_t)lo, (in_int_t)hi';; esac
cat > "$T/d.c" <<C
#include <stdio.h>
#include "$K.h"
int main(void){ unsigned lo,hi; while(scanf("%x %x",&lo,&hi)==2) printf("%08x\n",(unsigned)$K($ARG)); return 0; }
C
gcc -O1 -fwrapv -I"$T" -I"$R/kernels/$K" "$T/d.c" "$T/k.c" -o "$T/o"; "$T/o"
