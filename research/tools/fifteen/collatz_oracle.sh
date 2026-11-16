#!/usr/bin/env bash
# collatz_oracle.sh {collatz|collatz64} < VEC.hex > VEC.exp -- the gate oracle compiled from kernels/<k>/<k>.c itself
# (CALL_KERNEL stubbed, main renamed). VEC lines are "lo hi" hex words; collatz reads lo, collatz64 reads hi:lo.
# Reproduces col13.exp / c6414.exp exactly (checked 2026-11-16) and produced col14 / c6415 (n = 1 added).
set -euo pipefail
K=$1; R=$(cd "$(dirname "$0")/../../.." && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
sed 's/^int main(void)/int main_unused(void)/' "$R/kernels/$K/$K.c" > "$T/k.c"
if [ "$K" = collatz64 ]; then ARG='(in_int_t)(((unsigned long long)hi<<32)|lo)'; else ARG='(in_int_t)lo'; fi
cat > "$T/d.c" <<C
#include <stdio.h>
#include "$K.h"
int main(void){ unsigned lo,hi; while(scanf("%x %x",&lo,&hi)==2) printf("%08x\n",(unsigned)$K($ARG)); return 0; }
C
gcc -O1 -fwrapv -I"$T" -I"$R/kernels/$K" "$T/d.c" "$T/k.c" -o "$T/o"; "$T/o"
