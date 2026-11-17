#!/usr/bin/env bash
# preload_oracle.sh < PRELOAD_VEC > EXP -- the oracle for a preloaded xorshift run, compiled from kernels/xorshift/xorshift.c
# itself: the kernel's own loop, with its counter's start value `int i = 0;` replaced by a variable PRELOAD_I0 (the only
# edit; CALL_KERNEL stubbed and main renamed as research/tools/fifteen/kernel_oracle.sh does).
# Input lines: "seed rounds_bench i0 n" (hex). The hardware loop (research/data/fifteen/xorshift_predec.mlir) is a do-while
# on (i, x, n = rounds - 1): body with i, continue while i < n (signed). With i = i0 and n preloaded, and the entry guard
# rounds_bench > 0 taken on the bench's own (12-bit masked) rounds, the body runs n - i0 + 1 times (i0 <= n). The C loop
# from the same state is `while (i < rounds)` with i = i0, rounds = n + 1 (so n <= 2^31 - 2). Output: x as %08x.
# Refuses a state the C cannot express (n = INT_MAX, i0 > n, rounds_bench & 0xFFF == 0).
set -euo pipefail
R=$(cd "$(dirname "$0")/../../.." && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
grep -c '^  int i = 0;$' "$R/kernels/xorshift/xorshift.c" | grep -qx 1 || { echo "preload_oracle: kernel's 'int i = 0;' not found once" >&2; exit 1; }
{ echo 'extern int PRELOAD_I0;'; sed -e 's/^int main(void)/int main_unused(void)/' -e 's/^  int i = 0;$/  int i = PRELOAD_I0;/' "$R/kernels/xorshift/xorshift.c"; } > "$T/k.c"
cat > "$T/d.c" <<'C'
#include <stdio.h>
#include <stdlib.h>
#include "xorshift.h"
int PRELOAD_I0;
int main(void){ unsigned s, rb, i0, n;
  while (scanf("%x %x %x %x", &s, &rb, &i0, &n) == 4) {
    if ((rb & 0xFFFu) == 0 || (int)rb <= 0) { fprintf(stderr, "rounds_bench must be in 1..0xFFF\n"); return 1; }
    if ((int)n == 0x7fffffff || (int)i0 > (int)n) { fprintf(stderr, "state not expressible in C: i0 %x n %x\n", i0, n); return 1; }
    PRELOAD_I0 = (int)i0;
    printf("%08x\n", (unsigned)xorshift((in_int_t)s, (in_int_t)((int)n + 1)));
  }
  return 0; }
C
gcc -O1 -fwrapv -I"$T" -I"$R/kernels/xorshift" "$T/d.c" "$T/k.c" -o "$T/o"; "$T/o"
