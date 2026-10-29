#!/usr/bin/env bash
# C-wit: expected results of the witness inputs, computed by compiling the kernel functions
# themselves (extracted verbatim from kernels/<k>/<k>.c, everything from the function's
# signature to the closing brace before main), never from a run.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
W="${TMPDIR:-/tmp}/cwit-expected.$$"; mkdir -p "$W"
ext() { awk -v f="$2" '$0 ~ "^int "f"\\(" {p=1} p {print} p && /^}/ {exit}' "$ROOT/kernels/$1/$1.c"; }
{ echo '#include <stdio.h>'; echo 'typedef int in_int_t;'; ext xorshift xorshift; ext collatz collatz
  cat <<'C'
int main(void) {
  printf("xorshift(2463534242, 4) = %u\n", (unsigned)xorshift((in_int_t)2463534242u, 4));
  printf("collatz(7) = %d\n", collatz(7));
  return 0;
}
C
} > "$W/e.c"
gcc -O0 -o "$W/e" "$W/e.c" && "$W/e"
rm -rf "$W"
