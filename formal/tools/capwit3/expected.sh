#!/usr/bin/env bash
# C-witgen (copied from capwit2/expected.sh, C-wit): expected results of the witness inputs,
# computed by compiling the kernel functions themselves (extracted verbatim from
# kernels/<k>/<k>.c, from the function's signature to the closing brace), never from a run.
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/../../.." && pwd)"
W="${TMPDIR:-/tmp}/cwitgen-expected.$$"; mkdir -p "$W"
ext() { awk -v f="$2" '$0 ~ "^int "f"\\(" {p=1} p {print} p && /^}/ {exit}' "$ROOT/kernels/$1/$1.c"; }
{ echo '#include <stdio.h>'; echo 'typedef int in_int_t;'; ext ipow ipow
  cat <<'C'
int main(void) {
  printf("ipow(3, 7) = %d\n", ipow(3, 7));
  return 0;
}
C
} > "$W/e.c"
gcc -O0 -o "$W/e" "$W/e.c" && "$W/e"
rm -rf "$W"
