#!/usr/bin/env bash
# gcd_oracle.sh < VEC.hex > VEC.exp -- the gcd gate oracle compiled from the C, the same method as
# research/tools/fifteen/kernel_oracle.sh (which reads kernels/<k>/<k>.c; gcd has no kernels/ directory: its C is
# Dynamatic's integration-test/gcd/gcd.c, not vendored here).
# The C: gcd_kernel.c beside this script = audit/oracle/gcd_kernel.c of commit c4e69e111 (the auditor's copy of
# dynamatic main integration-test/gcd/gcd.c, sha256 759d5c3b...; includes replaced by `typedef int in_int_t;`, main
# dropped). VEC lines are two hex words, (a, b) = (first, second). The bench masks both operands to nonnegative
# (cells/hw/gen_bench.py DOMAIN_RESTRICTIONS "gcd": a & 0x7FFFFFFF, b & 0x7FFFFFFF); the oracle applies the same mask.
set -euo pipefail
H=$(cd "$(dirname "$0")" && pwd); T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
cat > "$T/d.c" <<C
#include <stdio.h>
#include "$H/gcd_kernel.c"
int main(void){ unsigned a,b; while(scanf("%x %x",&a,&b)==2) printf("%08x\n",(unsigned)gcd((in_int_t)(a & 0x7FFFFFFFu), (in_int_t)(b & 0x7FFFFFFFu))); return 0; }
C
gcc -O1 -fwrapv "$T/d.c" -o "$T/o"; "$T/o"
