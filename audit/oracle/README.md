gcd_hw oracle check. gcd_kernel.c = dynamatic main integration-test/gcd/gcd.c (sha256 in gcd.c.sha256) with the
two includes replaced by `typedef int in_int_t;` and main() dropped. oracle_gcd.c runs it on the 16 (a,b) pairs
from cells/hw/gcd_rig.v (claude/research 19a93c1). Command: gcc -O0 -o og oracle_gcd.c && ./og.
Result oracle_out.txt: all 16 expected values in gcd_rig.v's table equal the C's output.
