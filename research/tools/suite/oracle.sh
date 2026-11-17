#!/usr/bin/env bash
# oracle.sh KERNEL < VEC.hex > VEC.exp -- the generic suite oracle (kernels/SUITE.md): the kernel's own C,
# compiled with gcc -O1 -fwrapv, CALL_KERNEL stubbed and main renamed (research/tools/fifteen/kernel_oracle.sh's
# recipe), with the bench's argument mapping read off the C signature, not written per kernel:
#   the bench drives at most MAX_WORDS = 2 operand words (cells/hw/gen_bench.py); arguments take them in order,
#   a 32-bit argument one word, a 64-bit argument two (low word first, then high).  A 1-argument i32 kernel ignores
#   the second word.  No input masks.  One result per vector, printed as 8 hex digits (the bench's 32-bit out0).
# VEC.hex is the bench's format: two 8-digit hex words per line (cells/gls/ps/ps7_bench.v reads it with $readmemh,
# word 2j = op0 and 2j+1 = op1 of vector j).  Source: kernels/K/K.c, else dynamatic/integration-test/K/K.c (the
# same lookup as bdc/frontend.sh).
# Refuses (exit 2), rather than print an answer that is not the bench's:
#   - a kernel cells/hw/gen_bench.py masks (DOMAIN_RESTRICTIONS): the bench changes its inputs; use
#     research/tools/fifteen/kernel_oracle.sh, which applies the same masks;
#   - an array or pointer argument (memory: waits for the bench ABI work), an argument that is not 32 or 64 bits,
#     more than 2 words in all, a result wider than 32 bits.
# ORACLE_CC (default gcc) picks the compiler.  Checked 2026-11-17: reproduces research/data/eventgraph/gate/ipow17.exp
# and research/data/alltable/isp17.exp byte for byte from their .hex files (research/tools/suite/check_oracle.sh).
set -euo pipefail
K=${1:?usage: oracle.sh KERNEL < VEC.hex > VEC.exp}
R=$(cd "$(dirname "$0")/../../.." && pwd)
SRC=$R/kernels/$K; [ -d "$SRC" ] || SRC=$R/dynamatic/integration-test/$K
[ -f "$SRC/$K.c" ] || { echo "oracle.sh: no source $SRC/$K.c" >&2; exit 2; }
MASK=$(python3 -c "import sys; sys.path.insert(0, sys.argv[1]); import gen_bench; print(sys.argv[2] in gen_bench.DOMAIN_RESTRICTIONS)" \
       "$R/cells/hw" "$K") || { echo "oracle.sh: cannot read cells/hw/gen_bench.py DOMAIN_RESTRICTIONS" >&2; exit 2; }
if [ "$MASK" != False ]; then
  echo "oracle.sh: $K has a bench input mask (cells/hw/gen_bench.py DOMAIN_RESTRICTIONS): its answers are not the" \
       "unmasked C's; use research/tools/fifteen/kernel_oracle.sh" >&2; exit 2
fi
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
sed 's/^int main(void)/int main_unused(void)/' "$SRC/$K.c" > "$T/k.c"
# The signature: the definition `RET K(T0 a0, T1 a1) {` in the C (comments stripped).  Types are kept as written
# (typedefs included) and sized by the compiler, so in_int_t = long long takes two words without this script knowing.
python3 - "$SRC/$K.c" "$K" > "$T/d.c" <<'PY'
import re, sys
def die(msg):
    print(msg, file=sys.stderr); sys.exit(2)
src, k = open(sys.argv[1]).read(), sys.argv[2]
src = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
src = re.sub(r"//[^\n]*", " ", src)
m = re.search(r"(^|[;}\n])\s*([A-Za-z_][\w \t]*?)\b" + re.escape(k) + r"\s*\(([^)]*)\)\s*\{", src)
if not m:
    die("oracle.sh: no definition of %s(...) { in the C" % k)
ret, params = m.group(2).strip(), m.group(3).strip()
types = []
if params and params != "void":
    for p in params.split(","):
        p = p.strip()
        if "[" in p or "*" in p:
            die("oracle.sh: %s has an array / pointer argument (%s): memory kernels wait for the bench ABI" % (k, p))
        pm = re.match(r"(.+?)\s*\b([A-Za-z_]\w*)$", p)
        if not pm:
            die("oracle.sh: cannot read the type of argument %r" % p)
        types.append(pm.group(1))
decl = "\n".join("  %s a%d = (%s)take(w, &k, (int)sizeof(%s));" % (t, i, t, t) for i, t in enumerate(types))
words = " + ".join("(int)sizeof(%s) / 4" % t for t in types) or "0"
print('''#include <stdio.h>
#include <stdlib.h>
#include "%(k)s.h"
static unsigned long long take(const unsigned *w, int *k, int bytes) {
  unsigned long long v;
  if (bytes == 4) { v = w[*k]; *k += 1; }
  else if (bytes == 8) { v = (unsigned long long)w[*k] | ((unsigned long long)w[*k + 1] << 32); *k += 2; }
  else { fprintf(stderr, "oracle.sh: an argument of %%d bytes (the bench takes 32- or 64-bit ones)\\n", bytes); exit(2); }
  return v;
}
int main(void) {
  unsigned w[2];
  if (%(words)s > 2) { fprintf(stderr, "oracle.sh: %(k)s needs %%d operand words, the bench has 2\\n", %(words)s); return 2; }
  if (sizeof(%(ret)s) > 4) { fprintf(stderr, "oracle.sh: %(k)s returns more than 32 bits\\n"); return 2; }
  while (scanf("%%x %%x", &w[0], &w[1]) == 2) {
    int k = 0;
%(decl)s
    (void)k;
    printf("%%08x\\n", (unsigned)%(k)s(%(args)s));
  }
  return 0;
}''' % dict(k=k, ret=ret, words=words, decl=decl, args=", ".join("a%d" % i for i in range(len(types)))))
PY
${ORACLE_CC:-gcc} -O1 -fwrapv -I"$T" -I"$SRC" "$T/d.c" "$T/k.c" -o "$T/o"
"$T/o"
