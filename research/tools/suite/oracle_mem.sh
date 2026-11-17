#!/usr/bin/env bash
# oracle_mem.sh KERNEL VEC.hex > VEC.exp -- the gate oracle for the bench's v2 vector format
# (research/data/suite/bench/README.md): any number of operand words, and arrays.  The kernel's own C, compiled with
# gcc -O1 -fwrapv, CALL_KERNEL stubbed and main renamed (the recipe of research/tools/fifteen/kernel_oracle.sh and of
# the suite's research/tools/suite/oracle.sh), with the argument mapping read off the C signature, not written per
# kernel:
#   per call, the file holds the operand words (arguments in signature order, a 32-bit one one word, a 64-bit one its
#   low word then its high word), then every element of each array argument in signature order, one 32-bit word per
#   element (an element narrower than 32 bits takes the word's low bits, as the bench's host port does).
#   The array's length is the C's own (`T a[N]` -> sizeof), so a file built for another length does not line up
#   with whole calls and is refused.
# Prints one 8-hex-digit line per call: the result (the bench's 32-bit out0; a result narrower than 32 bits is masked
# to its width, because the bench zero-extends it -- cells/hw/gen_bench.py load_signature).
# ORACLE_RUNS=R (default 1) calls the kernel R times per call on the same arrays without refilling them, as the
#   bench does with NRUNS=R, and prints the LAST result (a kernel that writes its arrays sees its own writes).
# ORACLE_MEMOUT=FILE also writes, per call, every array's final contents: "call=J mem=M data=w0,w1,..." (8 hex digits
#   each), the form ps7_bench.v's +MEMDUMP=1 prints them in (BENCHMEM lines).
# Source: kernels/K/K.c, else dynamatic/integration-test/K/K.c (bdc/frontend.sh's lookup).  Refuses (exit 2) a
# pointer argument (no length), a 2-D array, an element or argument wider than 64 / an element wider than 32 bits,
# a result wider than 32 bits, a file that is not a whole number of calls, or one without the v2 header.
set -euo pipefail
K=${1:?usage: oracle_mem.sh KERNEL VEC.hex > VEC.exp}; VEC=$(readlink -f "${2:?usage: oracle_mem.sh KERNEL VEC.hex}")
R=$(cd "$(dirname "$0")/../../.." && pwd)
SRC=$R/kernels/$K; [ -d "$SRC" ] || SRC=$R/dynamatic/integration-test/$K
[ -f "$SRC/$K.c" ] || { echo "oracle_mem.sh: no source $SRC/$K.c" >&2; exit 2; }
head -1 "$VEC" | grep -q '^// benchvec words=[0-9]* mems=[0-9]*' || { echo "oracle_mem.sh: $VEC has no v2 header" >&2; exit 2; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
sed 's/^int main(void)/int main_unused(void)/' "$SRC/$K.c" > "$T/k.c"
python3 - "$SRC/$K.c" "$K" > "$T/d.c" <<'PY'
import re, sys
def die(msg):
    print(msg, file=sys.stderr); sys.exit(2)
src, k = open(sys.argv[1]).read(), sys.argv[2]
src = re.sub(r"/\*.*?\*/", " ", src, flags=re.S)
src = re.sub(r"//[^\n]*", " ", src)
m = re.search(r"(^|[;}\n])\s*([A-Za-z_][\w \t]*?)\b" + re.escape(k) + r"\s*\(([^)]*)\)\s*\{", src)
if not m:
    die("oracle_mem.sh: no definition of %s(...) { in the C" % k)
ret, params = m.group(2).strip(), m.group(3).strip()
if re.sub(r"\b(static|inline|extern)\b", "", ret).strip() == "void":
    die("oracle_mem.sh: %s returns void: the bench completes a run on out0, so a kernel without a result is not supported yet (research/data/suite/bench/README.md)" % k)
scal, arrs, args = [], [], []
if params and params != "void":
    for p in params.split(","):
        p = p.strip()
        if "*" in p:
            die("oracle_mem.sh: %s has a pointer argument (%s): no length to read" % (k, p))
        am = re.match(r"(.+?)\s*\b([A-Za-z_]\w*)\s*\[([^\]]+)\]\s*$", p)
        if am:
            if p.count("[") > 1:
                die("oracle_mem.sh: %s has a 2-D array argument (%s)" % (k, p))
            arrs.append((am.group(1), am.group(3)))
            args.append("b%d" % (len(arrs) - 1))
            continue
        pm = re.match(r"(.+?)\s*\b([A-Za-z_]\w*)$", p)
        if not pm:
            die("oracle_mem.sh: cannot read the type of argument %r" % p)
        scal.append(pm.group(1))
        args.append("a%d" % (len(scal) - 1))
bufs = "\n".join("static %s b%d[%s];" % (t, i, d) for i, (t, d) in enumerate(arrs))
nel = "\n".join("  nel[%d] = (int)(sizeof(b%d) / sizeof(b%d[0])); esz[%d] = (int)sizeof(b%d[0]);" % (i, i, i, i, i)
                for i in range(len(arrs)))
decl = "\n".join("    %s a%d = (%s)take(w, &k, (int)sizeof(%s));" % (t, i, t, t) for i, t in enumerate(scal))
words = " + ".join("(int)sizeof(%s) / 4" % t for t in scal) or "0"
fill = "\n".join("    for (i = 0; i < nel[%d]; i++) b%d[i] = (%s)w[k++];" % (i, i, t) for i, (t, _) in enumerate(arrs))
dump = "\n".join(('    if (mo) { fprintf(mo, "call=%%d mem=%d data=", call); for (i = 0; i < nel[%d]; i++) '
                  'fprintf(mo, "%%s%%08x", i ? "," : "", (unsigned)b%d[i] & msk(esz[%d])); fprintf(mo, "\\n"); }')
                 % (i, i, i, i) for i in range(len(arrs)))
print('''#include <stdio.h>
#include <stdlib.h>
#include "%(k)s.h"
%(bufs)s
static int nel[8], esz[8];
static unsigned long long take(const unsigned *w, int *k, int bytes) {
  unsigned long long v;
  if (bytes <= 4) { v = w[*k]; *k += 1; }
  else if (bytes == 8) { v = (unsigned long long)w[*k] | ((unsigned long long)w[*k + 1] << 32); *k += 2; }
  else { fprintf(stderr, "oracle_mem.sh: an argument of %%d bytes\\n", bytes); exit(2); }
  return v;
}
static unsigned msk(int bytes) { return bytes >= 4 ? 0xffffffffu : (1u << (8 * bytes)) - 1u; }
int main(int argc, char **argv) {
  static unsigned w[1 << 20];
  int nw, nm, nwords = 0, call, i, r, runs = argc > 2 ? atoi(argv[2]) : 1, per;
  char line[512];
  FILE *f = fopen(argv[1], "r"), *mo = argc > 3 ? fopen(argv[3], "w") : NULL;
%(nel)s
  if (!f || !fgets(line, sizeof line, f) || sscanf(line, "// benchvec words=%%d mems=%%d", &nw, &nm) != 2) {
    fprintf(stderr, "oracle_mem.sh: no v2 header\\n"); return 2; }
  if (nw != %(words)s || nm != %(narr)d) {
    fprintf(stderr, "oracle_mem.sh: the file says words=%%d mems=%%d, %(k)s's C has %%d words and %(narr)d arrays\\n",
            nw, nm, %(words)s); return 2; }
  if (sizeof(%(ret)s) > 4) { fprintf(stderr, "oracle_mem.sh: %(k)s returns more than 32 bits\\n"); return 2; }
  for (i = 0; i < nm; i++) if (esz[i] > 4) { fprintf(stderr, "oracle_mem.sh: array %%d has %%d-byte elements\\n", i, esz[i]); return 2; }
  while (nwords < (1 << 20) && fscanf(f, " %%x", &w[nwords]) == 1) nwords++;
  per = nw; for (i = 0; i < nm; i++) per += nel[i];
  if (per == 0 || nwords %% per) { fprintf(stderr, "oracle_mem.sh: %%d words is not a whole number of %%d-word calls\\n", nwords, per); return 2; }
  for (call = 0; call * per < nwords; call++) {
    int k = call * per;
    unsigned res = 0;
%(decl)s
%(fill)s
    for (r = 0; r < runs; r++) res = (unsigned)%(k)s(%(args)s);
    printf("%%08x\\n", res & msk((int)sizeof(%(ret)s)));   /* the bench zero-extends a narrower out0 */
%(dump)s
  }
  return 0;
}''' % dict(k=k, ret=ret, words=words, narr=len(arrs), bufs=bufs, nel=nel, decl=decl, fill=fill, dump=dump,
            args=", ".join(args)))
PY
# The v2 file may carry // comments after its header; strip them before the C reads hex words.
{ head -1 "$VEC"; tail -n +2 "$VEC" | sed 's://.*$::'; } > "$T/vec.hex"
${ORACLE_CC:-gcc} -O1 -fwrapv -I"$T" -I"$SRC" "$T/d.c" "$T/k.c" -o "$T/o"
"$T/o" "$T/vec.hex" "${ORACLE_RUNS:-1}" ${ORACLE_MEMOUT:+"$ORACLE_MEMOUT"}
