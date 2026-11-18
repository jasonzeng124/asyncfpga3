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
# Source: kernels/K/K.c, else research/data/suite/dynsrc/K/K.c (the repository's copy of Dynamatic's test, so a tree
# without dynamatic/ has an oracle), else dynamatic/integration-test/K/K.c (bdc/frontend.sh's lookup).  A source
# without K.h (some of Dynamatic's tests keep their types in the .c) is compiled into the driver itself; `int main()`
# is renamed as `int main(void)` is; a source that uses _BitInt is compiled with clang (gcc 13 has none) unless
# ORACLE_CC is set.
# An array the kernel's interface does not have: Dynamatic's frontend drops a memref the kernel never reads
# (unused_arg's `a`), and the bench has a memory per memref of the handshake.func.  If the frontend output
# build/frontend/K/comp/handshake_transformed.mlir exists, the file holds the C arrays it names, in C order; every
# other C array is filled twice (all 0, then all 0xa5a5a5a5 cast to its type) and the oracle REFUSES a call whose
# result or remaining arrays differ between the two (an array that matters cannot be left out).
# Refuses (exit 2) a pointer argument (no length), a 2-D array, an element or argument wider than 64 / an element
# wider than 32 bits, a result wider than 32 bits, a file that is not a whole number of calls, or one without the v2
# header.
set -euo pipefail
K=${1:?usage: oracle_mem.sh KERNEL VEC.hex > VEC.exp}; VEC=$(readlink -f "${2:?usage: oracle_mem.sh KERNEL VEC.hex}")
R=$(cd "$(dirname "$0")/../../.." && pwd)
SRC=$R/kernels/$K; [ -d "$SRC" ] || SRC=$R/research/data/suite/dynsrc/$K; [ -d "$SRC" ] || SRC=$R/dynamatic/integration-test/$K
[ -f "$SRC/$K.c" ] || { echo "oracle_mem.sh: no source $SRC/$K.c" >&2; exit 2; }
head -1 "$VEC" | grep -q '^// benchvec words=[0-9]* mems=[0-9]*' || { echo "oracle_mem.sh: $VEC has no v2 header" >&2; exit 2; }
T=$(mktemp -d); trap 'rm -rf "$T"' EXIT
mkdir -p "$T/dynamatic"; echo '#define CALL_KERNEL(f, ...) f(__VA_ARGS__)' > "$T/dynamatic/Integration.h"
sed -E 's/^int main[[:space:]]*\([[:space:]]*(void)?[[:space:]]*\)/int main_unused(void)/' "$SRC/$K.c" > "$T/k.c"
# no K.h: the driver includes the kernel's C itself (its typedefs / macros live there), and k.c is not linked again
HDR=1; [ -f "$SRC/$K.h" ] || HDR=0
CC=${ORACLE_CC:-gcc}; if [ -z "${ORACLE_CC:-}" ] && grep -q '_BitInt' "$SRC/$K.c"; then CC=clang; fi
python3 - "$SRC/$K.c" "$K" "$HDR" "$R" > "$T/d.c" <<'PY'
import os, re, sys
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
            arrs.append((am.group(1), am.group(3), am.group(2)))
            args.append("b%d" % (len(arrs) - 1))
            continue
        pm = re.match(r"(.+?)\s*\b([A-Za-z_]\w*)$", p)
        if not pm:
            die("oracle_mem.sh: cannot read the type of argument %r" % p)
        scal.append(pm.group(1))
        args.append("a%d" % (len(scal) - 1))
# which C arrays the file (the bench) holds: the memrefs of the frontend's handshake.func, if it is there
mlir = os.path.join(sys.argv[4], "build", "frontend", k, "comp", "handshake_transformed.mlir")
held = [n for _, _, n in arrs]
if os.path.exists(mlir):
    sys.path.insert(0, os.path.join(sys.argv[4], "bdc"))
    from hs import parse
    fn = [f for f in parse.parse_module(open(mlir).read(), filename=mlir) if not f.is_declaration][0]
    held = [a.name for a in fn.args if a.raw.startswith("memref")]
    if [n for _, _, n in arrs if n in held] != held:
        die("oracle_mem.sh: the frontend's memrefs %s are not C arrays of %s in C order (%s)"
            % (held, k, [n for _, _, n in arrs]))
pres = [i for i, (_, _, n) in enumerate(arrs) if n in held]      # in the file, in C order
absn = [i for i in range(len(arrs)) if i not in pres]            # filled twice, must not matter
npass = 2 if absn else 1
bufs = "\n".join("static %s b%d[%s];" % (t, i, d) for i, (t, d, _) in enumerate(arrs))
bufs += "\n" + "\n".join("static %s s%d[%s];" % (t, i, d) for i, (t, d, _) in enumerate(arrs) if i in pres and absn)
nel = "\n".join("  nel[%d] = (int)(sizeof(b%d) / sizeof(b%d[0])); esz[%d] = (int)sizeof(b%d[0]);" % (i, i, i, i, i)
                for i in range(len(arrs)))
decl = "\n".join("    %s a%d = (%s)take(w, &k, (int)sizeof(%s));" % (t, i, t, t) for i, t in enumerate(scal))
words = " + ".join("(int)sizeof(%s) / 4" % t for t in scal) or "0"
fill = "\n".join("    for (i = 0; i < nel[%d]; i++) b%d[i] = (%s)w[k++];" % (i, i, arrs[i][0]) for i in pres)
fill += "\n" + "\n".join("    for (i = 0; i < nel[%d]; i++) b%d[i] = (%s)(pass ? 0xa5a5a5a5u : 0u);" % (i, i, arrs[i][0])
                         for i in absn)
save = "\n".join("      for (i = 0; i < nel[%d]; i++) { if (pass && s%d[i] != b%d[i]) same = 0; s%d[i] = b%d[i]; }"
                 % (i, i, i, i, i) for i in pres) if absn else ""
dump = "\n".join(('    if (mo) { fprintf(mo, "call=%%d mem=%d data=", call); for (i = 0; i < nel[%d]; i++) '
                  'fprintf(mo, "%%s%%08x", i ? "," : "", (unsigned)b%d[i] & msk(esz[%d])); fprintf(mo, "\\n"); }')
                 % (m, i, i, i) for m, i in enumerate(pres))
print('''#include <stdio.h>
#include <stdlib.h>
#include "%(inc)s"
%(bufs)s
static int nel[8], esz[8], held[8] = {%(held)s};
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
    fprintf(stderr, "oracle_mem.sh: the file says words=%%d mems=%%d, %(k)s's C has %%d words and %(narr)d arrays"
            " the bench holds\\n", nw, nm, %(words)s); return 2; }
  if (sizeof(%(ret)s) > 4) { fprintf(stderr, "oracle_mem.sh: %(k)s returns more than 32 bits\\n"); return 2; }
  for (i = 0; i < %(narrall)d; i++) if (esz[i] > 4) { fprintf(stderr, "oracle_mem.sh: array %%d has %%d-byte elements\\n", i, esz[i]); return 2; }
  while (nwords < (1 << 20) && fscanf(f, " %%x", &w[nwords]) == 1) nwords++;
  per = nw; for (i = 0; i < %(narrall)d; i++) if (held[i]) per += nel[i];
  if (per == 0 || nwords %% per) { fprintf(stderr, "oracle_mem.sh: %%d words is not a whole number of %%d-word calls\\n", nwords, per); return 2; }
  for (call = 0; call * per < nwords; call++) {
    unsigned res = 0, res0 = 0;
    int pass, same = 1;
    for (pass = 0; pass < %(npass)d; pass++) {
    int k = call * per;
%(decl)s
%(fill)s
    for (r = 0; r < runs; r++) res = (unsigned)%(k)s(%(args)s);
    if (pass && res != res0) same = 0;
    res0 = res;
%(save)s
    }
    if (!same) { fprintf(stderr, "oracle_mem.sh: call %%d: an array the file does not hold changes the answer\\n", call); return 2; }
    printf("%%08x\\n", res & msk((int)sizeof(%(ret)s)));   /* the bench zero-extends a narrower out0 */
%(dump)s
  }
  return 0;
}''' % dict(k=k, ret=ret, words=words, narr=len(pres), narrall=len(arrs), bufs=bufs, nel=nel, decl=decl, fill=fill,
            dump=dump, save=save, npass=npass, held=", ".join("1" if i in pres else "0" for i in range(len(arrs))) or "0",
            inc=(k + ".h") if sys.argv[3] == "1" else "k.c", args=", ".join(args)))
PY
# The v2 file may carry // comments after its header; strip them before the C reads hex words.
{ head -1 "$VEC"; tail -n +2 "$VEC" | sed 's://.*$::'; } > "$T/vec.hex"
if [ "$HDR" = 1 ]; then $CC -O1 -fwrapv -I"$T" -I"$SRC" "$T/d.c" "$T/k.c" -o "$T/o"
else $CC -O1 -fwrapv -I"$T" -I"$SRC" "$T/d.c" -o "$T/o"; fi
"$T/o" "$T/vec.hex" "${ORACLE_RUNS:-1}" ${ORACLE_MEMOUT:+"$ORACLE_MEMOUT"}
