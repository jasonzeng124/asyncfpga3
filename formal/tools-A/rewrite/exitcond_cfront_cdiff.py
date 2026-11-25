# exitcond_cfront_cdiff.py -- record (shard A, 2026-11-20): cfront's reading of the C (with CF_IFTEST=1 and the multidecl patch,
# as used by the four exit-test proofs of nested / varshift / brhash / quadrec) against gcc -O0 -fwrapv on 208 vectors per kernel.
# Paths as run: a patched tools copy at /tmp/.../T (made by ringfuse_autoproof.sh with CF_IFTEST=1 CF_MULTIDECL=1), research kernels/.
# Result 2026-11-20 07:41 UTC: nested / varshift / brhash / quadrec 208 vectors, 0 mismatches each. A test, not a proof.
import sys, os, re, random, subprocess
sys.path.insert(0, '/tmp/claude-0/sub1/T/formal/tools/autoproof')
import cfront
os.environ['CF_IFTEST'] = '1'
M = 1 << 32
for k in sys.argv[1:]:
    src = open(f'/tmp/claude-0/rs/kernels/{k}/{k}.c').read()
    body = src[src.index(f'int {k}('):src.index('int main')]
    rnd = random.Random(1)
    vec = [(0, 0), (1, 1), (5, 3), (-1, 7), (2**31 - 1 if k != "nested" else 30, 5), (-2**31, 9), (12345, 64), (42, 50)] + \
          [((rnd.randrange(-2**31, 2**31) if k != "nested" else rnd.randrange(-3, 40)), rnd.randrange(-3, 300)) for _ in range(200)]
    c = "#include <stdio.h>\ntypedef int in_int_t;\n" + body + "int main(){int x,n;while(scanf(\"%d %d\",&x,&n)==2)printf(\"%u\\n\",(unsigned)" + k + "(x,n));}\n"
    open(f'cdiff/{k}.c', 'w').write(c)
    subprocess.run(['gcc', '-O0', '-fwrapv', '-o', f'cdiff/{k}', f'cdiff/{k}.c'], check=True)
    out = subprocess.run([f'cdiff/{k}'], input="\n".join(f"{x} {n}" for x, n in vec), capture_output=True, text=True).stdout.split()
    P = cfront.front(f'/tmp/claude-0/rs/kernels/{k}/{k}.c', k)
    bad = 0
    for (x, n), o in zip(vec, out):
        r, _ = cfront.run(P, [x % M, n % M], 1000000)
        if r != int(o): bad += 1; print(k, 'MISMATCH', x, n, r, o)
    print(k, len(vec), 'vectors, mismatches', bad)
