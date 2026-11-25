# exitcond_cfront_cdiff_w64.py -- record (shard A subagent, 2026-11-20): cfront with CF_BREAK / CF_DEFINE / CF_CONSTTEST / CF_W64 /
# CF_MULTIDECL (the reading used by the lfsrfind / fold64 / twoloops / nest3 exit-test proofs) vs gcc -O0 -fwrapv.
# Result: fold64 213, lfsrfind 214, twoloops 214 (n within its declared <= 128), nest3 210 vectors (a, b <= 8): 0 mismatches each.
# Paths as run (a patched tools copy under /tmp). A test, not a proof.
# cdiff_w64.py -- cfront (patched copy /tmp/claude-0/sub2/cft: iftest, multidecl, break, define, consttest, w64)
# vs gcc -O0 -fwrapv, for fold64 (1 x int64 arg) and lfsrfind (2 x int32 args). Env flags as given by the caller.
import sys, os, re, random, subprocess
sys.path.insert(0, '/tmp/claude-0/sub2/cft/autoproof')
import cfront
for k in sys.argv[1:]:
    path = f'/tmp/claude-0/rs/kernels/{k}/{k}.c'
    src = open(path).read()
    hdr = open(f'/tmp/claude-0/rs/kernels/{k}/{k}.h').read()
    td = re.search(r'typedef[^;]*in_int_t;', hdr).group(0)
    body = re.sub(r'^#include.*$', '', src[:src.index('int main')], flags=re.M)
    rnd = random.Random(1)
    if k == 'fold64':
        sp = [0, -1, 1, -2**63, 2**63 - 1, -2**31, 2**31 - 1, 2**32 - 1, 2**32, 255, 256, 0x1122334455667788, -256]
        vec = [(x,) for x in sp] + [(rnd.randrange(-2**63, 2**63),) for _ in range(200)]
        main = 'int main(){long long x;while(scanf("%lld",&x)==1)printf("%u\\n",(unsigned)' + k + '(x));}\n'
        W = 64
    else:
        if k == 'lfsrfind':
            sp = [0, -1, 1, -2**31, 2**31 - 1, 0x8000, 0xFFFF, 0x10000]
            vec = [(a, b) for a in sp for b in sp] + [(rnd.randrange(-2**31, 2**31), rnd.randrange(-2**31, 2**31)) for _ in range(150)]
        elif k == 'twoloops':   # declared: a any int32; n <= 128 (negative n: 0 trips)
            sa = [0, -1, 1, -2**31, 2**31 - 1, 77, 255, 256]
            sn = [-2**31, -1, 0, 1, 2, 30, 127, 128]
            vec = [(a, b) for a in sa for b in sn] + [(rnd.randrange(-2**31, 2**31), rnd.randrange(-2**31, 129)) for _ in range(150)]
        else:                   # nest3, declared: a <= 8, b <= 8 (negative: 0 trips)
            sp = [-2**31, -1, 0, 1, 2, 3, 4, 5, 7, 8]
            vec = [(a, b) for a in sp for b in sp] + [(rnd.randrange(-2**31, 9), rnd.randrange(-2**31, 9)) for _ in range(110)]
        main = 'int main(){int x,n;while(scanf("%d %d",&x,&n)==2)printf("%u\\n",(unsigned)' + k + '(x,n));}\n'
        W = 32
    open(f'cdiff/{k}.c', 'w').write("#include <stdio.h>\n" + td + "\n" + body + main)
    subprocess.run(['gcc', '-O0', '-fwrapv', '-o', f'cdiff/{k}', f'cdiff/{k}.c'], check=True)
    out = subprocess.run([f'cdiff/{k}'], input="\n".join(" ".join(map(str, v)) for v in vec), capture_output=True, text=True).stdout.split()
    P = cfront.front(path, k)
    bad = 0
    for v, o in zip(vec, out):
        r, _ = cfront.run(P, [x % (1 << W) for x in v], 1000000)
        if r != int(o): bad += 1; print(k, 'MISMATCH', v, r, o)
    print(k, len(vec), 'vectors (', len(out), 'gcc outputs ), mismatches', bad)
