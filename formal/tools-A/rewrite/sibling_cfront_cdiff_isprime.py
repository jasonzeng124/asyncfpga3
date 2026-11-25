# cdiff_isprime.py -- cfront with CF_W64 (the reading used by sub4's isprime proof; AP_* flags do not touch cfront)
# vs gcc -O0 -fwrapv on kernels/isprime/isprime.c. A test, not a proof. Vectors: -50..150, 7919, random in [-2^31, 10^6).
import sys, os, re, random, subprocess, tempfile
os.environ.update(CF_W64='1')
T = tempfile.mkdtemp(); os.makedirs(T + '/t')
subprocess.run(['cp', '-r', '/home/user/asyncfpga3/formal/tools/autoproof', T + '/t/'], check=True)
subprocess.run([sys.executable, '/home/user/asyncfpga3/formal/tools-A/rewrite/patches/cfront_w64_patch.py', T + '/t'], check=True)
sys.path.insert(0, T + '/t/autoproof')
import cfront
k = 'isprime'
path = f'/tmp/claude-0/rs/kernels/{k}/{k}.c'
src = open(path).read()
body = re.sub(r'^#include.*$', '', src[:src.index('int main')], flags=re.M)
rnd = random.Random(1)
vec = list(range(-50, 151)) + [7919, 7917, 65521, 65537, 999983, -2**31, 2**31 - 1 - 2**31] + [rnd.randrange(-2**31, 10**6) for _ in range(100)]
main = 'int main(){int x;while(scanf("%d",&x)==1)printf("%u\\n",(unsigned)' + k + '(x));}\n'
open(f'{T}/{k}.c', 'w').write("#include <stdio.h>\ntypedef int in_int_t;\n" + body + main)
subprocess.run(['gcc', '-O0', '-fwrapv', '-o', f'{T}/{k}', f'{T}/{k}.c'], check=True)
out = subprocess.run([f'{T}/{k}'], input="\n".join(map(str, vec)), capture_output=True, text=True).stdout.split()
P = cfront.front(path, k)
bad = 0
for v, o in zip(vec, out):
    r, _ = cfront.run(P, [v % (1 << 64)], 10000000)
    if r != int(o): bad += 1; print(k, 'MISMATCH', v, r, o)
print(k, len(vec), 'vectors (', len(out), 'gcc outputs ), mismatches', bad)
