# cdiff_factorial.py -- cfront with CF_PPIF / CF_STRLIT / CF_DEFINE (the reading used by sub4's factorial proof)
# vs gcc -O0 -fwrapv on research/data/suite/dynsrc/factorial/factorial.c. A test, not a proof.
# Vectors: n = -100..300 (declared range: main draws n = rand() % 100 with n > 1), plus extremes with short runs.
import sys, os, re, random, subprocess, tempfile
os.environ.update(CF_PPIF='1', CF_STRLIT='1', CF_DEFINE='1')
T = tempfile.mkdtemp(); os.makedirs(T + '/t')
subprocess.run(['cp', '-r', '/home/user/asyncfpga3/formal/tools/autoproof', T + '/t/'], check=True)
for p in ['/home/user/asyncfpga3/formal/tools-A/rewrite/patches/cfront_define_patch.py',
          '/tmp/claude-0/sub4/patches/cfront_ppif_patch.py', '/tmp/claude-0/sub4/patches/cfront_strlit_patch.py']:
    subprocess.run([sys.executable, p, T + '/t'], check=True)
sys.path.insert(0, T + '/t/autoproof')
import cfront
k = 'factorial'
path = f'/tmp/claude-0/rs/research/data/suite/dynsrc/{k}/{k}.c'
src = open(path).read()
body = re.sub(r'^#include.*$', '', src[:src.index('int main')], flags=re.M)
vec = list(range(-100, 301)) + [-2**31, -2**31 + 1, -1, 1000, 3001, 99999]
main = 'int main(){int x;while(scanf("%d",&x)==1)printf("%u\\n",(unsigned)' + k + '(x));}\n'
open(f'{T}/{k}.c', 'w').write("#include <stdio.h>\ntypedef int in_int_t;\n" + body + main)
subprocess.run(['gcc', '-O0', '-fwrapv', '-o', f'{T}/{k}', f'{T}/{k}.c'], check=True)
out = subprocess.run([f'{T}/{k}'], input="\n".join(map(str, vec)), capture_output=True, text=True).stdout.split()
P = cfront.front(path, k)
bad = 0
for v, o in zip(vec, out):
    r, _ = cfront.run(P, [v % (1 << 32)], 1000000)
    if r != int(o): bad += 1; print(k, 'MISMATCH', v, r, o)
print(k, len(vec), 'vectors (', len(out), 'gcc outputs ), mismatches', bad)
