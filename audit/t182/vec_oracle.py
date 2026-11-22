#!/usr/bin/env python3
"""T182 own vectors + oracle for test_flatten_array (research/data/suite/dynsrc/test_flatten_array/test_flatten_array.c):
output[a][b][c] = input[a][B-b-1][C-c-1], A=4 B=8 C=16, flat index a*128+b*16+c; input unchanged.
  gen OUT          v2 bench vector file (words=0 mems=2: input[512], output[512] per call), 3 calls
  check VEC LOG    parse BENCHMEM batch=j mem=m lines (+MEMDUMP=1) and compare both arrays with the C's final contents"""
import random, re, sys
A, B, C = 4, 8, 16; N = A * B * C
def kernel(inp, out):
    out = list(out)
    for a in range(A):
        for b in range(B):
            for c in range(C):
                out[a*B*C + b*C + c] = inp[a*B*C + (B-b-1)*C + (C-c-1)]
    return list(inp), out
def calls():
    r = random.Random(18246)
    c0 = ([r.randrange(1 << 32) for _ in range(N)], [0xDEADBEEF] * N)              # full-range words, sentinel output
    c1 = ([(i * 0x9E3779B1) & 0xFFFFFFFF for i in range(N)], [r.randrange(1 << 32) for _ in range(N)])
    x = [r.randrange(1 << 32) for _ in range(N)]
    c2 = (x, kernel(x, [0] * N)[1][::-1])                                           # output prefilled with a near-miss
    return [c0, c1, c2]
def gen(path):
    with open(path, 'w') as f:
        f.write('// benchvec words=0 mems=2\n// T182 own vectors (audit), 3 calls, seed 18246\n')
        for k, (i, o) in enumerate(calls()):
            for name, arr in (('input', i), ('output', o)):
                f.write(f'// call {k} {name}\n')
                for j in range(0, N, 8):
                    f.write(' '.join(f'{w:08x}' for w in arr[j:j+8]) + '\n')
def check(vec, log):
    cs = calls(); got = {}
    for line in open(log, errors='replace'):
        m = re.match(r'BENCHMEM batch=(\d+) mem=(\d+) n=(\d+) data=(\S+)', line)
        if m: got[(int(m[1]), int(m[2]))] = [int(w, 16) for w in m[4].split(',')]
    ok = 0
    for k, (i, o) in enumerate(cs):
        ei, eo = kernel(i, o)
        gi, go = got.get((k, 0)), got.get((k, 1))
        if gi is None or go is None: print(f'call {k}: NO DUMP'); continue
        bi = sum(x != y for x, y in zip(gi, ei)); bo = sum(x != y for x, y in zip(go, eo))
        print(f'call {k}: input bad {bi}/{N}, output bad {bo}/{N}'); ok += (bi == 0 and bo == 0 and len(go) == N)
    print(f'agreement {ok}/{len(cs)}')
if __name__ == '__main__':
    if sys.argv[1] == 'gen': gen(sys.argv[2])
    else: check(sys.argv[2], sys.argv[3])
