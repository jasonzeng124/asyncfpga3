#!/usr/bin/env python3
"""Loop trip counts / operand summary per vector (independent Python model of the C's control flow), to judge
whether the vectors exercise the loops; also prints n for array kernels."""
def s32(x): x &= 0xffffffff; return x - (1 << 32) if x >> 31 else x
def flat(k): return [[int(t, 16) for t in l.split()[2:]] for l in open(f'/root/agentA/out/{k}.flat')]
def fact(n):
    t1 = t2 = 0
    while n >= 3: n -= 3; t1 += 1
    while n > 0: n -= 1; t2 += 1
    return (t1, t2)
def idiv(a, b):
    if b == 0: return 'div0'
    a, b = abs(a), abs(b); return a // b
def isqrt(n):
    lo, hi, t = 0, n, 0
    while lo <= hi:
        t += 1; mid = (lo + hi) >> 1
        if mid * mid == n: return (t, 'exact')
        if mid * mid < n: lo = mid + 1
        else: hi = mid - 1
    return (t, 'noexact')
print('factorial trips (loop1,loop2):', [fact(s32(w[0])) for w in flat('factorial')])
print('iterative_division trips:', [idiv(s32(w[0]), s32(w[1])) for w in flat('iterative_division')])
print('iterative_sqrt trips:', [isqrt(s32(w[0])) for w in flat('iterative_sqrt')])
for k in ['if_loop_1', 'if_loop_2', 'dot2', 'gather', 'memsum', 'unused_arg']:
    print(k, 'n / b:', [s32(w[0]) for w in flat(k)])
tl = flat('test_loop_free')
print('test_loop_free branch:', [('a>0' if s32(w[0]) > 0 else 'b<0' if s32(w[1]) < 0 else 'else') for w in tl])
f = flat('fir'); print('fir:', [s32(sum(w[1000 + i] * w[999 - i] for i in range(1000))) for w in f], 'fwd call1:', sum(i*i for i in range(1000)))
