import random, sys
random.seed(20261119)
I = lambda: random.randint(-2**31, 2**31-1)
E = [0, 1, -1, 2, -2, 2**31-1, -2**31, 2**30, 0x7ffffffe, -2**31+1]
V = {}
V['xorshift'] = [(a, b) for a in E for b in (0, 1, -1, -2**31, 3)] + [(I(), random.randint(-3, 40)) for _ in range(60)]
V['ipow'] = [(a, b) for a in E for b in E] + [(I(), I()) for _ in range(60)]
V['collatz'] = [(n,) for n in [1, 2, 3, 6, 7, 27, 97, 871, 2**30, 2**31-1, 0x7ffffffe]] + [(random.randint(1, 10**6),) for _ in range(40)]
V['countloop'] = [(a, b) for a in E for b in (0, 1, -1, -2**31, 2**31-1 if False else 5)] + [(I(), random.randint(-5, 60)) for _ in range(40)]
V['isprime'] = [(n,) for n in [0, 1, 2, 3, 4, -1, -2**31, 2**31-1, 97, 91, 7919, 65521, 65537]] + [(random.randint(-100, 20000),) for _ in range(40)]
V['sqrtsub'] = [(n,) for n in [0, 1, -1, -2**31, 2, 3, 4, 1000, 9999]] + [(random.randint(-100, 20000),) for _ in range(30)]
for k, vs in V.items():
    open(f'vec_{k}.txt', 'w').write(''.join(' '.join(map(str, v)) + '\n' for v in vs))
