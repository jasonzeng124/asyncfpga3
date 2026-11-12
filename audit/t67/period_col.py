# T87: collatz period per step from two BENCHRES lines (n=27: 111 steps, n=6171: 261 steps): P = d(latmin) * fclk / d(steps)
import re, sys
def steps(n):
    s = 0
    while n != 1: n = n // 2 if n % 2 == 0 else 3 * n + 1; s += 1
    return s
r = [m for m in (re.search(r'fclk_ps=(\d+) .*op0=([0-9a-f]+) .*completed=(\d+) .*latmin=(\d+) .*odata=([0-9a-f]+) .*(DONE|HANG)', l) for l in open(sys.argv[1])) if m]
ok = all(int(m[5], 16) == steps(int(m[2], 16)) and m[6] == 'DONE' for m in r)
a, b = r[0], r[1]; sa, sb = steps(int(a[2], 16)), steps(int(b[2], 16))
P = (int(b[4]) - int(a[4])) * int(a[1]) / (sb - sa)
print(f"{sys.argv[1]}: oracle {'OK' if ok else 'MISMATCH'}; steps {sa}/{sb} latmin {a[4]}/{b[4]}; period {P/1000:.3f} ns (+-{int(a[1])/(sb-sa)/1000:.3f})")
