#!/usr/bin/env python3
"""T41 own oracle: parse vectors + expected constants from a tb_fast.v (and optional GOT lines from a sim log),
check each against my own trial-division primality (signed 32-bit n)."""
import re, sys
def isprime(n):
    if n < 2: return 0
    i = 2
    while i * i <= n:
        if n % i == 0: return 0
        i += 1
    return 1
tb = open(sys.argv[1]).read()
vec = {int(i): int(n) for i, n in re.findall(r"// vector (\d+): \{'n': (-?\d+)\}", tb)}
exp = {int(i): int(h, 16) for h, i in re.findall(r"if \(out0_got !== 32'h([0-9a-f]+)\)\s*\n\s*\$fatal\(1, \"vector (\d+):", tb)}
bad = 0
for i in sorted(vec):
    o = isprime(vec[i]); ok = exp.get(i) == o; bad += not ok
    print(f"vec {i:2d} n={vec[i]:6d} oracle={o} tb_expected={exp.get(i)} {'OK' if ok else 'MISMATCH'}")
print(f"{len(vec)} vectors, {len(exp)} expected checks, {bad} mismatches; primes: {sum(isprime(v) for v in vec.values())}")
for log in sys.argv[2:]:
    t = open(log).read()
    lat = re.findall(r"^LAT (\d+) ", t, re.M)
    print(log, "LAT lines:", len(lat), "PASS" if re.search(r"^PASS$", t, re.M) else "no PASS", "| fatal:", re.findall(r".*(?:fatal|FATAL|timeout).*", t)[:2])
    got = {int(i): int(h, 16) for i, h in re.findall(r"^GOT (\d+) ([0-9a-fx]+)$", t, re.M) if 'x' not in h}
    if got:
        mism = [i for i in got if got[i] != isprime(vec[i])]
        print("  GOT lines:", len(got), "values vs own oracle mismatches:", mism, "| GOT:", " ".join(f"{i}:{got[i]}" for i in sorted(got)))
