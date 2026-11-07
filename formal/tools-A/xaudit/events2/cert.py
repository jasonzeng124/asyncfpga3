#!/usr/bin/env python3
"""Untrusted certificate finder for Events2Time (E3). Prints cycle ratios and the
potentials that `Events2Time.Beh.rate_upper` / `rate_lower` need; the Lean side
re-checks every inequality with `decide` (a wrong certificate fails to check, it
cannot produce a wrong theorem).

Input: JSON {"N": n, "arcs": [[j, p, src, off, lo, hi], ...]} where arc (j,p) is
pin p of stage j reading stage src; lo = loF j + loG j p, hi = hiF j + hiG j p.
Usage: cert.py NET.json
"""
import json, sys
from fractions import Fraction

def cycles(N, arcs):
    # simple cycles of the counter graph (edge src -> j), smallest node first
    out = []
    def go(s, cur, seen, path):
        for a in arcs:
            j, p, src, off, lo, hi = a
            if src != cur:
                continue
            if j == s:
                out.append(path + [a])
            elif j > s and j not in seen:
                go(s, j, seen | {j}, path + [a])
    for s in range(N):
        go(s, s, {s}, [])
    return out

def main(path):
    net = json.load(open(path))
    N, arcs = net["N"], [tuple(a) for a in net["arcs"]]
    cs = cycles(N, arcs)
    dead = [c for c in cs if sum(a[3] for a in c) == 0]
    live = [c for c in cs if sum(a[3] for a in c) > 0]
    print(f"{len(cs)} simple cycles, {len(dead)} token-free")
    hi_c = max(live, key=lambda c: Fraction(sum(a[5] for a in c), sum(a[3] for a in c)))
    lo_c = max(live, key=lambda c: Fraction(sum(a[4] for a in c), sum(a[3] for a in c)))
    H, k = sum(a[5] for a in hi_c), sum(a[3] for a in hi_c)
    L, kl = sum(a[4] for a in lo_c), sum(a[3] for a in lo_c)
    g = lambda a, b: __import__("math").gcd(a, b)
    T, K = H // g(H, k), k // g(H, k)
    T2, K2 = L // g(L, kl), kl // g(L, kl)
    print(f"max cycle ratio (hi): {H}/{k} steps per token (cycle {[(a[0], a[1]) for a in hi_c]})")
    print(f"max cycle ratio (lo; rate upper bound): {L}/{kl} steps per token (cycle {[(a[0], a[1]) for a in lo_c]})")
    # lower certificate: pi(src) + K hi <= pi(j) + T off on every arc (longest paths)
    pi = [0] * N
    for _ in range(N + 1):
        for (j, p, src, off, lo, hi) in arcs:
            pi[j] = max(pi[j], pi[src] + K * hi - T * off)
    m = min(pi); pi = [x - m for x in pi]
    assert all(pi[src] + K * hi <= pi[j] + T * off for (j, p, src, off, lo, hi) in arcs)
    # upper certificate: sigma = tree towards the min-ratio cycle
    sigma, rho = {}, {}
    for a in lo_c:
        sigma[a[0]] = a
    # potentials around the cycle: rho(j) >= rho(src) + T2 off - K2 lo
    cyc = lo_c
    rho[cyc[0][2]] = 0
    for a in cyc:
        j, p, src, off, lo, hi = a
        rho.setdefault(j, rho[src] + T2 * off - K2 * lo)
    changed = True
    while changed:
        changed = False
        for a in arcs:
            j, p, src, off, lo, hi = a
            if j not in sigma and src in rho:
                sigma[j] = a; rho[j] = rho[src] + T2 * off - K2 * lo; changed = True
    if len(sigma) < N:
        print("upper certificate: some stage reaches no critical cycle (not strongly connected)")
    else:
        m = min(rho.values()); rho = {j: r - m for j, r in rho.items()}
        for j, a in sigma.items():
            assert rho[a[2]] + T2 * a[3] <= rho[j] + K2 * a[4], (j, a)
    print(json.dumps({"lower": {"T": T, "K": K, "pi": pi},
                      "upper": {"T'": T2, "K'": K2, "sigma": [sigma[j][1] for j in range(N)] if len(sigma) == N else None,
                                "rho": [rho.get(j) for j in range(N)]}}))

if __name__ == "__main__":
    main(sys.argv[1])
