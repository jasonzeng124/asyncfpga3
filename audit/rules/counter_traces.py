#!/usr/bin/env python3
"""Own per-pin transport-delay simulations (1 ps ticks) for audit claims 3-5.
Model: each LUT output at t = f(pin_k(t - arc_k)); each wire is a transport delay.
Not derived from the formal shard's Lean files; INITs taken from cells/rtl."""
import functools

def wave(events, init):
    """piecewise-constant signal: events = [(t, v)] sorted"""
    def f(t):
        v = init
        for te, ve in events:
            if t >= te: v = ve
        return v
    return f

# ---------------- claim 3: rule I vs the latch (bd_latch odd bit, INIT B8B8: q = en ? d : q_fb)
def latch(Td, Toff, aD=124, aEn=124, aQ=124, w=295, T_end=5000):
    INIT = 0xB8
    d_pin = wave([(Td, 1)], 0)                  # new data arrives at D pin at Td (old 0)
    en_pin = wave([(0, 1), (Toff, 0)], 0)       # enable high from 0, falls at the pin at Toff
    q = {}
    def qout(t):
        if t < 0: return 0
        if t in q: return q[t]
        fb = qout(t - aQ - w)                   # value at I2 pin aQ ago = output (aQ + w) ago
        idx = (fb << 2) | (en_pin(t - aEn) << 1) | d_pin(t - aD)
        q[t] = (INIT >> idx) & 1
        return q[t]
    for t in range(T_end): qout(t)
    final = q[T_end - 1]
    edges = [t for t in range(1, T_end) if q[t] != q[t - 1]]
    return final, edges[:8]

def rule_I_raw(Td, Toff, aD=124, aEn=124, w=295):
    # tighten.py rule I data side: D-pin arrival + max D arc + loop_wire; close side: enable pin + en arc
    return (Toff + aEn) - (Td + aD + w)

print("claim 3: latch, D arc 124, en arc 124, I2 arc 124, loop wire 295 ps")
for Td, Toff in [(1000, 1000 + 295 + 50), (1000, 1000 + 295 + 123), (1000, 1000 + 295 + 124), (1000, 1000 + 295 + 250)]:
    m = rule_I_raw(Td, Toff)
    guard = 200  # req_guard floor
    fin, ed = latch(Td, Toff)
    print(f"  Td={Td} Toff={Toff}: rule I raw margin {m:+d} (guarded {m-guard:+d}); output edges {ed} -> "
          f"{'clean capture' if len(ed) == 1 else 'CORRUPT: a runt circulates in the loop for ever (transport model)'}")

# ---------------- claim 4: rule F vs FASTFALL chain (bd_delay FASTFALL: s1 = a; s_{i+1} = s_i & a)
def ff_chain(N, T_rise, arc=124, hop=600, tap=295, head_w=295, T_end=6000):
    """a falls at t=0 (driver output), rises again at T_rise. hop: wire stage i -> i+1;
    tap: wire a -> each side pin; head_w: wire a -> stage 0."""
    a = wave([(-10000, 1), (0, 0), (T_rise, 1)], 1)
    s = [None] * N
    @functools.lru_cache(None)
    def out(i, t):
        if t < -5000: return 1
        if i == 0: return a(t - arc - head_w)
        return out(i - 1, t - arc - hop) & a(t - arc - tap)
    tail = [out(N - 1, t) for t in range(-100, T_end)]
    rises = [t - 100 for t in range(1, len(tail)) if tail[t] and not tail[t - 1]]
    falls = [max(t for t in range(-100, T_rise) if out(i, t) == 1) + 1 for i in range(N)]  # last fall of each stage before reuse
    return rises, falls

N, arc, hop, tap, head = 3, 124, 600, 295, 295
matched = head + arc + (N - 1) * (hop + arc)   # rise through every link
print(f"\nclaim 4: FASTFALL N={N}, arcs {arc}, chain hop {hop}, side tap {tap}; matched rise latency {matched} ps")
for T in [None]:
    pass
r0, falls = ff_chain(N, 10**6)
t_flush = max(falls)
print(f"  per-stage output fall times {falls}; rule F t_flush = {t_flush}")
for T_rise in [t_flush + 1, t_flush + 200, t_flush + (hop - tap) + 1]:
    rises, _ = ff_chain(N, T_rise)
    first = rises[0] if rises else None
    print(f"  input re-rises at {T_rise} (rule F raw margin {T_rise - t_flush:+d}): tail first rises at "
          f"{first} = input + {first - T_rise if first is not None else None} ps "
          f"({'SKIPS links' if first is not None and first - T_rise < matched else 'matched'})")
