#!/usr/bin/env python3
"""Host-side independent replica of the gcd_bench_gen UNIFORM-mode batch,
for step 2 of the measurement task: validate before you measure.

Reproduces, in Python, exactly what build/gen/gcd_bench_gen.v's bridge FSM
does in hardware for BCTRL.mode=0 (UNIFORM):
  - the 32-bit Fibonacci-ish LFSR (gen_bench.py's lfsr_n1/lfsr_n2 expression)
  - gcd's "nonnegative" domain mask (clear bit 31 of each operand word --
    see gen_bench.py's DOMAIN_RESTRICTIONS / apply_domain_masks)
  - kernels' actual gcd algorithm (Stein's binary gcd, from
    dynamatic/integration-test/gcd/gcd.c -- the same algorithm bdc compiled),
    not math.gcd, so this is a genuine independent re-derivation of the
    per-run RESULT, not just a re-derivation of the operand stream
  - the rotate-left-1-then-XOR running signature the FSM accumulates in SIG

Usage:
    python3 host_gcd_replay.py <seed_hex_or_dec> <n_runs>
Prints (one per line, hex where it matters for a direct xsdb diff):
    SIG=0x........
    LASTOP0=0x........
    LASTOP1=0x........
    LASTRESULT=<decimal>
"""
import sys


def advance(x):
    x &= 0xFFFFFFFF
    newbit = ((x >> 31) ^ (x >> 21) ^ (x >> 1) ^ x) & 1
    return ((x << 1) | newbit) & 0xFFFFFFFF


def rotl1(x):
    x &= 0xFFFFFFFF
    return ((x << 1) | (x >> 31)) & 0xFFFFFFFF


def gcd_stein(a, b):
    """Literal transcription of dynamatic/integration-test/gcd/gcd.c's gcd(),
    valid for a, b in [0, 2**31 - 1] (bdc's compiled domain -- see
    gen_bench.py's gcd DOMAIN_RESTRICTIONS comment for why the mask makes
    this safe from the same int32-overflow hang that unrestricted operands
    hit)."""
    if a == 0:
        return b
    if b == 0:
        return a
    k = 0
    while ((a | b) & 1) == 0:
        a >>= 1
        b >>= 1
        k += 1
    while a > 0 and (a & 1) == 0:
        a >>= 1
    while b > 0 and (b & 1) == 0:
        b >>= 1
    while a != 0:
        diff = a - b
        if a < b:
            b = a
        if diff >= 0:
            a = diff
        else:
            a = -diff
        while a > 0 and (a & 1) == 0:
            a >>= 1
    return b << k


def replay(seed, n):
    state = seed if seed != 0 else 1
    sig = 0
    last_op0 = last_op1 = last_result = 0
    for _ in range(n):
        lfsr_n1 = advance(state)
        lfsr_n2 = advance(lfsr_n1)
        op0 = state & 0x7FFFFFFF
        op1 = lfsr_n1 & 0x7FFFFFFF
        result = gcd_stein(op0, op1) & 0xFFFFFFFF
        sig = rotl1(sig) ^ result
        last_op0, last_op1, last_result = op0, op1, result
        state = lfsr_n2
    return sig, last_op0, last_op1, last_result


def main():
    if len(sys.argv) != 3:
        print("usage: host_gcd_replay.py <seed_hex_or_dec> <n_runs>", file=sys.stderr)
        sys.exit(2)
    seed = int(sys.argv[1], 0) & 0xFFFFFFFF
    n = int(sys.argv[2], 0)
    sig, op0, op1, result = replay(seed, n)
    print(f"SEED=0x{seed:08x}")
    print(f"N={n}")
    print(f"SIG=0x{sig:08x}")
    print(f"LASTOP0=0x{op0:08x}")
    print(f"LASTOP1=0x{op1:08x}")
    print(f"LASTRESULT={result}")


if __name__ == "__main__":
    main()
