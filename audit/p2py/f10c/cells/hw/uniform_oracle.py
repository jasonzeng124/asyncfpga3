#!/usr/bin/env python3
"""Derive the expected SIG of a UNIFORM-mode batch.

The FIXED batch has had an oracle since hw/golden_sig.txt existed.  The UNIFORM
batch -- 2000 runs, every one a different input, the largest test in the suite
-- has never had one: it checked that the bench did not hang and nothing else.
It does not need to be that way.  UNIFORM is not random, it is an LFSR with a
host-supplied seed, and every step of it is in gen_bench.py:

    lfsr_n1 = {lfsr[30:0],    lfsr[31]^lfsr[21]^lfsr[1]^lfsr[0]}
    lfsr_n2 = {lfsr_n1[30:0], lfsr_n1[31]^lfsr_n1[21]^lfsr_n1[1]^lfsr_n1[0]}
    bench_op0 <= mask0(lfsr)      bench_op1 <= mask1(lfsr_n1)      lfsr <= lfsr_n2

so the whole input sequence is reproducible from the seed, the kernel is a
function, and SIG is a fold over the results with no timing in it.  Replaying
all three in python gives a value the board must match.

The masks are DOMAIN_RESTRICTIONS from gen_bench.py, and they are reproduced
here rather than imported because getting them wrong in the same direction in
both places is exactly the failure an oracle exists to catch.  The kernels are
transcribed from kernels/<k>/<k>.c (gcd from build/frontend/gcd/comp/gcd.c),
INCLUDING their int32 wrap-around, because the hardware has it too: isprime's
`d*d <= n` overflows for d > 46340 and the circuit does not stop to complain.

  hw/uniform_oracle.py <kernel> [seed_hex] [n_runs]
"""
import sys

M32 = 0xFFFFFFFF
M64 = 0xFFFFFFFFFFFFFFFF


def s32(x):
    x &= M32
    return x - (1 << 32) if x >> 31 else x


def s64(x):
    x &= M64
    return x - (1 << 64) if x >> 63 else x


def lfsr_next(s):
    fb = ((s >> 31) ^ (s >> 21) ^ (s >> 1) ^ s) & 1
    return ((s << 1) & M32) | fb


# --- kernels, transcribed from the C ---------------------------------------

def k_gcd(a, b):
    a, b = s32(a), s32(b)
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
        diff = s32(a - b)
        if a < b:
            b = a
        a = diff if diff >= 0 else s32(-diff)
        while a > 0 and (a & 1) == 0:
            a >>= 1
    return s32(b << k)


def k_collatz(n):
    n = s32(n)
    steps = 0
    while n != 1:
        n = n >> 1 if (n & 1) == 0 else s32(3 * n + 1)
        steps += 1
    return steps


def k_collatz64(n):
    n = s64(n)
    steps = 0
    while n != 1:
        n = n >> 1 if (n & 1) == 0 else s64(3 * n + 1)
        steps += 1
    return steps


def k_xorshift(seed, rounds):
    x = seed & M32
    for _ in range(s32(rounds)):
        x = (x ^ (x << 13)) & M32
        x ^= x >> 17
        x = (x ^ (x << 5)) & M32
    return s32(x)


def k_ipow(b, e):
    b, e, r = s32(b), s32(e), 1
    while e > 0:
        if e & 1:
            r = s32(r * b)
        b = s32(b * b)
        e >>= 1
    return r


def k_isprime(n):
    n = s32(n)
    if n < 2:
        return 0
    d = 2
    while s32(d * d) <= n:
        r, s, half = n, d, n >> 1
        while s <= half:
            s = s32(s << 1)
        while s >= d:
            if r >= s:
                r = s32(r - s)
            s >>= 1
        if r == 0:
            return 0
        d += 1
    return 1


# --- how each kernel's operand words are drawn -----------------------------
# (words, mask function taking the two raw LFSR states, kernel callable)

def _collatz_mask(w0, w1):
    v = w0 & 0x0000FFFF
    return (1 if v == 0 else v), w1


def _collatz64_mask(w0, w1):
    # n is 64 bits: word0 = low, word1 = high, high masked to zero.  The
    # zero->1 rule fires only when the WHOLE value is zero.
    return (1 if w0 == 0 else w0), 0


KERNELS = {
    "gcd":       (lambda w0, w1: (w0 & 0x7FFFFFFF, w1 & 0x7FFFFFFF),
                  lambda a, b: k_gcd(a, b)),
    "ipow":      (lambda w0, w1: (w0, w1), lambda a, b: k_ipow(a, b)),
    "xorshift":  (lambda w0, w1: (w0, w1 & 0x00000FFF),
                  lambda a, b: k_xorshift(a, b)),
    "collatz":   (_collatz_mask,   lambda a, b: k_collatz(a)),
    "collatz64": (_collatz64_mask, lambda a, b: k_collatz64((b << 32) | a)),
    "isprime":   (lambda w0, w1: (w0, w1), lambda a, b: k_isprime(a)),
}


# The null DUT is not opaque either: gen_bench.py's is_null branch assigns
# out0_data to the XOR of the ARGUMENT words, after the same domain masks.
# WORDS is how many of (op0, op1) are actually arguments -- collatz and isprime
# take one 32-bit argument, so op1 is drawn and masked but never read.
WORDS = {"gcd": 2, "ipow": 2, "xorshift": 2, "collatz": 1, "collatz64": 2,
         "isprime": 1}
for _k, _n in list(WORDS.items()):
    KERNELS[_k + "_null"] = (
        KERNELS[_k][0],
        (lambda n: (lambda a, b: a if n == 1 else a ^ b))(_n))


def uniform_sig(kernel, seed, n_runs):
    mask, fn = KERNELS[kernel]
    lfsr = seed & M32
    if lfsr == 0:
        lfsr = 1
    sig = 0
    for _ in range(n_runs):
        n1 = lfsr_next(lfsr)
        n2 = lfsr_next(n1)
        op0, op1 = mask(lfsr, n1)
        v = fn(op0, op1) & M32
        sig = (((sig << 1) & M32) | (sig >> 31)) ^ v
        lfsr = n2
    return sig


if __name__ == "__main__":
    k = sys.argv[1]
    seed = int(sys.argv[2], 0) if len(sys.argv) > 2 else 0xACE12345
    n = int(sys.argv[3]) if len(sys.argv) > 3 else 2000
    print("0x%08x" % uniform_sig(k, seed, n))
