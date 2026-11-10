# T60 row 6: for each mismatching vector of the 100 MHz SLOW_MAX run, find which op0 bits must be flipped (same rounds)
# for my own xorshift model to give the simulated result. If every mismatch is explained by a corrupted op0 (seed)
# with the kernel itself correct, the failure is in the operand path, as research says (op0_to_core[28]).
import sys, re
def xs(x, r):
    for _ in range(r):
        x ^= (x << 13) & 0xffffffff; x ^= x >> 17; x ^= (x << 5) & 0xffffffff
    return x
for l in open(sys.argv[1]):
    m = re.search(r"op0=(\w+) op1=(\w+) .* odata=(\w+)", l)
    if not m or 'BENCHRES' not in l: continue
    a, r, got = int(m[1], 16), int(m[2], 16) & 0xfff, int(m[3], 16)
    if xs(a, r) == got: continue
    sols = [b for b in range(32) if xs(a ^ (1 << b), r) == got]
    sols2 = [(b, c) for b in range(32) for c in range(b+1, 32) if not sols and xs(a ^ (1 << b) ^ (1 << c), r) == got]
    print(f"op0={a:08x} rounds={r} got={got:08x} expected={xs(a,r):08x} single-bit op0 flips explaining it: {sols} two-bit: {sols2[:3]}")
