# A data-dependent delay for the loop counter: design notes (2026-11-14, nothing built yet)

PROGRAM (owner, 2026-11-14): after the full-range re-baseline, win the time back with a delay chosen from the operands
(speculative completion). Read first: Nowick, "Design of a low-latency asynchronous adder using speculative completion",
IEE Proc. Computers and Digital Techniques, 1996
(https://www.cs.columbia.edu/~nowick/nowick-iee-pcgs-speculative-competion-96-published.pdf); van Berkel, Josephs and
Nowick, "Applications of asynchronous circuits", Proc. IEEE 1999
(https://www.cs.columbia.edu/~nowick/async-applications-PIEEE-99-berkel-josephs-nowick-published.pdf). The scheme keeps
single-rail bundled data and adds matched delays: a worst-case one and one or more short "speculative" ones; an abort
detection network on the operands decides, per operation, whether the short completion must be cancelled in favour of
the long one.

## The incrementer i + 1 (uaddi0)

- The abort condition is NOT just "the low k bits of i are all ones". The adder's inputs change from i_old to
  i_new = i_old + 1, so its carry chain also has to DISCHARGE the old carries: after i_old = 0x0FFF -> i_new = 0x1000 the
  sum changes in bit 0 only, but c_1..c_12 fall from 1 to 0 and bits 1..12 can glitch until they have. The settle is
  long when the previous increment carried far OR the current one will. Both are visible in i_new alone:
  long previous carry <=> the low k bits of i_new are all 0; long next carry <=> they are all 1. Abort = low k bits all 0
  or all 1: one LUT for k <= 5, probability 2 / 2^k per iteration (k = 4: 1 in 8).
- The abort LUT reads the latched i, which is stable before the request arrives (it is the adder's own input), so the
  short/long choice is a mux on the request path ahead of two chains, in the cell, and the only new race is the mux's
  select against the request -- the same rule-E shape as a steer, statically checkable.
- Static check for both cases: the short chain must cover every path whose carry stays inside bits 0..k (a case
  analysis: paths through c_j, j > k, are false when abort = 0). corner_audit / tighten have no case analysis; the
  check needs either a false-path list (carry-chain arcs above bit k) or a separate SDF in which those arcs are cut.

## The compare i + 1 < rounds (ucmpi1)

- A carry (borrow) chain compare does not get a short case from the same condition: a change in the low bits ripples
  up through every position where the two operands are equal (all high bits are 0 for small rounds), so the compare's
  settle is long almost every iteration. Speculative completion does not help it directly.
- What would: inside the loop the invariant i + 1 <= rounds holds (the body is entered only when i < rounds, and i + 1
  cannot overflow since i < rounds <= INT_MAX), so i + 1 < rounds <=> i + 1 != rounds. Inequality is a LUT tree (3
  levels for 32 bits), no ripple, with a short static worst case. That is an operator rewrite that relies on a loop
  invariant, close to the loop lowering the owner said to keep; NOT done without the owner's word. Asked in the
  journal (2026-11-14).

## Cost estimate (xorshift, full range)

On the full-range rebuild uaddi0 is 13 elements (~4.5 ns on the cycle). With k = 4: short chain ~ the 4-bit carry +
routing, roughly the x0.5 size (6, ~2 ns), so the average period gains ~2 ns x 7/8. A rare long iteration still costs
the full 13. The compare stays at its full static length unless the != rewrite is allowed.

## Plan for the cell (2026-11-14, not started)

- Opt-in bdc knob BDC_SPEC_INC=<inst>:<k>:<Nshort> on an `addi x, 1` unit: the unit gets two delay lines from the same
  `either` (Nshort and the full N), and a LUT on the request path `z_req = abort ? long : short` with
  `abort = (x[k-1:0] == 0) | (x[k-1:0] == all ones)` read from the unit's own input data (stable before `joined`,
  bundled by the upstream request). Falling: both lines are FASTFALL and the mux follows the selected one; the input
  data, hence `abort`, is held until the acknowledge falls.
- New cell under CLAUDE.md's rule: written as a variant in bdc's generated compute module (not in cells/rtl), with a
  routed-GLS check.
- The static check needs case analysis that corner_audit does not have: for the short case, cut the CARRY4 arcs above
  bit k (they cannot toggle when abort = 0) and re-run rule A' / E against the short line; for the long case, the
  existing check against the long line. Both cases at nominal and worst. That tool is the first thing to build.
- Expected on xorshift full range: the 13-element line paid 1 in 8 iterations (k = 4), a ~6-element line otherwise:
  about -2 ns mean per iteration.
