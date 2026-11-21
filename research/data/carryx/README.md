# What a carry-tracking delay line could buy: an upper bound from the rule (2026-11-21, NEGATIVE)

Lead (JOURNAL 2026-11-1x "a carry-chain delay that tracks the adder"; never tried): a matched delay line whose elements
are CARRY4 stages would track the data path's carry chain over the CARRY4 band, so the rule would no longer size it for
data at the band's slow end (CARRY4 / F7F8 / FF at 1) against LUT elements at 0.20.

Bound, before building anything: the sizing rule (auto_size.sh's rule(): corner_audit CA_SIZERULE=1 at bands 0.20 and
0.31, chains at 0.20, merged by merge_rules.py, with flow v10's environment incl. CA_BENCHCAP=1) on flow v10's shipped
route of each kernel, seed 1, as built (the untrimmed routed JSON of the byte-identical rebuild, board_rebuild.sh),
three arms (carryx.sh):
- A: as the flow (CARRY4=1, SELMUX2_1=1, SLICE_FFX=1) -- **reproduces the farm's rule_I.vh exactly** on both kernels
  (the control);
- B: CARRY4 at 0.20 (an IDEAL carry replica: zero mismatch, the most it could buy);
- C (collatz only): CARRY4 and F7/F8 at 0.20.

| kernel s1 (P) | lines that change A -> B (of all sized) | on the critical cycle |
|---|---|---|
| xorshift (16.35 ns) | UCMPI1 9 -> 8, UCMPI0 5 -> 4, UADDIRD0D 8 -> 6 (3 of 70) | UCMPI1: one element, ~0.4 ns (~2 %) |
| collatz (14.48 ns) | UADDI0 3 -> 2, UADDI1 3 -> 1 (2 of 72); C adds UCMPI0 10 -> 9 | none (its loop test ucmpi2, an F7/F8 equality tree, does not move even in C) |

So the CARRY4 band's pessimism sizes at most one element on these loops' cycles: the cycle's matched delays are set by
the LUT / wire content of their data paths, which the LUT elements already track (same band). A carry replica cell
(a cells/rtl change, rule support, GLS evidence) would buy <= ~2 % on xorshift and nothing on collatz. Not pursued.
It may still matter for robustness to the CARRY4 band's true position (BOARD-QUEUE item 36): if the board puts that
band low, nothing here changes; the rule already assumes its slow end.
