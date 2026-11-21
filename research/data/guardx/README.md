# A 10 % guard at the steers: what it costs (2026-11-21)

Why: formal's B24 steer screen calls a route fine only with no pulses at a path error of x <= 0.10 (condition side
+x, request side -x, at research's bands). Flow v10's collatz64 s1 (rule CLEAN, PASS 4 / 4) has pulses at x = 0.08:
its loop-exit steer ucond_br6 sees the request 954 ps after the 64-bit n == 2 compare's output (6572 vs 5618 ps at
band 0.20), +588 ps after the rule's E guard (0.97 x request vs 1.03 x select). The rule and formal's screen agree on
the margin; they differ on how much is enough. CLAUDE.md: 8.5 % is the median ring scatter, not a guardband.

Measured (guardx.sh: the sizing rule on flow v10's s1 route of each kernel as built, rule E / J guard 0.90 / 1.10
instead of 0.97 / 1.03, everything else as the flow; the 0.97 / 1.03 arm reproduces the farm's rule_I.vh exactly):

| kernel s1 (P) | lines that grow | on the critical cycle |
|---|---|---|
| xorshift (16.35 ns) | UCMPI1 9 -> 11, UCMPI0 5 -> 7, ULINK_N12__2 1 -> 2 | UCMPI1 +2 elements (~0.75 ns, ~+5 %) |
| collatz (14.48 ns) | UCMPI2 7 -> 9, UCMPI0 10 -> 12, ULINK_N_INDEX_11 1 -> 2 | UCMPI2 +2 (~+5 %) |
| collatz64 (21.53 ns) | UCMPI2 13 -> 18, UCMPI0 13 -> 16, ULINK_N14__1 2 -> 3 | none on this route's cycle (uaddi0 / umux0 / uselect0) |

So a 10 % steer guard is about two elements on the loop test where it is on the cycle. research/tools/auto/
auto_size.sh AUTO_GUARD_E=0.90,1.10 (opt-in) makes the flow size with it; the first end-to-end test is collatz64 s1
(RUNS /tmp/bot/runs/g10), to be screened by formal's tool when it ships a route.
