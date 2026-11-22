# Item 46: the latch-fed steer race on silicon (2026-11-22)

Two routes of the same kernel and seed, test_flatten_array s2 (a memory kernel), judged by the same vectors and rules:
- unpadded/ -- flow v11's own route (farm suite13t_s5a_v11_2b/22, su_test_flatten_array_2_10, sdf e82284b6, no trims;
  trimmed fasm 77d4a54c): rule CLEAN, PASS 4 / 4. Formal B36: its steer ucond_br14 reads a condition from
  ulink_n101_folink's latch with a split slack of +1 / +72 ps (fast / slow corner), and formal's race-only adversary
  gets a wrong answer at kappa 0.03; our draw model rates the same race 263 +- 56 ps (z 4.72).
- padded/ -- the same kernel and seed under flow v11 + AUTO_RACE_KAPPA=0.13 (local, /tmp/bot/scripts/rk_launch.sh): at
  it 10 (v11's route) the check found kappa 0.000 and padded ULINK_N101_FOLINK 1 -> 4; the late phase shipped it 11
  (rk11_test_flatten_array_2_11, BD_SYMTRIM, sdf 2361eec8, 110 recorded trims, trimmed fasm 5fcd82f8 = the bits its
  draws judged): rule CLEAN, PASS 4 / 4, weakest latch-fed race kappa 0.241; call latency 31.9 vs 28.6 us.
Each spec rebuilds byte for byte with research/tools/suite/board_rebuild.sh (checked 2026-11-22 00:15). The padded
spec carries TRIM_STAGEFIX=1 and BD_DEFINES=-DBD_SYMTRIM in ENV: board_rebuild.sh now hands ENV to its trim step and
refuses a rebuild where any recorded trim is refused (before that fix this route came out with 10 multi-stage
request lines untrimmed -- fasm 594e53a1, bits never judged).
