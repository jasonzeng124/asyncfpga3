# C-10f: is the C-element feedback race (RT_FB) real on shipped designs?

Shard C, probe 10f, 2026-10-27. IN PROGRESS (notes kept current as work proceeds).

## Status so far

(1) Muller pipeline, 8 placer seeds (1..8), nextpnr 9c732bc6303458df, toolchain.sh ok,
fasm_audit PASS on every seed, seed 1 FASM read back from the bits is byte-identical to
10d's fixture. Python evidence (10d's unchanged rt_all.py on 11b's unchanged fasm2lean
read-back), `formal/tools/rtfb/build/muller/summary.txt`:

| variant | failing stages mean [range] of 64 | worst slack ps mean [range] |
|---|---|---|
| indep | 40.9 [37..43] | -641 [-726..-594] |
| fast  | 11.9 [7..16] | -133 [-188..-117] |
| slow  | 10.2 [6..15] | -218 [-325..-184] |
| fastE | 7.2 [4..12] | -67 [-94..-47] |
| slowE | 7.2 [4..12] | -154 [-231..-116] |
| sdf   | 0.1 [0..1] | +96 [-7..+206] |

Every slowE failure (58 over 8 seeds) has its feedback on physical pin 1, 2 or 3; none on
4 or 5; pin 6 is never used for feedback.

Next: Lean summaries per seed; shipped gcd_hw (C-10e's 4 routes, project flow).
