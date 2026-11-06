# PROGRAM item 4: the other kernels through the full stack

Per kernel, its latest validated sizes, 4 fresh routes (bdc/fusion_bench.py --route: RTL check, audits, nextpnr-SDF
GLS), then per route the FASM assembled to a .bit, the netlist decoded from that .bit (fasm2net), the prjxray SDF, and
cells/gls/fid/soak_fid.py ... bit --gate at SLOW_MAX (max), FAST_MIN (min) and the combined worst case (worst: delay
chains at band 0.21, CARRY4/F7F8/FF at SLOW_MAX, the rest 0.288, + the measured residual as scatter, region 0.02 /
wire 0.126 / draw 1). Oracles: fusion_bench's, derived from the C in kernels/. Queue: scratch k4.sh at 841995d1,
nextpnr 9c732bc6303458df.

results.tsv: one row per route x config; bits_vs_json is cells/gls/fid/fasm_equiv.py on the decoded netlist against
the routed JSON (run after the sims, with the 2026-11-05 constant-LUT fold).

- ipow T9 (BD_DSP=1, research/data/ipow_dsp1_sizes_T9.vh), seeds 29-32: 12/12 PASS, 4/4 EQUIVALENT. tighten.py's
  exit 1 on these routes is rule D's 8 select screens (informational, as in the T9 record); rules E/J 0.
- collatz T3 (BD_DSP=1, research/data/collatz_sizes_T3.vh), seeds 1-4: 12/12 PASS, 4/4 EQUIVALENT. tighten.py exit 1 =
  rule D's 6 select screens; rules E/J 0.
- xorshift T3 (BD_DSP=1, research/data/xorshift_sizes_T3.vh), seeds 1-4: 12/12 PASS, 4/4 EQUIVALENT. tighten.py exit 1
  = rule D's 8 select screens; rules E/J 0.
- collatz64 T4 (BD_DSP=1, research/data/collatz64_sizes_T4.vh), seeds 1-4: 12/12 PASS, 4/4 EQUIVALENT. tighten.py exit
  1 = rule D's 6 select screens; rules E/J 0.
- isprime rule-E-6 pads (BD_DSP=1 BD_RLOC_ARB=1, research/data/isprime_dsp1_rulee6_sizes.vh), seeds 25-28: 12/12 PASS,
  4/4 EQUIVALENT (after e574b300: soak_fid had refused every isprime run before simulating, because its 31 constant
  result bits had "no same-driver net"). Audits: rule D 30 screens, rule E 2 on seeds 25 and 26 (both pass the full
  stack, worst case included), J 0.

**Item 4 done: 60/60** (5 kernels x 4 routes x {SLOW_MAX, FAST_MIN, worst case}), 20/20 routes bits EQUIVALENT.
Not shown: anything below these vectors (fusion_bench's, from the C), or other scatter draws (one per route).

**REVISION (2026-11-06): isprime fails on a fresh route.** The same rule-E-6 pad sizes, fresh seed 30 (route made for item 3's
8-route check): FAST_MIN fast mode hangs on vector 1 (timeout; SLOW_MAX PASS). Seed 29: 3/3 PASS. So isprime's 4-route
12/12 above does not hold in general -- its select pads were never rule-E clean, and the full stack now finds a route where
that matters. isprime needs its pads fixed (rule E on 8+ routes) before it is a validated kernel. Item 4 is 48/48 for the
other four kernels; isprime: 22/24 runs on 8 routes (seeds 25-32), both failures on seed 30 (FAST_MIN and worst case, fast-mode hang).
