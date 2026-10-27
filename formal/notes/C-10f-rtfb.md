# C-10f: is the C-element feedback race (RT_FB) real on shipped designs?

Shard C, probe 10f, 2026-10-27. IN PROGRESS (notes kept current as work proceeds).

## Results so far

(1) Muller pipeline, 8 seeds: 4..12 of 64 fail at slowE (mean 7.2), worst -116..-231 ps.
Under PERFECT correlation (every element at one corner end) 5 of 8 seeds still have 1-3
failing stages (seed 3: -112 ps at slow max). Seed 1 (10d's) happens to be a clean one.
Failures: feedback on physical pins 1/2/3 only; pin 6 never carries feedback.

(2) gcd_hw (10e's routes, project flow): seeds 2 and 4: 0/363 C-elements fail in every
one-corner variant; worst slowE +375 / +234 ps, both the RIG's bd_c2n_set uenv1 (a bare
2-cell Muller ring in gcd_rig.v); the kernel's own worst is ~+950..1230 ps; under
H_INDEP 8/363 fail. Seeds d and 3: bitstream being written here (10e's died).

(3) No LUT-pin constraint anywhere (cells/, bdc/, patches/); the nextpnr binary has no
LOCK_PINS string.

Tools: formal/tools/rtfb/{route_muller.sh,muller_rt.sh,rtfb_design.py,gcd_rt.sh,summarize.py}.
