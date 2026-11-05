# PROGRAM item 3: shrink the matched delays to what the sim proves

Base: BQ#2's gcd_hw R5 sizes (research/data/gcd_hw_sizes_R5.vh). Each step is research/tools/shrink_sizes.py
(every size n -> ceil(f*n)) routed on BQ#2's 8 seeds (6,7,8,9,10,11,13,14; pinned NEXTPNR_SEED, same pads and v4
placement), then the full stack: the combined worst case first (the gate: matched-delay chains at 0.21,
CARRY4/F7F8/FF at SLOW_MAX, the rest 0.288, + the measured residual as scatter), then SLOW_MAX and FAST_MIN.
A step that fails is reverted. nextpnr 9c732bc6303458df. Speed: laps in the fixed window on vectors 6/12/13 of the
worst-case run, paired by seed against BQ#2's own worst-case rows (research/data/fid/bq2_worstcase.tsv).

| step | sizes moved | worst case | corners | laps vs R5 (paired mean, range) |
|---|---|---|---|---|
| s90 (x0.9) | 19 (compute/select delays >= 10 links, -1..-2 links) | **8/8 PASS**, EQUIVALENT | queued | vec6 0.999 (0.891-1.086), vec12 1.000, vec13 0.996 |
| s75 (x0.75) | 52 | running | | |

s90: the gate holds, but it buys no measurable speed: a ~2% shorter compute delay is below the +-10% route-to-route
scatter of the laps, and the mean over 8 paired routes is 1.00. Audits (s90_audits.txt, informational under item 1):
rule A 0-2 per route at the old 8.5% guard (raw margins positive), rule E 8 on seed 6, rule J -57 ps guarded on seed 11;
all 8 pass the full stack anyway.
