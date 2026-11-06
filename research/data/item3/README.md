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
| s75 (x0.75) | 52 | **8/8 PASS**, EQUIVALENT (seed 9 rerun after the disk-full void) | **16/16 PASS** (s75_corners.tsv) | vec6 1.074 (1.000-1.155), vec12 1.074, vec13 1.074 |

s90: the gate holds, but it buys no measurable speed: a ~2% shorter compute delay is below the +-10% route-to-route
scatter of the laps, and the mean over 8 paired routes is 1.00. Audits (s90_audits.txt, informational under item 1):
rule A 0-2 per route at the old 8.5% guard (raw margins positive), rule E 8 on seed 6, rule J -57 ps guarded on seed 11;
all 8 pass the full stack anyway.

## Kernels (fusion_bench routes, soak_fid full stack, the item-4 flow)

Speed: sum of the 14 vector latencies of each full-stack run, paired by seed against the kernel's item-4 run of its
validated sizes (same NEXTPNR_SEED, same flow); "speedup" = base / step.

| kernel step | sizes moved | routes | SLOW_MAX / FAST_MIN / worst | bits | speedup (corners; worst case) |
|---|---|---|---|---|---|
| xorshift T3 x0.75 | 13 of 47 (0 stays 0) | 1-8 | **8/8, 8/8, 8/8** | 8/8 EQUIVALENT | 8 paired routes: 1.138 / 1.140 (1.10-1.18); 1.132 (1.09-1.19) |
| xorshift T3 x0.5 | 20 of 47 | 1-8 | **8/8, 8/8, 8/8** | 8/8 EQUIVALENT | 8 paired routes: 1.447 / 1.444 (1.37-1.50); 1.418 (1.34-1.47) |
| xorshift T3 operator delays only x0.25 (links at base) | 5 of 47 | 1-4 | **FAIL**: nominal routed GLS 4/4 (protocol error on out0; rule E: ucond_br2/3/5 steers); full stack seed 1: both corners PASS, worst case FAIL (seeds 2-4 not run) | - | - |
| xorshift T3 x0.375 | 20 of 47 | 1-4 | **FAIL**: nominal nextpnr-SDF routed GLS fails 4/4 (protocol error on out0); full stack not run | - | - |
| xorshift T3 x0.25 | 20 of 47 | 1-4 | **FAIL**: SLOW_MAX 4/4, FAST_MIN 2/4 (seed 3 FAIL, seed 4 hung), worst 0/3 (seed 4 not run) | - | - |

T3's own full stack on seeds 5-8 (the baseline for the pairing): 12/12 PASS (seed 8's worst case rerun after the
disk-full window). x0.5 audits (informational): rule A 4-6, rule E 2-10, rule H 0-1 per route; the full stack passes all 12. T3 on seeds 5-8 and x0.25 are
queued. **A step this far below the rules needs a negative control on this flow:** if x0.25 also passes, x0 (every delay
line at its floor) is next, and the gate has to fail somewhere for these passes to mean anything.
A first xorshift s75 run is discarded: shrink_sizes clamped 0 -> 1 then, adding 18 delay lines to T3's handshakes
(it routed slower than T3); fixed in the tool before the rerun above.

x0.25 is the negative control on this flow: seeds 1 and 2 pass BOTH uniform corners and fail only the combined worst
case (protocol error on out0), so it is item 1's slow-cell/fast-chain corner that catches a too-short delay. Seed 3 fails
FAST_MIN too; seed 4's FAST_MIN sims ran 30-47 min with no output (normal: ~10) and were killed, its worst case not run.
The nominal nextpnr-SDF routed GLS already failed seeds 3 and 4 (vector 4 wrong result). x0.375 fails where x0.25 partly passed: uniform scaling with ceil is not monotone (a ratio between two delay lines, not a
length floor). The deepest uniform step that holds for xorshift is x0.5.

Operator-only x0.25 fails too, at a different pair: the comparator delays (ucmpi0 23 -> 6) are themselves select-race
guards -- the compare result is the select of the ucond_br steers, and rule E flags ucond_br2/3/5 on every route. A
uniform factor cannot find per-cell floors that differ this much (umux3's empty-pipe race, the steers' compare race).
Next: per-cell sizing at the worst-case corner (each line shortened to what its own pair allows), not a global factor.

| collatz T3 x0.5 | 24 sizes | 1-4 | **FAIL**: SLOW_MAX 4/4, FAST_MIN 3/4 (seed 2: fast-mode hang on vector 2), worst 3/4 (seed 3) | - | - |

collatz x0.5 fails two different configs on two routes; its seed 2 passes the worst case but hangs at FAST_MIN (the
combined worst case does not subsume the fast corner). collatz x0.75 and operator-only x0.5 are queued.
| ipow T9 x0.5 | 31 sizes | 29-32 | **FAIL**: SLOW_MAX 4/4, FAST_MIN 4/4, worst 2/4 (seed 30: out0 0XX00003, seed 32) | - | - |

ipow x0.5 passes both uniform corners on every route and fails only the combined worst case (2 of 4): the slow-cell /
fast-chain corner of item 1 again the one that catches it. Per-cell candidates (corner_audit, per-cell max over 4
routes) for collatz and ipow are queued; the uniform x0.75 for collatz64 and isprime is running.
| collatz T3 per-cell (corner_audit, per-cell max over 4 routes) | 15 of 42 (249 -> 200 links) | 1-8 | **8/8, 8/8, 8/8** | 8/8 EQUIVALENT | 8 paired routes: 1.157 / 1.153 (1.07-1.27); 1.155 (1.10-1.26) |

collatz per-cell holds on all 12 where uniform x0.5 failed two (FAST_MIN on seed 2, worst case on seed 3). Seeds 5-8 owed
(PROGRAM: 8 routes) before it is a result.
| ipow T9 per-cell (corner_audit, per-cell max over 4 routes) | 23 of 52 (332 -> 251 links) | 29-32 | **4/4, 4/4, 4/4** | 4/4 EQUIVALENT | 1.041 / 1.024 (0.98-1.06); 1.024 (0.97-1.07) |

ipow per-cell holds everywhere (incl. seeds 30 and 32, where x0.5 failed the worst case) but buys only 2-4%: the lines
that set ipow's cycle, uselect0 (52 -> 51) and the multiply umuli1 (47 -> 36), stay near T9 because rule A binds them at
the corner. The rules leave little room on ipow; the sim's floor lies between this and x0.5 (nominal 1.47x, fails).
| xorshift T3 operator delays only x0.5 (links at base) | 5 of 47 | 1-4 | **4/4, 4/4, 4/4** | 4/4 EQUIVALENT | 1.073 / 1.054 (1.02-1.10); 1.053 (1.04-1.07) |

Operator-only x0.5 is safe but buys 5-7%, against 1.44x for uniform x0.5: most of xorshift's cycle is in the LINK request
delays (rdly), which are also where its select races live (umux3's empty pipe). Speed and risk sit in the same lines.
| collatz64 T4 x0.75 | 15 sizes | 1-4 | **4/4, 4/4, 4/4** | 4/4 EQUIVALENT | 1.173 / 1.175 (1.12-1.21); 1.166 (1.11-1.19) |
| isprime x0.75 | 15 sizes | 25 (of 25-28) | **FAIL**: seed 25 FAST_MIN hangs (fast mode, vector 4); rest not run | - | - |

isprime's base sizes (rule-E-6 pads) were never ratcheted, so it had the least slack; per-cell audits on its base routes
are running instead.
| ipow T9 x0.75 | 18 sizes | 29-36 | **8/8, 8/8, 8/8** | 8/8 EQUIVALENT | 8 paired routes: 1.135 / 1.132 (1.05-1.19); 1.129 (1.02-1.19) |

ipow x0.75 (uniform) beats ipow's per-cell sizes (1.02x): the rules at the corner are more conservative than the sim here
too. ipow's floor lies between x0.75 (holds) and x0.5 (fails the worst case on 2 of 4 routes).
| isprime per-cell (corner_audit, per-cell max over 4 routes) | 13 of 15 sized lines (199 -> 147 links) | 25-28 | **4/4, 4/4, 4/4** | 4/4 EQUIVALENT | 1.056 / 1.063 (1.03-1.08); 1.064 (1.05-1.08) |

## Per-kernel summary (deepest step that holds the full stack; speedup paired by seed, worst case)

| kernel | step | routes | speedup, combined worst case | corners |
|---|---|---|---|---|
| xorshift | x0.5 (x0.375, x0.25 fail) | 8 | 1.418x | 1.447 / 1.444 |
| collatz | per-cell (x0.5 fails) | 8 | 1.155x | 1.157 / 1.153 |
| collatz64 | x0.75 | 4 (5-8 running) | 1.166x | 1.173 / 1.175 |
| ipow | x0.75 (x0.5 fails; per-cell 1.02x) | 8 | 1.129x | 1.135 / 1.132 |
| isprime | per-cell (x0.75 fails) | 4 | 1.064x | 1.056 / 1.063 |
| gcd_hw (BQ#2 R5) | x0.75 | 8 | 1.074x laps | 1.057 / 1.043 laps (R5 corner rows exist on 5 / 4 seeds) |

Against BOARD-QUEUE #1/#2 for gcd: R5 x0.75 is 1.07x BQ#2's laps (BQ#2 itself ~1.9x BQ#1's), i.e. ~2.0x BQ#1.
None of these is a board candidate until it has 8 routes on every config; the board list's item 3 stays BQ#3 for now.
