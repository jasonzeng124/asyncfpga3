# gcd_bench_gen on the full stack (bits-decoded netlist + prjxray SDF + GLS_MODEL=fid)

The bench harness (`cells/hw/gen_bench.py`) simulated with its routed delays for the first time, driven by
`cells/gls/ps/ps7_bench.v` (the AXI3 master of the gcd_ps GLS running `hw/xsdb_bench_gen.tcl`'s run_batch; it reads
the bench's own illegal-transition sticky, 0x58, after every batch) and watched by `cells/gls/ps/gen_bench_mon.py`
(kernel handshake at driver pins, FSM state sampled 3 ns after each aclk rise, `BILL` = a transition gen_bench.py's
`st_legal` forbids).

Builds (scratch worktrees; `cells/hw/build_bench.sh gcd` with BQ#4's flags:
`BDC_SELECT_PADS=hw/gcd_hw_pads.json BD_RLOC=v4 BD_SIZES=research/data/gcd_ps/gcd_ps_sizes_P1.vh NEXTPNR_SEED=3`,
nextpnr 9c732bc6303458df, toolchain.sh all ok):

| tag | harness | bit md5 | audits (audit_route.sh) |
|---|---|---|---|
| nh3 | today's (2-flop synchronisers), histogram compiled out (`nohist.sh`) | 464c573f | A/E/F/H/I/J 0, D 38 |
| au3 | the same with the synchroniser reverted (`nohist.sh` then `august.sh`: cdc_bench.sh's "august" sed) | 53b40d67 | A/E/F/H/I/J 0, D 38 |

`nohist.sh` ties the latency histogram's write data to 0 so yosys drops its 1024 flops: with them BD_RLOC=v4 does not
place (nextpnr's RLOC repair strands the uori2/uori4 columns, then asserts, seeds 3 and 4), and v2 would not be BQ#4's
kernel (rule A -144 ps once, rule E 5-11 elements short on ucond_br10-18). The histogram only observes.

Gate (gate.vvp): ANNOTATE_DONE, 0 SDF warnings, on both; fasm_equiv: EQUIVALENT on both.

## nh3: RTZ tail (logs nh3_{max,min}_{fixed16,uni32}.log)
| corner | batch | SIG (oracle) | latmin-max | cycles/run | tail (cycles/run - latmin) | per run: S_ACK+S_RTZ+S_NEXT | kernel RTZ |
|---|---|---|---|---|---|---|---|
| SLOW_MAX | FIXED gcd(48,18) x16 | 00020002 (fold of 6, derived) | 170-171 | 176.06 | 6.06 | 5 | 12.7 ns |
| FAST_MIN | FIXED gcd(48,18) x16 | 00020002 | 63-63 | 68.0 | 5.0 | 4 | 4.6 ns |
| SLOW_MAX | UNIFORM seed 1 x32 | b2d15eed (= hw/uniform_oracle.py gcd 1 32) | 96-1297 | - | - | 5 (every run) | 12.7 ns |
| FAST_MIN | UNIFORM seed 1 x32 | b2d15eed | 36-462 | - | - | 4 (every run) | 4.6 ns |

0 illegal transitions in all four. The tail is the null floor (5.0 on the board for all four nulls); the board's gcd
tail (README 22.992 exact / rtz_cost_results.tsv 12.142, both d741ae57, August build not archived) is not reproduced.

## au3: phase sweep (au3_max_sweep.log)
SLOW_MAX, 2-run FIXED gcd(48,18) batches, FCLK0 period 10000 + 2*batch ps (the PS7 model changes it between
batches). i_ack arrives ~36 cycles after issue, so each 2 ps step moves its phase by ~72 ps. The testbench's 5 ms
cap stopped the run after batch 127 (FCLK0 10254 ps).
- Batches 0-4, 18 and 23-127: normal (latency 172 -> 168 cycles as the period grows, SIG 0000000a = derived, sticky 0).
- Batches 5-22 except 18 (FCLK0 10010-10044 ps): 13 batches with the bench's own illegal-transition sticky set, 011 -> 001
  (S_WAIT_ACK -> S_PREP) in 12, 011 -> 000 in batch 19, which HANGS (completed 0/2). The other four (6, 17, 21, 22)
  complete out of protocol: runs captured 2-27 cycles after issue (a stale o_req from the run before). The monitor
  saw 17 BILL. 001 and 000 are bitwise mixes of 011 and the intended 100, the mechanism gen_bench.py's comment
  describes; the board's code was 110 (another mix: which bit is late is route-dependent).
- SIG stayed 0000000a in the completing batches only because FIXED repeats one operand pair.
