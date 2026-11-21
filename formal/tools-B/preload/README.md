# tools-B/preload: reach the paths no vector can reach, and see which delays set the period (shard B, UNTRUSTED simulation)

All tools work on a decode directory made by shard C's `formal/tools/margin/run.sh` (bench mode: `KV= BV= SYNTH= ROUTED=`,
`DRAWS=N` for the ordinary draws), which holds `net.json`, `bnd.json`, `routed.json`, `simx`, `net.simx`, `gclass.txt`.
run.sh decodes with RC_TREE=1 (research's arcs) since 2026-11-17 22:30. Results: formal/FOR-RESEARCH.md B2-B4.

## Preloaded loop state (FOR-RESEARCH B2)
A loop counter starts from a constant that reaches the loop header through an entry link (xorshift `ulink_n6` = i0,
collatz / collatz64 `ulink_n7` = steps0). `preload_net.py` makes that link's latch state nodes hold I0 from t = 0 (checked
constant 0 in an ordinary run's dump first), i.e. the same bitstream with the entry constant tied to I0; `oracle.c` is the
kernel's C loop (copied verbatim) started from the same state. One command:

    KERNEL=xorshift prun.sh DECODE_DIR OUT 0x3ffffff0 ulink_n6 "0x92d68ca2,0x40000001 ..." NDRAWS SEED0 [JOBS]
    KERNEL=collatz  prun.sh DECODE_DIR OUT 0x3ffffff0 ulink_n7 "0x10000,0 ..." NDRAWS SEED0

(`DRAW_XBAND=0.8,1.0` for slow-carry draws; `TMAX` ps, default 4e8; `DRAWS_EXTRA="--inject I.json"` for a negative control.)
`constlinks.py NET ROUTED DUMP` lists the links whose latches never move in a run: the candidates (check in the kernel
Verilog that the link feeds a loop header mux's entry input). Vectors whose answers need the full input range (collatz 32 /
64-bit, outside the bench's masks) are in `vec/`.

## Is the long path exercised, and how much time does it have?
- `inject_carry.py NET SLICE PS OUT.json`: +PS on the carry-in of one CARRY4 (outside the band: a negative control). The
  preload must fail with it where ordinary vectors pass (xorshift: +20 ns into bit 16 of uaddi0).
- `carryslack.sh DECODE OUT KERNEL I0|- LINK|- "PAIRS" CELLREGEX SEED0 N [HI]`: bisects that injection to 50 ps: the
  largest extra delay every one of N draws survives (a consequence slack: an upper bound of the settle margin). For a
  counter, put the carry in the LAST increment (collatz: n = 0x10000 with steps0 = 0x3ffffff0), or a late carry is
  absorbed before it is read.

## Which delays set the period (FOR-RESEARCH B4)
- `period.py NET ROUTED DUMP CELLREGEX`: median per-iteration time from a dump (rises of the header's request OR).
- `linesens.py SIMX NET.simx NET.json ROUTED OUT --cell 'udut\.umux0\.uor$' -- SIMX_ARGS`: +500 ps on each delay line's first
  LUT, one at a time; dP/dX 1 = on the period-setting cycle, 0 = not (18 s a route).
- `zeroline.py NET ROUTED OUT 'REGEX'`: scale named lines to 0 on the same placement (what the line costs there, apart from
  re-placement). Not a buildable circuit.
- `joinscan.py KERNEL_bench.v SIZES.vh`: joins fed by two sized operators (static, sizes only: candidates, not results).
