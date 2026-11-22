# if_loop_1 seed 1 on the automatic path: the host's fill misses the RAM's WE setup (subagent `ifloop`, 2026-11-18)

Farm suite9 task 77 shipped route `su_if_loop_1_1_7` (SDF b2ad5a7b, P 27.52 ns, EQUIVALENT, ffmux-clean), NOT CLEAN
(9 sized rows short after the finish phase), and 2 of its 4 draws failed with `MEMORY wrong in batch(es) 0-7`, cycles
0: draws 10101 and 10104.  Everything routed here: nextpnr `6e5d224472232d5d` (`cells/verify/toolchain.sh`: every
patch fingerprint ok), seed 1, `--freq 83` (build_bench.sh), BDC_AUTO=1, on a node at load 40+ on 16 cores.  One
kernel, one placer seed: nothing here is a 4-seed claim (out/ifloopguard.sh is the farm request that would make one).

## 1. Reproduced

- **The route.** `lane2.sh` (LANE_NORUN=1, BDC_AUTO=1) from the farm loop's own `sizes_final.vh` (= `sizes_7.vh`),
  seed 1, at this branch's 3b2de0f95 (the farm's loop ran at eaef0dec): SDF **b2ad5a7b** (the farm's), FASM identical
  to memauto's earlier rebuild of the same route, bitstream identical but for the header's date.
- **Draw 10101** (`bench_gate.sh ... draw:10101`, GATE_MEMEXP from `oracle_mem.sh`, i.e. from the C) on call 0 of
  `research/data/suite/vec/if_loop_1.hex` alone (n = 100, expected 25f68469): **FAIL 0/1, MEMORY wrong in batch 0**.
  Its BENCHRES line is the farm's batch-0 line field for field (cycles 484, latmin 237, sig/odata x, t=24859024).
  Read back: every word's **high 16 bits are right and its low 16 bits are x** (`ffe9xxxx, fffaxxxx, ...`).
- The run log has **100 `RAMB18 SETUP VIOLATION ... c_000008 ... WE (input moved 515 ps before the edge, needs 532 ps)`**,
  one per host write, every 156 ns from 1.03 us, and nothing else: c_000008 is `umem_controller1_uport.umem0.uram`
  (RAMB18_X0Y22), the low half of the 32-bit word, whose setup line `BD_SZ_..._UMEM0_USETUP` is **2** elements.  The
  GLS RAM model (cells/gls/prims.v) poisons the word an edge with a setup violation writes, so the host's whole fill of
  the low half is x, the kernel reads x (odata x) and the read-back is wrong in every call.

## 2. The race (waveform of the first host write, draw 10101)

The host slot is one more one-hot slot on the plain `bdc_memport` (bdc/mem.py): `m_req = |s_req`,
`m_we = (s_req[0] & s_we[0]) | (s_req[1] & s_we[1])`, the RAM clock is `m_req -> usetup (DSETUP) -> ubuf -> CLKARDCLK`.
The bench's sequencer sets we / data one aclk before it raises `mem_hreq` (gen_bench.py), but the port's mux gates
WE / ADDR / DI with the request itself, so **the host's request launches both sides of the RAM's setup check**:

| t after `bridge_i.mem_hreq` rises (flop at SLICE_X8Y99) | clock side | payload side |
|---|---|---|
| +753 | `m_req` (LUT at X18Y97) | |
| +1356 / +1858 | the 2 usetup elements (X20Y99) | |
| +2245 | `ram_clk` (ubuf, X20Y99) | |
| +2403 | | `m_we` (LUT at **X8Y50**, beside the RAMs: a 49-row wire from the request flop) |
| +2949 .. +3051 | | WEA0..3 at RAMB18_X0Y22 |
| **+3566** | CLKARDCLK (a 1321 ps wire from X20Y99 down to the BRAM) | |

WE arrives 3566 - 3051 = **515 ps** before the edge; the model's TSU_WE (prjxray BRAM_L, as tighten.py's T_SU) is 532.
DI and ADDR on the same RAM had 886 / 844 ps (need 737 / 566); the high half's RAM (umem1, USETUP 5) had 1270 ps on WE.
The matched delay is umem0's DSETUP; the path it bundles is the host request through the port's one-hot WE LUT.

`research/tools/ramrace/` recomputes this from the delays the simulation baked (gen.py's `netlist_baked.v`) and matches
it to the picosecond (ram_race_all.py: clock and every payload pin from each request; race_path.py: arc by arc).  WE
margin = CLK - WE - 532 on route 7, per draw:

| draw | chains / rest / carry | the draw (scatter as drawn) | same band point, no scatter | verdict |
|---|---|---|---|---|
| 10101 | 0.230 / 0.287 / 0.526 | **-17** | +125 | FAIL |
| 10104 | 0.206 / 0.269 / 0.484 | **-61** | +95 | FAIL |
| 10102 | 0.247 / 0.234 / 0.375 | +243 | +159 | PASS |
| 10103 | 0.208 / 0.223 / 0.710 | +282 | +106 | PASS |

**What separates the passing draws is their within-die scatter, not the chain / rest ratio**: without scatter every
band point has +95..+159 ps (10103, which passed, has less than 10101, which failed); the draws' scatter moved the
margin by -142, -156, +84, +176 ps.  The two paths share nothing after the request flop and each is dominated by one
long wire (2.3 ns to the WE LUT; 1.4 ns from the setup line to the BRAM column): in 10101 the clock wire alone drew
1456 -> 1321 ps.  race_mc.py (the draws' model as gen.py applies it: per pip 1 + 0.126 N, a wire the mean of its pips,
per 10x10 region 1 + 0.02 N, per LUT arc 1 + 0.126 N; 20000 samples) puts the sd of this margin at **~112 ps**:
P(WE margin < 0) = 0.16 at 10101's band point, **0.28 at the rule's 0.31 corner** (+79 ps).  Over the draws' own
band distribution (the no-scatter margin is linear in the bands: +101 + 1388 (chains - 0.2) - 200 (rest - 0.2) ps,
which reproduces all four points above within 2 ps) that is **P(fail) ~ 0.10 per draw** for this route; 2 failures
in 4 draws is a 6 % event under it.

## 3. Did the rule see it?  It measured it and passed it

`tighten.py` rule B pairs exactly this race (same RAM, same pin, common source the PS clock): `umem0.uram: latest
payload WEA0, margin +101 ps (corner 0.20) / +79 ps (0.31)`, ok.  Rule B's guard is the vendor's T_SU + SLACK (0) and
nothing else -- rule A has its residual guard max(3 % t, 50 ps), rule E its 0.97 / 1.03 -- so a race whose scatter sd
is ~110 ps passed at under one sd.  The 9 sized rows the loop left short at it 7 (neg_7.txt; the rule run here, report
only, gives the farm's ca_7 rows line for line) are all kernel rows: H on ulink_n_trueResult_8 / _6 / _0, E on umux0
(launch ulink_n16__0), A'm on umux2.  **The race that failed was not among them.**  The line that fixes it is
**`BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM0_USETUP`** (2).

## 4. The rule's own raise, and the routes built with it

`BD_RAM_GUARD_PS=N` (new, opt-in, cells/verify/tighten.py; unset, tighten's output is byte-identical, checked with
PYTHONHASHSEED=1) adds N ps to rule B's window.  One step of the loop with it (the subagent's
out/scripts/rule_step.sh: corner_audit CA_SIZERULE=1 at both corners as auto_size.sh runs it, CA_FAST=1,
merge_rules.py, ratchet.py --raise-only --headroom 1) on route 7 with N = 350: B on umem0 **-249 / -271 ps** ("PAD
2->4"), and the step's output is **the farm's own sizes_8.vh line for line** (UMUX2 4->6, ULINK_N16__0 1->4,
TRUERESULT_0 / _6 / _8 UACK 1->3 / 3 / 5: the farm's ratchet_7) **plus `UMEM0_USETUP 2 -> 5`**.  Without the guard the
step adds nothing for the RAM.

Routes (seed 1, BDC_AUTO=1):

| route | sizes | SDF | host race at 0.31 (worst pin, unguarded) | draws |
|---|---|---|---|---|
| route 7 (shipped) | sizes_7 | b2ad5a7b | umem0 WE **+79** (sd 113, P<0 0.28) | 2 / 4 (farm) |
| u3 | sizes_7 + USETUP_0 3 | c030af6f | umem0 DI +374, WE +681 (P<0 ~0) | 10101, 10104 stopped after 3 batches: no RAMB18 violation, but **x in batch 0** (below) |
| 8u3 | sizes_8 + USETUP_0 3 | 1c5db738 | - | 10101, 10104 stopped after 2 batches: both right, SIG clean, no RAMB18 event (replaced by the next row) |
| **8g** | **sizes_8 + USETUP_0 5 (the guarded rule's step)** | **3386e563** | umem0 >= +1073; **umem1 WE +238** (sd 132, P<0 0.05) | **8 / 8 PASS 8/8** (10101-10108, the new gate), 0 RAMB18 events, every SIG clean |

**u3 shows why a NOT CLEAN route's short rows matter.**  With only the RAM line raised, the re-placed route's own rule
(report only) has E on umux0 (uj0, launch ulink_n16__0) at -152 / -210 ps, I / H on ulink_n_trueResult_0, C on
umem1.uco -162 / -292.  In both draws the first kernel access of the first call put **x on the RAM clock**
(`RAMB18 CLOCK ... went 0 -> x`, 400 / 200 lines, every access of run 0 of batch 0): the windowed dump traces it to
`umux0.j0`, which saw `ctl_req` (n16__0_req) 133 ps before the select (`n16__0_data`, a link latch no token had written
yet, x since power-up) -- rule E's race -- and passed x through `either -> udly -> n10__0_req -> umem_controller1_s0_req
-> m_req -> usetup -> ram_clk`.  Run 0 returned x, run 1 the right value, and **bench_gate.sh said PASS 3/3** on those
batches: the repeatability latch compares with `!=` (never true against an x reference) and odata is the last run's.
Only SIG (the fold of every run) showed x.  This is the start-up pattern subagent hangs found on ipow seed 4
(research/data/suite/hangs.md, SIM-VS-BOARD row 6): silicon has no x, and the start-up x is the visible symptom of a
real select race (later runs see a stale select, not x); the rule had flagged it.  +META_INIT=0/1 was not run here.

**8g: the two draws that failed and the two that passed on route 7, and 4 more (10105-10108: chains / rest
0.305 / 0.226, 0.231 / 0.243, 0.295 / 0.214, 0.228 / 0.289), all PASS 8/8**, every array read back right, no RAMB18
event, no x in any SIG.  Latency of an n = 100 call (latmin, 12 ns cycles) on 10101-10104: 237 / 240 / 228 / 233,
route 7's farm draws 237 / 241 / 226 / 233: the longer setup line is not on the loop's cycle.

**8g is NOT CLEAN either.**  The guarded rule (report only) on it: umem0 fixed (+726 / +723 with the guard), but the
re-placement moved the thin race to **umem1** (USETUP 5 unchanged: B -7 / -112 with the guard, i.e. +343 / +238
unguarded) and opened **A on uselect0 at -491 / -720**; the loop's next step (rule_step.sh on 8g) raises
UMEM1_USETUP 5 -> 7 and USELECT0 5 -> 11 (2 lines, against route 7's 6).  Built (seed 1, SDF 27e43d42), that
route's guarded rule has every B and kernel row clean and ONE short row: C on umem1.uco, -228 / -342 ps (unguarded:
rule C is the read side; it was short on u3 too).  No draws on it.  Each re-placement moves the small
margins; the loop's answer (phase 2: raise and re-route until the rule is clean) is the only one that converges, and a
guard is what makes "clean" cover the draws' scatter.

## 5. Host path or kernel?  How it should be sized

The race is the **port's host slot**: bdc/mem.py's plain port with the bench's request flop.  WE toggles only on host
writes (a load station drives `p_we = 0`), and the slot is on every memory of every kernel the bench builds
(`--host-mem`), so every memory kernel has this race on every RAM.  It is thin or not by placement: on route 7 the OR
and the setup line were placed beside the bench's request flop (top of the die) and the mux LUTs beside the RAMs, so
the payload's wire is long and the clock's short; the kernel's own slot on the same RAMs (a load: only ADDR toggles)
had +1681 / +2369 ps at 0.31 (its request starts near the RAMs).  The same structure serves a kernel's store slot
(its own request gates WE / DI), so a kernel that writes has the race on its own slot too.

How to size it: **rule B is the right row** (it already pairs the race from the common source); it lacks a guard for
the scatter.  **`BD_RAM_GUARD_PS=400`** = 3 x the largest sd the draws' scatter gives the worst race of any route
in section 6 (67-132 ps on those 17 races; a race behind a long setup line scatters more, 170-225 ps, but those had
> 4.5 ns).  The runs here used 350 (the first estimate); on route 7, 400 gives the same step, checked: B -299 / -321 ps,
"PAD 2->4" (the row measured as depending on UMEM0_USETUP), + the finish phase's headroom = 5, the same sizes file.  The exact version would be
k x the race's own sd from its pips (race_mc.py does it per route; tighten.py sees no pips).
Rule C (the read side: DCO line vs the RAM's DO) has the same two-long-wires shape and no guard either; not measured.

## 6. Measured

### Other memory routes (farm suite9's shipped routes, rebuilt here from their own sizes and seed; SDF = the farm's)

`research/tools/ramrace/route_check.sh` on each: every RAM x every request x pin class at the rule's two corners
(chains 0.20, the rest 0.20 / 0.31, CARRY4 / F7F8 / FF / RAMB18 1.0, no scatter), the worst over the corners, and the
draws' scatter sd at 0.31.  Host = the bench's fill / read-back slot; kernel = the load stations (ADDR only).

| route | SDF | RAMs | host request: worst margin (RAM, pin, request, corner) | sd at 0.31 | P(<0) per draw at 0.31 | kernel loads: worst ADDR | draws (farm suite9) |
|---|---|---|---|---|---|---|---|
| if_loop_1 s1 (route 7) | b2ad5a7b | 2 | **+79** (RAMB18_X0Y22 WE, mem_hreq, 0.31) | 113 | 0.282 | +1561 (RAMB18_X0Y22) | **2 / 4** |
| gather s1 | 33b77519 | 4 | **+1787** (RAMB18_X1Y26 ADDR, mem_hreq[1], 0.31) | 104 | 0.000 | +1494 (RAMB18_X1Y26) | 4 / 4 |
| gather s2 | 86c9d605 | 4 | **+234** (RAMB18_X1Y29 DI, mem_hreq[1], 0.31) | 92 | 0.011 | +792 (RAMB18_X1Y29) | 4 / 4 |
| gather s3 | 4e41e339 | 4 | **+661** (RAMB18_X1Y32 DI, mem_hreq[1], 0.31) | 115 | 0.000 | +785 (RAMB18_X1Y32) | 4 / 4 |
| gather s4 | 4902271a | 4 | **+1446** (RAMB18_X1Y22 DI, mem_hreq[1], 0.20) | 112 | 0.000 | +2721 (RAMB18_X1Y22) | 4 / 4 |
| dot2 s1 | cd975c99 | 4 | **+1622** (RAMB18_X1Y24 ADDR, mem_hreq[1], 0.31) | 112 | 0.000 | +1783 (RAMB18_X1Y24) | 4 / 4 |
| dot2 s2 | 4d68e57e | 4 | **+1154** (RAMB18_X1Y14 DI, mem_hreq[1], 0.31) | 113 | 0.000 | +2170 (RAMB18_X1Y14) | 4 / 4 |
| dot2 s4 | 9ff7f65b | 4 | **+367** (RAMB18_X1Y17 DI, mem_hreq[1], 0.31) | 111 | 0.001 | +1477 (RAMB18_X1Y17) | 4 / 4 |
| memsum s2 | 38436143 | 2 | **+2339** (RAMB18_X0Y16 ADDR, mem_hreq, 0.20) | 114 | 0.000 | +2491 (RAMB18_X0Y16) | 4 / 4 |
| memsum s4 | d8d78d23 | 2 | **+1160** (RAMB18_X0Y24 DI, mem_hreq, 0.20) | 94 | 0.000 | +1019 (RAMB18_X0Y24) | 4 / 4 |
| if_loop_2 s1 | ae0edcb6 | 2 | **+2003** (RAMB18_X1Y23 WE, mem_hreq, 0.20) | 125 | 0.000 | +2726 (RAMB18_X1Y23) | 4 / 4 |
| test_bitint s1 | cf69bd3e | 2 | **+551** (RAMB18_X1Y19 DI, mem_hreq[0], 0.20) | 67 | 0.000 | +955 (RAMB18_X1Y18) | 4 / 4 |
| test_bitint s2 | 3696e956 | 2 | **+992** (RAMB18_X1Y16 DI, mem_hreq[1], 0.20) | 89 | 0.000 | +1359 (RAMB18_X1Y16) | 4 / 4 |
| test_bitint s3 | fc7854a3 | 2 | **+572** (RAMB18_X1Y23 DI, mem_hreq[0], 0.20) | 96 | 0.000 | +1043 (RAMB18_X1Y23) | 4 / 4 |
| test_bitint s4 | b0c5f05a | 2 | **+1320** (RAMB18_X1Y25 DI, mem_hreq[0], 0.20) | 89 | 0.000 | +1471 (RAMB18_X1Y25) | 4 / 4 |
| if_loop_1 s1, 8g (here) | 3386e563 | 2 | **+238** (RAMB18_X1Y30 WE, mem_hreq, 0.31) | 132 | 0.051 | +1551 (RAMB18_X1Y30) | 8 / 8 (here) |
| if_loop_1 s1, u3 (here) | c030af6f | 2 | **+374** (RAMB18_X1Y17 DI, mem_hreq, 0.31) | 112 | 0.000 | +2084 (RAMB18_X1Y17) | - |

Every farm route rebuilt here came out with the farm's SDF (11 of 11 rebuilt: memsum s2 / s4, dot2 s1 / s4, gather s3 /
s4, if_loop_2 s1, test_bitint s1-s4; gather s1 / s2 and dot2 s2 were memauto's rebuilds, also the farm's).  The sd column
is the draws' scatter on the worst (RAM, pin) at the 0.31 corner (race_mc.py, 4000 samples); P(<0) is per draw AT that
corner (the draws' band points sit inside the corners).  Only if_loop_1 seed 1 was thin enough to fail; gather s2 (DI
+234, P 0.011) and dot2 s4 (DI +367, P 0.001) are the next two, and a 400 ps guard would pad both.  A load slot's
margin is never the thin one here (its request is launched near the RAMs).

### Files

- `cells/verify/tighten.py`: `BD_RAM_GUARD_PS` (opt-in; unset, output identical).
- `research/tools/eventgraph/bench_gate.sh`: a batch whose SIG has x / z is not a pass; any `RAMB18 ` line (a setup /
  hold violation, or a RAM clock that went x) fails the run.  On a clean run the verdict line is unchanged (route 7's
  worst-band full stack: PASS 8/8, the same line); on u3's draw 10101 (batches 0-2) the old code says PASS 3/3, the new
  FAIL 0/3 `| X in a run's result (SIG) in batch(es) 0 | RAMB18 timing events 400`.  No published farm draw
  (5249 benchres files on claude/cluster) had an x SIG with a right odata.  The farm keeps no run.log, so whether a
  passing farm draw ever printed a RAMB18 line is not known; on this node the 5 run logs that did had all failed.
- `research/tools/ramrace/`: `decode_bake.sh` (the .bit decoded, gen.py at one point of the delay model, no
  simulation), `ram_race_all.py` (each RAM's clock vs its payload from every request, on the baked delays),
  `race_path.py` (one race arc by arc, per draw), `race_mc.py` (the draws' scatter, Monte Carlo), `route_check.sh`.

### Open

- The flow change itself: auto_size.sh with `BD_RAM_GUARD_PS=400` on the memory kernels, 4 seeds
  (out/ifloopguard.sh, a farm request, not filed).
- Rule C (DCO vs the RAM's DO, the read side) has no guard either; on u3 it was negative even unguarded (-162 / -292).
- A per-race guard from the race's own scatter (its pips) instead of a fixed 400 ps.
- u3's start-up x under +META_INIT=0/1 (what the stale-select race does after start-up on that route).
