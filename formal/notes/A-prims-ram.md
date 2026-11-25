# A-prims-ram: digital semantics of RAMB18E1 as bd_mem instantiates it

Probe PrimsRam, shard A. Started 2026-10-29 08:39 UTC. North-star goal 1 ("RAMB18E1 if a
design uses them"). Builds on PrimsSeq (`Formal/Core/Prims/SeqFlop.lean`: `ap`, `winVal`,
`EqOn`, `NoRise`, `lastRise`, `kmux`).

STATUS: done (3 Mathlib-free files, check.sh OK 09:00 UTC, §6). All goals of the probe proved; nothing in Wip except the data script.

## Plan
1. Read bd_mem.v and its users (bdc/mem.py, bdc/emit.py), the prjxray BRAM SDF, the iverilog
   stand-in (cells/sim/bd_prims_sim.v), B's LibEndMemMlink MemPort.
2. `Formal/Core/Prims/Ram.lean`: Kleene word/address algebra (decoder, read, write, three
   write modes), the timed relation `RamRel`, theorems, non-vacuity witness.
3. `Formal/Core/Prims/RamXray.lean`: the prjxray numbers as data (integer ps).
4. `Formal/Core/Prims/RamBd.lean`: the bundled-data obligation of bd_mem, derived.

## 1. What bd_mem instantiates (verified from cells/rtl/bd_mem.v), and who uses it

Expected configuration confirmed: `RAMB18E1 RAM_MODE=TDP`, port A x18 read and write, port B
width 0 and tied off, `DOA_REG=0`, `WRITE_MODE_A=WRITE_FIRST`, `CLKARDCLK = ram_clk` = the
single explicit buffer (`LUT1 2'h2`, or BUFG when `USE_BUFG=1`; bdc emits USE_BUFG=0) after the
`DSETUP` bd_delay of `req`; `ack` = `DCO` bd_delay of the same `ram_clk` net. `ENARDEN=1`,
`REGCE=0`, `RSTRAM/RSTREG=0`, `ADDRARDADDR={addr,4'b0}` (word bits [13:4], 1024 x 16),
`DIADI=wdata`, `DIPADIP=0`, `WEA={we,we}`, `DOADO=rdata`. No INIT_xx / INIT_A: contents 0.
So the clock IS the request edge: synchronous read on CLKARDCLK, latch-mode output.

Users: `bdc/mem.py` (`bdc_memport[_arb]_<AW>_<DW>_<N>` instantiates `ram_count(dw)`
bd_mem's per port, `DW=16` each, one DSETUP/DCO pair per RAM); `bdc/emit.py` `_op_load`,
`_op_store`, `_op_mem_controller` (Dynamatic `handshake.load/store/mem_controller`).
**No kernel in `kernels/` uses memory**: kernels/README.md says they are "memory-free by
construction" (collatz, collatz64, ipow, isprime, xorshift; gcd_hw too). The memory path is
exercised by Dynamatic's own memory kernels (bdc/AUDIT.md names `single_loop`, `fir`, and
Dynamatic's `gcd`, which `slack.py` rejects at a mem_controller cycle) and by testbenches/
board rigs: `cells/tb/tb_bdc_mem.v`, `tb_bdc_memseq.v`, `tb_mem.v`, `cells/hw/mem_port_ps.v`,
`mem_arb_ps.v`, `mem_bist_ps.v` (board PASS recorded in bdc/AUDIT.md and cells/hw/MEM_DCO.md).
So RAMB18E1 is in no design the formal capstone covers; it matters for Stage-6 kernels.

## 2. prjxray-db data (`zynq7/timings/BRAM_L.sdf`, toolchain copy, sha256 71fdc426...5302f)

`BRAM_R.sdf` is identical up to the tile name. Script: `Wip/PrimsRam/bram_xray.py` (prints the
numbers; `--check Formal/Core/Prims/RamXray.lean` reports DRIFT; a mutated 2454 -> 2453 is
reported, and the mutated Lean file fails `bram_slow_wf`). Integer ps.

| arc (cell suffix) | fast | slow |
|---|---|---|
| CLKARDCLKU -> DOADOU, `RAMB18TDP_U_DOA_REG_U_0` (bd_mem: DOA_REG=0) | 585..1098 | 1353..2454 |
| same, `DOA_REG_U_1` (not used) | 204..327 | 468..882 |
| SETUP / HOLD ADDRAU | – | (-360..566) / (-566..360) |
| SETUP / HOLD WEAU | – | (-197..532) / (-532..197) |
| SETUP / HOLD DIADIU, TDP WRITE_MODE WF (= NC) | – | (-667..737) / (-737..667) |
| SETUP / HOLD DIADIU, TDP WRITE_MODE RF | – | (-405..241) / (-241..405) |

Findings from the data itself:
- Corners: IOPATH `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`; TIMINGCHECK one pair, slow only
  (`makesdf.py`), as for the slice flops: **H_WINDOW_SLOW_ONLY**. No rise/fall anywhere.
- Every BRAM check pair has the shape SETUP = (-h, s), HOLD = (-s, h). The widest window is
  `[-SETUP_MAX, HOLD_MAX]` = `[HOLD_MIN, -SETUP_MIN]` either way (`windows_symmetric`): ADDR
  `[e-566, e+360]`, WE `[e-532, e+197]`, DI(WF) `[e-737, e+667]` (aperture 1404 ps).
- The DI window depends on the write mode (RF: `[e-241, e+405]`); bd_mem's WRITE_FIRST has the
  wider one.
- **Coverage gap**: TDP numbers exist only for the UPPER RAMB18 (`..U` pins). There is no
  ADDRAL/WEAL/DIADIL check and no CLKARDCLKL->DOADOL arc in TDP mode (bram_xray.py prints
  ABSENT). A bd_mem placed in RAMB18_Y0 gets the U numbers: **H_BRAM_LU_SAME**, untested.
- No minimum period/pulse width, no collision window: **H_BRAM_PERIOD**.
- The iverilog stand-in `cells/sim/bd_prims_sim.v` RAMB18E1 uses the slow maxima for setup
  (566/737/532) and 2454 for CO, which match; but it has **no hold check**, a single delay
  (`assign #2454`, no [cqLo, cqHi] band, no X), and on a setup violation it only prints and
  counts: it does NOT poison the output, contrary to its header ("prints a violation and
  poisons the output"). So a sim with a violated window still stores/reads the right data.
  (cells/ is frozen; this is for the lead / FOR-RESEARCH.)

## 3. The model (Lean, `Formal/Core/Prims/Ram.lean`)

Generic `aw`, `dw`; bd_mem is `aw = 10`, `dw = 16`. Reuses SeqFlop's `ap`/`winVal`/`EqOn`/
`NoRise`/`lastRise`/`wpt`/`winVal_X_of_ne` and SeqNext's `kmux`.
- Per edge `e`, ADDR bits, WE, DI bits are read over their own windows (`ap`: value if constant
  on the window, else X).
- Decoder `sel a w` = Kleene AND of literals: 1 iff address exactly `w`, 0 iff a DEFINITE bit
  disagrees, else X (**H_BRAM_DECODE_KLEENE**).
- Write `wnext`: bit `j` of word `w` := `kmux (we AND sel w) din_j old`. X only on cube words and
  only where old ≠ new.
- Read `kread`: Kleene merge of the bit over the address cube.
- Read disturb flag `rdis`: if true, a read with an X wordline also merges the cube words with the
  value read. `rdis = false` is **H_BRAM_READ_NONDESTRUCTIVE**. All theorems hold for both
  except `mem_read_keeps_nd` (stated for `rdis = false`).
- Output (`onext`, DOA_REG=0): WF `kmux we din read`; RF `read`; NC `kmux we old read`. Old value
  to `e+cqLo`, `merge old new` on `(e+cqLo, e+cqHi]`, new after. **X choice: X is never resolved**
  (no H_FF_RESOLVE analogue): an X word or X DOADO stays X until a clean access rewrites/rereads
  it. Weaker than silicon, sound.
- Array = hidden state signal `m`, updated right after the edge (H_BRAM_PERIOD).
- INIT/INIT_A at power-up (H_GSR). bd_mem: all zero (`bdInit`, `bdInitA`).

## 4. Results (problem statements)

All in `Formal.Core.Prims.Ram`. "Clean" = the pin constant on its window.

Combinational level:
- `kread_def`, `wnext_self`, `wnext_other`, `wnext_read`, `onext_read`, `onext_rf`,
  `onext_nc_write`: definite inputs give the Boolean RAM.
- `onext_wf_write`: WRITE_FIRST with WE=1 outputs DI, whatever the address (even X).
- `sel_mono`, `kread_mono`, `wnext_mono`, `onext_mono`; `wnext_sound`, `onext_sound`: for EVERY
  Boolean completion of sampled WE/ADDR/DI/array/old output, the Boolean RAM (`bwnext`,
  `bonext`) result is covered by the K3 one (X is sound w.r.t. "the RAM saw some binary value").
- `wnext_outside`: a word outside the address cube never changes (any WE, DI, rdis).

Timed (`RamRel T md rdis init initA ck a we din m dout`; assumed: `T.Ok`, a rising edge `e`,
no edge in `(e, t)`):
- `mem_write`: clean ADDR=v, WE=1, DI=d ⇒ `m t v = d`, other words unchanged.
- `mem_read_keeps` (clean ADDR, WE=0 ⇒ array unchanged); `mem_read_keeps_nd` (rdis=false: WE=0 alone).
- `read_out`: clean read ⇒ DOADO = `m e v` after `cqHi` (any mode).
- `wf_read_during_write`: WF, clean WE=1 and DI=d ⇒ DOADO = d after `cqHi`, **no address
  hypothesis**. `rf_read_during_write`: RF returns the old word. `nc_keeps_out`: NC keeps DOADO
  at all times until the next edge.
- `write_then_read`: clean write at `e1`, clean read of the same address at the next edge `e2` ⇒
  DOADO = data written, after `e2 + cqHi`.
- `power_up`: INIT and INIT_A before the first edge.
- X containment: `x_outside_cube` (any edge, any violation: words outside the sampled address
  cube unchanged), `x_only_addressed` (clean address ⇒ only that word can change, even with WE/DI
  violated), `x_flushed_by_read`, `x_flushed_by_write` (X does not stick in DOADO / the word).
- Not optimistic: `di_violation_X` (DI bit changes in its window, WE=1, ADDR clean ⇒ stored bit X
  and WF DOADO bit X), `we_violation_X` (WE changes in its window, stored bit ≠ data ⇒ X).
- Non-vacuity: `ramSim_rel` / `ramRel_inhabited`: for every input, mode, rdis and timing with
  `cqLo ≤ cqHi`, explicit `simM`/`simO` satisfy every rule.
- NOT covered: port B, parity, cascade, ECC, FIFO, DOA_REG=1, the constant pins, clock
  runts/X/pulse width/minimum period, resolution of disturbed cells, rise/fall, fast windows.

Bundled data (`RamBd.lean`; events at ONE corner: req `r`, ram_clk `b ≥ r + sLo`, CLKARDCLK
`e ∈ [b+wLo, b+wHi]`, ack `k ≥ b + cLo` from the same net, payload at the pins stable on
`[p, q]`, `p ≤ r + dP`, `q ≥ k`):
- `access_ok`: payload stable over all three windows ⇒ after `e+cqHi` (to the next edge) DOADO =
  `wfResult` (data written, or word read) and the array is the Boolean update.
- `bd_access_ok`: **derived obligation**: (setup) `dP ≤ sLo + wLo + lo` for ADDR, WE, DI;
  (hold) `wHi + hi ≤ cLo`; (clock-to-out) `wHi + cqHi < cLo` ⇒ DOADO at `ack` is right, if no
  other CLKARDCLK edge in `(e, k]`. `hold_from_co` + `bram_hold_le_cq`: hold is implied by the CO
  obligation at both prjxray corners (360/197/667 ≤ cqHi).
- `bd_obligation_slow` / `bd_mem_slow`: bd_mem (aw 10, dw 16, WF, INIT 0) at the slow corner
  needs exactly `dP + 737 ≤ sLo + wLo` (DI setup dominates ADDR's 566 and WE's 532) and
  `wHi + 2454 < cLo`. Fast corner: `wHi + 1098 < cLo` with the same (slow-only) windows.
- `co_necessary`: if `cLo ≤ wHi + cqHi`, the admissible placement `e = b+wHi`, `k = b+cLo` makes
  EVERY run read DOADO bit ≠ 1 at ack on the first write of a 1 (INIT_A=0): 0 before the band,
  X in it. So the CO obligation is exact at the band ends (a negative control that fails).
- `setup_necessary`: a DI change at the pin inside the DI window gives X.
- `out_until_next`: DOADO stays valid until the next edge's `cqLo`.
- NOT covered: the delay lines (B's `LibEndMemMlink.MemPort`/Bundling give `sLo`, `cLo`), the
  DOADO→consumer route and consumer window (H_RDATA_ROUTE), the RTZ phase and next access
  (B's `rtz_serialised`, bdc/mem.py's `hold` gate), BUFG insertion (it changes `wLo/wHi`).

Relation to B's `MemPort` (Formal/Cells/LibEndMemMlink.lean): B's `setup_ok` (`tSU ≤ dsLo`),
`hold_ok`, `rdata_before_ack` (`tCO ≤ dcLo`) are the arithmetic halves of `bd_access_ok`, with
abstract datasheet `tSU/tHD/tCO`. Differences: (1) here the numbers are prjxray's and per pin
(tSU = 737 for DI in WF, tCO = 2454 slow); (2) B measures `dcLo` from `tClkR`; here the ack tap is
at `ram_clk` before the BRAM pin route, so the obligation carries the route max `wHi`
(`wHi + cqHi < cLo`); B's `tClkR + tCO ≤ tAckR` matches only if `tClkR` is the ubuf output and the
route is folded into tCO; (3) strict `<` here (at `e+cqHi` itself the model is still in the band).
B could instantiate `tSU := 737, tCO := 2454 + wHi + 1`.

## 5. Census answer: which kernels use bd_mem
None of `kernels/` (all memory-free by construction, kernels/README.md), not gcd_hw. bd_mem is
emitted by `bdc/mem.py` for Dynamatic `load`/`store`/`mem_controller` (Stage 6), exercised by
`cells/tb/tb_bdc_mem*.v`, `tb_mem.v` and the board rigs `cells/hw/mem_port_ps.v`, `mem_arb_ps.v`,
`mem_bist_ps.v`. Candidate memory kernels named in bdc/AUDIT.md: Dynamatic's `single_loop`,
`fir`, `gcd` (currently rejected by `slack.py` at the mem_controller cycle).

## 6. Check

```
formal/check.sh Formal/Core/Prims/SeqNext.lean Formal/Core/Prims/SeqFlop.lean \
  Formal/Core/Prims/SeqLatch.lean Formal/Core/Prims/SeqXray.lean \
  Formal/Core/Prims/Ram.lean Formal/Core/Prims/RamXray.lean Formal/Core/Prims/RamBd.lean
...
[audit] 1018 declarations checked
[check] OK
```
(-DautoImplicit=false; 1018 includes the Seq dependencies; RamXray imports SeqXray for
`XCorner`/`cs`.) Not yet in `Formal.lean`: the lead adds Ram, RamXray, RamBd (after the Seq
modules). Mutation controls: `bram_xray.py --check` on a copy with 2454→2453 reports DRIFT, and
that copy fails to compile (`bram_slow_wf`).

## 7. Next
- Feed `bd_obligation_slow` into C's timing checker as a row per bd_mem (DSETUP path min vs
  payload max + 737; DCO path min from ram_clk vs ram_clk→CLKARDCLK max + 2454), and into B's
  MemPort instantiation.
- Test H_BRAM_LU_SAME (Y0 vs Y1 placement, the DCO sweep of cells/hw/MEM_DCO.md at both sites)
  and H_BRAM_READ_NONDESTRUCTIVE (address-violating reads followed by a BIST).
- Fix the iverilog stand-in's claim (no poisoning, no hold check) via FOR-RESEARCH.
