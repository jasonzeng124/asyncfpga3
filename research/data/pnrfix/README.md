> STOPPED EARLY on the coordinator's request (2026-11-17 ~19:15): every run listed below finished; the fipowh4 s26 patched-route decode did not.

# pnrfix: the constant site pins nextpnr leaves unrouted (the NOT EQUIVALENT / FFMUX-gap routes)

Subagent `pnrfix`, 2026-11-17, cluster node.  Every nextpnr used here was built in `/tmp/bot/sa/pnrfix/` from
`openXC7/nextpnr-xilinx` at `bfdeaf7c` + `patches/` in `cloud/setup-toolchain.sh`'s order; nothing under `$TC` was
touched.  Installing the patch is the bot's / owner's decision.

## 1. Verdict per kind

| kind (as fasm_equiv / ffmux_scan print it) | real on the die? | cause | fixed by |
|---|---|---|---|
| `DRIVER DIFFERS SLICE_X?Y?/F7BMUX/0 json ('bel', ../D6LUT, O6) bits ('const', 0)` + `HARMLESS .../D/A1 json 0 bits 1` (au_collatz_1_0; the farm's "benign F7BMUX input 0" kind) | **no: a false alarm** of fasm_equiv | the unrouted-GND mechanism below, on a LUT pin, where it is harmless by construction | `fasm_equiv.py` (clone commit `e8e1c9923`), not nextpnr |
| `DRIVER DIFFERS SLICE_X19Y65/F7AMUX/S0 json ('const', 0) bits ('const', 1)` (ipow x0.55 route 19, sdf d63bfd80; fipowh4 seeds 28 and 26) | **yes**: the F7 passes its other LUT; bits-decoded GLS **FAIL 11/17** (route 19) | `Arch::routeVcc()` gives up on the select's GND sink after 50 000 BFS wires and nothing routes it afterwards | `nextpnr-xilinx-const-sinks.patch` |
| flop with ZINI/ZRST but no xFFMUX bit (ffmux_scan) = `cell in routed JSON, not configured by the bits (HAS LOADS)` (fipowh4 seeds 6, 26, 29: CFF; collatz64 T4 seed 4 of 2026-11-08: C5FF) | **yes, in the bits**: D comes out of an FFMUX with no bit set, which selects none of its inputs.  What that does to an answer depends on the flop: fipowh4 6's decoded GLS still passes 17/17 (§5); the C5FF's loads are undriven (X) | the same: the D=GND sink of a yosys dfflegalize FDPE/FDCE is a routeVcc holdout | the same patch |

All three are one mechanism.  The journal's "a constant site pin left unrouted so the die reads its default instead"
is right; what was missing is why the pin is unrouted, and why only some pins matter.

## 2. The mechanism (nextpnr-xilinx bfdeaf7c + patches/, `xilinx/arch.cc`)

`Arch::route()` runs `routeClock()`, then router2 -- which skips `$PACKER_GND_NET` / `$PACKER_VCC_NET` entirely
("Hybrid GND/VCC strategy", `common/router2.cc`) -- then **`routeVcc()` as a post-router fill**, then
`fixupRouting()`.  `routeVcc()` routes each constant sink by an uphill BFS through *free* wires that stops at a wire
already on the constant net or at a pseudo-constant wire, **bounded at `iter_max = 50000` wires**.  A sink whose BFS
hits the bound is a *holdout*: it is counted in `N/M sinks bridged (K left to main router; max BFS 50000)`, listed
only with `NEXTPNR_LOG_CONST_HOLDOUTS=1` -- and then never routed.  "left to main router" is stale: the main router
has already run, and the router1 pass that routes const arcs runs only with `NPNR_ROUTER1_RECHECK`.

Why GND and not VCC: every INT IMUX / BYP_ALT / FAN_ALT has a **default** ppip from VCC_WIRE (prjxray
`ppips_int_l.db`: `INT_L.IMUX_L0.VCC_WIRE default`, `INT_L.BYP_ALT0.VCC_WIRE default`; 64 per INT tile), so VCC always
routes (782/782, 834/834, 914/914 sinks in the runs below) and an *unrouted* IMUX/BYP reads **1**.  GND enters an
INT tile only through GFAN0/GFAN1 (`GFANn.GND_WIRE`, real pips) and from there IMUX / BYP_ALT / FAN_ALT and the bounce
wires, or from an empty X0-SLICEL's A-LUT output (the chipdb's `CONST_DRIVER` pip; an unconfigured LUT is INIT 0) over
general wires.  Near a tile whose GFANs carry signals (au_collatz_1_0: `INT_L_X2Y42.GFAN0/GFAN1.WW4END1`,
`INT_R_X5Y63.GFAN0/GFAN1.NR1END1`) the BFS spends its 50 000 wires on general interconnect and quits.  It is not
blocked: for every real holdout in §7 (7, in 6 routes) an unbounded search through free wires finds a path.

What a holdout does on the die depends on the pin:
* **plain LUT input** (A1..A6 of a LUT1..6): `fixupRouting()` drops the `X_ORIG_PORT` of a pin no permutation pip
  reached (in a tile where any permutation pip is used; LUT inputs are entered only through permutation pips), so
  `fasm.cc get_lut_init()` evaluates the INIT with that logical input at 0 = GND.  The die's pin reads 1, the INIT does
  not read it.  **Harmless** (kind 1).  In a tile with no used permutation pip the mapping would stay and the INIT
  would read the 1: never seen (0 of 19 364 GND LUT pins in 19 routes, coarse scan), but the patch routes such a pin
  rather than trust it.
* **F7/F8 select** (S0 = the AX/BX/CX bypass pin) on GND: reads 1, the mux passes its other input.  **Wrong.**
* **flop D** on GND: the D input comes out of xFFMUX / x5FFMUX; its site pip is part of the route, so an unrouted D
  gets no FFMUX feature, and every FFMUX encoding in segbits has a 1 bit (e.g. `CLBLM_R.SLICEL_X1.CFFMUX.CX
  !30_35 30_36 !30_37 !30_38`): all-zero selects nothing.  **Wrong** (what the die then latches is not knowable from
  prjxray; the bits-decoded netlist has the flop unconfigured).
* **DSP48E1 CLK** on GND (a combinational multiply): INT CLK wires have no default ppip, so the pin is undriven;
  with every DSP register off nothing reads it.  **Harmless** (ipow seed 2, fipowh4 seeds 26 and 29; §7).

## 3. Kind 1 (au_collatz_1_0, sdf b0aaeccd): false alarm -- evidence

Route rebuilt from its recipe (`auto_size.sh` it 0 = lane2.sh, sizes none, BDC_AUTO=1, NEXTPNR_SEED=1, commit
4ce0399eb) with my base binary: SDF b0aaeccd, FASM bb08e518, routed JSON 69051eb0 -- byte-identical to
`/tmp/bot/runs/hw/au_collatz_1_0/`.  pnr.log: `$PACKER_GND_NET: 2534/2537 sinks bridged (3 left to main router; max
BFS 50000)`; the 3 holdouts are exactly the three D6LUT/A1 pins fasm_equiv lists (`$PACKER_GND_NET$LUT$108.A1`,
`$LUT$116.A1`, `$LUT$146.A1`).

SLICE_X3Y42 (CLBLL_L_X2Y42, SLICEL_X1):
* JSON: `$PACKER_GND_NET$LUT$108` on D6LUT is nextpnr's feed-through for MUXF7 input I0 = constant 0
  (`legalise_muxf_tree` -> `feed_through_lut`): `X_ORIG_TYPE LUT1`, `INIT ..0010` (O = I0), port A1 on
  `$PACKER_GND_NET`, **no `X_ORIG_PORT_A1`** (dropped by fixupRouting: A1 never got a permutation pip).  As the packer
  meant it: O = GND = 0.  As gen.py and fasm.cc read it (no pin carries I0): O = INIT[0] = 0.  0 either way.
* FASM: `CLBLL_L_X2Y42.SLICEL_X1.DLUT.INIT[63:0] = 64'b0...0`, and no `CLBLL_L_D1..D6` pip in that tile: the D-LUT
  pins are unrouted and read 1, and an all-zero INIT ignores them.  O6 = 0.
* F7BMUX input 0 = D6LUT O6 (hardwired): **0 on the die, 0 in the JSON.**  Its select CX is routed (net `..A[6]`).
* fasm_equiv compared ('bel', D6LUT, O6) with ('const', 0): it folded the bits side (INIT all 0, `lut_const`) but not
  the JSON side (INIT 2 is not a constant string, and its expansion path needs an `X_ORIG_PORT_A*`).  Same for
  SLICE_X6Y63 / SLICE_X7Y63.  The 3 HARMLESS rows are those three A1 pins (json 0, bits 1, the INIT ignores them).

## 4. Kind 2 (F7 select on GND): real -- evidence

Reproducer: ipow item 29 sizes x0.55, route 19 (JOURNAL 2026-11-17 11:51).  Rebuilt at d4fd13f9a (the HEAD of that
run): `BDC_MERGE_OUT_LINK=ucontrol_merge0 BDC_LINK_FASTFALL=1 BDC_MERGE_RES_LINK=ucontrol_merge0 NEXTPNR_SEED=19
BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=research/data/ipow_dsp1_sizes_T9s75_h4s3m_x55_bench.vh
./hw/build_bench.sh ipow` -> **sdf d63bfd80 = the journal's route 19**.  pnr.log `3350/3351 sinks bridged (1 left;
max BFS 50000)`, `HOLDOUT: bridge_i.udut.ushrsi0.$abc$...$21968...mux7.S0 (bel SLICE_X19Y65/F7AMUX)`.

* JSON (SLICE_X19Y65 = CLBLL_R_X13Y65 SLICEL_X1): F7AMUX `mux7` (a MUXF7 in `ushrsi0`, e >>= 1), S0 on
  `$PACKER_GND_NET`, input 0 = B6LUT (`..lut0`, f0), input 1 = A6LUT (`..lut1`, f1), both LUT4 INIT 0x0503 on
  different `A[...]` bits.  Meant: OUT = f0.
* FASM: ALUT / BLUT INITs and `AOUTMUX.F7`, but **no `CLBLL_R_X13Y65.CLBLL_L_AX.*` pip** and no BYP pip into it:
  AX reads 1 (BYP_ALT default).  Die: OUT = f1.
* fasm_equiv (old and new): `DRIVER DIFFERS SLICE_X19Y65/F7AMUX/S0 json ('const', 0) bits ('const', 1)`.
* **Bits-decoded GLS** (`research/tools/eventgraph/bench_gate.sh ... max`: fasm2net decode of the .bit, prjxray SDF,
  SLOW_MAX, ipow17 vectors, expected values from `kernel_oracle.sh ipow` = the committed ipow17.exp): **FAIL 11/17**.
  The six large exponents return 3^e' for a smaller e' (e = 0xfff -> d250a2ab, want 7cda6aab; 0xffff -> 7cda6aab, want
  4da6aaab; ... 0x7fffffff -> 8aaaaaab, want aaaaaaab; batch 10 in 260 cycles): the loop exits early.  Same 11/17 as
  the journal's draws 1901/1902.
* Same route, patched nextpnr: **PASS 17/17**, EQUIVALENT (old and new fasm_equiv); batch 10 = aaaaaaab in 294
  cycles.  The route's prjxray SDF (xray.sdf, what the GLS reads) is byte-identical to the defective route's.
* Second instance: farm fipowh4 seed 28 (commit 531cc693a, `ipow_dsp1_sizes_T9s75_h4_bench.vh`, the same knobs):
  the rebuild's holdout is `SLICE_X10Y41/F7AMUX` S0 -- the site the journal reports for that seed.

## 5. Kind 3 (flop D on GND): a real bitstream defect -- evidence

Reproducer: farm fipowh4 seed 6 (JOURNAL 2026-11-15 "seeds 6, 26, 29 FFMUX gap"), recipe as seed 28 above.
pnr.log `3350/3351 bridged`, `HOLDOUT: $auto$dfflegalize.cc:410:emulate_split_set_clr$21766.D (bel SLICE_X13Y43/CFF)`.

* JSON: an `FDPE` (yosys dfflegalize's emulation of a set+clear flop, in the bench harness) with D on
  `$PACKER_GND_NET`, PRE (SR) on a live AND, CE live; its Q feeds `SLICE_X9Y43/C6LUT`.  Meant: Q falls to 0 at the
  first enabled edge after a preset.
* FASM (CLBLM_R_X9Y43 SLICEL_X1): `CFF.ZINI`, `CEUSEDMUX`, `SRUSEDMUX` -- **no `CFFMUX.*`** and no CX pip.
  ffmux_scan: `CLBLM_R_X9Y43.SLICEL_X1.CFF`.
* fasm_equiv: `cell in routed JSON, not configured by the bits (HAS LOADS): SLICE_X13Y43/CFF`, `DRIVER DIFFERS
  SLICE_X9Y43/C/A2 json ('bel', 'SLICE_X13Y43/CFF', 'Q') bits ('const', 1)`, `LUT FUNCTION DIFFERS SLICE_X9Y43/C6LUT`.
* Bits-decoded GLS (same harness as §4): **PASS 17/17 with NOT EQUIVALENT**.  fasm2net leaves the flop out (nothing
  configures its D) and drives its one load pin with 1; on these 17 vectors that changes no answer and no latency
  (every BENCHRES batch / cycles / odata identical to the patched route's).  The flop is one of the cells yosys
  dfflegalize builds for the harness's `i_ack_latched` / `o_req_latched` (async set by the kernel's pulse, sync clear
  at S_ISSUE; `cells/hw/gen_bench.py`): D = 0 is that sync clear.  What the die does instead is not knowable from
  prjxray -- the flop is configured (ZINI, SR, CE), only its input mux is not.  The journal's other instances: xorshift
  pmf seed 2 (AFF) "the run returns X data"; collatz64 T4 seed 4 (C5FF) "gen.py stops" -- rebuilt here, below.
* Patched: **PASS 17/17, EQUIVALENT**; ffmux_scan clean.
* **The 5FF instance** (JOURNAL 2026-11-08 08:21): collatz64 T4 bench seed 4, rebuilt at 13d7e8064 (`NEXTPNR_SEED=4
  BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=research/data/collatz64_sizes_T4_bench.vh ./hw/build_bench.sh
  collatz64`) -> **sdf 1310d2ef, the journal's route**.  pnr.log `2819/2822 bridged`, HOLDOUT
  `$auto$dfflegalize.cc:410:emulate_split_set_clr$23629.D (bel SLICE_X27Y75/C5FF)` (+2 LUT pins).  FASM
  (CLBLL_R_X19Y75 SLICEL_X1): `C5FF.ZINI`, `COUTMUX.C5Q`, `SRUSEDMUX`, `CEUSEDMUX`, no `C5FFMUX.*` (IN_A / IN_B are one
  bit each; neither set).  Decoded + fasm_equiv: NOT EQUIVALENT (`cell ... not configured by the bits (HAS LOADS)`,
  its two loads `SLICE_X30Y74/B/A4`, `SLICE_X31Y74/B/A2` **undriven** in the bits, `LUT FUNCTION DIFFERS` x2) -- an X
  in any simulation of them.  Patched: EQUIVALENT, ffmux_scan clean (§7).

## 6. The patch: `nextpnr-xilinx-const-sinks.patch`

Base `bfdeaf7c`; applies after the eight patches in `setup-toolchain.sh`'s list (its "anything new not in the list
above" loop picks it up; checked: `git apply` on a fresh bfdeaf7c tree after the eight leaves `xilinx/arch.cc` /
`arch.h` identical to the tree the patched binary was built from).  Touches `xilinx/arch.cc` (+386) and
`xilinx/arch.h` (+1) only: no placer, packer, router2, routeVcc() or fasm.cc change.  Proposed section for
`patches/README.md`:

> ## nextpnr-xilinx-const-sinks.patch
>
> Base: `nextpnr-xilinx` at `bfdeaf7c`, after the patches above.  Applies to `xilinx/arch.cc`, `xilinx/arch.h`.
>
> **A GND sink that `routeVcc()` could not reach stayed unrouted, and on the die read the interconnect default.**
> `routeVcc()` routes the constant nets after router2, as a fill through the wires router2 left free, with an uphill
> BFS bounded at 50 000 wires; a sink that hits the bound is logged "left to main router" and never routed (no router
> runs after it).  An unrouted IMUX/BYP reads VCC through its default ppip; a flop's D gets no FFMUX bit.  For a LUT
> input on GND that is harmless (fixupRouting drops its X_ORIG_PORT and the INIT is written with that input at 0);
> for an F7/F8 select on GND (reads 1: the mux passes its other input) and a GND-D flop (its FFMUX selects nothing) it
> is a wrong bitstream under a correct netlist, SDF and JSON: fasm_equiv `DRIVER DIFFERS .../F7AMUX/S0 json const 0
> bits const 1` (ipow, 11/17 in the bits-decoded GLS) and ffmux_scan's FFMUX gap (~7 % of routes, AFF/BFF/CFF/C5FF).
>
> The fix is a pass, `Arch::repairConstSinks()`, between `routeVcc()` and `fixupRouting()`.  For each user of
> `$PACKER_GND_NET` / `$PACKER_VCC_NET` whose sink wire is not on the net, nothing is done if the FASM already gives
> the pin the constant without a route: a plain LUT input on GND in a tile with a used permutation pip (on VCC: in one
> without), FF SR on GND / CE on VCC, CARRY4 CIN / CYINIT, F7/F8 select on VCC, CLK / CE* / RST* of a DSP48E1 with
> every register off.  Every other such sink is routed: (1) routeVcc()'s own search, free wires only, bound 5 M
> instead of 50 k, never ending on a pseudo-constant SITEWIRE (route_const_arc's rule); (2) only if that fails, the
> path holding the fewest wires of signal nets (router2's STRENGTH_WEAK wires; never a root wire, a clock / LOCKED /
> FIXED wire or the other constant): those nets' branches through it are ripped up, the constant is bound, each
> disconnected sink is re-routed through free wires by least pip delay, and everything is restored if one cannot be.
> A sink that cannot be routed either way ends the pass in `log_error`: no bitstream rather than a wrong one.  Every
> run logs `Constant sinks routeVcc left unrouted: N (M where the FASM encodes the constant without a route: ...), F
> routed through free wires, R with rip-up, U left unrouted`.  `NEXTPNR_CONST_REPAIR_TEST=ripup` (tests only) skips
> (1) and makes (2) prefer signal wires.
>
> A route with no such sink is not touched (routed JSON, SDF, FASM byte-identical).  On one with such a sink nothing
> moves: step (1) adds wires to the constant net only, so placement, every signal net and the SDF stay byte-identical;
> the routed JSON differs only in `$PACKER_GND_NET`'s ROUTING (added wires), the FASM only by the added path's pips
> (+ the FFMUX feature).
>
> Fingerprint: `"Constant sinks routeVcc left unrouted|nextpnr-xilinx-const-sinks.patch|..."` (0x in every binary
> without this patch).

Why not a FASM-only fix: the select / D input has to be 0 on the die, and nothing makes a BYP pin 0 except a route
from a constant source (BYP_ALT's default is VCC; no FFMUX encoding is "0").  Why not just raise routeVcc()'s bound:
routeVcc() routes sinks in order and stops on any wire already on the net, so routing a former holdout changes the
search of every later sink -- the GND routing and FASM of routes whose only holdouts are harmless LUT pins would
change.  A separate pass after routeVcc() touches only the sinks that need it.

How the real holdouts were reached (step 1, free wires): route 19's F7 select by 9 wires from the empty A-LUT of
SLICE_X26Y65 (`CONST_DRIVER`) out on LOGIC_OUTS12 / WW4 / WW2 into BYP_ALT0 -> AX; fipowh4 6's CFF D by 9 wires from
INT_R_X9Y44's GFAN0 (already GND) through FAN_ALT4 / FAN_BOUNCE4 / FAN_BOUNCE_S3_4 / FAN_ALT1 / FAN_BOUNCE1 /
BYP_ALT2 -> CX -> CFFMUX.CX; fipowh4 28's F7 select by 10 wires from the empty A-LUT of CLBLL_L_X2Y43 over SE2 / EE4 /
SE2 into BYP_ALT1 -> AX.  Step (2) was needed once, by a DSP CLK on GND (§7, ipow seed 2) in an earlier state of the
patch that still routed it; the final patch leaves that pin alone.

## 7. Validation

Every comparison: the same pre-pnr JSON + XDC, the same seed, build_bench.sh's exact nextpnr command
(`--ignore-loops --seed S --freq 83 --timing-allow-fail`; `out/tools/pnr_direct.sh`).  Unpatched = `nextpnr-base`
(byte-identical to the installed binary, §11); patched = `nextpnr-fix` 6e5d224472232d5d.  "+GND only" means: the routed
JSON is identical once `$PACKER_GND_NET`'s ROUTING attribute is masked (both files loaded and compared whole), and that
attribute only gains (wire, pip, strength) entries -- none of the old ones changes or goes; so placement (every
NEXTPNR_BEL), cell parameters / attributes / connections and every other net's routing are identical.

### 7a. Routes with nothing to repair: byte-identical

| route (commit, recipe) | unpatched: GND holdouts | patched summary | routed JSON | SDF | FASM |
|---|---|---|---|---|---|
| au_collatz_1_0 = collatz s1 (4ce0399eb, BDC_AUTO=1, sizes none) | 3: A1 of three F7 feed-through LUT1s (kind 1) | 3 holdouts, 3 FASM-encoded | = 69051eb0 | = b0aaeccd | = bb08e518 |
| ipow s1 (41fd9a868, BDC_AUTO=1, none) | 0 | 0 | = 4363590a | = d68acaae | = ad935b9b |
| ipow s2 (same) | 1: DSP48E1 CLK on GND, every register off | 1, FASM-encoded | = 06aa1c3b | = 5e6667f1 | = 66c75c3d |

(ipow s1 and collatz s1 re-run with the final binary: JSON / SDF / FASM identical to the unpatched ones; collatz compared with the installed binary's 69051eb0, since my first base build of it carried a different `creator` string.)

VCC had 0 holdouts in every run (782/782 .. 914/914 bridged).

### 7b. Routes with a real holdout: the defect gone, nothing else moved

| route (commit) | real holdouts (unpatched) | patched: how | routed JSON | SDF | FASM | fasm_equiv | ffmux_scan | bits-decoded GLS, SLOW_MAX |
|---|---|---|---|---|---|---|---|---|
| ipow x0.55 r19 (d4fd13f9a) | F7AMUX S0 SLICE_X19Y65 | free wires (9) | +GND only (+9) | = d63bfd80 | +6, -0 | NOT EQ -> **EQ** | clean | **FAIL 11/17 -> PASS 17/17** |
| fipowh4 s6 (531cc693a) | CFF D SLICE_X13Y43 | free (9) | +GND only (+9) | = 7c8d883b | +8 (`CFFMUX.CX` ...), -0 | NOT EQ -> **EQ** | FLAG -> clean | 17/17 -> 17/17 (same cycles / odata) |
| fipowh4 s28 (531cc693a) | F7AMUX S0 SLICE_X10Y41 (+1 LUT pin) | free (10); LUT pin left | +GND only (+10) | = 7289a101 | +7, -0 | NOT EQ (`S0 json 0 bits 1`) -> **EQ** (old and new fasm_equiv) | clean | -- |
| fipowh4 s26 (531cc693a) | CFF D SLICE_X12Y44 **and** F7AMUX S0 SLICE_X13Y44 (+ DSP CLK, LUT pin) | free (2 sinks); 2 left | +GND only (+18) | = 36dd550d | +16, -0 | NOT EQ (flop not configured; DRIVER DIFFERS) -> not decoded (stopped) | FLAG -> clean | -- |
| collatz64 T4 s4, 2026-11-08 (13d7e8064) | C5FF D SLICE_X27Y75 (+2 LUT pins) | free (11); LUT pins left | +GND only (+11) | = 1310d2ef | +8 (`C5FFMUX.IN_B` ...), -0 | NOT EQ -> **EQ** | FLAG -> clean | -- |
| fipowh4 s29 (531cc693a) | CFF D SLICE_X12Y37 (SLICEM) (+ DSP CLK, left) | free (12) | +GND only (+12) | = 6ae3414c | +9 (`CFFMUX.CX` ...), -0 | NOT EQ (flop not configured) -> **EQ** | FLAG -> clean | -- |

Every real holdout in these routes was reached through free wires (step 1); no signal net moved, no SDF line changed.
Seed 26's F7 select was not in the journal (that route was already excluded for its FFMUX gap).

### 7c. Step (2), the rip-up

* **Real, once** -- ipow s2 with the earlier patch state (`nextpnr-fix-50157dc9`, which still routed a DSP CLK): the
  DSP CLK is fed from an INT CLK wire, which no free GND path reached, so step 2 took a 10-hop path through 1 wire of
  `bridge_i.udut.n10__1_data[9]`, ripped that net's 5-wire branch, re-routed its 1 lost sink (DSP B9).  Placement and
  all other nets identical; 1 SDF INTERCONNECT changed (that B9 arc, 900 -> 712 ps).  Bits-decoded GLS: **PASS 17/17,
  EQUIVALENT**.  (The final patch leaves this pin alone -- §7a.)
* **Forced** (`NEXTPNR_CONST_REPAIR_TEST=ripup`: step 1 skipped, step 2 *prefers* signal wires):
  route 19 -- 5 hops through 1 signal wire; ripped 5 wires of `$abc$22022$...NotGate$20493` (it held INT_R_X13Y65's
  GFAN0), 1 sink re-routed (a FF SR: 775 -> 1019 ps), GND +5 wires; decoded + fasm_equiv **EQUIVALENT**.
  fipowh4 s6 -- 6 hops through 1 signal wire; ripped 4 wires of `bridge_i.udut.n1__1_data[9]` (it held INT_R_X9Y43's
  GFAN1), 1 sink re-routed (a LUT A4: 757 -> 988 ps), GND +6; decoded + fasm_equiv **EQUIVALENT**.
  In both: placement and every other net identical, exactly one SDF line changed.  The restore path (a lost sink that
  cannot be re-routed) has not been triggered by any run.

## 8. Fingerprint for `cells/verify/toolchain.sh`

`out/toolchain.sh.proposed` / `out/toolchain.sh.diff` add one line to CHECKS:

    "Constant sinks routeVcc left unrouted|nextpnr-xilinx-const-sinks.patch|GND sinks routeVcc's 50k-wire BFS missed stayed unrouted (F7/F8 select read 1, constant-D flop had no FFMUX)"

The string is the new pass's summary log format, new to the binary.  Checked both ways with the proposed script:

| binary | sha256 (16) | `strings -a \| grep -cF` | proposed toolchain.sh |
|---|---|---|---|
| installed `$TC/openxc7/bin/nextpnr-xilinx` | 9c732bc6303458df | 0 | `MISSING nextpnr-xilinx-const-sinks.patch`, **exit 1** |
| my base build (bfdeaf7c + the 8 patches) | 08fe9ff3a5fd3245 | 0 | exit 1 |
| my patched build | 6e5d224472232d5d | 1 | all ok, exit 0 |

The current `toolchain.sh` passes the patched build too (all eight old fingerprints present).  Add the line when the
patched binary is installed, not before (it fails today's binary, by design).

## 9. fasm_equiv: the false alarm (clone commit `e8e1c9923`, `out/0001-fasm_equiv-...patch`)

Section 3 folded a constant LUT driver on the bits side only.  New `lut_fold()`: a driver LUT whose output is the same
for every value of its non-constant pins -- each side evaluated with its own INIT (gen.expand_lut_init) and its own
pin drivers, pins on a PSEUDO_GND/VCC cell held at that constant, every other pin (live or unconnected) free over 0/1 --
is compared as that constant and listed under a new benign kind `driver is a LUT whose output is constant given the
constants on its own pins (...)` (shown, never hidden).  A LUT that reads any live signal is never folded.

| input | old verdict | new verdict |
|---|---|---|
| au_collatz_1_0 (its recorded fid files) | NOT EQUIVALENT: DRIVER DIFFERS (3 x F7BMUX/0) | **EQUIVALENT** (the 3 pins now same driver; 478 folds listed) |
| negative control 1: that route's FASM with `CLBLL_L_X2Y42.SLICEL_X1.DLUT.INIT` = all ones, rebuilt to .bit (fasm2frames + xc7frames2bit) and decoded (fasm2net --ps7) | -- | **NOT EQUIVALENT**: `DRIVER DIFFERS SLICE_X3Y42/F7BMUX/0 json ('const', 0) bits ('const', 1)` + `LUT FUNCTION DIFFERS` |
| negative control 2: the JSON with that LUT's A1 on `$PACKER_VCC_NET` and `X_ORIG_PORT_A1 = I0` (the buffer now means 1) | -- | **NOT EQUIVALENT**: `DRIVER DIFFERS ... json ('const', 1) bits ('const', 0)` |
| ipow route 19, unpatched nextpnr (the real F7 defect) | NOT EQUIVALENT (S0 json 0 bits 1) | NOT EQUIVALENT, the same line |
| ipow route 19, patched nextpnr | EQUIVALENT | EQUIVALENT |

`cells/gls/fid/test_acceptance.py`: 30 passed (it does not exercise this function).

## 10. What this does not show / open problems

* **Nothing here ran on the board.**  The F7 defect's wrong answers and the fix's right ones are the bits-decoded
  GLS at one delay column (SLOW_MAX).  The defect is a logic difference (a mux select), so the column should not
  matter, but no draw or corner sweep was run on the fixed routes.
* For the flop-D kind, what the die latches from an FFMUX with no bit set is not knowable from prjxray (no all-zero
  encoding).  "Real" means: the bits do not implement the netlist's D = 0 (§5).
* Step (2) (rip-up) has run on one real route only (a DSP CLK, with the earlier patch state that still routed it;
  §7) and under the test switch.  The LUT-pin branch that routes a GND pin in a tile with no permutation pip has never
  been reached (that case was 0 in 19 routes / 19 364 GND LUT pins).  VCC never had a holdout.
* Holdout statistics are from the routes in §7 only (16 routes rebuilt or re-run here); the defect's frequency
  (FFMUX gap ~7 %, F7 select 2 of ~17 ipow routes) is the journal's.
* The repaired constant paths can be long (route 19's crosses 6 tiles on WW4/WW2 from an empty slice's A-LUT).
  Constants have no SDF arcs and the wires were free after routing, so no signal net or delay changes; they do use
  routing the design did not need.
* Anything keyed on the **routed-JSON md5** of a repaired route changes (its `$PACKER_GND_NET` ROUTING grows); the SDF
  md5 -- what the journal and BOARD-QUEUE use to name a route -- does not, nor does the prjxray SDF (xray.sdf).
* The new fasm_equiv fold judges a JSON LUT by gen.py's reading of it (a pin with no X_ORIG_PORT carries no input),
  which is also nextpnr's FASM writer's reading.  A nextpnr *netlist* bug that dropped the mapping of a live or VCC pin
  would read the same on both sides; that is outside what fasm_equiv compares (JSON vs bits).
* Until the patch is installed, `ffmux_scan.py` sees the flop kind from a FASM but not the F7-select kind.
  `out/tools/constsinks.py ROUTED.json` lists every GND/VCC sink on an F7/F8 select or a flop D whose site wire the
  constant net does not reach (`UNROUTED ...`), from the routed JSON alone.  On the 30 routed JSONs on this node it
  flagged exactly the two defect routes (and none of the 16 routes in `/tmp/bot/runs/hw`).  It does not look at DSP
  or other non-slice pins.
* `routeVcc()`'s log line still says "left to main router"; the new summary line under it says what happened.

## 11. Files and provenance

Deliverables, `/tmp/bot/sa/pnrfix/out/`:
* `nextpnr-xilinx-const-sinks.patch` (sha256 4ed1b65d421ab9e7) -- the nextpnr patch; `xilinx/arch.cc` +386,
  `xilinx/arch.h` +1.
* `toolchain.sh.proposed`, `toolchain.sh.diff` -- the fingerprint line (§8).  `cells/verify/toolchain.sh` itself is not
  changed anywhere.
* `0001-fasm_equiv-fold-a-driver-LUT-...patch`, `0002-fasm_equiv-lut_fold-never-fold-a-LUTRAM-...patch` --
  `git format-patch 41fd9a868..HEAD` of the clone (`/tmp/bot/sa/pnrfix/repo`, commits e8e1c9923, 6de2aabcf); they change
  `cells/gls/fid/fasm_equiv.py` only.  Nothing else in the repo is changed (`patches/`, `toolchain.sh`, `cloud/` are
  deliberately untouched: installing is not my decision).
* `tools/` -- the scripts the numbers come from (absolute scratch paths inside): `constsinks.py` (unrouted constant
  sinks on F7/F8 selects and flop D, from a routed JSON), `constpins_synth.py` (constant-tied F7/F8 selects and flop D
  in a post-synthesis JSON), `cmp_routes.py` (placement / per-net routing / SDF / FASM diff of two runs),
  `pnr_direct.sh` (build_bench.sh's exact nextpnr call on a saved pre-pnr JSON + XDC), `bench_build2.sh` (lane2.sh's
  build recipe in a worktree of the clone, with a shadow toolchain dir whose `bin/nextpnr-xilinx` is the binary under
  test and everything else a symlink into `$TC`), `make_bit.sh`, `fasm_to_equiv.sh` (FASM -> .bit -> fasm2net ->
  fasm_equiv).  The GLS runs are `research/tools/eventgraph/bench_gate.sh HW ipow_bench_gen WORK
  research/data/eventgraph/gate/ipow17.hex ipow17.exp max` from the clone (expected values regenerated with
  `research/tools/fifteen/kernel_oracle.sh ipow`; identical to the committed ipow17.exp).

Binaries (`/tmp/bot/sa/pnrfix/bin/`; GCC 13.3.0 as in the installed one, CMake Release as setup-toolchain.sh,
`-DCURRENT_GIT_VERSION=0.9.2-100-gbfdeaf7c` so the routed JSON's `creator` string matches the installed binary's):
* `nextpnr-base` 08fe9ff3a5fd3245 = bfdeaf7c + the eight patches.  Reproduces the installed 9c732bc6303458df
  byte-for-byte: au_collatz_1_0's routed JSON 69051eb0, SDF b0aaeccd and FASM bb08e518 from the same pre-pnr JSON
  (seed 1), and, from rebuilt netlists, the journal's sdf md5s d63bfd80 (ipow x0.55 route 19) and 1310d2ef
  (collatz64 T4 seed 4).
* `nextpnr-fix` **6e5d224472232d5d** = base + `nextpnr-xilinx-const-sinks.patch` as delivered.
* Earlier states of the patch, used for some runs as marked in §7: `nextpnr-fix1` 6c41bb27ddcf6d96 (no perm-tile LUT
  rule, no VCC-select / DSP rules, no test switch, no final log_error) and `nextpnr-fix-50157dc9` (no DSP rule).  On
  every route without a DSP-CLK holdout their outputs are byte-identical to `nextpnr-fix`'s (checked on route 19,
  fipowh4 6 and 28).

Toolchain log entries of these builds went to `/tmp/bot/sa/pnrfix/toolchain-scratch.log`, not `build/toolchain.log`.
