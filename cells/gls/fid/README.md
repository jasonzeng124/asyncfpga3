# `gls/fid/`: the netlist the board runs, built from its bitstream

`cells/gls/` simulates nextpnr's routed JSON, which is what the tool meant to
build. Three of the four worst bugs here were in the bitstream, where that JSON,
the SDF and every simulation were correct (`patches/README.md`). This directory
rebuilds the design from the `.bit` itself, decoded by prjxray, and runs the
unchanged `gls/` flow on the result.

```
cells/gls/fid/build_fid.sh  cells/build/hw/gcd_hw  WORK  [bit|fasm]   # ~2 min + compile
cells/gls/fid/run_fid.sh    WORK  [-j N]                              # 16 vectors
GATE=1 build_fid.sh ...  &&  (cd WORK && vvp gate.vvp)                 # ANNOTATE_DONE gate
```

| file | what it does |
|---|---|
| `fasm2net.py` | `.bit` (through prjxray `bit2fasm` + `bitread`) or FASM, plus prjxray-db, gives `fasm_routed.json` (nextpnr-shaped, so `gen.py` reads it unchanged), `fasm.sdf`, `routes.tsv`, `stubs.tsv`, `pipnames.tsv` and `report.txt` |
| `fasm_equiv.py` | compares the routed JSON with the bits: cell set, config, every pin's driver, every LUT's function over every input assignment, and every net's pip set |
| `inject_pinmap.py` | negative control: the lut-pinmap bug's mechanism applied to live LUT pins |
| `bit_control.py` | one deterministic bitstream bug re-applied to a route; prints one CONTROL line (interface below) |
| `dsp_latency.py` | each registered DSP48E1 of a routed-shaped JSON simulated alone; A/B register stages fitted against P = A(t-LA)*B(t-LB); `--ref` compares them with the routed JSON's AREG/BREG (the dsp_areg property) |
| `soak_fid.py` | routed GLS of a fusion_bench/flow.sh soak route (e.g. ipow, BD_DSP=1) on the routed JSON (`ref`) or on the bits (`fasm`, `bit`), built the way `fusion_bench.simulate_route()` builds it |
| `build_fid.sh`, `run_fid.sh` | the `gls/build.sh` and `gls/run.sh` equivalents for the gcd_hw rig |

## Controls, for `acceptance.py`

```
cells/gls/fid/bit_control.py ROUTE_DIR KIND [--work DIR] [--good] [--gls]
```

| KIND | what it writes |
|---|---|
| `dsp_constpins` | `fasm_audit.py --write-unpatched constpins-packer`: INMODE0..4, ALUMODE2/3 and OPMODE6 get no tile-constant bit |
| `dsp_constpins_inv` | `--write-unpatched constpins-inv`: the tile bit carries the net, not the logical value |
| `dsp_areg` | `--write-unpatched areg`. **On a route with a registered DSP** (cells/verify/fasm/probe.v's: AREG=1/ACASCREG=1, AREG=2/ACASCREG=2, AREG=0, all MREG=1) the real writer is used and the hard PROPERTY is checked by `dsp_latency.py`: each registered DSP of the bitstream-built netlist is simulated alone (the instance gen.py writes, its decoded CE/RST constants) and its simulated A/B register stage count must equal the routed JSON's AREG/BREG. Patched bits: AREG=1 decoded, 1 stage, PASS; unpatched: AREG=2/ACASCREG=1 decoded, and with yosys's AREG=1 wiring (CEA1=0) the A1 register never loads, so P=0 on every cycle: FAIL. Equivalence also flags DSP CONFIGURATION DIFFERS. If that writer changes no bit (ACASCREG=0 everywhere: every combinational route, e.g. ipow), the mechanism is INJECTED instead: every Z[AB]REG_2_[AB]CASCREG_1 bit cleared. **That fallback stays WEAK (audit r3.md 1):** the injected state (AREG=0 with the conjunction asserted) is one the old writer never produced, and it is caught only because the decoder REFUSES it. |
| `lut_pinmap` | `--write-unpatched pinmap`. If that changes no bit, `inject_pinmap.py` is used on live pins. If it changes only GND-tied pins it is functionally harmless, and the line says MISSED |
| `lut_pinmap_live` | always `inject_pinmap.py`: one live pin per comparator LUT is read as I0 |

What it does with the buggy FASM:
1. assembles it with the build's own fasm2frames and xc7frames2bit;
2. decodes the result with `fasm2net.py --bit`;
3. compares it with `fasm_equiv.py`;
4. with `--gls`, runs `soak_fid.py ... bit` (soak routes only).

`--good` first runs the unmodified bitstream through the same steps and
requires it to pass.

**Route dirs.** ROUTE_DIR is either:
- a soak route: `pnr/soak.{fasm,sdf}`, `pnr/soak_routed.json`, `tb_*.v`, with
  `input.mlir` in the parent; or
- a `build_hw.sh` dir: `<d>.fasm`, `<d>_routed.json`, `<d>.sdf`.

**Output** is exactly one line on stdout, with an exit status:

```
CONTROL <kind> DETECTED: <how> | equivalence: <verdict> | GLS: <soak lines>   exit 0
CONTROL <kind> MISSED: ...                                                    exit 1
CONTROL <kind> ERROR: <why>   (cannot run, or --good failed)                  exit 2
```

DETECTED means the bitstream-built flow did not pass the buggy bitstream:
- equivalence NOT EQUIVALENT, or
- GLS FAIL, which includes a decode the model REFUSES. For dsp_constpins and
  dsp_constpins_inv the GLS FAIL is now a simulated wrong result (the DSP
  configuration is modelled), not a refusal; or
- (dsp_areg with the real writer) PROPERTY FAIL: `dsp_latency.py` simulated
  a register stage count other than the routed JSON's AREG/BREG. The line
  then carries `| PROPERTY (dsp_latency.py, PASS|FAIL): ...`, and `--good`
  also requires the property to PASS on the unmodified bitstream.
  Example (probe route, seed 1; see the S7 commit):
  `cells/gls/fid/bit_control.py <probe dir> dsp_areg --good` prints
  DETECTED with `DSP48_X1Y14/DSP48E1 decoded AREG=2, simulated
  A_STAGES=NEVER ..., ref AREG=1 ... FAIL`.

`soak_fid.py SEEDDIR WORK ref|fasm|bit [--bit B] [--gate]` prints
`SOAK <kind> PASS lat=...` or `SOAK <kind> FAIL: ...` for each of the stalled
and fast harnesses, then `SOAK_VERDICT PASS|FAIL`, and exits 0 or 1.

**`acceptance.py --stack full --corner min|typ|max|band`** runs the bitstream
items on the full stack with no hand steps: the patched run decodes the
build's `.bit`, the unpatched run the `--write-unpatched` FASM assembled with
`bit_control.to_bit`; both use `xray_delay.py`'s SDF of the route (re-keyed by
`fasm2net.py`), `GLS_SDF_FIELD=<corner>` and `GLS_MODEL=fid`. gcd items run the
16 vectors one at a time (one ~3 GB vvp); soak items run `soak_fid.py ... bit`.
An unpatched bitstream caught only because the decoder refuses it prints
`MATCH (WEAK: by refusal)`; a dirty ANNOTATE gate makes the item INVALID.
Without `--stack` the harness is unchanged.

**`acceptance.py --items dsp_areg`** (either stack) runs the dsp_areg
PROPERTY on probe.v's route at inventory `route_dir` (`build/fid/dsp_probe`;
produce it with the `route_build` commands in `inventory.json`:
`cells/verify/toolchain.sh`, `cells/verify/fasm/check.sh`, then copy
`cells/build/verify/fasm/probe.{fasm,sdf}` and `probe_routed.json` there).
Both FASMs (the route's, and `--write-unpatched areg`'s) are assembled,
decoded by `fasm2net.py --bit`, and `dsp_latency.py --ref` runs on each.
MATCH iff the patched bits PASS (every registered DSP simulates the routed
AREG/BREG stages) and the unpatched bits FAIL on a DSP whose routed AREG/BREG=1
decodes as 2. A writer that changes no line is BLOCKED; identical bitstreams
are an ERROR. The item reads the bits whatever the configuration's netlist,
and no SDF; prims.v's DSP48E1 has no GLS_FID variant, so `--stack full` only
prefers the route's own `.bit` (probe has none). "Identical" is judged from
the sync word on: xc7frames2bit writes the frames file's path into the .bit
header, so two assemblies of one FASM in two dirs differ as files (this also
applies to the full-stack bitstream items' guard).
`research/data/fid/inventory.md` is generated: `cells/gls/fid/inventory_md.py`
(`--check` to test it is current).

## What comes from where

* **Connectivity and every LUT function come from the bits only.** Each sink
  pin is traced upstream through:
  - active pips (FASM `TILE.DST.SRC`; a bidirectional LV/LH pip takes its
    direction from the feature);
  - always-on ppips (`ppips_*.db` "always", which carry no bits);
  - tile-to-tile wire joins (`tileconn.json`);
  - the "default" ppip, where an IMUX, BYP_ALT or FAN_ALT with no pip set
    reads VCC.

  The trace stops at a decoded site output or at a tile VCC_WIRE/GND_WIRE.
  Two drivers on one node, an undriven node, or a route that ends at a site
  output nothing configured drives is an error.
* **Which bels exist is decided by the bits.** A LUT6 whose upper half is
  configured always exists. Any other bel exists only if something the bits
  configure reads it.
* **The routed JSON is used for names only.** The RTL net names that the
  testbenches watch are attached to the bits' nets by driver bel pin
  (`FASM2NET_ALIAS`). The SDF is re-keyed onto bel-named cells. If the bits say
  a sink has a different driver than the SDF arc, `report.txt` counts a
  DRIVER MISMATCH.
* **DSP48E1** (the configurations `prims.v` models) is decoded from
  the bits:
  - `AREG_0/AREG_2` (no bit means 1);
  - `Z<x>REG[0]` set means that register is off;
  - `ZAREG_2_ACASCREG_1` set means NOT (AREG=2 and ACASCREG=1);
  - `A_INPUT[0]`, `B_INPUT[0]`, `USE_DPORT[0]` and `USE_SIMD_*`.

  A/B registers (`dsp_reg_bits()`; S7): AREG_0 -> 0/0; neither bit with Z
  set -> AREG=1/ACASCREG=1; AREG_2 with Z set -> 2/2, clear -> 2/1; NEITHER
  bit with Z CLEAR (what the unpatched writer wrote for AREG=1) -> 2/1, with
  a NOTE in report.txt. That last row is an ASSUMPTION taken from
  `patches/nextpnr-xilinx-dsp-areg.patch` ("silicon reads it as AREG=2"):
  no board readback of it exists, and the board A/B on that patch ran while
  the constpins bug gated A to zero, so it could not have seen it. AREG_0
  with Z clear, or both bits, is refused. Registered DSPs (AREG/BREG 0/1/2,
  CREG, MREG, PREG; CLK with ZIS_CLK_INVERTED, CEA1/CEA2/CEB1/CEB2/CEC/CEM/
  CEP, RSTA/RSTB/RSTC/RSTM/RSTP resolved through routing) are modelled
  (`dsp_model.py` has the UG479 semantics; `gls/tb_dsp_reg.v` hand-checks
  the pipeline); ADREG/DREG/INMODEREG/OPMODEREG/ALUMODEREG/CARRYINREG/
  CARRYINSELREG=1 are still refused. nextpnr writes NO SDF arc for a
  registered DSP48E1, so its clock-to-out is a nominal 1000 ps parameter and
  its register inputs have no setup/hold check.

  Every control pin is resolved through routing like any other input, and the
  control words are formed from the result:
  - A pin driven through the tile's `DSP_GND_*`/`DSP_VCC_*` bit bypasses the
    site inverter (`patches/nextpnr-xilinx-dsp-constpins.patch`, measured on
    the board).
  - A pin with neither bit reads 1. This is the tile default the board showed
    under the unpatched writer, and it is an assumption here.
  - A routed pin goes through `ZIS_<pin>_INVERTED` (bit set means not
    inverted).

  The decoded words go to `cells/gls/dsp_model.py`,
  which `gen.py` uses too: it accepts the COMBINATIONAL configurations
  `prims.v` simulates (any OPMODE X/Y/Z per UG479 except X=P; INMODE[1] A
  gating; every ALUMODE in UG479's arithmetic and logic tables; CARRYIN with
  CARRYINSEL=000) and REFUSES the rest with the decoded words named:
  registers, CARRYINSEL other than 000, INMODE A1/B1/pre-adder bits with A
  not gated, a logic ALUMODE reading a nonzero multiplier, ALUMODE 10xx,
  Z=111, and P fed back with PREG=0 unless the output provably does not
  depend on it (e.g. X AND Z with X=0). A configuration other than the
  default multiply is listed in `report.txt` as a NOTE. Assumptions (written
  in `dsp_model.py`): with USE_DPORT=FALSE the pre-adder/D never reach the
  multiplier; with AREG=BREG=0 INMODE[0]/[4] do not matter once A is gated.
  A logic ALUMODE reading a GATED multiplier is simulated as UNKNOWN (every
  output bit x, `MUNK`): only the sum of the two partial products is known
  to be 0, not each word. The unpatched constpins writers decode to
  INMODE=11111, ALUMODE=1100, OPMODE6=1, which is exactly that case: they are
  SIMULATED with x outputs (the testbenches' `!==` fails on x), not refused.
  (An earlier version assumed both partial products 0 and gave every product
  0; the board's 965/2016 correct ipow products contradict that.) USE_MULT has no bit in prjxray-db and is
  assumed MULTIPLY. The pattern detector bits (MASK, PATTERN, ...) are
  consumed, but no modelled output reads them.

  **Pre-adder and B cascade (S8, share_test_2; `dsp_model.py` has the
  semantics).** On a site with `USE_DPORT[0]` the 25 D pins are traced, on
  one with `B_INPUT[0]` the 18 BCIN pins (always-on `DSP_1_BCIN<i> <-
  DSP_0_BCOUT<i>` ppips), and a BCOUT becomes an output of its cell only
  where such a BCIN reads it; a site with none of the three decodes, and
  every netlist without them comes out, byte for byte as before (checked on
  gather and xorshift routes: fasm_routed.json, fasm.sdf, routes.tsv,
  report.txt, equiv.txt, gen.py's netlists, xray_delay.py's SDF). Modelled:
  every register off, INMODE=00100 with USE_DPORT (AD = D + A2), BCIN in
  place of B, BCOUT = the selected B, only in the multiply P = Z + M;
  anything else with them is refused. `ZIS_INMODE_INVERTED` is consumed on
  such a site: INMODE comes in through the tie-off bits, which bypass the
  inverter.

  **ASSUMPTION (the D route).** A D pin has three sources in prjxray-db: the
  `DSP_GND_*` and `DSP_VCC_*` tie-off bits and ONE tile pip from a BYP
  (DSP_0) or FAN (DSP_1) interconnect wire, `DSP_<n>_D<i> <- DSP_FAN<j>_<k>`,
  which is in tile_type_DSP_*.json but has no segbits entry and is not an
  `always` ppip (fuzzer 071 lists only a node's single uphill pip as always;
  this node has three). The decoder takes "neither tie-off bit set" to mean
  the pin reads that wire (`Design.dsp_bitless`; the path in routes.tsv ends
  in the bit-less pip, and report.txt carries a NOTE per DSP that relies on
  it). nextpnr routes D that way and writes no bit for it. For it: Vivado
  routes a used D port through these wires; prjxray's fuzzer 101-dsp-pips
  drove 10% of D pins from LUTs and solved each tie-off as one positive bit
  (frames 26/27), and of all bits ever seen set in those frames of a DSP
  tile (mask_dsp_*.db) only two are explained by no segbit, so no per-pin
  "route enable" bit was ever seen set there; and the board's INMODE reading
  1 with no tie-off bit (unpatched constpins writer) is what an undriven FAN
  wire (INT default VCC) gives. NOT measured: no bitstream with a routed D
  pin has run on the board here. A D pin whose wire nothing drives (INT
  default) is refused, and so is a D pin on a tie-off bit (not modelled).
* **RAMB18E1** (bd_mem's configuration only; 2026-11-17). A RAMB18 half with
  `RAMB18_Y<h>.IN_USE` becomes one `RAMB18E1_RAMB18E1` cell named like
  nextpnr's bel (`RAMB18_X0Y26/RAMB18E1`). The lower half is prjxray's
  FIFO18E1 site, whose pins carry FIFO names (DO, RDCLK, RDEN, RST); both
  sites' tile wires carry the RAMB18E1 names (`BRAM_FIFO18_DOADO3`,
  `BRAM_RAMB18_CLKARDCLK`), so pins are named from the wire. Accepted, and
  nothing else (`decode_bram()` refuses every other feature of a BRAM tile,
  so an unknown bit stops the build instead of reaching the not-consumed
  list): port A x18 (`READ/WRITE_WIDTH_A_18`), port B at the unused encoding
  (`_1`) AND its enable a constant 0 after the site inverter (`ZINV_ENBWREN`
  absent = inverted; nextpnr ties ENBWREN to VCC with IS_ENBWREN_INVERTED),
  no DOA/DOB_REG, WRITE_FIRST (no WRITE_MODE bit), no INIT/INITP content,
  `ZINIT_A`/`ZSRVAL_A` (INIT_A/SRVAL_A = their complement, modelled),
  ADDRATIEHIGH0/1 decoded to 1, CLKARDCLK a live net, no reader of DOBDO/
  DOPBDOP; the unused half's and the tile's all-zero encodings (`*_WIDTH_*_1`,
  `RDADDR_COLLISION_HWCONFIG_DELAYED_WRITE`, `RSTREG_PRIORITY_*_RSTREG`,
  `RAMB36.RAM_EXTENSION_*_NONE_OR_UPPER`, `ZALMOST_*_OFFSET`) are consumed.
  Refused: cascade, FIFO mode, ECC, SDP, other widths, output registers,
  READ_FIRST/NO_CHANGE, INIT content, a live port B, and a RAMB36 that sets
  any RAMB36-level bit (widths 1 and 9). LIMITATION: a RAMB36 at width 36
  has NO bit of its own in prjxray-db (nextpnr writes READ/WRITE_WIDTH_18 in
  each half), and the site-pin pips of the RAMB18 and RAMB36 sites are the
  same always-on ppips, so the bits cannot tell it from two RAMB18 halves at
  one address: it decodes as two RAMB18E1 cells, and `fasm_equiv.py` then
  reports the cell sets differing (NOT EQUIVALENT). bd_mem never uses one. The model is
  `prims.v RAMB18E1_RAMB18E1` (its header: write-first x18 on a clean
  rising edge, power-up 0, a setup/hold violation of ADDR/DI/WE/EN/RST
  poisons the edge's word and DO with X). Timing: nextpnr writes NO arc and
  NO check for this cell, so `xray_delay.py` inserts them from prjxray-db
  `timings/BRAM_*.sdf`: CLKARDCLK -> DOADO/DOPADOP (585 : 1353 : 2454 ps,
  the DOA_REG=0 read) and the windows (largest end of each): ADDR 566/360,
  DI 737/667 (TDP WRITE_FIRST), WE 532/197, EN 443/227, RST 359/453 ps
  setup/hold. ASSUMPTION: the database has these windows only for the
  upper half (ADDRAU, ...), and both halves take them. `gen.py` refuses a
  RAMB18E1 whose SDF carries no clock-to-out or no SETUPHOLD
  (`GLS_RAM_NOMINAL=1` overrides, for a debugging run only). The SDF cell
  type is `RAMB18E1_RAMB18E1`, so `GLS_SDF_BAND_CELL=RAMB18E1_RAMB18E1=<b>`
  places its clock-to-out in the band (never measured on the board: like
  CARRY4/F7/FF, the slow end is the conservative corner for bd_mem, whose
  DCO must cover it). `fasm_equiv.py` section 2c compares the configuration,
  the EFFECTIVE CLK/EN/RST/ENB values (constant XOR inversion: nextpnr writes
  a GND tie as VCC + IS_*_INVERTED) and the driver of every ADDR/DI/DIP/WE
  pin. Self-test: `bram/README.md`.
* **Latches** (LDCE/LDPE: the four FFs of a slice with `LATCH` set). The latch
  is open while the clock pin equals the CLKINV bit. ZRST selects asynchronous
  clear, otherwise preset. `gen.py` now emits `SLICE_LATX` (`prims.v`) for a
  SLICE_FFX cell whose `X_ORIG_TYPE` is LDCE/LDPE; before this, such a cell
  was simulated as an edge-triggered flop.
* **Refused rather than mis-simulated:**
  - CLKINV on a flop;
  - asynchronous SR on a flop;
  - a 5FF in a latch slice;
  - LUTRAM/SRL, and any BRAM configuration other than bd_mem's RAMB18E1 (above);
  - ILOGIC in ISERDES/IDDR mode, and OLOGIC in any mode other than D1 to OQ;
  - a DSP outside its subset (see above; registered A/B/C/M/P are modelled);
  - a BUFGCTRL that does not reduce to O = I0.

  ILOGIC passthrough (ZINV_D) and the IOB33 input buffer are decoded. Every configured feature the decoder did not
  consume is listed in `report.txt`. On gcd_hw that list is empty.

## Naming (the convention F1's prjxray SDF is to use)

| thing | name | example |
|---|---|---|
| cell | its bel, as nextpnr's `NEXTPNR_BEL` writes it | `SLICE_X22Y80/D6LUT`, `BUFGCTRL_X0Y16/BUFGCTRL`, `IOB_X0Y34/IOB33/OUTBUF` |
| constant driver | `$VCC` / `$GND` (pin `Y`) | |
| net | its driver, `<bel>/<pin>`; constants `$const1` / `$const0` | `SLICE_X21Y73/A6LUT/O6` |
| wire | prjxray **node** name, from `NodeModel`'s rule (`specific_node_wires`, then `node_pattern_wires`, else the node's first `TILE/WIRE`) | `INT_L_X16Y79/NR1BEG0` |
| pip | prjxray tile pip `TILE.DST.SRC`, the FASM feature string (`pipnames.tsv` maps the ROUTING form to it) | `INT_L_X16Y80.IMUX_L47.NN2END0` |
| site pin | `SITEWIRE/<site>/<physical site pin>` | `SITEWIRE/SLICE_X22Y80/D5` |

`ROUTING` on every net uses nextpnr's grammar exactly
(`dst;src->dst;1` triples). A delay calculator that reads nextpnr's ROUTING
therefore reads the board's route the same way, and so does `gen.py`'s
`GLS_SCATTER_MODE=wire`. One difference: a LUT sink here is the PHYSICAL pin
the bits use (`D5`). nextpnr writes the pre-permutation cell pin through a
pseudo pip (`CLBLL_LL_D5->SITEWIRE/.../D1`).

**SDF onto this netlist.** Any SDF keyed by nextpnr cell names (nextpnr's own,
or F1's `xray_delay.py`, which uses nextpnr's as its template) goes through
`fasm2net.py --names ROUTED.json --sdf THAT.sdf`:

* Cell arcs move to the cell on the same bel.
* Each INTERCONNECT is keyed by its sink bel/pin, and its source is rewritten
  to the bits' driver.
* The text of the delay triple is kept verbatim, so `GLS_SDF_FIELD`
  min/typ/max still works.
* A sink the SDF has no arc for gets 0 ps. On gcd_hw these are the 16k pins
  nextpnr left unconnected, which the bits tie to a constant.

For per-pip delays, F1 can emit them keyed by `TILE.DST.SRC` and sum along
`routes.tsv`, which gives each sink's pip path from driver to sink.

## Results on gcd_hw (R5 + fast fall, nextpnr 9c732bc6303458df)

See `research/data/fid/f2_gcd_hw.md`.

## What this does NOT show

* **Delay.** The delays are nextpnr's, re-keyed. A right netlist with wrong
  delays is still not the board (F1).
* **Only what prjxray-db decodes.**
  - A bit the db does not know is invisible.
  - A feature with an all-zero encoding (`PRECYINIT.C0`, a BUFGCTRL input mux's
    default) reads as configured whenever the tile is in use. That is how the
    hardware behaves, and bit2fasm prints it.
  - The db's semantics (`default`/`always` ppips, the FASM `_Y0` = upper-site
    convention for IOB/OLOGIC) are trusted, not measured.
* **The site models are this script's reading of the slice.** They were
  cross-read against f4pga-xc-fasm2bels's `clb_models.py` and checked here only
  by agreement with nextpnr's JSON on one design. A shared misreading (for
  example F7AMUX input order) would be invisible to `fasm_equiv.py`.
* **A subset.** DSP configurations of `dsp_model.py` only (combinational, and registered A/B/C/M/P with nominal clock-to-out timing; the pre-adder with D and the B cascade combinationally, the D route on the assumption above); latches checked only on a three-latch
  test design (`research/data/fid/f2_phase2.md`); LUTRAM, async flops and
  BRAM other than bd_mem's RAMB18E1 are refused.
* **The RAMB18E1 is a model, not a measurement.** Its behaviour is UG473's for
  the one decoded configuration; its clock-to-out and setup/hold windows are
  prjxray-db's (sign-off bounds, the upper half's windows applied to both
  halves); none of it has been checked against the board. The model goes X on
  a violation instead of resolving metastably (GLS_FID's flops resolve), which
  is the pessimistic side for a gate. Byte writes (WEA bits that disagree)
  and a live port B are not modelled (X, and refused, respectively).
