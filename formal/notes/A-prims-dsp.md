# A-prims-dsp: digital semantics of DSP48E1 as ipow uses it

Probe PrimsDSP, shard A, session 2026-10-29. North-star goal 1 ("DSP48E1 ... if a design uses them").

STATUS: DONE (2026-10-29). `formal/check.sh Formal/Core/Prims/Xray.lean Formal/Core/Prims/DspData.lean
Formal/Core/Prims/Dsp.lean Formal/Core/Prims/DspTimed.lean` -> `[audit] 700 declarations checked`,
`[check] OK` (Xray is PrimsComb's, listed only so DspData's import has an olean; not edited).
Lean core only, no Mathlib, no bv_decide/native_decide. Only warnings: deprecated `if_pos`/`if_neg`.

## 1. Census: how ipow uses the DSP48E1

Source: a routed ipow build on disk, `/root/k3src_ipow/cells/build/hw/ipow_hw/` (probe K3's
build of `cells/hw/ipow_hw`, toolchain.txt: nextpnr 9c732bc6303458df, all 9 patch fingerprints
ok; files `ipow_hw.json` (yosys), `ipow_hw_routed.json`, `ipow_hw.sdf`). The kernel module is
bdc's `ipow_kernel.v`; the soak build of C-10n (6 DSP48E1) is not on disk, but it is the same
kernel through the same `synth_xilinx` (BD_DSP=1), and C-10n also reports 6 DSPs. Scripts:
`/tmp/claude-0/.../scratchpad/PrimsDSP/{dsp.py,trace.py,full.py,eff.py}` (read-only parsers).

- Two multiplies, `ipow_kernel.v:220` (`w_n36 = e0_data * e1_data`, the `b*b`/`r*b` operator
  whose request is `bd_delay_gated #(.N(DELAY))` of the join) and `:277` (`e3_data * e4_data`
  inside the select). Each is THREE cascaded DSP48E1 (yosys `mul2dsp`, 17-bit unsigned
  slices); placed in adjacent sites (DSP48_X0Y10/11/12 and X0Y26/27/28).
- Every cell: **all pipeline registers 0** (AREG ACASCREG BREG BCASCREG CREG MREG PREG ADREG
  DREG INMODEREG OPMODEREG ALUMODEREG CARRYINREG CARRYINSELREG; also in the routed JSON),
  INMODE 00000, ALUMODE 0000, CARRYINSEL 000, CARRYIN 0, C = D = 0, USE_MULT MULTIPLY,
  USE_DPORT FALSE, USE_SIMD ONE48, B_INPUT DIRECT. So ipow's DSPs are **combinational
  multiply-add only**; no registered stage is used (nothing for the Seq-style relations).
- Per multiply (a = e0, b = e1; same for e3/e4):

| cell | A | B | OPMODE[6:0] | Z | output used |
|---|---|---|---|---|---|
| head `sliceA[0].sliceB[0]` | a[16:0] (A[29:17]=0) | b[16:0] (B[17]=0) | 0000101 | 0 | P[16:0] = y[16:0], PCOUT, ACOUT |
| mid `sliceA[0].mul_sliceB_last` | A=0, A_INPUT=CASCADE, ACIN = head ACOUT | b[31:17] (B[17:15]=0) | 1010101 | PCIN>>>17 (head PCOUT) | PCOUT |
| tail `sliceA.last.sliceB[0]` | a[31:17] (A[29:15]=0) | b[16:0] | 0010101 | PCIN (mid PCOUT) | P[14:0] = y[31:17] |

  This matches flow.sh's own decode ("Z=000 at the head, Z=101 in the middle, Z=001 at the
  tail") and research's GLS model (`DSP48E1_DSP48E1`, ZMUX 0/5/1).
- Routed-JSON control pins: OPMODE[5:0] are constant nets XOR `IS_*_INVERTED` and agree with
  the yosys values; OPMODE6, INMODE*, ALUMODE[3:2], CARRYINSEL2 are unconnected tile-constant
  pins whose meaning depends on the const-pin patch (`patches/nextpnr-xilinx-dsp-constpins.patch`).
  I did not decode those myself; that the bitstream holds the yosys configuration is
  **H_FASM_DSP** (flow.sh runs `verify/fasm_audit.py` on every build: every DSP48E1
  register/const-pin bit read back from the FASM; the board ran ipow_ps 516/516 after the
  patch, flow.sh comment). Not re-run here.

## 2. Files

| file | what |
|---|---|
| `Formal/Core/Prims/Dsp.lean` | config record + the three ipow cells, UG479 function of the mode, cascade = C multiply, bit-level X models |
| `Formal/Core/Prims/DspData.lean` | GENERATED: prjxray-db DSP arcs (fast/slow corners) + nextpnr routed-SDF values |
| `Formal/Core/Prims/DspTimed.lean` | lumped bounded-delay stage, tightness/glitch witnesses, cascade settle theorem, bundled-data reading, numbers, non-vacuity |
| `Wip/PrimsDSP/dsp2lean.py` | the generator (+ `--check`) |

Data: prjxray-db `zynq7/timings/DSP_L.sdf` (= `DSP_R.sdf`, byte-identical) sha256
3f9923d175379d32f859a8d3e07992c0174cabe3b260c14b69394009fa1d0569, the toolchain copy
`~/dev2/lib/fpgatoolchain/openxc7/share/nextpnr/prjxray-db` (its slicel.sdf has the same sha as
the master copy PrimsComb used). Cell types used: `DSP48E1_AREG_0_A_INPUT_{DIRECT,CASCADE}_MREG_0_PREG_0_USE_DPORT_FALSE_USE_MULT_MULTIPLY`,
`DSP48E1_BREG_0_B_INPUT_DIRECT_MREG_0_PREG_0_USE_MULT_MULTIPLY`, `DSP48E1_PREG_0` (PCIN),
`DSP48E1_ACASCREG_0_A_INPUT_{DIRECT,CASCADE}` (ACOUT).

    python3 -I formal/lean/Wip/PrimsDSP/dsp2lean.py \
      ~/dev2/lib/fpgatoolchain/openxc7/share/nextpnr/prjxray-db/zynq7/timings \
      /root/k3src_ipow/cells/build/hw/ipow_hw/ipow_hw.sdf \
      formal/lean/Formal/Core/Prims/DspData.lean [--check]

| arc (ps) | fast min..max | slow min..max | nextpnr SDF |
|---|---|---|---|
| A→P | 609..1642 | 1391..3841 | 5400 |
| A→PCOUT | 631..1725 | 1434..4036 | 5400 |
| A→ACOUT | 219..303 | 473..723 | 5400 |
| ACIN→PCOUT | 543..1608 | 1278..3833 | 5200 |
| B→P | 571..1575 | 1310..3656 | 3850 |
| B→PCOUT | 593..1658 | 1354..3851 | 3850 |
| PCIN→P | 246..633 | 567..1518 | 1710 |
| PCIN→PCOUT | 267..716 | 611..1713 | 1710 |

## 3. What is proved (plain language)

**Configuration (Dsp.lean).** `ipow_cells_supported`, `ipow_cells_zsel`: the three transcribed
cells are in the modelled set and decode to Z = 0 / PCIN>>>17 / PCIN. `ug479_default_registered`:
a cell on UG479 defaults (registers = 1) is registered, so mapping a missing register attribute
to 0 (audit row on research d4896fe, item b) changes the class. The transcription from the
netlist to the Lean record is by hand (13 fields, in the table above).

**Function = C multiply (Dsp.lean).** Assumed: the UG479 function of this mode,
`P = PCOUT = (Z + signed(A[24:0])·signed(B[17:0])) mod 2^48`, ACOUT = A or ACIN (H_DSP_UG479;
the same expression as research's GLS g_mult branch, which the audit CONFIRMED against yosys
cells_sim on 92 configs). Proved: `ipowMul_eq`: the cascade wired as in the table computes
`(a·b) mod 2^32` for ALL naturals a, b (algebra, not enumeration). `(a*b) % 2^w` is textually
shard C's `Formal.Net.GcdHw.Ops.muli` (GcdHwLib.lean:37) at w = 32, i.e. MLIR `arith.muli` i32
(wrap-around), the kernel's `r * b` and `b * b`. Concrete checks `ipowMul_examples` (3^7 path,
0xFFFFFFFF², 1·0xFFFFFFFF, 2^16·2^16 = 0 mod 2^32), expected values from C arithmetic.

**X propagation (Dsp.lean §4).** Over Core's K3.
- `coarse` (any X input bit ⇒ every output bit X) is a monotone Kleene extension
  (`coarse_ext`), sound against every Boolean resolution (`coarse_sound`), and below EVERY
  monotone extension (`coarse_le_ext`): so it is sound for any gate network that computes the
  function, whatever the DSP's internal structure. `poison` + `coarse_greatest`: nothing more
  defined is sound for all realisations (adding `x_i xor x_i` to any network keeps the
  function and makes every output X when `x_i` is X).
- `lowBits_sound` / `lowK_sound`: "bit j of (a·b) mod 2^32 is defined when bits 0..j of both
  operands are" is sound against every Boolean resolution (the function's exact extension).
- `booth_breaks_lowBits`: a radix-4 Booth partial-product cell computes bit 0 = a0·b0 as
  `((b0·a0) xor b1) xor b1` (`boothBit0`, a monotone extension: `boothBit0_bool`,
  `boothBit0_mono`), which is X when b1 = X although bit 0 never depends on b1. The DSP48E1
  multiplier is Booth-based (UG479: two partial products), so the low-bit model needs the
  named hypothesis **H_DSP_LOWBITS**; `coarse` needs none. Recommendation for X audits: use
  `coarse` for DSP outputs.

**Timing (DspTimed.lean).** Model **H_DSP_LUMPED**: each DSP output port is a lumped
bounded-delay stage: at time t it equals f(v) whenever every input port i has held the defined
word v_i throughout [t − hi_i, t − lo_i], with (lo_i, hi_i) the prjxray band of that port pair
at ONE corner; at all other times it may be anything (wrong words, X, any number of glitches).
`transport_lumped`: per-port transport within the bands is one behaviour (the model is weaker).
- `lumped_admits_anything`, `lumped_tight`: inside the window ANY behaviour is admitted (X, or a
  defined word that is neither the old nor the new result), so a sample at T0 + hi − 1 is not
  guaranteed: the bound cannot be shortened in this model.
- `ipow_mul_settles`: for ANY arc table and cascade-wire window: operand slices constant at the
  DSP pins on [T0, T1] ⇒ at every t in [T0 + settleHi, T1 + settleLo] the head-P and tail-P ports
  carry defined words whose bundled 32-bit output is `muli32 va vb`. settleHi is the max over
  the 9 pin-to-output paths of the summed arc maxima (per path), settleLo the min of the summed
  minima. `ipow_bundled`: a request sampling dreq after the pin arrival reads the product if
  dreq ≥ settleHi and the operands are held until T0 + dreq − settleLo.
- `settle_px` (cascade wires 0): **settleHi = 7267 ps slow / 3074 ps fast**, settleLo = 1310 /
  571 ps. The critical path is a[16:0] → head A→PCOUT → mid PCIN→PCOUT → tail PCIN→P
  (4036 + 1713 + 1518 slow). A per-cell lumping (hull of each cell's arcs) would give 11728 ps
  slow (hand arithmetic, not in Lean), so the per-path bound matters.
- `settle_np`: with nextpnr's routed-SDF values the same paths give 12310 ps (its A→ACOUT is
  5400 ps against prjxray's ≤ 723). `nextpnr_vs_prjxray`: the nextpnr SDF is ABOVE prjxray's
  slow max on 6 arcs and BELOW it on two (B→PCOUT 3850 < 3851, PCIN→PCOUT 1710 < 1713): the SDF
  is not an upper bound arc by arc (by 1 and 3 ps; it is far above on the critical path).
- `ipow_mul_nonvacuous`: constant signals satisfy every hypothesis of `ipow_mul_settles` at the
  slow corner with a non-empty sampling interval (degenerate: shows consistency only).

What bundled data then requires of ipow's `umuli`: the request (bd_delay_gated chain) must
arrive at the capture latch no earlier than (latest operand arrival at the DSP pins) + 7267 ps
(slow corner, prjxray, cascade wires 0) + (P→capture route max) + capture setup, under one
consistent corner. compute.py's routed peaks (14295–16785 ps data arrival) include the fabric
routes; this is the DSP-internal part only.

## Negative controls
- `dsp2lean.py --check` passes on the real SDFs and reports DRIFT (exit 1) after one number is
  mutated (DSP_L/R PCIN→P slow max 1.518 → 1.418 ns, copy in scratchpad/PrimsDSP/mut). That
  mutation would change `settle_px`'s 7267 to 7167, so the Lean theorem would fail; the Lean side
  of the control was NOT run (needs a rebuild against the mutated data).
- `lumped_tight` and `booth_breaks_lowBits` are proved negative results; `ug479_default_registered`
  shows `Cfg.supported` can be false.

## 4. NOT modelled / hypotheses
- H_FASM_DSP (bitstream = yosys config), H_DSP_UG479 (function), H_DSP_LUMPED (timing),
  H_DSP_LOWBITS (only if the sharper X model is used).
- Cascade wire delay PCOUT→PCIN, ACOUT→ACIN: a parameter `cw`, 0 in the numbers (prjxray-db's
  DSP tile has no separate arc for it; nextpnr routes it as a dedicated wire). Not measured.
- Fabric routes into A/B and out of P: compose with `Lumped.constOn`; not instantiated here
  (needs the routed per-pin bands, C's front end has no DSP model: C-10n's 77,778 fallback arcs).
- Corner correlation (κ): each window is independent; the numbers use one corner throughout.
- Signed operands, other OPMODE/ALUMODE/INMODE, CARRYOUT, pattern detect, registered modes
  (unused by any design here; `cells/hw/mult_ps.v` uses AREG=1 but is a board test only).
- Internal X shorter than the window, pulse filtering, analogue behaviour of a mid-rail input.
- The prjxray numbers themselves (database values, not measured here).
- Whether nextpnr's lower values on two arcs matter: only if a check uses the SDF as an upper
  bound on those arcs alone (they are not on the critical path).

## 5. For the lead
- Add `Formal.Core.Prims.DspData`, `Formal.Core.Prims.Dsp`, `Formal.Core.Prims.DspTimed` to
  Formal.lean (they import only Core.Kleene and Core.Prims.Xray).
- Shard C: (a) `muli32 = Formal.Net.GcdHw.Ops.muli 32` is `rfl` (not stated in Lean to avoid an
  upward import); (b) the tcheck front end could take DSP arcs from `DspData` and the per-path
  composition of `ipow_mul_settles` instead of the SDF fallback; (c) B's IpowCells
  H_DATA_COMB (muli as zero-time function) can be discharged at the data level by
  `ipow_mul_settles` + a request bound.
- Suggested next probe: instantiate the routes: per-pin prjxray bands from ipow's routed JSON
  into A/B and out of P[16:0]/P[14:0], giving the full bundled-data margin of umuli0/umuli1
  against the routed bd_delay_gated chain, at both corners, 4 seeds.
