# A-fid3: the formal model against the research board-fidelity GLS, per primitive

Probe Fid3, shard A, session 2026-10-29. PROGRAM.md "The model must be gate-fidelity":
compare the model with the board-fidelity GLS on `claude/research` (read-only); where they
disagree, find out which is wrong; FEASIBILITY must grade every primitive.

STATUS: done (no Lean in this probe; every result below is an iverilog or Python/Float
experiment, not a theorem).

- **Research tip under test:** `origin/claude/research` **6524fa3** (2026-10-29). Sources were
  copied read-only with `git archive origin/claude/research cells/gls | tar -x` into
  `formal/tools-A/glsdiff3/run-1029/src/` (pruned to the files used). `prims.v` md5
  3e7423cb… (changed since 350f9be: 78de9c2 CARRY4/LATX transport, 923305d SLICE_FFX pins,
  666ea57 SETUPHOLD reader); `fid_core.vh` md5 2422ccea… (**unchanged** since 5567170).
- **Reproduce everything:** `sh formal/tools-A/glsdiff3/run-1029/run.sh` (about 4 min, iverilog 12,
  `-gspecify`, the flags of `cells/gls/build.sh`). It writes `out/suite.log` (the glsdiff suite,
  compare with `../out/run.log` = 350f9be and `../out/ref_5d535d7.log`), `out/f3.log` (research's
  own `fid/f3/run_f3.sh` on the same sources) and `out/extra.log` (this session's E1-E7). The
  compiled `.vvp` files and the work dir are deleted at the end; the stale tracked
  `glsdiff3/out/work/*.vvp` of the 2026-10-28 run were deleted too.
- **Proposed patches** (tested here, for the research branch; nothing in `cells/` was touched):
  `run-1029/patch/fid_core_centre.diff` (FID_RESOLVE centre) and `run-1029/patch/prims_x.diff`
  (flop and latch X semantics).

## 1. What changed since the last compare (350f9be, A-gls-compare-2 / FOR-RESEARCH §6-8)

| earlier finding | status at 6524fa3 | evidence (run-1029/out) |
|---|---|---|
| CARRY4 early edge under fid (O0 rises 23 ps after its cause through a 223 ps arc) | **FIXED** (78de9c2): per-(pin, output) transport | `tb_carry_saf`: O0 1223 / 1233 / 1423 (the acceptance values of FOR-RESEARCH §6). E1: 7 live pins, all 8 outputs, random arcs: **60/60** traces exact against the UG474 equations on per-arc-delayed pins (1039 reference edges); default model 2/60 (the check can fail) |
| SLICE_LATX early edge under fid | **FIXED** (78de9c2): per-pin transport, then the latch function | `tb_carry_saf`: LQ 3100 / 3110 / 3160 |
| SLICE_FFX pins sample-at-fire | **FIXED under fid** (923305d): CK/D/CE/SR transport, CK min-pulse-width law, SR in the aperture, BUFGCTRL transport | research `tb_f3_ff` PASS (fid) / FAIL (default) |
| default model SAF on every specify path | unchanged (by design; fid is opt-in) | suite `def`: 1-pin SAF 60/60, per-pin transport 14/60 |
| latch X pessimism (closed latch with CE = x goes x; CLR = x with D = q = SRVAL goes x) | **NOT fixed**, default and fid | `tb_seq_x` L1-L3 = x (Lean `LDCE_INIT`: 0) |
| flop X-as-0 on SR and CE (an x SR or CE is read as 0) | **NOT fixed**, default and fid. Research's new `tb_f3_kleene_ff` now *requires* fid = default on settled values, and its negative control is "x CE loads D", so the X-hiding behaviour is codified as correct | `tb_seq_x` F1, F2 = 1 (Lean FDRE_M/FFQ_SYNC: X) |
| FID_RESOLVE decides at TLOOP − WIN/2 | **NOT changed** (`fid_core.vh` unchanged) | 50% point 349 ps at TLOOP 424 (as before), 549 at TLOOP 624, 399 with WIN 50 (E2): the rule is exactly TLOOP − WIN/2 |
| GLS_SCATTER(_REGION) unbounded Gaussians | unchanged (`gen.py` 460/486/523) | code reading |
| LUT/MUXF Kleene X = Core `kevalSpec` | still equal | 43,767/43,767 (default and fid) |
| LUT per-pin transport under fid | still equal | 1-pin transport 60/60, XOR per-pin 60/60 |

## 2. Per-primitive fidelity table (for FEASIBILITY "Fidelity per primitive")

Grades: **A** = agrees with silicon by a measurement on this part or a vendor document that
fixes the behaviour; **B** = follows the documented structure or a faithful physical model, not
measured on this part; **C** = a stated assumption with no source, or known to be wrong.
"formal / GLS" grades are given separately where they differ.

| primitive | formal model (Lean) | research GLS (6524fa3, `GLS_MODEL=fid`) | silicon: what is known (source) | grade formal / GLS | test that would settle it |
|---|---|---|---|---|---|
| **LUT function and X** | Kleene mux tree from INIT, A6 at the root (`Core/LutTree`, `Lut.keval = kevalSpec`); hypothesis `H_mux_kleene` (a mid-rail select with equal data passes the data) | `?:` mux tree on the delayed pins (leaf-first; the order does not change values). Equal to Lean on 43,767/43,767 vectors | Structure: LUT6 = two LUT5 + A6 mux (UG474). Single-input change does not glitch (P. Alfke, comp.arch.fpga, informal, not a datasheet). Mid-rail select behaviour: no source | B / B (same model) | board: masked-pin toggle into a fabric edge counter (A-fidelity); SPICE of a pass-gate mux leaf |
| **LUT per-pin arcs** | per-pin bounded transport `[lo, hi]` then the zero-time function (`Events2Pin`, `Pure.Chan`) | per-pin transport, one SDF point per pin (`FID_LUT6`), 1 ps output sampler; `+FID_LEVEL_PS` for internal skew (default 0) | prjxray LUT arcs are flat per output; pin dependence is in site-pin delays (A-fidelity). Internal tree skew: unknown | B / B. GLS = one point of Lean's band (60/60 + 60/60) | per-pin delay ring (A-fidelity) |
| **LUT glitch / runt** | transport passes every pulse; inertial and involution channels are available (`Delay/{Inertial,Involution}`); which one is silicon is a hypothesis | every pulse ≥ 1 ps passes (transport) | no 7-series LUT pulse-rejection figure found (research f3_model.md, A-fidelity: estimated 15-50 ps from R·C, not measured) | B / B: transport is the hazard-pessimistic side; it is optimistic only for a proof that needs a narrow pulse to die | pulse-shrink experiment: XOR with a k-LUT-delayed copy into N hops and a toggle counter (A-fidelity R1) |
| **routing, buffered pips** | `Fidelity.DelayBound` per sink arc [FAST_MIN, SLOW_MAX]; Elmore `rcBound` with κ; shared corner + scatter \|ε\| ≤ κ (`Corner.lean`) | `fid/xray_delay.py`: prjxray `timing.py` RC tree (Buffer per buffered pip, Elmore over the downstream subtree, site-pin delays, fanout C). Transport ICBUF per sink. One SDF column (or `band` = one shared lerp) per run | all 3737 INT_L pips are `is_pass_transistor = 0` (A-fidelity scan of prjxray-db). prjxray's model is ±1.5% from Vivado (not silicon). Board: n=128 ring periods fall inside the summed bands (FEASIBILITY) | B / B for the band. GLS **scatter is unbounded Gaussian**, outside every κ-bounded theorem (FOR-RESEARCH §8, unchanged) | already partly done (ring periods); per-wire scatter from more rings |
| **routing, pass-transistor pips** | zero-delay alias (`H_alias`) | `PassTransistor(R)` in the RC tree (the only ones are fixed CLB site-pin aliases with `delay=null`, `res=0`) | prjxray-db: pass-transistor pips exist only as fixed tile-wire→site-pin aliases on this part (A-fidelity R2) | B / B (agree) | not separately observable |
| **MUXF7/F8** | `kmux` (Kleene), settle within hi; `H_muxf_kleene` for S toggles with D0 = D1 | `FID_MUX2`: per-pin transport, Kleene `?:` | structure per UG474; S-toggle with equal data: no source | B / B | board: D0 = D1 = 1, toggle S at ring rate, count OUT falls (expect 0) (A-fidelity M1) |
| **CARRY4** | Gen/Netlist: UG474 MUXCY/XORCY equations gate by gate, Kleene; band per arc | **per-(pin, output) transport, then the same equations** (78de9c2). E1: 60/60 exact on multi-pin random traces | MUXCY/XORCY structure (UG474); arcs per (pin, site output) from prjxray SDF. Note CARRY4 is read-once (each pin has one path to each output), so per-(pin, output) transport is what a transport cascade gives; the SDF arcs need not be additive (they end at site pins) | B / B (now agree; was GLS C) | carry-chain TDC style: launch an edge into CIN/S, sample the CO taps (standard TDC papers) |
| **FF (FDRE/FDSE) function and X** | master-slave Kleene tables `FDRE_M`, `FFQ_SYNC` (Gen/Netlist; PrimsSeq probe in progress) | `if (SR)` / `if (CE)` (default), `sr === 1` / `if (ce)` (fid): **x on SR or CE is read as 0** | an x (mid-rail or unknown) SR/CE gives an unknown next state; nothing documents a definite value | B / **C** (GLS wrong, optimistic: hides X). Fix tested: `patch/prims_x.diff` | `run-1029/run.sh` E7: F1, F2 must print x |
| **FF timing (CK→Q, setup/hold, aperture, min pulse width)** | named hypotheses only (`H_HK_STA`, rig `idx_setup`); no aperture or metastability model in Core | transport CK→Q; SDF SETUPHOLD aperture (negative SETUPHOLDs read since 666ea57) with an old/new choice and t_r = TAU_FF·ln(ap/2\|δ\|), TAU_FF = 75 ps; CK min pulse width TMPW 70 ± 20 ps | SETUPHOLD per pin in prjxray-db (Vivado numbers). Flop τ: Beer et al. ASYNC 2010, 57/51/73 ps at 130/90/65 nm; no 28 nm figure. Min pulse width: none found in prjxray-db (research could not read DS187) | B (timing as hypotheses) / C (TAU_FF, TMPW assumed) | hw/arb_mtbf-style synchroniser sweep (MMCM fine phase shift) for TAU_FF; CK runt sweep for TMPW |
| **latch (SLICE_LATX, LDCE/LDPE)** | `LDCE_INIT` via `Lut.keval` | per-pin transport (78de9c2); **X pessimistic** (closed + CE = x → x; CLR = x → x even when the result is SRVAL); no metastability at gate close (stated) | UG474: latch-mode storage element, gate on CK, enable CE, async SR. **No design uses LDCE/LDPE**: `bd_latch` stores on LUTs (cells/rtl/bd_latch.v header) | B / C (pessimistic, harmless today). Fix tested: `patch/prims_x.diff` | E7: L1-L3 must print 0 |
| **LUT state loop: C-element, LUT latch, arbiter q** (metastability) | B: `ArbInvolution` (`stF_runt`), `CElemInvolution.orb`; proved: a critical runt s* exists in (δ∞ − δ(0), δ∞) (`arb_eternal`). Float orbit (§3): s* = 0.50-0.58·TLOOP, deterministic either side; near s* the loop **circulates a pulse train** and resolves with TAU_eff ≈ 1.2-17·TLOOP | `FID_RESOLVE` on self-loop LUTs (gen.py): runt p < TLOOP decided at **TLOOP − WIN/2** (349 of 424 ps), N(0, WIN/4) noise, t_r = TAU·ln(WIN/2\|δ\|), TAU = WIN = 150 ps (assumption). During resolution the node **holds a clean value** (default) or x (`+META_X=1`); one runt reaches fanout, echoes ignored. Multi-cell loops get no resolver | none measured. Without the resolver (`+META_OFF=1`) the GLS's own transport loop circulates the runt forever with period TLOOP (E4: Q 1124↑ 1473↓ 1548↑ 1897↓ …), i.e. the echo is physical and the "rejection" is a modelling choice | B (Lean channel family, unmeasured) / **C** (centre has no derivation; TAU optimistic under involution; clean hold hides the pulse train) | **hw/arb_mtbf**: sweep the r1→r2 skew (MMCM fine phase or IDELAYE2 taps) and record P(r1 wins): the 50% point is at TLOOP/2 (involution) or TLOOP − WIN/2 (GLS), 137 ps apart at TLOOP 424; count q toggles per race with a ripple counter (train vs single runt); resolution-time histogram for TAU |
| **BUFGCTRL** | not modelled (clock only in rigs) | transport I0→O (fid) | no BUFG min pulse width in prjxray-db | — / B | — |
| **DSP48E1** | not modelled | combinational and registered modes; still iverilog module paths (SAF) | — | — / C (SAF) | only if a design's bundled cone runs through a DSP |

## 3. FID_RESOLVE: which decision point is right, and a justification for the threshold

**Plain statement.** Assumed: a LUT self-loop (q fed back to its own pin, loop delay TLOOP =
feedback wire + that pin's arc, gen.py's rule), a set pulse ("runt") of width s on the other
input, rise delay = fall delay (prjxray has no rise/fall split). Question: for which s does the
loop latch?

**The GLS's rule.** `delta = p − (TLOOP − WIN/2) + N(0, WIN/4)`: the 50% point is TLOOP − WIN/2,
measured at 349 (TLOOP 424), 549 (TLOOP 624) and 399 (WIN 50) ps (E2). The research rationale
(f3_model.md §2) is "the drive was removed before the loop could commit", i.e. the feedback must
arrive before the drive leaves. That is the right condition only if the runt's echo dies. It does
not: in the GLS's own transport loop with the resolver off, the runt circulates with period
TLOOP, high for s and low for TLOOP − s (E4, `+META_OFF=1`). A 200-400 ps pulse is several times the LUT arc
(45-124 ps in prjxray) and the estimated pip rejection width (15-50 ps, A-fidelity R1), so nothing
in the data suggests the echo is filtered (an inference, not a measurement). The decision is made by the duty cycle of the circulating pulse, not by the first
lap.

**Derivation of the centre.**
1. Symmetry (exact for any channel with δ↑ = δ↓): a circulating pattern "high s, low TLOOP − s"
   maps to "low s, high TLOOP − s" under 0/1 exchange. So if s grows lap by lap, TLOOP − s shrinks,
   and s = TLOOP/2 is the fixed point between latching and dying.
2. Lean's involution OR loop (Float transcription of `CElemInvolution.orb` with the exp channel
   `expDelay`; `run-1029/py/orb_tau.py`, E6; a computation, not a theorem): s*/TLOOP =
   0.500 / 0.502 / 0.514 / 0.543 / 0.581 for τ = 40 / 60 / 100 / 150 / 200 ps at TLOOP 424, and
   0.500-0.534 at TLOOP 624. The upward drift comes from the first lap, which starts from a long
   low history. Outside ±1 ps of s* the outcome is deterministic.
3. Rise ≠ fall would shift the centre to TLOOP·δ↓/(δ↑+δ↓) (from the symmetry argument; not
   computed here). prjxray gives no split, so TLOOP/2 is the reading of the data.

**Proposed threshold justification for research** (the patch `run-1029/patch/fid_core_centre.diff`
adds `+META_CENTRE_PM=` in per-mille of TLOOP, default 500; `-1` restores the old rule exactly,
E3):
- **Centre** CEN = TLOOP/2, with the stated band [0.50, 0.58]·TLOOP from the involution family
  (τ ≤ 200 ps). Measured with the patch: 50% at 212 (TLOOP 424) and 312 (TLOOP 624) (E3).
- **WIN** stays a noise and model-uncertainty width (assumption). Covering the band above needs
  WIN ≥ 0.08·TLOOP (34 ps at 424), which the default 150 ps does.
- **TAU is not on the pessimistic side under the involution model.** Near s* the orbit resolves
  with t_r ≈ TAU_eff·ln(1/|s − s*|), where TAU_eff = 503 / 799 / 1741 / 7242 ps for τ = 200 / 150 / 100 / 60
  (1.2-17 × TLOOP). That is because the per-lap gain is the slope δ′ of the channel at a pulse of
  about TLOOP/2, which is small when the pulse is wide compared with the slew. Real noise
  (lap-to-lap jitter) will shorten this, by an amount nobody has measured. Proposal: quote any
  fid MTBF number as "TAU = 150 ps assumed; the involution model gives ≥ 3× longer", or run with
  TAU = TLOOP as the pessimistic bracket.
- **During resolution, use `+META_X=1` for any run quoted as evidence.** The involution loop does
  not hold a value while it resolves. It emits a pulse train: 13-81 edges for |s − s*| from 30 down to
  0.01 ps at τ = 100 ps (E6), which fanout sees (for bd_arb: g1/g2 alternate while both requests are high).
  The GLS default holds a clean value, which hides the train. X covers it in Kleene semantics.
  Whether bd_arbiter's A0 hold tolerates the train is shard B's ArbInvolution question, not
  checked here.
- **Consequence for research's acceptance test.** `tb_f3_meta` A puts r2 360 ps after r1 and
  requires both winners. With the centre at TLOOP/2 it fails (r1 200/200, E5): the involution model
  says a request 360 ps late should lose every time. At DT = 212 the patched model passes (104/96).
  The unpatched model at DT = 212 gives r1 1/200, so the later request wins 199 times although it
  is half a loop late. The test's DT should be TLOOP/2 (or swept).

**Which is wrong.** Neither has a measurement. The GLS centre has no derivation, and it
contradicts the GLS's own transport loop behaviour (the echo circulates). The TLOOP/2 centre
follows from symmetry plus the Lean channel family. Grade: GLS **C**, formal **B**. The board
settles it (row "LUT state loop" in §2).

**Not covered here.** Loops through more than one cell (gen.py detects only self-loops). The C(r1, ~r2)
arbiter node is the same OR-loop shape as the runt test (its set term r1·~r2 is a runt of width
= the skew); `tb_f3_meta` uses the real bd_c2n INIT. Rise/fall asymmetry. Noise in the involution
orbit.

## 4. X semantics of flop and latch: the fix, tested

`run-1029/patch/prims_x.diff` (both models, about 40 changed lines):
- SLICE_FFX: next state `n0 = CE ? D : Q` (Verilog `?:` merges for x),
  then `SR===1 ? SRVAL : SR===0 ? n0 : (n0===SRVAL ? SRVAL : x)`. In fid this also replaces the
  clean-edge `else if (sr===1) … else if (ce)` path and the `nsf` used by the aperture and runt laws.
- SLICE_LATX: open (gate on, CE = 1) → D; closed (gate off **or** CE = 0) → hold; else merge;
  then the same SR merge.

Results (E7): `tb_seq_x` gives L1-L3 = 0 and F1, F2 = x in default and fid, the Lean values. The research
`run_f3.sh` on the patched prims.v passes every unit test and all three settled-value comparisons
(fid = default). It changes 408/3000 flop lines and 282/3000 CARRY4+latch lines of research's own
x-laden vectors (X-as-0 and latch pessimism were visible in them). Its negative-control `sed`
no longer matches (it reports WRONG); the retargeted mutation
`sed "/function nsf/,/endfunction/s/n0 = c ? dd : q;/n0 = (c !== 1'b0) ? dd : q;/"` is caught on
275/3000 lines.

## 5. Proposed updates to FOR-RESEARCH (the lead edits that file)

- §6: CARRY4 and SLICE_LATX now transport under fid (78de9c2): acceptance met (O0 1223/1233/1423,
  LQ 3100/3110/3160). Multi-pin CARRY4 60/60 (E1). DSP is still SAF. Mark the section FIXED for fid.
  The default build stays SAF.
- §7: still OPEN at 6524fa3, in both models. New: `tb_f3_kleene_ff` codifies the X-hiding flop.
  Give the tested diff `glsdiff3/run-1029/patch/prims_x.diff` and the retargeted mutation.
- §8: still OPEN. Replace the "Change" with `patch/fid_core_centre.diff` (`+META_CENTRE_PM`, default
  500), `tb_f3_meta` DT = TLOOP/2, the TAU caveat (involution TAU_eff ≥ 1.2·TLOOP), and
  "`+META_X=1` for evidence runs". Scatter is still unclipped.

## 6. What this does not show

- No Lean was written or checked. The involution numbers are a Float transcription of B's
  recurrence with A's exp channel (one lumped channel for LUT + wire), not a theorem.
  `arb_eternal`'s interval is the only proved statement.
- The research GLS was tested on unit testbenches, not on a routed design.
- "Silicon" entries are sources or estimates. Nothing here was measured on the board.
