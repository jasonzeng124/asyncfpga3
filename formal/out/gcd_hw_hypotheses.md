# gcd_hw: the hypotheses the end-to-end argument rests on

Draft. Shard A, 2026-10-27, written from the working tree at about 06:40 UTC. Sources: PROGRAM.md,
FEASIBILITY.md, the three journals, `formal/notes/*.md`, `formal/out/cell_constraints.{md,json}`, and
a grep of `formal/lean/Formal` for named hypotheses. No Lean was run and no route was rebuilt. Every
grade cites evidence that is already in the repo. Every name is quoted from the code or a note. A
hypothesis with no name in the sources is marked *(unnamed)*.

## 0. What is proved about gcd_hw today, and what is not

| id | result | status | what it covers |
|---|---|---|---|
| **R1** | `Formal.Net.GcdHw.Gcd.gcd_hw_graph_computes_gcd`, `gcd_hw_graph_live`, `_bounded`, `_no_infinite_run`, `_maximal` (`Formal/Net/GcdHwLive.lean:47,66,80,94,104`); `gcdC_nonneg31` (`GcdHwNat.lean:344`) | proved, core Lean | Token level only. Take the dataflow graph that bdc emits for gcd_hw, imported through bdc's own code (`formal/tools/dfimport/mlir2lean.py`, drift check `check.sh`). For 0 ≤ a, b < 2^31: every schedule and every control_merge arbitration ends with exactly `[Nat.gcd a b]` on `out0`; every partial run can be completed; all runs are bounded. No fairness hypothesis. |
| **R2** | `Formal.Timing.RtFbGcd.gcd{d,2,3,4}_{slowE,fastE}_safe` (`Formal/Timing/RtFbGcd.lean:52,91,130,169`) | proved per route (4 seeds) | RT_FB, the C-element own-feedback race, on every gcd_hw C-element whose response path survives the pruning. Assumes H_ONE_CORNER + H_RC_EXACT. |
| **R3** | `tcheck` verdicts on the 4 gcd_hw R5 routes (C-10e, C-10g, C-10h), each PASS by `Tcheck.verdict_sound` (`formal/tools/tcheck/Tcheck/Sound.lean:38`) | proved checker core; compiled executable; Python front end | Rules A, E, F, H, I and J, plus W (latch open width) and R (RT_FB), per instance. |
| **R4** | xaudit on gcd_hw R5 (`notes/A-xaudit-gcd.md`; engine `XAudit/Design.lean:197 noX_sound`) | verified engine; trusted parser and compiled code | One transaction (vector 1, a=7, b=0) for every delay in bands at most 2% wide and every power-up state. It does **not** certify at prjxray's one-corner widths (about 17%). |
| **R5** | `gcd_..._rd_ge3 : AllCyclesGe g 3` (`Wip/C9b/certs/`, checker `Net/RingCheck.lean:48`) | proved, but in `Wip/` (not claimed; 883 s) | Every cycle of bdc's ring graph for gcd has at least 3 storage stages. |

**The composition from R1 down to the circuit is not done.** Probe C-8l, the refinement of the
imported graph by the op cells with bdc's link placement, is in progress (`Wip/C8l/`), and nothing
from it is claimed. The pieces it would use are proved separately, but none of them is instantiated
on gcd_hw: `Ops.net_refines` (`Net/Ops.lean:272`), `OpsCM.amerge_op`/`amerge_forced` (`OpsCM.lean:278,359`),
`EndToEnd2.end_to_end2` (`EndToEnd2.lean:328`), `HandshakeLive`, `Ring`/`Bridge`, and B's cell
theorems (`cell_constraints.json`, 87 entries). Three of the cells gcd_hw instantiates have no model
of any kind: `bdc_muxn3_32`, the `bdc_amerge3_0` arbiter cascade, and the 20 yosys-inferred
`bdc_fused_*` datapaths (B-gcd-cells §3, §4).

**Column "gcd"** in the tables below:
- **now**: a result in R1-R4 depends on the hypothesis today.
- **cap**: the capstone composition needs it, and it is a hypothesis of a proved theorem that is not
  yet applied to gcd_hw.
- **other**: only cells or designs that gcd_hw does not use (with the reason).

**Grades** follow the fidelity table:
- **A**: established by documentation or by a measurement in the repo.
- **B**: credible, but untested.
- **C**: doubtful, or contradicted by evidence. The evidence is named.

## 1. Silicon primitives

| # | name (where) | plain statement | used by | grade | test | gcd |
|---|---|---|---|---|---|---|
| S1 | **H_KLEENE_LUT** (`Cells/Prelim.lean:9`, per mux `:35`; `Cells/MuxTree.lean:172`) = **H_mux_kleene** + **H_sram** (`Core/LutTree.lean:279`, `:272`) | Each 2:1 mux of the LUT tree is a Kleene mux: a valid select passes its leg, and a mid-rail select with equal, valid legs passes that value with no dip. SRAM leaves are static. This gives the closure semantics `Lut.keval` for any tree order. | ArbKleene, TernarySound/Exact/OnBits, LutAudit, Env/EnvFast hazard notion, C's Fasm `lutK`, XSim and the xaudit engine (every LUT is `Lut.keval`) | **B**. High for clean or late select edges. Low or unknown for a mid-rail select while equal legs move, because an NMOS-only tree can fail there (B-muxtree-fidelity §5). | Board glitch counter: a LUT with O6 independent of the toggled pin drives a ripple counter, A1 vs A6, about 1e10 toggles, expect 0 (A-lut-tree, B-muxtree §5 exp. 1). Metastable select from `bd_arb` grants on the arb_mtbf rig (`cells/hw/arb_mtbf_measure.py`), with legs static and legs rising (exp. 2). The GLS cannot test it: `SLICE_LUTX` is Kleene by construction. | now (R4), cap |
| S2 | **H_LUT62_SHARED_READ** (`Cells/TernaryOnBits2.lean:325` `SiteSync`; `ArbOverlapRace` `Decomp`) | O5 and O6 of one LUT6_2 read a shared pin A1..A5 at the same instant: one input buffer per pin, and the skew inside the tree is ignored. | Grant and overlap results that cancel q's route (bd_arbiter `ugrant`/`ustate`); bd_latch W=32 pairs; bd_steer; bd_datamux pairs | **B** (UG474 has one buffer per pin; the skew is not measured) | Board: a LUT6_2 with O5 = f(A3) and O6 = g(A3), both captured on a CARRY4 tapped delay line; measure the O5/O6 skew on one A3 edge. | cap (38 steers, 129×16 latch pairs, 9 arbiters) |
| S3 | **H_LUT_FIFO** (`Cells/OpsTimedMux.lean:207`; `Cells/FifoFidelity.lean:5`), **H_PIN_FIFO** (`Cells/ConstraintsSel.lean:206`), **H_TREE_FIFO** (`:211`), **H_WIRE_FIFO** (`Cells/OpsTimed.lean:13`), **H_LINE_FIFO** (`OpsTimedMux.lean:477`) | A LUT, each of its pin paths, a wire and a delay line are each an order-preserving (FIFO) read of their input. A single pin edge that leaves the function unchanged gives no output edge. | B's timed cell theorems: PipeTimed(N), OpsTimed*, ConstraintsSel, GcdCells, FifoFidelity | **B** (JSON: "fidelity grade B"). It is stronger than `Win`, which allows overtaking (see contradiction X1). | Board: LOCK_PINS with the feedback on A1 and the departing input on A5/A6 (ConstraintsSel doc). Every GLS run satisfies H_LUT_FIFO by construction (`FifoFidelity.gls_lut_fifo`), so the GLS cannot falsify it. | cap |
| S4 | **H_ZERO_DELAY_FN** (`Timing/Semantics.lean:25`), **H_ATOMIC_LUT** (C-8g), **H_LUT_SI** (`Net/OpsSteer.lean:20`), **H_GMW_GATE** (`Cells/TernarySound.lean:30`) | A LUT is one Boolean (or Kleene) function of its pins at one instant, followed by a delay. Multi-pin changes are not resolved through the tree. | tcheck `Run` (R3), RtFbGcd (R2), Ops* SI models, Events Race/Back | **B** (A-substrate). At equality it hides a real hazard: `boundary_function_hazard` (C-8g) shows that with simultaneous arrival an atomic LUT sees no glitch, while the mux tree crosses (1,1,0)→0 of the real INIT. | GLS with a per-level transport LUT model instead of `SLICE_LUTX`'s sample-at-fire, diffed against the current GLS (A-lut-tree row "exact model"; `formal/tools-A/gls-compare/run_all.sh` measures the GLS channel). | now (R2, R3), cap |
| S5 | **H_SETTLE**, **H_FB_FUND** (`Core/Env.lean:37,43`) | The SI environment models: a LUT's tree settles an input change before any other event, and the cell's own feedback pin is zero-delay (fundamental mode). | A's Env/EnvFast: `link_sound`, `mux_sound`, `muxD_sound`, `mergeD_sound`, `steer_sound` | H_SETTLE **B**. H_FB_FUND **C** as stated: real feedback routes are 200-900 ps, and the own-feedback race it assumes away fails on bare Muller pipelines (C-10f: 4-12 of 64 stages at slowE, 8 seeds) and under corner mixing on gcd_hw (A-xaudit-gcd: 4-10 candidates per seed, one 9 ps runt reproduced). The timed replacement is row C1. | Replace with C1's check; see test T2. | cap (cell SI specs only) |
| S6 | **H_ROUTE** (`Cells/OnNetlistTimed.lean:18`; C-11b), the window **H_BOUNDED** (`Win`, `Core/Substrate/Chan.lean:98`) | Each routed sink arc is a bounded delay within its band. Fanout branches are separate channels. All zynq7 prjxray pips that carry a delay are buffered. | All timed results | **B** (A-substrate). The "all buffered" part is **A** (C-11b: all 20211 pips with a delay are buffered, and the 18762 pass-transistor pips carry none). | 128-ring periods inside summed bands, re-measured on the current nextpnr (C-10c: the old comparisons predate `nextpnr-xilinx-lut-perm-sink.patch`); `formal/tools/prjxdelay/run.sh`. | now, cap |
| S7 | **H_RF_ASYM** (cell_constraints global; `Cells/MuxRtzTimed.lean:397`; `ArbCorners.RF`) | Rise and fall are equal within one corner column. prjxray has no rise/fall split (`makesdf.py:63`: the two triples are FAST and SLOW). | Every B inequality; tcheck (hulls, polarity ignored) | **B**. Unmeasured. NMOS pass trees physically favour fall (B-muxtree), so equality is a modelling choice. | Board: a CARRY4 TDC capturing the rise and the fall of one LUT arc separately; or two rings with the same route and opposite edge-polarity mix. | now, cap |
| S8 | MUXF7/F8 *(unnamed)*: xaudit models them as LUT3 0xCA; site-internal F7→F8 has no db entry and is taken as 0 (C-10g, "optimistic by < ~25 ps") | settle within the band; no glitch beyond Kleene | xaudit (R4), tcheck (R3) | **B** | prjxray-db fuzz of the F7→F8 hop, or a GLS row against the db | now |
| S9 | **H_CARRY4_SIM** (`Gen/Netlist.lean:32`; C-11d) | CARRY4 as `cells_sim.v` gate by gate (CYINIT as an OR; the silicon has a static mux, which agrees when one input is tied 0, as yosys uses it). xaudit decomposes it the same way into MUXCY/XORCY LUT3s; its hi cover is checked against prjxray, and the low-floor exceptions are listed. | Gen `prims_add_spec`; xaudit (R4, 38 CARRY4); any future H_COMPUTE_FN proof | **B** | Exhaustive vectors per fused unit in the routed GLS (`cells/gls`, must print ANNOTATE_DONE); extend fasm2lean to CARRY4 (C-11b, 3-5 d) | now (R4), cap |
| S10 | **H_FF_MS** (`Gen/Netlist.lean:35`) | FDRE/FDSE/FDCE/FDPE as an ideal master-slave pair. Setup, hold, CK→Q and metastability are not modelled. | Gen `bd_flink` | **B** for logic. Its timing is absent. | none planned | other: the kernel has no FF. The rig's idx/vector ROM is outside the cut (H_OPAQUE_CUT, row D17). |
| S11 | "metastability (no deadline)" (cell_constraints global; `Cells/CElemInvolution.lean` `c2_eternal`, `ArbInvolution.arb_grants_eternal`) | Proved under the involution channel: a runt width that never resolves always exists, and no fixed read time is safe. A liveness capstone needs the converse, "every contest resolves", which is not provable digitally. | B's arbiter results | n/a (a theorem, not a hypothesis). It makes **liveness depend on H_EXCL_REQ** (N4), so that gcd_hw's arbiters are never contested. | MTBF rig (`cells/verify/MTBF.md`); out of the north star's digital scope | cap |

## 2. Delay model

| # | name (where) | plain statement | used by | grade | test | gcd |
|---|---|---|---|---|---|---|
| D1 | **H_GRID** (`Core/Substrate/Chan.lean:16`) | time and delays in whole ps | everything | **A** (prjxray values are ns to 3 decimals) | none | now |
| D2 | **H_SEP** (A's: `Core/Discretize.lean:75` `Sep`; `Substrate/Real.lean` `chan_sample_win`) | No gate excitation has two transitions within one quantum q (1 ps), jointly over its fan-in. It is needed only to transfer discrete results to real time. | `transfer_win`, `circuit_sample_win`, `invariant_real_time` | **B** on data and handshake nets. **C** at arbiter inputs and same-sense near-ties (`Discretize.tie_counterexample`, `mutex_between`). | GLS: histogram of the minimum inter-transition gap per excitation at 1 ps (A-substrate §5) | cap |
| D3 | **H_REST** (`Substrate/Real.lean:22`), **H_QUIESCENT** (`Substrate/Legacy.lean:23`) | signals are constant before time 0 | `WinR`, tcheck `Run`, `chan_sample_winR` | **A** after reset | GLS from reset | now |
| D4 | **H_BOUNDED_DELAY** (`Net/Prelim.lean:13`, `BoundedDelay`) | C's per-arc relation. It is strictly larger than `WinR` (`boundedDelay_not_winR`): an output may hold while the input chatters. | tcheck `Run` (R2, R3) | **B**. It is sound as an over-approximation, but three C probes (8d, 8e, 8h) found it the wrong channel for SI and ordering proofs, because it admits echoes. | none (it is a superset) | now |
| D5 | **H_FIXED_DELAY** (`Net/EndToEnd.lean:42`) = **H_ONE_DELAY_PER_ARC** (A-substrate §5) | one delay per arc for the whole run | `EndToEnd.end_to_end`, `race2_sound`, `Tcheck.verdict_sound_fixed` | **B**. `end_to_end2` drops it under H_PULSE, and `Win` theorems never need it. | GLS with per-transition random delays (`cells/gls/gen.py` `GLS_SCATTER`) | cap |
| D6 | **NoOvertake** / **H_NO_OVERTAKE** (`Net/Bridge.lean:253`), **H_INERTIAL** (C-8g), **H_LUMP** (C-8g) | channels never reorder (NoOvertake); every node is an inertial `[lo, hi]` channel, of which only the lower-bound cause window is used (H_INERTIAL); a req path made of route + LUT1 + route is one channel with summed bounds (H_LUMP) | Bridge (discharges Ring's H_SI), `MullerTimed` FbBound | NoOvertake **B**. H_INERTIAL **B** as used, **C** if filtering were used (`Substrate.inertial_not_win`; the involution channel shrinks pulses continuously). | GLS pulse train through LUT + route at both corners, checking that each output edge lags its cause by at least lo (C-8g) | cap |
| D7 | **H_PULSE** (`Net/PerLinkEvent.lean:295`, C-8h) | per-event transport keeps order, given a minimum pulse width on each control net. It is not discharged from the protocol. | `end_to_end2` (per-event pins) | **B** | GLS monitor: minimum phase length per control net | cap |
| D8 | **H_ENDPOINTS** (`Substrate/CornerNat.lean:14`) | each arc's delay is bounded by prjxray FAST and SLOW endpoints (Elmore per sink arc) | the corner model, `EndpointOK` | **B** | ring periods against summed endpoints | cap |
| D9 | **H_AFFINE** (`Substrate/Real.lean:42`) | nominal delay is affine in ONE corner scalar c ∈ [0,1] | `endpoints_sound_real`, `bundle_real_of_check` | **C** in general (PVT has 3 axes, and arc types respond differently). **B** for matched paths: on the 128-ring rebuild S/F is 2.81-3.06 per ring (A-kappa). | Two ring types (LUT-heavy and wire-heavy) at ≥ 3 temperature or VCCINT points: are the period pairs collinear? | cap |
| D10 | **H_SHARED_CORNER** (`Substrate/Real.lean:42`; `RealizesAt c`) | one corner per die, at least within one handshake | corner model | **B** (slot and group permutation tests p = 0.73 and 0.66, no gradient seen) | 128 rings at two die temperatures | cap |
| D11 | **H_SCATTER κ** (`CornerNat.lean:57` `Kappa`, `:120` `Scat`; ℝ `Core/Delay/Corner.lean:200`) and the difference form **κd** (`Core/Delay/CornerDiff.lean:76` `DiffScat`) | each arc lies within ±κ of its nominal delay at the shared corner. Rules E and A are sound iff κd ≤ 0.1988 and κd ≤ 1/11 (`ruleE_sound_diff`, `ruleA_sound_diff`, both tight). | every bundling `EndpointOK`; rule E/A soundness | Form **B**. Value **C** for per-path κ ≤ 0.2: `kappa.py` gives κ ≥ 0.311 on 7-link rings. **But** those rings were predicted with pre-lut-perm-sink SDFs (C-10c), which A-kappa does not cite (contradiction X4). κd is unmeasured, so it is **B**/open. | T1: a differential two-path ring (shared body, two tails, scan-selected LUT mux; ≥ 64 pairs per class, 4 seeds, 2 temperatures) → `python3 formal/tools-A/kappa/kappa.py pairs FILE`; commit the `ro_many` raw logs → `kappa.py rawlogs` | cap |
| D12 | **H_ONE_CORNER** (`Timing/RoutedCePair.lean:20`; C-10d) = **H_DIE_SLOW** / **H_DIE_FAST** (`Cells/OnNetlistArb.lean:47`) = xaudit's "one-corner" band | The whole die sits at one prjxray corner, and each element lies anywhere in that corner's [min, max]. | R2 (`gcd*_slowE_safe`), R3, B's routed arbiter safety (`OnNetlistArb`), xaudit flags | **B, contested**. 10c finds silicon at 0.61-0.68 × slow_max for the ring population, which is inside. It becomes **C** if A's per-path κ ≥ 0.311 survives a re-measurement on the current binary. C-10e's version adds a scatter band (contradiction X3). | T1 and T2 | now (R2, R3) |
| D13 | **H_RC_EXACT** (`Timing/RoutedCePair.lean:22`) | delay = intrinsic(corner) + Elmore RC, with RC independent of the corner | R2 (`slowE`/`fastE`) | **B**. The Elmore term is not cross-checked against `prjxray/timing.py` (C-11b). | `formal/tools/prjxdelay/run.sh` against the research `xray_delay.py` and the rings | now (R2) |
| D14 | **H_INDEP** (`Cells/OnNetlistArb.lean:49`; `RoutedCePair.lean:19`) | each element anywhere in [fast_min, slow_max], independently | the sound "box" instantiation | **A** given D8. It is conservative, and too pessimistic to pass: RT_FB fails 5-9 per gcd route, and the A0 fork fails 8/8 on link_arb. | none needed | (alternative to D12) |
| D15 | **H_BAND_772_1155** (`Timing/Rules.lean:27`) and C-10e's "H_ONE_CORNER plus scatter band" | each element within 0.772× / 1.155× of its corner interval (skew.py's GUARD_LO/HI) | rules E and J; tcheck band variants | **B**. It is a κ statement (D11) with κ ≈ 0.2, and CLAUDE.md: "8.5% is the median ring scatter, not a guardband". | T1 | now (R3) |
| D16 | **H_WIRE_RATIO** (`Cells/ArbCorners.lean:862`) | one fast/slow ratio k per margin | B's guarded rule J (`fast_neg_iff`, `guard_universal`) | **C**. The measured per-wire ratio band is p10 0.37 .. p90 0.82, and with per-wire ratios the guarded rule J fails by −118.5 ps (audit row 36, `ruleJ_perwire_cex`). | T1 (per-wire), or replace with per-arc corner bands (A's `CornerModel`) | cap (9 arbiters) |
| D17 | **H_FALLBACK_BAND** (C-10e:94), **H_UNKNOWN_ROUTE** (C-10f:147), **H_OPAQUE_CUT** (C-10f:312), **H_CONE** (`Timing/RtFbGcd.lean:18`) | Arcs with no prjxray number lie in the SDF band. An unwalkable long line is [0, 10^5] ps. FF/carry/IOB/BSCAN outputs do not respond inside the window. Pruned C-elements cannot violate (Python Dijkstra, not in Lean). | R3 (fallback), R2 (the other three) | FALLBACK **C**: it is not a bound, and nextpnr's SDF has slow max only (C-10e). UNKNOWN_ROUTE **A** (conservative, never on a feedback). OPAQUE_CUT **B**. CONE **B** (monotonicity; unverified code). | T3: 10h's front end (`formal/tools/tcheck/run4.sh d 2 3 4`); emit H_CONE's backward distances as a Lean certificate | now |
| D18 | **H_EXTRACT_MIN** (C-10e:123), **H_SEGMENT**, **H_BUNDLED_T0**, **H_LEVEL**, **H_CLEAN_EDGE**, **H_CONTROLLING**, **H_ONE_SAMPLE_PER_WIRE** (C-10g:316-335) | the obligation shapes of tcheck's rules: minimal Dijkstra chains, storage crossing as pass-through, boundary nets launch at t=0, first level = this transaction, one transition at the dominator, AND-stage fall bounded by its side tap, one delay per shared RC prefix | R3 | EXTRACT_MIN **C**: violated in 293 of 948 prjxray H rows, by up to 942 ps, though no verdict flipped. 10h discharges it by certificate (`Timing/Unroll.lean` `pot_sound`, `Tcheck/Cert.lean` `cverdict_sound`; in progress). CLEAN_EDGE **B/C**: 252 of 322 credited instances are LUT-output X and need a hazard-free gate. The others **B**. | T3; GLS with per-transition random delays on the prefix gates (C-10g) | now |

## 3. Cell obligations (gcd_hw instances in brackets; B-gcd-cells §2)

The ids are `formal/out/cell_constraints.json`'s. "rule" is the project rule that approximates the
obligation, with B's verdict.

| # | name (where) | plain statement | used by | grade | test | gcd |
|---|---|---|---|---|---|---|
| C1 | **own feedback before neighbour response**, stated nine ways: **H_ENV_LATENCY** (`Cells/CElemTiming.lean:408`, `dlmax + dwmax ≤ dlmin + E`), **FbBound** / **H_FB_DELAY** (`Net/MullerTimed.lean:726`, strict `<`), **Race** (`Core/XAudit/Events.lean:168`, `≤`), **Back** (`Events2.lean:200`, `≤`), RT_FB (tcheck R; R2), **H_FB_BEFORE_INPUT** (`Net/MullerSI.lean:23`), **H_FB_FAST** (`Cells/LinkHandshake.lean:21`), ids `bd_c*.env_latency` | A C-element's (or latch's) own feedback reaches its pin before any neighbour can respond to its output edge. | B's C-element/link/pipe timing, MullerTimed, Events/xevents, R2 | gcd_hw at one corner: **B** (10f: 0 failures on 4 seeds, worst slowE +234 ps; DUT thinnest +19 ps). Under the guard band: **C** at the rig's `urig.uenv1.u` (seeds 2 and 4: −7, −37, −95 ps; C-10g). Under corner mixing: **C** (xaudit `indep`: 4-10 candidates per seed, a 9 ps runt in `ucontrol_merge4.uarb1.ua2` reproduced). On bare Muller pipelines: **C** (C-10f). No project rule checks it. | T2. Tools: `formal/tools/rtfb/gcd_rt.sh`; `formal/tools/tcheck/run3.sh d 2 3 4` (R rows); xaudit `fbrace.py` | now (R2, R3), cap [184 c2n + 153 c2 + 23 c3/c4 + 9 arbiter A-loops] |
| C2 | **H_SEL_ORDER** (`Cells/ConstraintsSel.lean:4`), **H_SELORD** (`Cells/PipePerPin.lean:21`); ids `bd_c*.sel_order` | per pin, with site pins: the feedback reaches its mux select before the first departing req/ack does | ConstraintsSel, PipePerPin, FifoFidelity | **B** on gcd_hw: R2 uses per-pin prjxray site delays. Pin-1 feedback is common in C's fixtures (12/36; 24/64 on muller64; JOURNAL-B "PIN 1 FEEDBACK IS COMMON"). No rule checks it. | a FASM pin gate with a site-pin table (B-obligations: about 0.5 d), or LOCK_PINS | cap |
| C3 | ids `bd_c*.pulse_width`, `.reset_width`; **H_PW**, **H_RST_PW** | minimum input pulse and reset widths | CElemTiming, CTreeTimed | **B** | GLS monitor | cap |
| C4 | Latch: ids `bd_latch[*].setup_data` (rule I: missing term, the feedback-pin arc), `.setup_pulse` (unchecked; the binding constraint on the Bt2 routes), `.hold` (rule H: missing site pins), `.loop_bound`; **H_LATCH** (`Cells/LinkTimed.lean:461`) | data settles at the latch LUT pins before the enable, and holds past its fall; the enable pulse is wide enough | Latch, Bundling, LinkTimed, PipeTimed(N), EndToEnd (`H_LATCH_CELL`, `EndToEnd.lean:428`) | **B**. tcheck on gcd_hw: rule I 75/75 and rule H 157-158/158 agree; 2 H rows fail under prjxray site pins + band, which are thin margins (C-10e). W (open width) min +336 ps. | `formal/tools/tcheck/run.sh` (H, I), `run3.sh` (W) | now (R3), cap [184 latches] |
| C5 | rule L and **isoEn** (`Core/Env.lean:461`; `link_needs_isoEn` `:655`) | the latch output settles before the enable falls; the enable branch reaches the latch before the receiver's ack returns | `Env.link_sound` | **B**. Rule L is in tighten.py. isoEn has no tool. | add an isoEn row to tcheck (routed enable-net max against the min round trip through the receiver) | cap |
| C6 | **H_GFLUSH** (`Cells/GcdCells.lean:33`); id `bd_delay_gated.gate` | the stale stage value of a gated delay line is gone from the next LUT's chain pin before the new gate rise reaches its tap pin; stage 1 must also outlast the `uor` and `g[0]` hops | `GcdCells.no_early`, `ConstraintsFastFall.gated_not_early` | **B**. Rule F checks it without the in-flight term `(p i).hi − (q i).lo`. tcheck finds 2 F lines thin or negative under the band (C-10g). | tcheck F rows with the in-flight term added | cap [29] |
| C7 | ids `bd_delay[sym].pulse_width`, `bd_delay[FASTRISE].ack_flush` | delay-line pulse width and ack flush | Bundling, PipeTimedN | **B** | rules A-E edge window | cap [97 rdly, 169 uack, 21 udly] |
| C8 | bd_steer: ids `bd_steer.bundled_s_setup` / `.bundled_s_hold` (both **unproved** in the JSON; `SteerEnv.H_S_PIN`, `steer_s_pin_of_wire`, B-ops-timed), **H_ACK_SKEW** (missing id `bd_steer.ack_or_skew`), **H_STEER_SEL** (`Net/OpsSteer.lean:27`), `Held` | the select reaches the steer LUT's `s` pin before the joined request (setup), and stays there while the request is high (hold) | OpsSteer.steer_op, OpsTimed, EnvFast `steer_sound` | **B**. Rule E checks setup without site pins; tcheck finds 7 E gates thin or negative under the band (C-10g). Hold is unchecked, and the shards disagree on whether it is needed (X6). | `formal/tools/tcheck/run2.sh` (E); `skew.py -v`; add a hold row | cap [38, every loop exit] |
| C9 | bd_mux: **H_MUX_RTZ** (`Cells/MuxRtzTimed.lean:5`), **H_RTZ_ENV** (`:39`), EnvFast `rtz`; ids `bd_mux.uxa_rtz(_env)`, `.uya_rtz(_env)`; select: **H_BUNDLED_S** (`MuxRtzTimed.lean:106`), **H_S_PIN0/1**, **H_MUX_SEL** (`Net/OpsMux.lean:23`), EnvFast `sHold`, `crSettle`; data: **H_BUNDLED_Z** (`ConstraintsMux.lean:292`) / **H_MUX_DATA** (rule A); forks: `bd_mux.isochronic_forks` (unproved), EnvFast `zaIso`/`zaSettle`; **H_OR_SKEW**, **H_DEP_J0/J1** (missing ids, B-ops-timed) | The previous token's x_ack/y_ack fall before the next z_ack rises. The select is at uj0/uj1 before ctl_req and is held past ctl_req's fall at uj1. Data before z_req. The fork conditions. | MergeMuxSI, MuxRtzTimed, OpsMux.mux_op, OpsTimedMux, EnvFast `mux_sound`/`muxD_sound` | RTZ: **B** for gcd_hw (all 21 muxes have DELAY=12); **C** for N=0 lines (`fast_adv_N0_fails`; `uxa_rtz_env` about −6 ps at adversarial fast with the guard). Select and data: **B** (rule E/A without site pins). Forks: **B** (unproved). | GLS assertion "x_ack and y_ack both low at every z_ack↑" (A-envfast-2); tcheck A/E rows | cap [21] |
| C10 | bd_arbiter: **H_A0_FORK** (`Cells/ArbHeldTimed2.lean:319`; ids `bd_arbiter.a0_fork_client{1,2}`, rule J exact without site pins), `bd_arbiter.rt1/rt1b/rt2*`, **H_SERVER_MIN** (`ArbHeldTimed2.lean:10`), **H_Q_BEFORE_REREQ** (`Cells/ArbBinary.lean:770`), `bd_arbcell.req_separation` (uncheckable statically), **H_GRANT_FORK** (C-12c:194; no B file states it), **H_ARB**, **H_ARB_EXCL** (`Net/OpsCM.lean:20,23`) | A0's fall reaches ua_k before A0 → ustate → q → ugrant → g_k does; handover exclusion by relative timing; the server's minimum latency; the request fork into ustate/ugrant is isochronic with respect to q's route; a grant follows its request and the two grants are never high together | ArbHeldTimed(2), ArbA0Fork, ArbCorners(Pin), OnNetlistArb, OpsCM | H_A0_FORK: **C** under the project's own guard band (link_arb: negative 7/8 at the fast corner with the band, OnNetlistArb; gcd_hw: 3 J clients thin or negative under the band, C-10g; rule J 8 ps optimistic with q on A5, ArbCornersPin). **B** at one unguarded corner (8/8 safe). H_GRANT_FORK **B** (unchecked; transport fails once wq_g > wq_s). H_SERVER_MIN **B**. **The `bdc_amerge3_0` cascade (an arbiter as client of another) is in no theorem.** | T5; `formal/tools/grantfork/extract.py` on the gcd_hw routes; rule J' (B-arb-a0fork) | cap [9] |
| C11 | bdc_amerge: **H_AMERGE_RTZ** (`Net/OpsCM.lean:28`); index/data bundling against R0 *(unnamed; B-gcd-cells §3)* | after A0↓, the previous winner's A_k falls before z_req rises again; the index `won = g2 \| A2` and the data mux settle before z_req | `OpsCM.amerge_op` | **B** (one LUT against the whole matched delay). Index bundling: no theorem. | tcheck row (C-8j); GLS monitor on `won` at z_req↑ | cap [8] |
| C12 | `bdc_muxn3_32` *(no hypothesis; a gap)* | the 3-way loop-header mux: decode `ctl_req & (s == k)`, 3-way exclusion, RTZ for 3 acks | C-8j: Python SI model, 594 states, 0 violations; Lean closure not written | — (unmodelled) | write the Lean closure (C-8j, about 0.5 d) | cap [1] |
| C13 | **H_COMPUTE_FN** (B-gcd-cells:110,131), **H_COMPUTE_DELAY** (`Net/OpsJoin.lean:24`; C-8f:175) | The synthesized LUT/CARRY4 netlist of each `bdc_fused_*` unit equals its MLIR op. The cone's max delay is at most the matched delay's min (rule A). | `OpsJoin.join_op` (data as a zero-time function) | FN: **B** (yosys trusted; no check). B-gcd-cells (not re-verified here) notes the gcd_rig GLS located a misbehaviour in the abs unit `uselect1`. DELAY: **B** on the 4 R5 routes (tcheck A: 185/200 rows equal to the rule, the disagreements come only from the band), but rule A is route-sensitive: the gcd bench build did not converge on rule A in 6 iterations (research/JOURNAL.md). | Per-unit exhaustive or random vectors through the routed GLS; extend C-11b's whole-design bits = yosys equivalence to the fused units (3-5 d) | cap [20] |
| C14 | **H_FORK_DATA** (C-8f) | per fork branch, the data wire settles before the req wire | `OpsFork.fork_op` (via Held) | **B**. It is a pure route skew obligation, with no B theorem and no rule (B-gcd-cells §3). | a tcheck row | cap [52] |
| C15 | **H_CTREE_ATOMIC** (`Net/OpsFork.lean:13`), **H_ATOMIC_CELL** (`Cells/CTree.lean:17`); ids `bd_ctree.node_fork`, `.ack_wait` | a C-tree acts as one N-input C-element | OpsFork/OpsJoin; CTree (reachable-set equality) | **B**. CTreeTimed gives the timed form; tree latency is unchecked on routes. | tcheck row | cap |
| C16 | Reset: **H_RESET** (`Net/EndToEnd.lean:416`), **H_RESET_CLEAN** (`Net/Ring.lean:18`), **H_RST_LONG** (`Core/Env.lean:392`), **H_RST_EARLY**; the rig's initial token `uenv1` (`bd_c2n_set`) release order *(unnamed; B-gcd-cells §2c, §4.8)* | Reset is held until every node settles, and released before the first edge. The rig ring starts with exactly one token. | EndToEnd, Ring, Env, OpsTimed | **B** | GLS that shortens the reset hold (tb_ring's HOLD comment documents the power-up-X failure) | cap |
| C17 | **H_ISO_FORK** (`Cells/LinkHandshake.lean:13`), **H_LT_FIRST** (`:41`) | isochronic forks in LinkHandshake's any-N deadlock freedom; bd_link_dctl's header timing | LinkHandshake | ISO_FORK **C** (not physical; C-8d: a non-isochronic feedback fork loses the token). LT_FIRST **B**. | — | other (C's pin-level EndToEnd/PerLink replace ISO_FORK; `bd_link_dc` is not emitted) |

## 4. Network

| # | name (where) | plain statement | used by | grade | test | gcd |
|---|---|---|---|---|---|---|
| N1 | **Held** / **H_BUNDLE** (`Net/Ops.lean:81`) | each channel's bus is stable from just after req↑ until after ack↓, at the consumer's pins | `Ops.net_refines` and every op theorem | **B**. It is discharged per channel by the rows of C4-C14 through tcheck. | tcheck (all rules) | cap [all 252 channels] |
| N2 | **H_CEL_SI** (`Net/OpsCM.lean:26`), **H_WIRE_DI** (`Net/OpsFork.lean:10`), **H_DELAY_LUMPED** (`OpsCM.lean:26`), **H_DATA_COMB** (`OpsCM.lean:37`) / **H_DATA_WIRE** | SI/DI op models: a C-element moves only to a value all its inputs had one tick earlier; each fan-out wire has its own unbounded delay; OR + matched delay are one node; data is zero-time, with all data delay pushed into Held | Ops* (C-8f, C-8j) | **B**. The control model is more general than bounded delays. H_CEL_SI needs C1/C2. | follows from C1, C2 and N1 | cap |
| N3 | **H_ONE_INVOCATION** (`Net/GcdHwLib.lean:427` `Inv`) | at most one token on the control spine | R1 | **A**: proved for gcd_hw from the initial store (`closed_of_check`, `GcdHwLive.lean:58`) | — | now (proved) |
| N4 | **H_EXCL_REQ** (`Net/OpsCM.lean:51`) | at a loop header the entry and back-edge requests are never pending together; then `amerge_forced` turns the arbiter's choice into a fixed stream | `OpsCM.amerge_forced` | **B**. It follows from N3 at token level; the circuit-level derivation is open (C-8j item 2). It does not exclude handover races (C10). | the ring counting argument (C-8j: 0.5-1 d); GLS monitor "never both r1 and r2 high" | cap [8 amerges] |
| N5 | **H_SOURCE_ETERNAL** (`Net/GcdHw.lean:11`) | the 4 source→fork→constant chains are always-valid literals | R1 | **B** (bd_src holds req high; a wire) | GLS: the 4 bd_src req nets stay high (C-8i) | now |
| N6 | unbounded FIFO channels *(unnamed; C-8i, C-8k)* | the token model gives every channel unbounded capacity; bdc's links hold 1-2 slots and wires are rendezvous | R1 | **B** for safety (determinacy transfers to any capacity in which the schedule fits, `KahnBounded`). Liveness does **not** transfer (C-8k). | needs N7, N8 and HandshakeLive at circuit level | now |
| N7 | **H_ONE_TOKEN** (C-9-ring.md:131), **H_ONLY_LINKS_STORE** (C-9b:145) | each ring closes holding exactly one four-phase token (D=2); mux/steer/fork/join hold nothing | `Ring.ring_three`/`k_tokens`; RingCheck (R5) | **B**, unproved. emit.py's comment reports tb_ring measurements (1-2 stages dead, 3 live). tb_ring's occupancy sweep never varies the token count (JOURNAL-C 03:12). | tb_ring-style sweep with a mux/steer in the ring; promote R5's certificate out of Wip | cap |
| N8 | **H_SI** (`Net/Ring.lean:23`), **H_FB_SETTLED** (`Cells/LibCtlMergeMux.lean:36`) | interleaving semantics; feedback settled | Ring; discharged by Bridge under persistence + NoOvertake, except that the feedback fork must be isochronic | **B** | as D6 | cap |
| N9 | **H_CEL_FAIR**, **H_SRC_LIVE**, **H_SNK_LIVE** (`Net/HandshakeLive.lean:180-182`) | fairness and environment liveness for pipeline liveness | HandshakeLive | **B** | — | cap (circuit liveness) |
| N10 | PipeRun/PipeRun2 fields **H_SRC**, **H_SNK**, **H_SRC_DATA**, **H_LATCH_CELL** (`EndToEnd.lean:423-429`), **H_PIN_R/A/G/D**, **H_DBAND** (`EndToEnd2.lean:84-89`); **Sep**, **Hold**, **SetupHold** (`HandshakeMuller.lean:182,189`; `Handshake.lean:203`), PerLink **H_SEP**/**H_HOLD**/**H_SRC_SETUP_HOLD** (`Net/PerLink.lean:90-92`) | pin-level pipeline contract; source data changes only with a request rise; per-link separation and hold margins (rules I and H) | `end_to_end2`, `fifo_of_timing2`, `pipeline_fifo` | **B**. The rig's a/b data come from an FF-driven vector ROM indexed by idx, which moves only under rst (gcd_rig.v; the contract is unstated, B-gcd-cells §4.8). | tcheck H/I/W; GLS | cap |
| N11 | **H_INITBUF** / **H_INITBUFA/B** (`Net/OpsGcd.lean:23`) | initial-token buffers on the hand-drawn graph | `OpsGcd.gcd_circuit` | — | — | **other**: 8b's hand-drawn graph only; gcd_hw's kernel has no initial token (B-gcd-cells §2a), and that graph deadlocks for a ≠ 0 (`OpsLive.gcd_stuck`) |
| N12 | input range (theorem precondition `a b < 2^31`, `GcdHwLive.lean:47`) | non-negative i32 inputs | R1 | **A**: all 16 rig vectors satisfy it (`cells/hw/gcd_rig.v:148-163`). Negative inputs genuinely loop (C-8i). | — | now |
| N13 | `Ops.*` = bdc's Verilog semantics *(unnamed; C-8i)*; fused region = one strict node *(unnamed)*; n-way mux index ≥ n never fires *(unnamed)* | Nat mod 2^w as bdc emits it (shift ≥ w follows Verilog, not MLIR poison); not proved equal to `BitVec` | R1 | **B** (the mux index is unreachable here: indices are cm literals) | `bdc/test_compute.py`-style exhaustive vectors; the BitVec equality (about 1 h, C-8i) | now |

## 5. Toolchain and netlist

| # | name (where) | plain statement | used by | grade | test | gcd |
|---|---|---|---|---|---|---|
| T1 | **H_PAD_IDENTITY** (`Net/Import/Netlist.lean:26`), **H_BUF_IDENTITY** (`Gen/Netlist.lean:44`) | IBUF/OBUF and BUFG are zero-delay identities | Import, Gen | **B** | — | other (top-level pads, removed by `-noiopad`; BUFG only in `bd_mem_ack`) |
| T2 | **H_IMPLICIT** (`formal/tools/fasm2lean/fasm2lean.py:35`; C-11b:75), **H_TIE** | implicit (bit-less) pips are inferred when exactly one candidate source is driven; ties are constants | fasm2lean, R2 ("the bitstream is always the source") | **B**: the read-back equals nextpnr's FASM netlist on 4 seeds. LV/LVB long lines through bidirectional pips are not walked (132-374 pins per gcd route → D17). | `formal/tools/fasm2lean/check.sh`, `fasm2lean2/check.sh` | now (R2) |
| T3 | pin permutation *(unnamed)*: physical INIT and pins = logical cell up to the placer's permutation | The proofs are about logical INITs; the router permutes pins (BLUT 0x3220.. vs logical 0x00E8..), which moves delay by up to about 0.5 ns. | FasmLink (proved for link + arbiter, 4 seeds), PinAssign; for gcd_hw, xaudit's `routed2x.py` re-encodes through `X_ORIG_PORT` (fasm_audit's encoding) | **B** for gcd_hw. `fasm_audit` PASSes (7442 LUT sites), but whole-design bits = netlist is not proved (C-11b: 3-5 d). | extend `fasm2lean2/check.sh` to gcd_hw | now (R2, R4), cap |
| T4 | the graph import *(unnamed)* | the Lean graph is bdc's in-memory graph (drift-checked), and bdc's emitted Verilog implements that graph. The importer unsets `BDC_*`; the R5 routes used `BDC_SELECT_PADS` and `BD_SIZES`, which change only DELAY values (B-gcd-cells §1). | R1 | **B** | `formal/tools/dfimport/check.sh --lean`; a structural diff of the emitted Verilog against `GcdHw.rules` | now |
| T5 | the C reference *(unnamed)* | `gcdC` (`GcdHwProof.lean:72`) is a hand transcription of the fixture's `cf_transformed.mlir`, not of a `kernels/` source (gcd_hw has none). Dynamatic's lowering of gcd.c is trusted. The i1 rewrites are proved (`gEv_eq`, `gSc_eq`). | R1 | **B**. Agreement with `uniform_oracle.k_gcd` and with the audit's `gcd_kernel.c` is argued, not checked. | compare `gcdC` (`#eval`) with `cells/hw/uniform_oracle.py:k_gcd` on the 16 rig vectors and random pairs | now |
| T6 | toolchain identity: nextpnr sha256 9c732bc6303458df, yosys 0.62, prjxray-db, research `xray_delay.py` (D8) | the routes are what the flow produces | R2-R4 | **A** for R3/R4 (`cells/verify/toolchain.sh` ok, recorded). Caveats: the toolchain check cannot see missing runtime libraries (A-xaudit-gcd §1); `.bit` files differ in 4 header bytes across runs, so CLAUDE.md's `cmp` gives false differences (JOURNAL-C 03:35); the dsp-areg fingerprint cannot fail (JOURNAL-B, Bmt). | `cells/verify/toolchain.sh`; compare FASM, not `.bit` | now |

## 6. Trust base

| # | item | grade | note |
|---|---|---|---|
| B1 | Lean 4.35.0 kernel, lake, Mathlib built from source (only imported modules); `formal/check.sh` with `scan.py` and the `collectAxioms` audit (only propext, Classical.choice, Quot.sound) | **A** | Negative controls run: a hidden sorryAx and native_decide both fail the audit (JOURNAL 02:59). `decide +kernel` certificates are kernel evaluation. |
| B2 | compiled executables: `xaudit` (engine proved equal to XSim; parser `XAudit/Parse` and compiled code trusted; one verdict re-checked in the kernel, `XAudit/Check.lean`), `tcheck` (`verdict_sound`; parser and compiled code trusted), `xevents`/`xevents2` | **B** | Re-check selected verdicts in the kernel. tcheck is a separate lake project; `sync.sh --check` guards its copies of the Lean sources. |
| B3 | untrusted front ends that produce the checked instances: `routed2x.py` (cut, primitive decomposition, bands), tcheck `extract.py`/`rules2.py`/`rules3.py`/`certs.py` (obligation shapes, "unverified"; C-10e "Structural identification"), `rtfb_design.py` (H_CONE), `mlir2lean.py` (WF checked in the kernel, content trusted), the Gen/Import generators (yosys output), `fasm2lean*.py`, `kappa.py` | **B** | Each is a hypothesis about the mapping from the design to the instance. A wrong shape gives a sound verdict about the wrong question. |

## 7. Contradictions between shards (same assumption, stated differently)

- **X1. Which delay channel.** A-substrate recommends `Win` (non-FIFO, per-transition delay) and
  proves that inertial filtering is never derivable from it.
  - Other proofs assume FIFO: A's own `Events*` (`Beh`: "monotone warp"), B's H_LUT_FIFO/H_PIN_FIFO/
    H_WIRE_FIFO, and C's NoOvertake/EPin.
  - Others assume something else again: C-8g's H_INERTIAL, EndToEnd's H_FIXED_DELAY, and Prelim's
    BoundedDelay, which C itself calls wrong for SI proofs.
  - A's EnvFast data exemption ("a runt there has died out before the window opens") is an inertial
    assumption. It contradicts A-substrate's own rule that no proof may rely on filtering.
  - A FIFO result does not transfer to `Win`. The capstone has to pick one channel, and the S3/D6
    grades then apply to all of it.
- **X2. Strictness of the own-feedback race (C1).** FbBound is strict (`<`). Race, Back and
  H_ENV_LATENCY are `≤`. C-12c finds transport correct iff `e_lo ≥ dw_hi`, but inertial hazard-free
  only iff `e_lo > dw_hi`. C-8g shows that equality crosses a function hazard of the real INIT in a
  mux-tree LUT (`boundary_function_hazard`); the `≤` forms are sound only under the atomic-LUT S4.
  Following CLAUDE.md, take the strict form.
  - A's Env/EnvFast results take the same race as **H_FB_FUND** (zero-delay feedback), i.e. they
    assume it away.
- **X3. "One corner".**
  - H_ONE_CORNER means "each element anywhere in one corner's [min, max]" in C-10d, B's
    OnNetlistArb and xaudit.
  - In C-10e it means "one corner **plus** the 0.772/1.155 scatter band" (D15): same name, different
    set.
  - A's model is H_SHARED_CORNER + H_AFFINE + H_SCATTER κ: a continuous corner c, with scatter
    relative to nominal.
  - B's guarded rule J adds H_WIRE_RATIO (one k), which the measured per-wire ratios contradict.
  - R2's verdict is stated under C-10d's meaning.
- **X4. The evidence on κ.** A-kappa's κ ≥ 0.311 comes from 7-link ring ratios.
  - C-10c shows that all ring comparisons used SDFs written before `nextpnr-xilinx-lut-perm-sink.patch`.
    After correction, the prjxray model predicts comparable rings within 1.1% (median).
  - A-kappa does not cite 10c, and it notes that model-vs-model κ is already 0.17.
  - Neither "κ ≥ 0.31 refutes rules E and A" nor "κ is small" is established. FEASIBILITY.md
    §3b states the first more strongly than this allows.
- **X5. Name collisions.**
  - **H_SEP**: A means "no two transitions within one quantum". C's PerLink means rule I's
    separation margin.
  - **H_LATCH**: C-8a means an abstract node-level latch contract. B's LinkTimed means a Kleene-mux
    latch LUT on its pins.
  - **H_PULSE**: C-8h means a per-event minimum pulse for order preservation. B's
    OnNetlistTimed:120 means inputs held for `dhi + whi`.
  - **H_LUT_FIFO**: the JSON global means "an unchanged-function pin edge gives no output edge".
    OpsTimedMux/FifoFidelity mean "the output is a FIFO read of the excitation".
  - Reset goes by three names for one assumption: H_RESET, H_RESET_CLEAN and H_RST_LONG.
  - H_KLEENE_LUT ≡ H_mux_kleene ∧ H_sram is consistent across shards.
- **X6. Does bd_steer need a select hold?**
  - A's EnvFast says no: `steer_sound`, "No hold assumption is needed".
  - B-ops-timed says yes: `bundled_s_hold`, `ρ(2k+1)+Wq.hi ≤ sE+Ws.lo`, unproved in the JSON.
  - C's `Held` requires the bus stable until after ack↓.
  - The difference is probably the environment model: A encodes the next `s` change causally after
    the ack. Until that is settled, keep the hold (the longer requirement).
- **X7. "Never both requests high" vs what the arbiter needs.** H_EXCL_REQ removes contention at the
  loop headers.
  - B's handover results (H_A0_FORK, RT1/RT2) and C-12c's H_GRANT_FORK still apply to every
    sequential handover.
  - `bd_arbcell.req_separation` concerns same-sense edges within one loop delay, which H_EXCL_REQ
    does not state.
- **X8. Stale cross-references.**
  - B-gcd-cells says no `Formal/Net/GcdHw*.lean` exists, and that `sel_order` is unproved in the
    JSON. Both are now out of date (C-8i/8k landed; the JSON P4 update marks sel_order proved).
  - xaudit's one certified transaction is vector 1 (a=7, b=0). That is the `b == 0` early exit, so it
    exercises almost none of the loop, which is the kind of near-degenerate vector CLAUDE.md warns
    about.

## 8. Top 5 tests that would retire the most C-graded hypotheses

The C-graded items: D9 H_AFFINE, D11 κ value, D12 H_ONE_CORNER (contested), D16 H_WIRE_RATIO,
D17 H_FALLBACK_BAND, D18 H_EXTRACT_MIN and H_CLEAN_EDGE at LUT X, S5 H_FB_FUND, C1 under the band
or corner mixing, C10 H_A0_FORK under the band, C9 RTZ at N=0, D2 H_SEP at arbiter inputs, and
C17 H_ISO_FORK (not needed for gcd_hw).

1. **T1, the on-die differential two-path experiment, with the rings re-measured on the current
   binary.**
   - Build a ring with a shared body that splits into two tails, rejoined at a scan-selected LUT mux.
     The shared body and any common offset cancel.
   - Use ≥ 64 pairs per path class, 4 seeds and 2 die temperatures (or VCCINT points). Re-run
     `ro_many_top` on nextpnr 9c732bc6303458df and keep the raw logs.
   - Analyse with `python3 formal/tools-A/kappa/kappa.py pairs FILE` and `kappa.py rawlogs DIR --pred PRED.tsv`.
   - **Decides:** D11 (κ, κd), D15, D12 (contested), D9 (collinearity across temperatures), D16 (per-wire
     ratio) and D10. It also decides every verdict that is C only "under the band": C1 at `uenv1`,
     C10 H_A0_FORK, and the thin rows of C4, C6 and C8.
   - Board time: about 1 day once the rig exists.
2. **T2, own feedback against the neighbour response, on one die.**
   - Board: a C-element pair with LOCK_PINS putting the feedback on A1 (slowest) and the neighbour's
     return on A6. Sweep the neighbour's delay with a scan-selected tap. Count runts with an
     async-reset ripple counter.
   - GLS: the 4 gcd_hw R5 routes at slow and fast corners with `GLS_SCATTER` (`cells/gls/gen.py`),
     all 16 vectors, after the transport-LUT build of test 4 below. It must print ANNOTATE_DONE with
     no SDF warning.
   - **Decides:** S5 H_FB_FUND, C1 with its strictness question (X2), C2, and whether the
     corner-mixed race candidates (`ucontrol_merge4.uarb1.ua2`, `uenv1`) occur on silicon.
3. **T3, finish the tcheck front end** (C-10h; no board).
   - Add the CARRY4, F7/F8 and site-hop arcs, walk LV/LVB long lines in fasm2lean, emit full
     crossing-graph certificates, and emit H_CONE's backward distances as a Lean certificate.
   - Run with `cd formal/tools/tcheck && ./run4.sh d 2 3 4`, then `formal/tools/rtfb/gcd_rt.sh`.
   - **Retires:** D17 H_FALLBACK_BAND and H_UNKNOWN_ROUTE, D18 H_EXTRACT_MIN (10h: done for H, F and R),
     and H_CONE (C→A, or a real failure found). Add rows for H_FORK_DATA, isoEn, bd_steer hold,
     H_AMERGE_RTZ and the in-flight term of rule F (C6), so that the B rows C5, C6, C8, C11 and C14
     get route verdicts.
4. **T4, the board LUT tests of B-muxtree-fidelity §5.**
   - Glitch counter, with the toggled pin on A1 and on A6.
   - Metastable select on the arb_mtbf rig (`cells/hw/arb_mtbf_measure.py`), with legs static and
     legs rising.
   - A CARRY4-TDC measurement of LUT6_2 O5/O6 skew and of rise against fall.
   - Alongside, the GLS fix that A-gls-compare asks for: a transport per-level LUT model instead of
     sample-at-fire, so that a GLS can show the runts the proofs reason about.
   - **Decides:** the low-confidence case of S1 (mid-rail select with moving legs), S2, S7, S4's
     equality hazard, and D2 H_SEP at arbiter inputs (near-tie behaviour).
5. **T5, an arbiter handover race on one die.**
   - Build `bd_arbiter` copies placed with q on A3 and on A5 (the pin permutation of ArbCornersPin),
     driven by `arb_prot_measure.py`-style alternating clients at the minimum server latency, with a
     grant-overlap detector whose site pins are included (Bov).
   - On the gcd_hw routes, run `python3 formal/tools/grantfork/extract.py` and the proposed rule J'
     (B-arb-a0fork) with per-pin site delays.
   - **Decides:** C10 (H_A0_FORK under the band, H_GRANT_FORK, H_SERVER_MIN), D16 H_WIRE_RATIO, and,
     with test 3's monitor, N4 H_EXCL_REQ at circuit level.

Cheapest first step, with no board: a GLS of gcd_hw at both corners with monitors. It covers all 16
vectors; at the same seed it must reproduce the board-queue route's SDF md5 a9c4e265 (A-xaudit-gcd).
The monitors are: rtz (x_ack/y_ack low at z_ack↑), the steer and mux select hold, never both
requests high at an amerge, the bd_src req nets high, and the minimum inter-transition gap per
excitation. It grades N4, N5, C8, C9 and D2 from B toward A or C, but it cannot test S1-S3 (X1, and
`FifoFidelity.gls_lut_fifo`).
