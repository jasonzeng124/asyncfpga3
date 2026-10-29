# A-e8hyp (probe E8Hyp): design_verdict8's hypotheses against shards B and C

STATUS (2026-10-29): partial. `Formal/Core/XAudit/Events8Bridge.lean` typechecks with no error
and no warning against a private overlay of the Events chain; the check.sh run is in §7.
Bridges: reset (time shift), SelOK (from B's steer theorem), SelPart (by construction).
Gaps proved in Lean: SatPin vs C/B's window channel (time origin, overtaking). H_ARB: no
B/C statement implies it, and B's own theorems REFUTE it under a contested runt (§3.4).
Joint witness: SatPin + constants + reset proved jointly satisfiable iff a reset fixpoint
exists (Lean); gcd_hw has one on all 4 seeds (untrusted script, matches B's Lean reset values
name for name). HARB7 / SelOK / SelPart / HDsub jointly on a gcd_hw run: not proved
(untrusted evidence only, §5).

## 1. What design_verdict8 assumes (read in the Lean)

`Events8Beh.design_verdict8` (Events8Beh.lean:79). Besides the decidable checks (`Recog6`,
`Net4.OK7`, the accepted log, the per-item Bool checks), the hypotheses are:

| name | Lean | plain meaning |
|---|---|---|
| SatPin | `SatPin d plG x` (Events2PinDesign.lean:60) | every gate of the parsed control skeleton (LUTs, and 1-input route buffers) reads each input through ITS OWN monotone warp in the gate's band `(g.lo, g.hi)`, for all `t ≥ 0`; a warp reads time 0 before `lo` |
| constants | `∀ t, x (d.wire 0) t = false`, `∀ t, x (d.wire 1) t = true` | the parser's GND / VCC nets |
| reset | `1 ≤ T`, `∀ t, x (d.wire rw) t = decide (t < T)` | rst high on `[0, T)`, then low forever: one clean release |
| H_ARB | `HARB7 net b rn x cv` (Events7Beh.lean:102) | every virtual node (arbiter `ctl`, the two grants, `R0`) has a node behaviour `ND7` in its bands (the virtual mux core of A-events4 §1); the real grant / `R0` wires carry it; merge `R0` is low at 0 |
| SelOK | `bh.SelOK` (Events7Core.lean:234) | at a filtered pin, whenever a request-copy read shows transaction `k` (count `2k+1`), the select the pin sees is `sel grp k` |
| SelPart | `SelPart sel parts` (Events7Excl.lean:39) | two groups of one partition are never both true at the same index (gcd: one partition `[16, 56, 57]`, the three patterns of `umux21`'s 2-bit select) |
| HDsub | `HDsub bh parts J hl` | probe HDsub's; not treated here |

`sel` is universally quantified OUTSIDE the existential realisation `bh`, so the user of the
theorem picks it; SelOK then ties it to what the steer gates read.

## 2. Mapping table (for gcd_hw_hypotheses.md's A rows)

"Bridge" = a Lean theorem in `Events8Bridge.lean` deriving A's hypothesis from the other
statement. "Gap" = what the other statement does not give, with a Lean counterexample where
there is one.

| A hypothesis | closest B / C statement | bridge (Events8Bridge) | exact gap | grade / status |
|---|---|---|---|---|
| **SatPin** (per-pin monotone transport, from t = 0) | C: `Fasm.Behaves` (Net/Fasm/Basic.lean:106; a HYPOTHESIS: LUT core and each pin route are B's `CElemTiming.WinDelay` windows; built for link_arb / CePair only, not gcd_hw). B: `WinDelay`, `Loop`, `FifoFidelity.PinLut`, the `Rd` read maps of LibGap* (not monotone) | `transport_win`: A's channel ⊆ `WinDelay`. So B/C theorems over `WinDelay` apply to A's behaviours; the converse direction, which a discharge needs, fails | (1) time origin, `win_origin_gap`: `WinDelay` leaves `[0, hi)` free; A reads the input's time-0 value there. (2) FIFO, `win_overtake_gap`: `WinDelay 1 3` turns the clean step `2 ≤ t` into `F F F T F T T…` (a runt) with a quiet origin; no monotone warp does (B's H_LUT_FIFO / NoOvertake, S3). (3) no Lean map from A's parsed skeleton `d` (routed JSON, trusted reader) to C's `PNet` (FASM). No shard derives SatPin: it is the model | B (model); open by nature |
| **constants** (wires 0 / 1) | C: `Behaves.H_TIE` (tie pins constant from configuration) | none needed: same content | only the d ↔ PNet net map (as above) | A (tie-offs) |
| **reset** (rst = `t < T`) and, through SatPin, the **time-0 state** | B: `ResetGcd.gcd_reset_binary` (gNet: 3322-node RTL-level control net, GMW `Bounded D W` runs, ANY power-up, rst held on `(0, E]`: every control node at its reset value on `[(21+2)(D+W+1), E]`); `ResetGcdWave.gcd_boot` / `gcd_clean_release` (release) | `satPin_origin`: SatPin makes time 0 a combinational fixpoint (so A silently assumes a settled power-up). `satPin_shift`: a physical trace obeying the per-pin relation from `t0` (monotone reads) and quiet on `[t0 - H, t0]` (H ≥ every band end) is, shifted to `t0`, a SatPin behaviour. B's reset theorem supplies exactly the quiet window (control nodes constant at reset value), with `t0 = (21+2)(D+W+1) + H ≤ E` | (1) gNet ↔ d: no Lean map. Untrusted: A's skeleton fixpoint has the same 16 ones as `gcd_reset_ones`, 4 seeds (§5). (2) B's GMW reads are not monotone, so `PhysPin` (monotone) is the SatPin FIFO gap again. (3) A's reset is ONE clean release, never re-asserted; B allows any rst behaviour in a window (B more general, so this direction is fine). (4) `T` must come after the quiet window: release at `t0 + T`, `E ≥ t0 + T`. | B; discharged modulo (1), (2) |
| **H_ARB** (`HARB7`) | B: `ArbHeldTimed.rt1_exclusion` / `rt2_*` (handover scenario `Scn`, horizon `Hz`), `OnGcdArbFix` / `OnGcdArbA0` / `OnGcdArbKappa` (the 36 routed gcd_hw arbiters, one corner or κ), `ArbA0Fork` (no early ack). C: `OpsCM.AMerge` fields H_ARB1/2/EXCL (Ops-model HYPOTHESES), `CapstoneCut.gcd_hw_arbiters_uncontended'` (Ops model: no free contest) | none. `nd7_follow` / `nd7_steady` (Lean) state what HARB7 adds: bounded response | (1) content: HARB7 is a refinement (each grant = C(r_b, ctl·[σ = b]) through warps in bands, `R0` = OR with taps); B proves exclusion, one consequence, in one handover scenario up to `Hz`. (2) time base: C's are SI tick relations, unbounded delay, on Ops channels, not on A's wires. (3) HARB7 asserts a BOUNDED decision: the virtual grant's band is the grant LUT band (`tools-A/xaudit/events4/model.py:275`); only `ctl` may wait (up to 10^12 ps after A0 falls, :263). Under a contested runt B proves the real cell can do what no virtual core does: `ArbInvolution.arb_grants_eternal` (both grants pulse forever at the critical gap), `ArbBinary` §4 (a forever-circulating pulse, overlapping grants), `ArbResolve.no_deadline`. So HARB7 is FALSE on contested traces and can only be justified from "never contested" ON A'S TRACES. C's uncontended theorem is in the Ops model, not linked to A's wires. | B on uncontested traces; C (false) on contested ones; open |
| **SelOK** | B: `LibGapSteer.steer_pin_ok` / `steer_box_exact` (one token; select stable on `[S0, S1)` = H_S_STABLE; setup `S0 + Shi ≤ R + Rlo`, hold `F + Rhi ≤ S1 + Slo`; iff for fixed delays), `KleeneBox` (K3 versions; same right sides), `LibGapMux.join_box_exact`, `LibGapMuxN` (decode), `OpsTimed2.steer_hold_of_ackfall` (hold from the sender's ack-fall contract). C: tcheck rule E (setup only; 465/472 agree, band-only failures, C-10h); hold: no rule | `sel_read_of_steer`: one select read, PROVED BY B's `steer_pin_ok` through the embedding `rdOf` / `extZ` (A's truncated ℕ warp as B's ℤ read map; the time-0 value extended to negative time). `selOK_of_steer`: `Beh7.SelOK` for multi-bit selects from, per filtered pin and select bit, B's H_S_STABLE plus B's setup / hold against every copy's band. `selOK_of_hold`: the same with an open-ended hold (B's finite form needs a transaction end `F k`, which a run stuck inside a transaction does not have; `hold_of_window` converts) | (1) H_S_STABLE is a data-path fact (the select latch holds through each transaction: C's H_BUNDLE / H_LATCH_HOLD of the select channel); A's skeleton cuts the 32 select nets into free inputs, so it is outside A's model. (2) hold half: no checker (C has rule E for setup only). (3) DONE in `Events8BridgeSel.design_verdict8_sel`: design_verdict8 with `bh.SelOK` replaced, at every REAL filtered pin, by B's H_S_STABLE (open-ended hold) and H_SETUP_PIN on the select WIRES of the parsed netlist, with explicit bands `selLo` / `selHi` (steer gate + `top` path + stage LUT, or the stage LUT alone; `svOf_shape`, `sel_warp`). (4) virtual filtered pins (each grant's `ctl·[σ=b]` pin): their select is HARB7's σ, so SelOK there is part of H_ARB | B; bridged at netlist level (`design_verdict8_sel`), data-path premise open |
| **SelPart** | none in B / C (a token-level fact: one select value per transaction) | `selPart_of_value`: if every group of a partition is the indicator of its own pattern of ONE value sequence, SelPart holds. Choosing `sel` that way (the user chooses `sel`) discharges it | that the three decode gates of `umux21` read the same 2 bits in the same transaction is part of SelOK (per-bit windows); the partition reading `[16, 56, 57]` is trusted (cert8.py) | A by construction (given SelOK for that `sel`) |
| HDsub | — | — | probe HDsub | — |

## 3. Notes on each bridge

### 3.1 SatPin
SatPin is the semantic hypothesis "the chip is a SatPin behaviour". Nothing in B or C proves
that of the chip; C's corresponding object is also a hypothesis (`Behaves`). The useful facts:
- the inclusion is A ⊆ C (`transport_win`), so every B/C theorem about window-channel behaviours
  covers A's behaviours too (for the same netlist and bands);
- A is narrower in two exactly-identified ways (`win_origin_gap`, `win_overtake_gap`). The
  first is the time-origin assumption of §3.2; the second is H_LUT_FIFO / NoOvertake
  (FifoFidelity's `ce_not_fifo` shows a real-INIT LUT with skewed pins breaks FIFO reads of the
  pin-level excitation; A's per-pin model does not need that, but each pin's own route must still
  be FIFO).

### 3.2 Time origin and reset
`satPin_origin` makes the hidden assumption explicit: at A's time 0 the whole skeleton is a
combinational fixpoint (with rst = 1). `ringD_unsat` shows this can fail (an unreset inverter
loop has no SatPin behaviour at all). `satPin_shift` is the bridge from a physical power-up
trace: everything quiet on a window of length ≥ the largest band, then the per-pin relation.
B's `gcd_reset_binary` delivers the quiet window for every control node from ANY power-up; the
two missing links are the node map gNet ↔ d and monotone reads.

### 3.3 SelOK and SelPart
The ℤ embedding is exact where it matters: before `lo` A's warp reads time 0, B's read map
reads a negative time, and the extension `extZ` gives the time-0 value there (`rdOf_read`).
`M 0 = 0` (no transaction at time 0) rules out the reads before `lo`.

### 3.4 H_ARB
What HARB7 says about the real wires on a run: grants exclusive; a grant rises only when its
request and the virtual `ctl` (¬A0, late by ≥ the A0 → state → q → grant arcs) are read high and
σ picks it; it then rises within the grant LUT band; it falls only when both are read low. Under
contention with `ctl` already high, σ picks a winner and that grant rises within the LUT band:
a bounded arbitration time. B's digital race results show the real cell can instead oscillate
forever or overlap at the critical gap, so HARB7 is not a property of the cell, only of
uncontested use. The route to discharge it:
1. prove "never contested" on A's traces (both requests read high while no grant is held never
   happens; C has it only in the Ops model, `gcd_hw_arbiters_uncontended'`);
2. prove, in B's per-cell model with A's per-pin semantics, that an uncontested `bd_arbiter`
   with routed arcs IS a virtual-core behaviour (not done anywhere).

## 4. Lean (`formal/lean/Formal/Core/XAudit/Events8Bridge.lean`)

Imports `Events8Beh`, `Net.Fasm.Basic` (C; gives B's `CElemTiming.WinDelay`), `Cells.LibGapSteer` (B).

| theorem | statement (plain) |
|---|---|
| `warp_lo_le_hi` | a warp's band has `lo ≤ hi` |
| `transport_win` | A's transport `[lo, hi]` ⇒ B/C's `WinDelay lo hi` |
| `win_origin_gap` | a `WinDelay 1 1` pair that is not an A transport (origin) |
| `win_overtake_gap` | `ovI` (step at 2), `ovO` (high at 3, low at 4, high from 5): quiet before 3, `WinDelay 1 3`, not an A transport |
| `satPin_origin` | SatPin (any band table) ⇒ time 0 is a fixpoint of every gate |
| `PhysPin`, `satPin_shift` | per-pin monotone relation from `t0` + quiet window ⇒ the shifted trace is SatPin |
| `xs`, `find_drv`, `satPin_exists` | WF + one driver per wire + a time-0 fixpoint ⇒ a SatPin `plG` behaviour with that time-0 state and any undriven inputs |
| `satPin_exists_iff` | SatPin behaviours with time-0 state σ0 exist ⇔ σ0 is a fixpoint |
| `core_hyps_exist` | the same with constant wires 0 / 1 and reset `t < T` (undriven, rst ≠ wire 1) |
| `ringD`, `ringD_unsat` | negative control: an unreset inverter loop has no SatPin behaviour |
| `rdOf`, `extZ`, `rdOf_read` | A's ℕ warp as B's ℤ read map, exact on reads |
| `sel_read_of_steer` | one select read from B's `steer_pin_ok` |
| `selOK_of_steer` | `Beh7.SelOK` from per-bit H_S_STABLE + B's setup / hold against every copy's band |
| `sel_read_hold`, `hold_of_window`, `selOK_of_hold` | the same with an open-ended hold (covers a run that stays inside a transaction for ever); B's finite window implies it |
| `selPart_of_value` | SelPart for indicator groups of one value sequence |
| `nd7_follow`, `nd7_steady` | H_ARB gap: a virtual stage (grant) follows its agreeing pin reads with no hold; steady reads ⇒ steady from `t0 + hiF` (bounded response) |

`formal/lean/Formal/Core/XAudit/Events8BridgeSel.lean` (imports `Events8Bridge`):

| theorem | statement (plain) |
|---|---|
| `chkT_pathOK` | a successful tree check of one path is a path of existing gate inputs |
| `selLits`, `selGate`, `selLo`, `selHi`, `selFn`, `selFn_congr` | per real filtered pin: its select literals, the gate reading them, the band of each bit read, the pattern function |
| `selBase`, `svOf_shape`, `sel_warp` | the realised select `svOf` is `selFn` of the bit wires, each read through a warp in `[selLo, selHi]` |
| `design_beh8_sv` | `design_beh8`, also exposing `bh.sv = svOf` at real nodes |
| **`design_verdict8_sel`** | `design_verdict8` with `bh.SelOK` replaced by: SelOK at the VIRTUAL filtered pins only (part of H_ARB), and at the real ones, per select literal: transaction `k` starts no earlier than `R j p k`; the select wire is `vb … k` from `S0 … k` on while the source was in transaction `k` at most `hiC − selLo` before; setup `S0 + selHi ≤ R + loC` for every copy; `sel` = `selFn` of the bit values |

Plain language for `design_verdict8_sel`. Assumed: everything design_verdict8 assumes except
SelOK; SelOK at the arbiter grants' virtual σ pins; and at every real steer / mux-join / decode
pin, that each select bit's wire is stable at a per-transaction value from a time `S0` with
B's setup margin against the request copies, until the request copy can no longer show that
transaction. Proved: the same conclusion as design_verdict8. Not covered: why the select wires
are stable (they are free inputs of A's skeleton: the data path), the virtual pins' SelOK.
Non-vacuity of the new premises (argued, not mechanised): with select inputs constant from the
time-0 fixpoint, every select-bit wire is constant (SatPin), so `S0 = 0`, `vb` = that constant,
`R j p k` = the first time the source count is `2k+1` satisfy them provided no transaction
starts before `selHi − loC` (true when `T ≥ max selHi`, since counts stay 0 under reset).

What neither file covers: HARB7 (gap only), HDsub, the d ↔ gNet and d ↔ PNet node maps, the
data-path stability premise H_S_STABLE.

## 5. Joint non-vacuity

**Proved (Lean).** `core_hyps_exist`: on every well-formed netlist with one driver per wire,
undriven wires 0, 1, rw (rw ≠ wire 1), SatPin, the constants and the reset hold together as soon
as a time-0 fixpoint with wire 0 low, wire 1 high and rst high exists; `satPin_exists_iff` shows
the fixpoint is also necessary. So the outer, x-only hypotheses are jointly satisfiable exactly
when the skeleton has a reset state. `ringD_unsat`: that condition can fail.

**Untrusted evidence for gcd_hw** (`formal/lean/Wip/E8Hyp/fix0.py`, on the xaudit skeleton that
xevents8 reads, regenerated with `tools-A/xaudit/events7/rerun/prep.sh`; skeleton md5s
d af88a1eb97c8, 3 080423e23154, 4 c8bbbde45f15, 5 e1c128d599c3): Kleene iteration from all-X with
rst = 1, constants, and the 32 free select inputs X ends with all 1747 LUT outputs definite (4
sweeps) on every seed. So a binary time-0 fixpoint exists for EVERY choice of the selects (Kleene
soundness), i.e. the hypothesis of `core_hyps_exist` holds on gcd_hw (modulo the reader).
- The 16 LUTs at 1 are, by name, B's `gcd_reset_ones` set minus rst (names as listed in
  B-reset-gcd.md:161; the Lean list `ResetGcd.onesL` is gNet indices): the 9 arbiter `ustate` q
  (`ucontrol_merge2/3/4/6/9/10/11/12.uarb1`, `12.uarb2`), `usource3/5/7/13`, `uenv1`, and both
  `upsnk` elements. Two independent routes (B's Lean on gNet, this script on A's routed
  skeleton) agree.
- The grants and `R0` are 0 at the fixpoint, consistent with HARB7's time-0 conjunct.
- Negative control `--norst`: with rst X, 0/1747 outputs are definite.

**Untrusted run** (`Wip/E8Hyp/sim0.py`: one SatPin behaviour, every pin read with the fixed
slow-corner `arc_lo + lut_lo` shift, from that fixpoint, rst released at 20 ns, the selects held
constant), seed d: selects 0: 1012 output events, quiescent from 191.5 ns; selects 1: 200
events, quiescent from 57.9 ns. On both runs the two grants of every arbiter are never high
together and there is no free contest (both requests high with no grant held: 0). With constant
selects SelOK and SelPart hold for `sel` = the constant decode (argued, not mechanised: needs the
`svOf` exposure of §4). The runs stop early (the skeleton with frozen selects deadlocks), so
they are weak witnesses: a quiescent tail satisfies every count condition trivially. HARB7
(ND7 existence) and HDsub were not checked on them.

**Not done:** a Lean joint witness of HARB7, SelOK, SelPart and HDsub on a gcd_hw run (the
gcd_hw netlist is not a Lean term; xevents8 reads it at run time).

## 6. Suggested next probes
1. **E8SelC** (~0.5 d): compose `design_verdict8_sel`'s select-wire premises with C's
   H_BUNDLE / H_LATCH_HOLD of the select channels (the data latch holds while its consumer's
   request is up), and add a rule-E-style checker row for the hold half (`t + selLo ≤ u + hiC`).
2. **E8Arb** (~1 d): "never contested" on A's traces from A's own counts (the spine-token
   argument of C-8r at count level), then an uncontested `bd_arbiter` as a virtual-core behaviour
   in the per-pin model. Without both, H_ARB stays the open hypothesis it is.
3. Node maps: d ↔ gNet (names agree, §5) and d ↔ PNet (FASM), as kernel-checked tables.

## 7. Check

(pending)
