import Formal.Cells.AMergeGates
import Formal.Cells.ArbCorners

/-!
# Probe Cm2: timed arc forms of the control_merge obligations (amerge2)

Probe Cm (`B-amerge.md`, `AMerge2Proof`) proved `bdc_amerge2_0` speed
independent under the scheduling filters H_BUNDLED_IDX and H_IDX_ACK_FORK and
showed each needed. This file gives their ARC forms in the style of 7h
(`ArbHeldTimed`): time is `Int` ps, every LUT output is the rise-fast OR
channel of 7h with the REAL INIT, every route and arc a named field, and the
arbiter part of each run is 7h's / 7j's `Run` + `Scn`/`Scn2`, whose exact
traces (`g2_eq`, `g2_eq2`, `R0_lo`, `R0_lo2`, `A2_low_before`,
`A2_low_after2`, `TA_ge*`) are reused unchanged.

The cascade obligation H_RT2_CASCADE (amerge3) is in `AMergeTimedC.lean`.

## The wrapper (bdc/emit.py `emit_amerge(0, 2)`)

    bd_arbiter uarb1 (r1 = in0_req, A1 = in0_ack, r2 = in1_req, A2 = in1_ack,
                      R0 = r0, A0 = z_ack, g1, g2)
    index = g2 | in1_ack     (yosys-inferred LUT2, INIT 4'hE, pins [g2, in1_ack];
                              H_YOSYS_MAP, AMergeGates.idx2)
    uor (LUT1 2'h2) + bd_delay_gated #(DELAY) : r0 -> z_req

`index = 1` names client 2 (`in1`), `index = 0` client 1 (`in0`).

## Model of the wrapper's own parts (`Wd`, all named)

* index LUT: `Idx`, the 7h rise-fast OR channel of `idx2` (INIT 0xE through
  `lutB`): `Idx t = idx2 (g2 view, A2 view at xr) || idx2 (.. at xf)`, each
  pin delayed by its route (`wgi`, `wai`, site pin included).
* consumer: the index is captured at a point reached through `wid` (pure
  transport, the index's route + any fork/latch-D path, max side, H_WIRE_TRANSPORT);
  the request reaches that point `dz` after R0 (uor arc + DELAY line rise +
  z_req route + consumer enable path, min side; H_REQ_PATH, `ReqZ`). The
  capture needs the index settled `su` before the request (setup).
* the capture instant `Zr` of the NEW token is any instant caused by R0 being
  high at some `u` after R0 fell for the previous token (`ReqZ`); the minimal
  case `Zr = RR + dz` is the one the counter-traces use.
-/

namespace Formal.Cells.AMergeTimed
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-! ## The inferred index LUT (amerge2) -/

/-- `index = g2 | in1_ack`, the REAL inferred INIT (`AMergeGates.idx2`, 4'hE). -/
abbrev IX (g a : Bool) : Bool := AMergeGates.idx2 g a

theorem IX_eq (g a : Bool) : IX g a = (g || a) := AMergeGates.idx2_eq g a

/-- The wrapper's delays (ps). Every field is a named hypothesis about the
routed design. Test: routed SDF INTERCONNECT + prjxray site-pin and IOPATH
data (cell_constraints.json `conventions.arc_kinds`); GLS assertion
"index stable at z_req capture". -/
structure Wd where
  /-- route `g2` (ugrant.O6) -> index LUT pin I0, incl. site pin. -/
  wgi : Int
  /-- route `in1_ack` (ua2.O6) -> index LUT pin I1, incl. site pin. -/
  wai : Int
  /-- index LUT O6 arcs (prjxray: flat over pins; rise = fall per corner). -/
  xr : Int
  xf : Int
  /-- index output -> consumer capture point (max side, H_WIRE_TRANSPORT). -/
  wid : Int
  /-- R0 -> uor -> bd_delay_gated (rise) -> z_req -> consumer capture point
  (min side, H_REQ_PATH). -/
  dz : Int
  /-- consumer setup. -/
  su : Int
  /-- H_NONNEG: causality. -/
  H_NONNEG : 0 ≤ wgi ∧ 0 ≤ wai ∧ 0 ≤ wid ∧ 0 ≤ dz ∧ 0 ≤ su
  /-- H_ARC_POS: a LUT arc is positive (45 ps at FAST_MIN). -/
  H_ARC_POS : 0 < xr
  /-- H_RISE_LE_FALL (7h): what makes the OR channel rise-fast; prjxray gives
  rise = fall per corner, which satisfies it. -/
  H_RISE_LE_FALL : xr ≤ xf

/-- The index LUT output (rise-fast OR channel of the real INIT). -/
def Idx (W : Wd) (s : Sigs) (t : Int) : Bool :=
  IX (s.g2 (t - W.wgi - W.xr)) (s.A2 (t - W.wai - W.xr)) ||
  IX (s.g2 (t - W.wgi - W.xf)) (s.A2 (t - W.wai - W.xf))

/-- The index as the consumer sees it. -/
def Cons (W : Wd) (s : Sigs) (t : Int) : Bool := Idx W s (t - W.wid)

theorem idx_of_g (W : Wd) (s : Sigs) (t : Int) (h : s.g2 (t - W.wgi - W.xr) = true) :
    Idx W s t = true := by
  unfold Idx; rw [IX_eq, h]; simp

theorem idx_of_gf (W : Wd) (s : Sigs) (t : Int) (h : s.g2 (t - W.wgi - W.xf) = true) :
    Idx W s t = true := by
  unfold Idx; rw [IX_eq, IX_eq, h]; simp

theorem idx_of_a (W : Wd) (s : Sigs) (t : Int) (h : s.A2 (t - W.wai - W.xr) = true) :
    Idx W s t = true := by
  unfold Idx; rw [IX_eq, h]; simp

theorem idx_false (W : Wd) (s : Sigs) (t : Int)
    (h1 : s.g2 (t - W.wgi - W.xr) = false) (h2 : s.A2 (t - W.wai - W.xr) = false)
    (h3 : s.g2 (t - W.wgi - W.xf) = false) (h4 : s.A2 (t - W.wai - W.xf) = false) :
    Idx W s t = false := by
  unfold Idx; rw [IX_eq, IX_eq, h1, h2, h3, h4]; rfl

/-- **H_REQ_PATH.** The consumer captures the new token at `Zr`, caused (through
uor, the DELAY line and the z_req route, together at least `dz`) by R0 being
high at an instant `u` after R0 fell for the previous token at `TRx`. -/
def ReqZ (s : Sigs) (TRx Hz Zr dz : Int) : Prop :=
  ∃ u, TRx ≤ u ∧ u < Hz ∧ u + dz ≤ Zr ∧ s.R0 u = true

section
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

/-! ## H_BUNDLED_IDX, race 1: the new owner's grant (client 1 -> client 2) -/

/-- The request cannot reach the consumer before `RR + dz` (R0 is low on `[TR, RR)`). -/
theorem Zr_ge (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) {W : Wd} {Zr : Int}
    (hZ : ReqZ s (TR D t0) Hz Zr W.dz) : RR D TA + W.dz ≤ Zr := by
  obtain ⟨u, h1, h2, h3, h4⟩ := hZ
  by_cases hc : u < RR D TA
  · rw [R0_lo R S u h1 hc h2] at h4; exact absurd h4 (by simp)
  · omega

/-- **H_BUNDLED_IDX (new owner), arc form.** Launch: `q`'s fall at ustate O6.
Data: q -> ugrant.I2 (`wq`) -> g2 rise (`g2r`) -> index pin (`wgi`) -> index
rise (`xr`) -> consumer (`wid`) + setup (`su`). Request: q -> ustate.I2
(`wfb`) -> R0 rise (O5 from I2, `Rrq`) -> uor + DELAY + z_req (`dz`). -/
def BidxA (D : Dl) (W : Wd) : Prop :=
  D.wq + D.g2r + W.wgi + W.xr + W.wid + W.su ≤ D.wfb + D.Rrq + W.dz

/-- **Sufficiency.** Under `BidxA` the consumer sees `index = 1` (client 2, the
new owner) from `su` before the capture to the horizon, for every server, every
capture instant allowed by H_REQ_PATH, every run of the real arbiter. -/
theorem bidx_new_owner (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) {W : Wd} {Zr : Int}
    (hZ : ReqZ s (TR D t0) Hz Zr W.dz) (H : BidxA D W) :
    ∀ t, Zr - W.su ≤ t → t - W.wid - W.wgi - W.xr < Hz → Cons W s t = true := by
  intro t h1 h2
  have hz := Zr_ge R S hZ
  have := W.H_NONNEG
  unfold Cons; apply idx_of_g
  rw [g2_eq R S _ (by omega)]
  unfold BidxA at H; unfold RR at hz; unfold G2
  simp; omega

/-- **Counter-trace.** If `BidxA` fails, then with the minimal request path
(`Zr = RR + dz`) the consumer still sees `index = 0` (the PREVIOUS owner,
client 1) `su` before the capture of client 2's token. Needs 7g's fork
(`A0Fork`, so A2 is still low) and H_Z_IN_SRV: the server's minimum response
`smin` (R0 -> ... -> z_ack) includes the request path `dz` (the consumer
acknowledges only what it captured). -/
theorem bidx_new_owner_counter (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) {W : Wd}
    (H_fork : A0Fork D) (H_Z_IN_SRV : W.dz ≤ D.smin) (hnot : ¬ BidxA D W) :
    Cons W s (RR D TA + W.dz - W.su) = false := by
  have := W.H_NONNEG; have := W.H_ARC_POS; have := W.H_RISE_LE_FALL
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  have ho := S.H_ORDER
  have hTA2 := TA2_ge R S
  have hlow := A2_low_before R S (by unfold A0Fork at H_fork; unfold G2 QB; omega)
  unfold BidxA at hnot
  unfold Cons
  apply idx_false
  · rw [g2_eq R S _ (by omega)]; unfold G2 RR at *; simp; omega
  · exact hlow _ (by unfold T2; omega) (by omega)
  · rw [g2_eq R S _ (by omega)]; unfold G2 RR at *; simp; omega
  · exact hlow _ (by unfold T2; omega) (by omega)

/-! ## H_BUNDLED_IDX, race 2: the previous owner's ack tail (client 2 -> client 1) -/

/-- In the mirror handover A2 stays high until `T1b` (its fall instant): the
C-element holds through its own feedback while g2 or A0 is high at its pins. -/
theorem A2_hi_before2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, t < T1b D t0 TA → t < Hz → s.A2 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER; have := S.H_SETTLED
  refine int_ind (fun t => t < T1b D t0 TA → t < Hz → s.A2 t = true) t0
    (fun t ht _ _ => S.H_A2_init t ht) ?_
  intro t ht ih hb hz
  rw [R.H_A2 t, CE_eq, CE_eq, ih (t - D.wfa2 - D.c2f) (by omega) (by omega) (by omega)]
  by_cases hg : t - D.wg2 - D.c2f < G2b D t0 TA
  · have e : s.g2 (t - D.wg2 - D.c2f) = true := by
      rw [g2_eq2 R S _ (by omega)]; simp [hg]
    rw [e]; simp
  · have hA : t - D.wa02 - D.c2f < TA := by unfold T1b at hb; omega
    have e : s.A0 (t - D.wa02 - D.c2f) = true := A0_hi1b S _ (by omega) hA
    rw [e]; simp

theorem Zr_ge2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) {W : Wd} {Zr : Int}
    (hZ : ReqZ s (TRb D t0) Hz Zr W.dz) : RRb D TA + W.dz ≤ Zr := by
  obtain ⟨u, h1, h2, h3, h4⟩ := hZ
  by_cases hc : u < RRb D TA
  · rw [R0_lo2 R S u h1 hc h2] at h4; exact absurd h4 (by simp)
  · omega

/-- **H_BUNDLED_IDX (previous owner), arc form.** The index must have FALLEN
(client 1 now owns) `su` before the capture. `ack` is the race named in
B-amerge.md: A0 fall -> ua2.I1 (`wa02`) -> A2 fall (`c2f`) -> index pin
(`wai`) -> index fall (`xf`) -> consumer (`wid`) + `su`, against A0 fall ->
ustate.I4 (`wa0s`) -> q rise (`qr`) -> ustate.I2 (`wfb`) -> R0 rise (`Rrq`) ->
`dz`. `gack` and `grant` are the g2 legs (g2's fall at ua2 and at the index
LUT), each OR-ed over g2's two fall causes (r2 via I1, q via I2): the r2 leg
contains a whole server response `smin` and holds with large margin. -/
structure BidxB (D : Dl) (W : Wd) : Prop where
  ack : D.wa02 + D.c2f + W.wai + W.xf + W.wid + W.su ≤ D.wa0s + D.qr + D.wfb + D.Rrq + W.dz
  gack : D.wr2g + D.g2f + D.wg2 + D.c2f + W.wai + W.xf + W.wid + W.su ≤
      D.wr2s + D.Rf2 + D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + W.dz ∨
    D.wq + D.g2f + D.wg2 + D.c2f + W.wai + W.xf + W.wid + W.su ≤ D.wfb + D.Rrq + W.dz
  grant : D.wr2g + D.g2f + W.wgi + W.xf + W.wid + W.su ≤
      D.wr2s + D.Rf2 + D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + W.dz ∨
    D.wq + D.g2f + W.wgi + W.xf + W.wid + W.su ≤ D.wfb + D.Rrq + W.dz

/-- **Sufficiency.** Under `BidxB` and the arbiter's own RT2b (needed so that
A2 falls at all), the consumer sees `index = 0` from `su` before the capture of
client 1's token to the horizon, for every server and every capture instant. -/
theorem bidx_old_owner (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) {W : Wd} {Zr : Int}
    (H_RT2 : RT2b D) (hZ : ReqZ s (TRb D t0) Hz Zr W.dz) (H : BidxB D W) :
    ∀ t, Zr - W.su ≤ t → t - W.wid < Hz → Cons W s t = false := by
  intro t h1 h2
  have hz := Zr_ge2 R S hZ
  have := W.H_NONNEG; have := W.H_ARC_POS; have := W.H_RISE_LE_FALL
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  have hTA := TA_ge2 R S
  have hTA2 := TA2_ge2 R S
  obtain ⟨b1, b2, b3⟩ := H
  obtain ⟨p1, p2, p3, p4⟩ := H_RT2
  have hlow := A2_low_after2 R S (by unfold T1b G2b QBb; unfold TRb at hTA; unfold RRb QBb at hTA2; omega)
  unfold TRb at hTA; unfold RRb QBb at hz
  unfold Cons
  apply idx_false
  · rw [g2_eq2 R S _ (by omega)]; unfold G2b QBb; simp; omega
  · exact hlow _ (by unfold T1b G2b QBb; omega) (by omega)
  · rw [g2_eq2 R S _ (by omega)]; unfold G2b QBb; simp; omega
  · exact hlow _ (by unfold T1b G2b QBb; omega) (by omega)

/-- **Counter-trace (the ack race).** If the A0 -> ua2 -> A2 -> index leg (at
the rise arc `xr`; = `xf` at a consistent corner) is slower than the A0 -> q ->
R0 -> z_req leg, then with the minimal request path the consumer still sees
`index = 1` (the PREVIOUS owner, client 2) `su` before the capture of client
1's token. For every server: TA cancels. -/
theorem bidx_old_owner_counter (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) {W : Wd}
    (hnot : D.wa0s + D.qr + D.wfb + D.Rrq + W.dz < D.wa02 + D.c2f + W.wai + W.xr + W.wid + W.su)
    (hz : RRb D TA + W.dz - W.su - W.wid - W.wai - W.xr < Hz) :
    Cons W s (RRb D TA + W.dz - W.su) = true := by
  unfold Cons; apply idx_of_a
  apply A2_hi_before2 R S _ _ hz
  unfold T1b RRb QBb; omega

/-- **Counter-trace (the grant leg).** If g2's fall has not reached the index LUT
(at its rise-arc view) by the setup instant, the stale index is 1 as well. -/
theorem bidx_old_owner_counter_g (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) {W : Wd}
    (hnot : RRb D TA + W.dz - W.su - W.wid - W.wgi - W.xr < G2b D t0 TA)
    (hz : RRb D TA + W.dz - W.su - W.wid - W.wgi - W.xr < Hz) :
    Cons W s (RRb D TA + W.dz - W.su) = true := by
  unfold Cons; apply idx_of_g
  rw [g2_eq2 R S _ hz]
  have : RRb D TA + W.dz - W.su - W.wid - W.wgi - W.xr =
      RRb D TA + W.dz - W.su - W.wid - W.wgi - W.xr := rfl
  simp only [decide_eq_true_eq]; omega

end

/-! ## H_IDX_ACK_FORK: the `in1_ack` fork into the index LUT vs the client loop

After client 2 has been served, its ack A2 rises at `Ar`; the client sees it and
drops `r2` at `t1 ≥ Ar + cmin` (H_CLIENT_MIN: `cmin` is the minimum client
response from A2 at ua2's output, its route to the client included). g2 then
falls (ugrant O6, real INIT, 7h's channel), and `index = g2 | A2` must stay 1:
A2's rise must reach the index LUT before g2's fall does. Only ugrant's
relation is needed (`H_g2`, 7h's `Run.H_g2` verbatim), q being held low by A0
(H_Q_HELD: `ArbHeldTimed.FS_hold`, A0 high holds q). -/

/-- The fork scenario (window `[Tq, Hz)`, horizon before A2 falls). -/
structure FkScn (D : Dl) (W : Wd) (s : Sigs) (Tq Ar t1 Hz cmin : Int) : Prop where
  H_ORDER : Tq ≤ Ar ∧ Ar < t1 ∧ t1 < Hz
  /-- H_Q_HELD: q low through the window (client 2 owns, held by A0). -/
  H_q : ∀ t, Tq ≤ t → t < Hz → s.q t = false
  /-- client 2's request: high, drops at `t1`. -/
  H_r2 : ∀ t, Tq ≤ t → t < Hz → s.r2 t = decide (t < t1)
  /-- client 2's ack: rises at `Ar`, high to the horizon. -/
  H_A2 : ∀ t, Tq ≤ t → t < Hz → s.A2 t = decide (Ar ≤ t)
  /-- H_CLIENT_MIN. -/
  H_CLIENT : Ar + cmin ≤ t1
  /-- H_SETTLED: r2 and q were settled in g2's and the index's views before
  A2 rose (g2 rose long before: A2 = C(g2, A0)). -/
  H_SETTLED : Tq + D.wr2g + D.wq + D.g2f + W.wgi + W.xf ≤ Ar ∧ Tq + W.wai + W.xf ≤ Ar

/-- **H_IDX_ACK_FORK, arc form.** Launch: A2 rise at ua2.O6. Data: A2 ->
index.I1 (`wai`) -> index (`xr`). Request (the other fork branch): A2 ->
client -> r2 fall (`cmin`) -> ugrant.I1 (`wr2g`) -> g2 fall (`g2f`) ->
index.I0 (`wgi`) -> index (`xf`). -/
def IdxAckFork (D : Dl) (W : Wd) (cmin : Int) : Prop :=
  W.wai + W.xr ≤ cmin + D.wr2g + D.g2f + W.wgi + W.xf

section
variable {D : Dl} {W : Wd} {s : Sigs} {Tq Ar t1 Hz cmin : Int}

/-- **Sufficiency.** Under `IdxAckFork` the index stays 1 from A2's rise to the
horizon (no low glitch while client 2's token is still acknowledged). -/
theorem idx_ack_fork_hold
    (hg2 : ∀ t, s.g2 t =
      (FG2 (s.r1 (t - D.wr1g - D.g2r)) (s.r2 (t - D.wr2g - D.g2r)) (s.q (t - D.wq - D.g2r)) ||
       FG2 (s.r1 (t - D.wr1g - D.g2f)) (s.r2 (t - D.wr2g - D.g2f)) (s.q (t - D.wq - D.g2f))))
    (F : FkScn D W s Tq Ar t1 Hz cmin) (H : IdxAckFork D W cmin) :
    ∀ t, Ar ≤ t → t < Hz → Idx W s t = true := by
  intro t h1 h2
  have := W.H_NONNEG; have := W.H_ARC_POS; have := W.H_RISE_LE_FALL
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  have ho := F.H_ORDER; have hs := F.H_SETTLED; have hc := F.H_CLIENT
  unfold IdxAckFork at H
  by_cases hA : Ar ≤ t - W.wai - W.xr
  · apply idx_of_a; rw [F.H_A2 _ (by omega) (by omega)]; simp [hA]
  · apply idx_of_gf
    rw [hg2, FG2_eq, FG2_eq, F.H_r2 (t - W.wgi - W.xf - D.wr2g - D.g2f) (by omega) (by omega),
      F.H_q (t - W.wgi - W.xf - D.wq - D.g2f) (by omega) (by omega)]
    have : t - W.wgi - W.xf - D.wr2g - D.g2f < t1 := by omega
    simp [this]

/-- **Counter-trace.** If A2's rise reaches the index LUT after g2's fall (the
actual client was fast), the index is 0 at the instant g2's fall arrives, while
A2 is high at its source: the index has stopped naming client 2 inside its
token's acknowledge phase. -/
theorem idx_ack_fork_counter
    (hg2 : ∀ t, s.g2 t =
      (FG2 (s.r1 (t - D.wr1g - D.g2r)) (s.r2 (t - D.wr2g - D.g2r)) (s.q (t - D.wq - D.g2r)) ||
       FG2 (s.r1 (t - D.wr1g - D.g2f)) (s.r2 (t - D.wr2g - D.g2f)) (s.q (t - D.wq - D.g2f))))
    (F : FkScn D W s Tq Ar t1 Hz cmin)
    (hnot : t1 + D.wr2g + D.g2f + W.wgi + W.xf < Ar + W.wai + W.xr)
    (hz : t1 + D.wr2g + D.g2f + W.wgi + W.xf < Hz) :
    s.A2 (t1 + D.wr2g + D.g2f + W.wgi + W.xf) = true ∧
    Idx W s (t1 + D.wr2g + D.g2f + W.wgi + W.xf) = false := by
  have := W.H_NONNEG; have := W.H_ARC_POS; have := W.H_RISE_LE_FALL
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  have ho := F.H_ORDER; have hs := F.H_SETTLED
  have gl : ∀ τ, t1 + D.wr2g + D.g2f ≤ τ → τ < Hz → s.g2 τ = false := by
    intro τ h1 h2
    rw [hg2, FG2_eq, FG2_eq, F.H_r2 (τ - D.wr2g - D.g2r) (by omega) (by omega),
      F.H_r2 (τ - D.wr2g - D.g2f) (by omega) (by omega)]
    have e1 : ¬ (τ - D.wr2g - D.g2r < t1) := by omega
    have e2 : ¬ (τ - D.wr2g - D.g2f < t1) := by omega
    simp [e1, e2]
  refine ⟨by rw [F.H_A2 _ (by omega) hz]; simp; omega, ?_⟩
  apply idx_false
  · exact gl _ (by omega) (by omega)
  · rw [F.H_A2 _ (by omega) (by omega)]; simp; omega
  · exact gl _ (by omega) (by omega)
  · rw [F.H_A2 _ (by omega) (by omega)]; simp; omega

/-- With the minimal client (`t1 = Ar + cmin`), `¬ IdxAckFork` is exactly the
counter-trace's condition: the arc inequality is necessary and sufficient. -/
theorem idx_ack_fork_counter_minclient
    (hg2 : ∀ t, s.g2 t =
      (FG2 (s.r1 (t - D.wr1g - D.g2r)) (s.r2 (t - D.wr2g - D.g2r)) (s.q (t - D.wq - D.g2r)) ||
       FG2 (s.r1 (t - D.wr1g - D.g2f)) (s.r2 (t - D.wr2g - D.g2f)) (s.q (t - D.wq - D.g2f))))
    (F : FkScn D W s Tq Ar t1 Hz cmin) (hmin : t1 = Ar + cmin) (hnot : ¬ IdxAckFork D W cmin)
    (hz : t1 + D.wr2g + D.g2f + W.wgi + W.xf < Hz) :
    s.A2 (t1 + D.wr2g + D.g2f + W.wgi + W.xf) = true ∧
    Idx W s (t1 + D.wr2g + D.g2f + W.wgi + W.xf) = false := by
  unfold IdxAckFork at hnot
  exact idx_ack_fork_counter hg2 F (by omega) hz

/-- **The glitch is inside z_ack's high phase** whenever z_ack (A0) cannot fall
before `t1 + wr2s + Rf2 + smin` (7j's `TA_ge2`: r2 -> R0 -> server) and the
r2 -> g2 -> index leg is shorter than that: so the consumer, which holds its
data until z_ack falls (the library's broad window), reads a wrong index. -/
theorem idx_ack_fork_in_window {TAf : Int} (hTAf : t1 + D.wr2s + D.Rf2 + D.smin ≤ TAf)
    (hleg : D.wr2g + D.g2f + W.wgi + W.xf < D.wr2s + D.Rf2 + D.smin) :
    t1 + D.wr2g + D.g2f + W.wgi + W.xf < TAf := by omega

end

end Formal.Cells.AMergeTimed
