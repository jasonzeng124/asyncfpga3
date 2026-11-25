import Formal.Cells.AMergeTimedW

/-!
# Probe Cm2: H_RT2_CASCADE (bdc_amerge3_0), timed arc form

`bdc_amerge3_0` cascades two `bd_arbiter`s: `uarb2.r1 = uarb1.R0`
(`acc1_req`), `uarb1.A0 = uarb2.A1` (`acc1_ack`), `uarb2.R0 = r0` -> uor ->
DELAY -> `z_req`, `uarb2.A0 = z_ack`. So arbiter 1's SERVER is arbiter 2's
ustate O5 + its own server + its ack C-element `ua1`. 7h's RT2 for arbiter 1
(`ArbHeldTimed.rt2_exclusion`) needs the server's response bounds `TA ≥ TR +
smin` and `TA2 ≥ RR + smin`; here they are DERIVED from arbiter 2's gates
(real INITs, 7h's channels) and arbiter 2's server (H_SERVER_MIN with `smin`
of arbiter 2 = uor + DELAY + consumer -> z_ack):

* fall response `sF = wr1s + Rf1 + smin + wa01 + c1f` (arbiter 2's fields):
  acc1_req fall -> uarb2.ustate.I0 -> R0 fall (O5) -> server -> z_ack fall ->
  uarb2.ua1.I1 -> acc1_ack fall;
* rise response `sR = wr1s + Rr1 + smin + wa01 + c1r`: the same for the rise.

`rt2_cascade` (client 1 -> client 2 of arbiter 1) and `rt2_cascade2` (the
mirror) are then 7h's / 7j's RT2 with `2·smin` split into `sF + sR` and the
pulse/fork legs using `sR`. Arbiter 2 is restricted to the case where it stays
with `acc1` during arbiter 1's handover (its own input `in2` idle; q2 = 1),
the case where acc1_ack's low phase is shortest.
-/

namespace Formal.Cells.AMergeTimedC
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

theorem FS_keep : ∀ r1 a0 : Bool, FS r1 false true a0 = true := by decide

/-- Arbiter 2's fall response as arbiter 1's server (ps). -/
def sF (D2 : Dl) : Int := D2.wr1s + D2.Rf1 + D2.smin + D2.wa01 + D2.c1f
/-- Arbiter 2's rise response as arbiter 1's server (ps). -/
def sR (D2 : Dl) : Int := D2.wr1s + D2.Rr1 + D2.smin + D2.wa01 + D2.c1r

/-- The cascade seen from arbiter 2 (`uarb2`), during one handover of arbiter 1:
its client-1 request `acc1_req` (= arbiter 1's R0) is high before `TRx`, low on
`[TRx, RRx)`; its client-1 ack `acc1_ack` (= arbiter 1's A0) is high on
`[ta, TA)`, low on `[TA, TA2)`, high from `TA2`; z_ack (arbiter 2's A0) is
high on `[tz, TZ)`, low on `[TZ, TZ2)`, high from `TZ2`; `TZ`, `TZ2`, `TA`,
`TA2` free. -/
structure CScn (D2 : Dl) (s2 : Sigs) (TRx RRx ta TA TA2 tz TZ TZ2 Hz : Int) : Prop where
  H_ORDER : ta < TA ∧ TA < TA2 ∧ TA2 < Hz ∧ tz < TZ ∧ TZ < TZ2 ∧ TZ2 < Hz ∧ TRx ≤ TA
  H_acc_hi : ∀ t, t < TRx → t < Hz → s2.r1 t = true
  H_acc_lo : ∀ t, TRx ≤ t → t < RRx → t < Hz → s2.r1 t = false
  /-- arbiter 2's own client (`in2`) idle during the window. -/
  H_r2 : ∀ t, t < Hz → s2.r2 t = false
  /-- arbiter 2 owned by `acc1` before the window (q2 = 1). -/
  H_q_init : ∀ t, t < tz → s2.q t = true
  H_ack : ∀ t, ta ≤ t → t < Hz → s2.A1 t = (decide (t < TA) || decide (TA2 ≤ t))
  H_Z : ∀ t, tz ≤ t → t < Hz → s2.A0 t = (decide (t < TZ) || decide (TZ2 ≤ t))
  H_Z_prev : s2.A0 (tz - 1) = false
  /-- H_SETTLED: acc1_ack's rise and z_ack's rise had reached ua1's views
  before acc1_req fell (the four-phase order z_ack↑ -> acc1_ack↑ -> ... ->
  acc1_req↓). -/
  H_SETTLED : ta + D2.wfa1 + D2.c1f ≤ TRx ∧ tz + D2.wa01 + D2.c1f ≤ TRx
  /-- H_ACK1_PULSE: acc1_ack's low phase outlasts uarb2.ua1's own loop (the
  `bd_c2.pulse_width` obligation of instance uarb2.ua1; no runt). -/
  H_PULSE : TA + D2.wfa1 + D2.c1f ≤ TA2

section
variable {D2 : Dl} {s2 : Sigs} {TRx RRx ta TA TA2 tz TZ TZ2 Hz : Int}

theorem q2_hi (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    ∀ t, t < Hz → s2.q t = true := by
  have := D2.H_NONNEG; have := D2.H_LOOP_POS; have := C.H_ORDER
  refine int_ind (fun t => t < Hz → s2.q t = true) tz (fun t ht _ => C.H_q_init t ht) ?_
  intro t _ ih hz
  rw [R2.H_q t, C.H_r2 (t - D2.wr2s - D2.qr) (by omega),
    ih (t - D2.wfb - D2.qr) (by omega) (by omega), FS_keep]
  rfl

theorem R0_2_hi (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    ∀ u, u < TRx + D2.wr1s + D2.Rf1 → u < Hz → s2.R0 u = true := by
  intro u h1 h2
  have := D2.H_NONNEG; have := D2.H_RISE_LE_FALL
  rw [R2.H_R0 u, FR_eq, FR_eq, C.H_acc_hi (u - D2.wr1s - D2.Rf1) (by omega) (by omega),
    q2_hi R2 C (u - D2.wfb - D2.Rfq) (by omega)]
  simp

theorem R0_2_lo (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    ∀ u, TRx + D2.wr1s + D2.Rf1 ≤ u → u < RRx + D2.wr1s + D2.Rr1 → u < Hz →
      s2.R0 u = false := by
  intro u h1 h2 h3
  have := D2.H_NONNEG; have := D2.H_RISE_LE_FALL
  rw [R2.H_R0 u, FR_eq, FR_eq, C.H_acc_lo (u - D2.wr1s - D2.Rr1) (by omega) (by omega) (by omega),
    C.H_acc_lo (u - D2.wr1s - D2.Rf1) (by omega) (by omega) (by omega),
    C.H_r2 (u - D2.wr2s - D2.Rr2) (by omega), C.H_r2 (u - D2.wr2s - D2.Rf2) (by omega)]
  simp

/-- z_ack cannot fall before `TRx + wr1s + Rf1 + smin`. -/
theorem TZ_ge (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    TRx + D2.wr1s + D2.Rf1 + D2.smin ≤ TZ := by
  have ho := C.H_ORDER
  have := D2.H_NONNEG
  have e1 : s2.A0 TZ = false := by rw [C.H_Z TZ (by omega) (by omega)]; simp; omega
  have e0 : s2.A0 (TZ - 1) = true := by rw [C.H_Z _ (by omega) (by omega)]; simp; omega
  obtain ⟨u, hu, hR, hv⟩ := R2.H_SRV TZ (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : tz ≤ u := by
    by_cases hc : tz ≤ u
    · exact hc
    · have := hv (tz - 1) (by omega) (by omega)
      rw [C.H_Z_prev, e0] at this; exact absurd this (by simp)
  by_cases hc : TRx + D2.wr1s + D2.Rf1 + D2.smin ≤ TZ
  · exact hc
  · have := R0_2_hi R2 C u (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- acc1_ack cannot fall before z_ack's fall has crossed ua1's fall arc. -/
theorem TA_ge_c (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    TZ + D2.wa01 + D2.c1f ≤ TA := by
  have ho := C.H_ORDER; have hs := C.H_SETTLED
  have := D2.H_NONNEG; have := D2.H_RISE_LE_FALL; have := D2.H_LOOP_POS
  have hA : s2.A1 TA = false := by rw [C.H_ack TA (by omega) (by omega)]; simp; omega
  refine Classical.byContradiction fun hc => ?_
  have e1 : s2.A1 (TA - D2.wfa1 - D2.c1f) = true := by
    rw [C.H_ack _ (by omega) (by omega)]; simp; omega
  have e2 : s2.A0 (TA - D2.wa01 - D2.c1f) = true := by
    rw [C.H_Z _ (by omega) (by omega)]; simp; omega
  rw [R2.H_A1 TA] at hA
  simp only [CE_eq, e1, e2] at hA
  simp at hA

/-- z_ack cannot re-rise before `RRx + wr1s + Rr1 + smin`. -/
theorem TZ2_ge (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    RRx + D2.wr1s + D2.Rr1 + D2.smin ≤ TZ2 := by
  have ho := C.H_ORDER
  have := D2.H_NONNEG
  have hTZ := TZ_ge R2 C
  have e1 : s2.A0 TZ2 = true := by rw [C.H_Z TZ2 (by omega) (by omega)]; simp
  have e0 : s2.A0 (TZ2 - 1) = false := by rw [C.H_Z _ (by omega) (by omega)]; simp; omega
  obtain ⟨u, hu, hR, hv⟩ := R2.H_SRV TZ2 (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : TZ ≤ u := by
    by_cases hc : TZ ≤ u
    · exact hc
    · have := hv (TZ - 1) (by omega) (by omega)
      rw [C.H_Z (TZ - 1) (by omega) (by omega), e0] at this; simp at this <;> omega
  by_cases hc : RRx + D2.wr1s + D2.Rr1 + D2.smin ≤ TZ2
  · exact hc
  · have := R0_2_lo R2 C u (by omega) (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- acc1_ack cannot re-rise before z_ack's re-rise has crossed ua1's rise arc. -/
theorem TA2_ge_c (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    TZ2 + D2.wa01 + D2.c1r ≤ TA2 := by
  have ho := C.H_ORDER; have hp := C.H_PULSE; have hs := C.H_SETTLED
  have := D2.H_NONNEG; have := D2.H_RISE_LE_FALL; have := D2.H_LOOP_POS
  have hTA := TA_ge_c R2 C
  have hA : s2.A1 TA2 = true := by rw [C.H_ack TA2 (by omega) (by omega)]; simp
  refine Classical.byContradiction fun hc => ?_
  have view : ∀ d, D2.c1r ≤ d → d ≤ D2.c1f →
      CE (s2.g1 (TA2 - D2.wg1 - d)) (s2.A0 (TA2 - D2.wa01 - d)) (s2.A1 (TA2 - D2.wfa1 - d)) =
        false := by
    intro d hd1 hd2
    have f1 : s2.A1 (TA2 - D2.wfa1 - d) = false := by
      rw [C.H_ack _ (by omega) (by omega)]; simp; omega
    have f2 : s2.A0 (TA2 - D2.wa01 - d) = false := by
      rw [C.H_Z _ (by omega) (by omega)]; simp; omega
    rw [f1, f2, CE_eq]; simp
  rw [R2.H_A1 TA2, view D2.c1r (by omega) (by omega), view D2.c1f (by omega) (by omega)] at hA
  simp at hA

/-- **The cascade server.** Arbiter 2 + its server, seen as arbiter 1's server,
answers acc1_req's fall no sooner than `sF` and its rise no sooner than `sR`. -/
theorem cascade_server (R2 : Run D2 s2) (C : CScn D2 s2 TRx RRx ta TA TA2 tz TZ TZ2 Hz) :
    TRx + sF D2 ≤ TA ∧ RRx + sR D2 ≤ TA2 := by
  have := TZ_ge R2 C; have := TA_ge_c R2 C; have := TZ2_ge R2 C; have := TA2_ge_c R2 C
  unfold sF sR; constructor <;> omega

end

/-! ## Arbiter 1's RT2 with the cascade server -/

/-- **H_RT2_CASCADE, arc form (client 1 -> client 2 of arbiter 1).** 7h's
`RT2` fields with arbiter 1's `smin` replaced by the derived cascade responses:
one rise response `sR` where 7h has one `smin` (pulse, forkA), `sF + sR` where
7h has `2·smin` (g1, forkG). The tightest leg (`pulse`) reads: ua_i's fall
loop of arbiter 1 (`c1f + wfa1`) <= acc1_ack fall -> uarb1.ustate -> q ->
R0 (acc1_req) rise (`wa0s + qf + wfb + Rrq`) -> uarb2.ustate.I0 -> R0 ->
uor + DELAY + consumer -> z_ack -> uarb2.ua1 -> acc1_ack rise (`sR`). -/
structure RT2C (D : Dl) (sF sR : Int) : Prop where
  pulse : D.c1f + D.wfa1 ≤ D.wa0s + D.qf + D.wfb + D.Rrq + sR
  g1 : D.wr1g + D.g1f1 + D.wg1 + D.c1f + D.wfa1 ≤
    D.wr1s + D.Rf1 + sF + sR + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa01
  forkA : D.wa01 + D.c1f ≤ D.wa0s + D.qf + D.wfb + D.Rrq + sR + D.wa02 + D.c2r
  forkG : D.wr1g + D.g1f1 + D.wg1 + D.c1f ≤
    D.wr1s + D.Rf1 + sF + sR + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa02 + D.c2r

/-- Mirror direction (client 2 -> client 1 of arbiter 1): 7j's `RT2b` likewise. -/
structure RT2Cb (D : Dl) (sF sR : Int) : Prop where
  pulse : D.c2f + D.wfa2 ≤ D.wa0s + D.qr + D.wfb + D.Rrq + sR
  g2 : D.wr2g + D.g2f + D.wg2 + D.c2f + D.wfa2 ≤
    D.wr2s + D.Rf2 + sF + sR + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa02
  forkA : D.wa02 + D.c2f ≤ D.wa0s + D.qr + D.wfb + D.Rrq + sR + D.wa01 + D.c1r
  forkG : D.wr2g + D.g2f + D.wg2 + D.c2f ≤
    D.wr2s + D.Rf2 + sF + sR + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa01 + D.c1r

/-- Arbiter 2's side of the cascade that is not determined by arbiter 1's run. -/
structure CSide (D2 : Dl) (s2 : Sigs) (TRx ta TA TA2 tz TZ TZ2 Hz : Int) : Prop where
  H_ORDER : tz < TZ ∧ TZ < TZ2 ∧ TZ2 < Hz
  H_r2 : ∀ t, t < Hz → s2.r2 t = false
  H_q_init : ∀ t, t < tz → s2.q t = true
  H_Z : ∀ t, tz ≤ t → t < Hz → s2.A0 t = (decide (t < TZ) || decide (TZ2 ≤ t))
  H_Z_prev : s2.A0 (tz - 1) = false
  H_SETTLED : ta + D2.wfa1 + D2.c1f ≤ TRx ∧ tz + D2.wa01 + D2.c1f ≤ TRx
  H_PULSE : TA + D2.wfa1 + D2.c1f ≤ TA2

section
variable {D1 D2 : Dl} {s1 s2 : Sigs} {t0 ta TA TA2 Hz tz TZ TZ2 : Int}

theorem cscn_of (R1 : Run D1 s1) (S1 : Scn D1 s1 t0 ta TA TA2 Hz)
    (hr : ∀ t, s2.r1 t = s1.R0 t) (hA : ∀ t, s2.A1 t = s1.A0 t)
    (K : CSide D2 s2 (TR D1 t0) ta TA TA2 tz TZ TZ2 Hz) :
    CScn D2 s2 (TR D1 t0) (RR D1 TA) ta TA TA2 tz TZ TZ2 Hz := by
  have ho := S1.H_ORDER; have hk := K.H_ORDER
  have := TA_ge R1 S1; have := D1.H_NONNEG
  exact
  { H_ORDER := by omega
    H_acc_hi := fun t h hz => by rw [hr]; exact R0_hi R1 S1 t h hz
    H_acc_lo := fun t h1 h2 hz => by rw [hr]; exact R0_lo R1 S1 t h1 h2 hz
    H_r2 := K.H_r2
    H_q_init := K.H_q_init
    H_ack := fun t h1 h2 => by rw [hA]; exact S1.H_A0 t h1 h2
    H_Z := K.H_Z
    H_Z_prev := K.H_Z_prev
    H_SETTLED := K.H_SETTLED
    H_PULSE := K.H_PULSE }

/-- **H_RT2_CASCADE sufficient (client 1 -> client 2 of arbiter 1).** Under the
arc conditions `RT2C` with the cascade responses of arbiter 2's real gates and
7g's fork, arbiter 1's two acknowledges are never both high, for every server
of arbiter 2 satisfying H_SERVER_MIN and every run of both arbiters. -/
theorem rt2_cascade (R1 : Run D1 s1) (S1 : Scn D1 s1 t0 ta TA TA2 Hz) (R2 : Run D2 s2)
    (hr : ∀ t, s2.r1 t = s1.R0 t) (hA : ∀ t, s2.A1 t = s1.A0 t)
    (K : CSide D2 s2 (TR D1 t0) ta TA TA2 tz TZ TZ2 Hz)
    (H : RT2C D1 (sF D2) (sR D2)) (H_fork : A0Fork D1) :
    ∀ t, t < Hz → (s1.A1 t && s1.A2 t) = false := by
  have := D1.H_NONNEG
  obtain ⟨hF, hR⟩ := cascade_server R2 (cscn_of R1 S1 hr hA K)
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold TR at hF; unfold RR QB at hR; unfold A0Fork at H_fork
  apply rt2_exclusion R1 S1
  · unfold T1 G1 QB; omega
  · unfold T1 T2 G1 QB; omega
  · unfold G2 QB; omega

/-- **Counter-trace (cascade at its minimum).** If arbiter 2 + its server answer
in exactly `sF`/`sR` and acc1_ack re-rises at ua1 of arbiter 1 before g1's fall
gets there (`¬` the g1 leg's race), arbiter 1's A1 never falls and A1, A2 are
both high when A2 rises (7h's `rt2_counter`). -/
theorem rt2_cascade_counter (R1 : Run D1 s1) (S1 : Scn D1 s1 t0 ta TA TA2 Hz) {sf sr : Int}
    (hmin : TA = TR D1 t0 + sf ∧ TA2 = RR D1 TA + sr)
    (hnot : TA2 + D1.wa01 ≤ G1 D1 t0 TA + D1.wg1)
    (H_g2_there : G2 D1 TA + D1.wg2 ≤ TA2 + D1.wa02) (hz : T2 D1 TA2 < Hz) :
    s1.A1 (T2 D1 TA2) = true ∧ s1.A2 (T2 D1 TA2) = true := by
  apply rt2_counter R1 S1 _ H_g2_there hz
  have := D1.H_RISE_LE_FALL
  omega

/-- **H_RT2_CASCADE sufficient, mirror direction (client 2 -> client 1).** -/
theorem cscn_of2 (R1 : Run D1 s1) (S1 : Scn2 D1 s1 t0 ta TA TA2 Hz)
    (hr : ∀ t, s2.r1 t = s1.R0 t) (hA : ∀ t, s2.A1 t = s1.A0 t)
    (K : CSide D2 s2 (TRb D1 t0) ta TA TA2 tz TZ TZ2 Hz) :
    CScn D2 s2 (TRb D1 t0) (RRb D1 TA) ta TA TA2 tz TZ TZ2 Hz := by
  have ho := S1.H_ORDER; have hk := K.H_ORDER
  have := TA_ge2 R1 S1; have := D1.H_NONNEG
  exact
  { H_ORDER := by omega
    H_acc_hi := fun t h hz => by rw [hr]; exact R0_hi2 R1 S1 t h hz
    H_acc_lo := fun t h1 h2 hz => by rw [hr]; exact R0_lo2 R1 S1 t h1 h2 hz
    H_r2 := K.H_r2
    H_q_init := K.H_q_init
    H_ack := fun t h1 h2 => by rw [hA]; exact S1.H_A0 t h1 h2
    H_Z := K.H_Z
    H_Z_prev := K.H_Z_prev
    H_SETTLED := K.H_SETTLED
    H_PULSE := K.H_PULSE }

theorem rt2_cascade2 (R1 : Run D1 s1) (S1 : Scn2 D1 s1 t0 ta TA TA2 Hz) (R2 : Run D2 s2)
    (hr : ∀ t, s2.r1 t = s1.R0 t) (hA : ∀ t, s2.A1 t = s1.A0 t)
    (K : CSide D2 s2 (TRb D1 t0) ta TA TA2 tz TZ TZ2 Hz)
    (H : RT2Cb D1 (sF D2) (sR D2)) (H_fork : A0Fork2 D1) :
    ∀ t, t < Hz → (s1.A1 t && s1.A2 t) = false := by
  have := D1.H_NONNEG
  obtain ⟨hF, hR⟩ := cascade_server R2 (cscn_of2 R1 S1 hr hA K)
  obtain ⟨h1, h2, h3, h4⟩ := H
  unfold TRb at hF; unfold RRb QBb at hR; unfold A0Fork2 at H_fork
  apply rt2_exclusion2 R1 S1
  · unfold T1b G2b QBb; omega
  · unfold T1b T2b G2b QBb; omega
  · unfold G1b QBb; omega

end

/-! ## H_BUNDLED_IDX for amerge3's `index[0]` (arbiter 1's new owner)

`index[0] = won1 & ~won2` (inferred LUT4 0x000E, pins [in1_ack, g2(arb1),
g2(arb2), in2_ack], `AMergeGates.idx3l`). During arbiter 1's handover from
in0 to in1 with arbiter 2 staying with acc1 (in2 idle, H_IN2_IDLE), index[0]
must rise to 1 before the capture. The request path now runs through arbiter
2: acc1_req (arbiter 1's R0) -> uarb2.ustate.I0 -> R0 (O5) -> uor -> DELAY ->
z_req, so the race has one more O5 arc + route of slack than amerge2's. The
pins of the arbiter-2 side (`g2(arb2)`, `in2_ack`) are low throughout and
their routes do not enter. -/

open Formal.Cells.AMergeTimed in
/-- index[0] as the consumer sees it (rise-fast OR channel, real INIT; the
in2 pins' routes are folded into `w2`, irrelevant while they are low). -/
def Cons3 (W : Wd) (w2 : Int) (s1 s2 : Sigs) (t : Int) : Bool :=
  let u := t - W.wid
  AMergeGates.idx3l (s1.A2 (u - W.wai - W.xr)) (s1.g2 (u - W.wgi - W.xr))
      (s2.g2 (u - w2 - W.xr)) (s2.A2 (u - w2 - W.xr)) ||
  AMergeGates.idx3l (s1.A2 (u - W.wai - W.xf)) (s1.g2 (u - W.wgi - W.xf))
      (s2.g2 (u - w2 - W.xf)) (s2.A2 (u - w2 - W.xf))

open Formal.Cells.AMergeTimed in
/-- **amerge3 race 1, arc form.** -/
def BidxA3 (D1 D2 : Dl) (W : Wd) : Prop :=
  D1.wq + D1.g2r + W.wgi + W.xr + W.wid + W.su ≤ D1.wfb + D1.Rrq + D2.wr1s + D2.Rr1 + W.dz

section
open Formal.Cells.AMergeTimed
variable {D1 D2 : Dl} {s1 s2 : Sigs} {t0 ta TA TA2 Hz tz TZ TZ2 : Int}

/-- **Sufficiency.** Under `BidxA3` the consumer sees `index[0] = 1` from `su`
before the capture of in1's token (for every capture instant caused by
arbiter 2's R0 after it fell, every server, every run of both arbiters). -/
theorem bidx3_new_owner (R1 : Run D1 s1) (S1 : Scn D1 s1 t0 ta TA TA2 Hz) (R2 : Run D2 s2)
    (hr : ∀ t, s2.r1 t = s1.R0 t) (hA : ∀ t, s2.A1 t = s1.A0 t)
    (K : CSide D2 s2 (TR D1 t0) ta TA TA2 tz TZ TZ2 Hz)
    (H_IN2_IDLE : ∀ t, s2.g2 t = false ∧ s2.A2 t = false)
    {W : Wd} {w2 Zr : Int} (hZ : ReqZ s2 (TR D1 t0 + D2.wr1s + D2.Rf1) Hz Zr W.dz)
    (H : BidxA3 D1 D2 W) :
    ∀ t, Zr - W.su ≤ t → t - W.wid - W.wgi - W.xr < Hz → Cons3 W w2 s1 s2 t = true := by
  intro t h1 h2
  have C := cscn_of R1 S1 hr hA K
  have := W.H_NONNEG; have := D1.H_NONNEG; have := D2.H_NONNEG; have := D2.H_RISE_LE_FALL
  obtain ⟨u, hu1, hu2, hu3, hu4⟩ := hZ
  have hu : RR D1 TA + D2.wr1s + D2.Rr1 ≤ u := by
    by_cases hc : RR D1 TA + D2.wr1s + D2.Rr1 ≤ u
    · exact hc
    · rw [R0_2_lo R2 C u hu1 (by omega) hu2] at hu4; exact absurd hu4 (by simp)
  have hg : s1.g2 (t - W.wid - W.wgi - W.xr) = true := by
    rw [g2_eq R1 S1 _ h2]; unfold BidxA3 at H; unfold RR at hu; unfold G2; simp; omega
  unfold Cons3
  simp only [AMergeGates.idx3l_eq, (H_IN2_IDLE _).1, (H_IN2_IDLE _).2, hg]
  simp

/-- **Counter-trace.** If `BidxA3` fails, then with the minimal request path the
consumer still sees `index[0] = 0` at the setup instant of in1's capture
(needs 7g's fork of arbiter 1 and H_Z_IN_SRV for arbiter 2's server; won1 = 0
already forces index[0] = 0 whatever the in2 pins do). -/
theorem bidx3_new_owner_counter (R1 : Run D1 s1) (S1 : Scn D1 s1 t0 ta TA TA2 Hz)
    (R2 : Run D2 s2) (hr : ∀ t, s2.r1 t = s1.R0 t) (hA : ∀ t, s2.A1 t = s1.A0 t)
    (K : CSide D2 s2 (TR D1 t0) ta TA TA2 tz TZ TZ2 Hz)
    {W : Wd} {w2 : Int} (H_fork : A0Fork D1) (H_Z_IN_SRV : W.dz ≤ D2.smin)
    (hnot : ¬ BidxA3 D1 D2 W) :
    Cons3 W w2 s1 s2 (RR D1 TA + D2.wr1s + D2.Rr1 + W.dz - W.su) = false := by
  have C := cscn_of R1 S1 hr hA K
  have := W.H_NONNEG; have := W.H_ARC_POS; have := W.H_RISE_LE_FALL
  have := D1.H_NONNEG; have := D2.H_NONNEG; have := D1.H_RISE_LE_FALL
  have ho := S1.H_ORDER
  obtain ⟨_, hR⟩ := cascade_server R2 C
  have hlow := A2_low_before R1 S1 (by unfold A0Fork at H_fork; unfold G2 QB; omega)
  unfold BidxA3 at hnot; unfold sR at hR
  have g1 : s1.g2 (RR D1 TA + D2.wr1s + D2.Rr1 + W.dz - W.su - W.wid - W.wgi - W.xr) = false := by
    rw [g2_eq R1 S1 _ (by omega)]; unfold G2 RR at *; simp; omega
  have g2' : s1.g2 (RR D1 TA + D2.wr1s + D2.Rr1 + W.dz - W.su - W.wid - W.wgi - W.xf) = false := by
    rw [g2_eq R1 S1 _ (by omega)]; unfold G2 RR at *; simp; omega
  have a1 := hlow (RR D1 TA + D2.wr1s + D2.Rr1 + W.dz - W.su - W.wid - W.wai - W.xr)
    (by unfold T2; omega) (by omega)
  have a2 := hlow (RR D1 TA + D2.wr1s + D2.Rr1 + W.dz - W.su - W.wid - W.wai - W.xf)
    (by unfold T2; omega) (by omega)
  unfold Cons3
  simp only [AMergeGates.idx3l_eq, g1, g2', a1, a2]
  simp

end

/-! ## Non-vacuity: an explicit cascade at a consistent corner

Arbiter 1 is `AMergeTimedW.W1g a b cq S1` (client 1 -> client 2, server `S1`)
and arbiter 2 is `C2 a b cq S2`: it stays with `acc1` (q2 = 1, in2 idle),
its z_ack server answers in exactly `S2`. With `S1 = b + S2 + a` = `sF = sR`
at zero routing, arbiter 1's A0 trace IS arbiter 2's ua1 output: the cascade
server is realised and its derived bounds are attained with equality. -/

open Formal.Cells.AMergeTimedW in
/-- Arbiter 2's traces (TZ = 2b + S2, TZ2 = RR1 + b + S2, RR1 = b + S1 + a + cq). -/
def C2 (a b cq S2 : Int) : Sigs where
  r1 := (W1g a b cq (b + S2 + a)).R0
  r2 := fun _ => false
  q := fun _ => true
  R0 := fun t => decide (t < b + b) || decide (b + (b + S2 + a) + a + cq + b ≤ t)
  g1 := fun t => decide (t < b + b) || decide (b + (b + S2 + a) + a + cq + b ≤ t)
  g2 := fun _ => false
  A0 := fun t => (decide (-1000 - a ≤ t) && decide (t < b + b + S2)) ||
    decide (b + (b + S2 + a) + a + cq + b + S2 ≤ t)
  A1 := (W1g a b cq (b + S2 + a)).A0
  A2 := fun _ => false

open Formal.Cells.AMergeTimedW in
theorem C2_run (a b cq S2 : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S2) (hs : a ≤ 500 ∧ b ≤ 500) :
    Run (dW a b cq S2 h) (C2 a b cq S2) := by
  have ⟨h1, h2, h3, h4⟩ := h; have ⟨h5, h6⟩ := hs
  exact {
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [C2, dW, FS_bool] <;> omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [C2, W1g, dW, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [C2, W1g, dW, FG1_eq]; omega
  H_g2 := by intro t; simp [C2, dW, FG2_eq]
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [C2, W1g, dW, CE_eq]; omega
  H_A2 := by intro t; simp [C2, dW, CE_eq]
  H_SRV := by
    intro t ht
    have e : t = -1000 - a ∨ t = b + b + S2 ∨ t = b + (b + S2 + a) + a + cq + b + S2 := by
      exact Classical.byContradiction fun hc => ht (by rw [Bool.eq_iff_iff]; simp [C2]; omega)
    rcases e with rfl | rfl | rfl
    · exact ⟨-1000 - a - S2, by simp [dW], by rw [Bool.eq_iff_iff]; simp [C2] <;> omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [C2]; omega⟩
    · exact ⟨b + b, by simp [dW], by rw [Bool.eq_iff_iff]; simp [C2] <;> omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [C2]; omega⟩
    · exact ⟨b + (b + S2 + a) + a + cq + b, by simp [dW], by rw [Bool.eq_iff_iff]; simp [C2] <;> omega,
        fun v _ _ => by rw [Bool.eq_iff_iff]; simp [C2]; omega⟩ }

open Formal.Cells.AMergeTimedW in
theorem C2_side (a b cq S2 : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S2) (hs : a ≤ 500 ∧ b ≤ 500)
    (Hz : Int) (hz : b + (b + S2 + a) + a + cq + (b + S2 + a) < Hz) :
    CSide (dW a b cq S2 h) (C2 a b cq S2) b (-1000) (b + (b + S2 + a))
      (b + (b + S2 + a) + a + cq + (b + S2 + a)) (-1000 - a) (b + b + S2)
      (b + (b + S2 + a) + a + cq + b + S2) Hz := by
  have ⟨h1, h2, h3, h4⟩ := h; have ⟨h5, h6⟩ := hs
  exact {
  H_ORDER := by omega
  H_r2 := fun _ _ => rfl
  H_q_init := fun _ _ => rfl
  H_Z := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [C2]; omega
  H_Z_prev := by simp [C2] <;> omega
  H_SETTLED := by simp [dW]; omega
  H_PULSE := by simp [dW]; omega }

open Formal.Cells.AMergeTimedW in
/-- **Non-vacuity of H_RT2_CASCADE, generic in the corner.** For every
consistent-corner arc set (`a ≤ 500`, `b ≤ 500`) and every arbiter-2 server
`S2 ≥ 0`: both arbiters have runs for all t, they are wired as the cascade
(`hr`, `hA` by `rfl`), every hypothesis of `rt2_cascade` holds, and the
cascade server's derived bounds are attained exactly. -/
theorem cascade_nonvacuous (a b cq S2 : Int) (h : 0 < a ∧ 0 ≤ b ∧ 0 ≤ cq ∧ 0 ≤ S2)
    (hs : a ≤ 500 ∧ b ≤ 500) (Hz : Int)
    (hz : b + (b + S2 + a) + a + cq + (b + S2 + a) < Hz) :
    Run (dW a b cq (b + S2 + a) (by omega)) (W1g a b cq (b + S2 + a)) ∧
    Scn (dW a b cq (b + S2 + a) (by omega)) (W1g a b cq (b + S2 + a)) 0 (-1000)
      (b + (b + S2 + a)) (b + (b + S2 + a) + a + cq + (b + S2 + a)) Hz ∧
    Run (dW a b cq S2 h) (C2 a b cq S2) ∧
    (∀ t, (C2 a b cq S2).r1 t = (W1g a b cq (b + S2 + a)).R0 t) ∧
    (∀ t, (C2 a b cq S2).A1 t = (W1g a b cq (b + S2 + a)).A0 t) ∧
    CSide (dW a b cq S2 h) (C2 a b cq S2) (TR (dW a b cq (b + S2 + a) (by omega)) 0) (-1000)
      (b + (b + S2 + a)) (b + (b + S2 + a) + a + cq + (b + S2 + a)) (-1000 - a) (b + b + S2)
      (b + (b + S2 + a) + a + cq + b + S2) Hz ∧
    RT2C (dW a b cq (b + S2 + a) (by omega)) (sF (dW a b cq S2 h)) (sR (dW a b cq S2 h)) ∧
    A0Fork (dW a b cq (b + S2 + a) (by omega)) ∧
    b + (b + S2 + a) = TR (dW a b cq (b + S2 + a) (by omega)) 0 + sF (dW a b cq S2 h) ∧
    b + (b + S2 + a) + a + cq + (b + S2 + a) =
      RR (dW a b cq (b + S2 + a) (by omega)) (b + (b + S2 + a)) + sR (dW a b cq S2 h) := by
  have ⟨h1, h2, h3, h4⟩ := h; have ⟨h5, h6⟩ := hs
  refine ⟨W1g_run _ _ _ _ _ (by omega), W1g_scn _ _ _ _ _ (by omega) Hz hz, C2_run _ _ _ _ h hs,
    fun _ => rfl, fun _ => rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have : TR (dW a b cq (b + S2 + a) (by omega)) 0 = b := by simp [TR, dW]
    rw [this]; exact C2_side a b cq S2 h hs Hz hz
  · exact ⟨by simp [sR, dW]; omega, by simp [sF, sR, dW]; omega, by simp [sR, dW]; omega,
      by simp [sF, sR, dW]; omega⟩
  · simp [A0Fork, dW] <;> omega
  · simp [TR, sF, dW] <;> omega
  · simp [RR, QB, sR, dW] <;> omega

/-- The two corners of gcd_hw's amerge3 (`DELAY = 24`, arbiter 2's server =
uor + 24 hops = 25 arcs): SLOW_MAX `S2 = 3100`, FAST_MIN `S2 = 1125`; the
resulting cascade responses `sF = sR` are 3376 / 1214 ps. Arbiter 1's
tightest leg, `pulse`, has margin `qf + Rrq + sR − c1f` (routes 0) =
3526 / 1256 ps. -/
theorem cascade_corners :
    sR (AMergeTimedW.dW 124 152 150 3100 (by omega)) = 3376 ∧
    sR (AMergeTimedW.dW 45 44 42 1125 (by omega)) = 1214 := by
  simp [sR, AMergeTimedW.dW]

open Formal.Cells.AMergeTimedW Formal.Cells.AMergeTimed in
/-- **Non-vacuity of amerge3 race 1 (SLOW_MAX, DELAY = 24).** The explicit
cascade of `cascade_nonvacuous` with `S2 = dz = 25 × 124 = 3100`: BidxA3 holds
(margin `cq + b + dz − a − x` = 3154 ps), the capture caused by arbiter 2's R0
rise at 3954 is a legal `ReqZ`, and index[0] at the consumer is 0 at 3899 and
1 from 3900 (= G2 + x) through the capture's setup instant 7054. -/
theorem bidx3_nonvacuous_slow :
    BidxA3 (dW 124 152 150 3376 (by omega)) (dW 124 152 150 3100 (by omega)) (wW 124 3100 (by omega)) ∧
    ReqZ (C2 124 152 150 3100) (TR (dW 124 152 150 3376 (by omega)) 0 + 0 + 152) 8000 7054 3100 ∧
    (∀ t, 7054 ≤ t → t < 8000 →
      Cons3 (wW 124 3100 (by omega)) 0 (W1g 124 152 150 3376) (C2 124 152 150 3100) t = true) ∧
    Cons3 (wW 124 3100 (by omega)) 0 (W1g 124 152 150 3376) (C2 124 152 150 3100) 3899 = false ∧
    Cons3 (wW 124 3100 (by omega)) 0 (W1g 124 152 150 3376) (C2 124 152 150 3100) 3900 = true := by
  have N := cascade_nonvacuous 124 152 150 3100 (by omega) (by omega) 8000 (by omega)
  obtain ⟨R1, S1, R2, hr, hA, K, -, -, -, -⟩ := N
  have hZ : ReqZ (C2 124 152 150 3100) (TR (dW 124 152 150 3376 (by omega)) 0 + 0 + 152) 8000 7054 3100 :=
    ⟨3954, by simp [TR, dW], by omega, by omega, by simp [C2]⟩
  have H : BidxA3 (dW 124 152 150 3376 (by omega)) (dW 124 152 150 3100 (by omega)) (wW 124 3100 (by omega)) := by
    simp [BidxA3, dW, wW]
  refine ⟨H, hZ, fun t h1 h2 => ?_, ?_, ?_⟩
  · exact bidx3_new_owner R1 S1 R2 hr hA K (fun _ => ⟨rfl, rfl⟩) (W := wW 124 3100 (by omega))
      (w2 := 0) hZ H t (by simp [wW]; omega) (by simp [wW]; omega)
  · simp [Cons3, AMergeGates.idx3l_eq, wW, W1g, C2]
  · simp [Cons3, AMergeGates.idx3l_eq, wW, W1g, C2]

end Formal.Cells.AMergeTimedC
