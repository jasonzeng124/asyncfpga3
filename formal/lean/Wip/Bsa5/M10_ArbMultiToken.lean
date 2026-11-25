-- Bsa5 mutant M10 of Formal/Cells/ArbMultiToken.lean: one change, MTRun H_SLOW_REREQ 4M -> 3M. Expected: FAIL.
import Formal.Cells.ArbHeldTimed2

/-!
# Probe Barb2: multi-token exclusion of the held `bd_arbiter`

7h (`ArbHeldTimed`) and 7j (`ArbHeldTimed2`) prove grant/ack exclusion for ONE
handover, under scenarios `Scn` / `Scn2` whose settled state is asserted on the
whole past (`H_q_init`, `H_A1_init`, `H_r2 : ∀ t < Hz, r2 t`, ...). A segment of a
multi-token run never satisfies them literally (an earlier handover contradicts
`H_A1_init`). This file chains them anyway, reusing the original theorems
unchanged, by SPLICING:

* `splice s P B`: the run from `B` on, the stylised settled state `P` (A0 low)
  before. `splice_run`: if the run is quiet in `P` on `[B, B+M)` and `P` is a gate
  fixed point, the spliced traces satisfy every gate relation and the server
  relation for ALL t (H_M: `M` bounds every read offset).
* `win1`, `win2` = the WINDOWED one-handover theorems: settled state only on
  `[B - M, t0)`, requests only on `[B - M, Hz)`, A0 only from its last rise
  (`a ≤ B`). Proof: build the spliced run, show it meets 7h's `Scn` / 7j's `Scn2`
  (H_SETTLED from `B + M ≤ t0`), apply `rt1_exclusion`, `q_eq`, `g1_eq`, `g2_eq`,
  `A1_low_after`, `TA_ge`, `TA2_ge` (and 7j's mirrors), transport back on
  `[B, Hz)`. Output: exclusion on `[B, Hz)`, the next settled state on
  `[TA2 + 3M, Hz)`, R0 high from `TA2`, and (under `CX`) C's tick fields.
* `persist`: a settled state persists while the holder keeps its request,
  whatever A0 and the losing request do.
* `MTRun`: an infinite alternating-contention schedule (four-phase clients,
  no withdrawal, H_SLOW_REREQ `TA2 + 4M ≤ u`, H_HOLD `u + 2M ≤ t0 (k+1)`).
  `inv_all`: induction over handovers.

**Assumed:** `Run` (7h's gate model), H_M, RT1 + RT2 (7h), RT1b + RT2b (7j) as
arc inequalities, `MTRun`; for C's tick fields also `CX`.
**Proved:** `mt_exclusion` (grants never both high at any t ≥ B0, infinitely many
handovers); `H_ARB_EXCL_of_mt` (C's field, any sampling); `H_ARB12_of_mt` (C's
H_ARB1, H_ARB2, H_ARB_EXCL at 1 ps ticks). Non-vacuity: `mt_nonvacuous` (periodic
run, all delays nonzero, two handovers per 48 ps period).
**NOT covered:** a re-request earlier than H_SLOW_REREQ (four-phase allows the
releasing client to re-raise as soon as its ack falls; the extra races are named
in notes/B-arb-multi-token.md but not proved); C's H_AMERGE_RTZ (needs `z_req`,
which B's model abstracts into the server); A0Fork is not needed for grants;
non-alternating schedules (a solo client, idle periods); metastability (a race
outside RT1/RT1b is a different scenario, not modelled here).
-/

namespace Formal.Cells.ArbMultiToken
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-! ## Settled states -/

/-- A settled value for every signal but A0. -/
structure St where
  r1 : Bool
  r2 : Bool
  q : Bool
  R0 : Bool
  g1 : Bool
  g2 : Bool
  A1 : Bool
  A2 : Bool
  deriving DecidableEq

/-- Client 1 holds the grant (client 2 waiting). -/
def P1 : St := ⟨true, true, true, true, true, false, true, false⟩
/-- Client 2 holds the grant (client 1 waiting). -/
def P2 : St := ⟨true, true, false, true, false, true, false, true⟩

/-- The internal signals equal `P` at `t`. -/
def Q (s : Sigs) (P : St) (t : Int) : Prop :=
  s.q t = P.q ∧ s.R0 t = P.R0 ∧ s.g1 t = P.g1 ∧ s.g2 t = P.g2 ∧ s.A1 t = P.A1 ∧ s.A2 t = P.A2

/-- `P` is a fixed point of every gate, whatever A0 is. -/
def FixA (P : St) : Prop :=
  ∀ a : Bool, FS P.r1 P.r2 P.q a = P.q ∧ FR P.r1 P.r2 P.q = P.R0 ∧ FG1 P.r1 P.r2 P.q = P.g1 ∧
    FG2 P.r1 P.r2 P.q = P.g2 ∧ CE P.g1 a P.A1 = P.A1 ∧ CE P.g2 a P.A2 = P.A2

/-- `P`'s internal state is a fixed point whatever A0 and the LOSING request do,
as long as the winner (`c = true`: client 1) keeps its request up. -/
def Ins (P : St) (c : Bool) : Prop :=
  ∀ r1 r2 a : Bool, (c = true → r1 = true) → (c = false → r2 = true) →
    FS r1 r2 P.q a = P.q ∧ FR r1 r2 P.q = P.R0 ∧ FG1 r1 r2 P.q = P.g1 ∧
    FG2 r1 r2 P.q = P.g2 ∧ CE P.g1 a P.A1 = P.A1 ∧ CE P.g2 a P.A2 = P.A2

theorem fix_P1 : FixA P1 := by unfold FixA; decide
theorem fix_P2 : FixA P2 := by unfold FixA; decide
theorem ins_P1 : Ins P1 true := by unfold Ins; decide
theorem ins_P2 : Ins P2 false := by unfold Ins; decide

/-- **H_M**: `M` bounds every single read offset (route + fall arc) of the arbiter. -/
structure MB (D : Dl) (M : Int) : Prop where
  pos : 1 ≤ M
  q : D.wr1s + D.qf ≤ M ∧ D.wr2s + D.qf ≤ M ∧ D.wfb + D.qf ≤ M ∧ D.wa0s + D.qf ≤ M
  R0 : D.wr1s + D.Rf1 ≤ M ∧ D.wr2s + D.Rf2 ≤ M ∧ D.wfb + D.Rfq ≤ M
  g1 : D.wr1g + D.g1f1 ≤ M ∧ D.wr2g + D.g1f2 ≤ M ∧ D.wq + D.g1fq ≤ M
  g2 : D.wr1g + D.g2f ≤ M ∧ D.wr2g + D.g2f ≤ M ∧ D.wq + D.g2f ≤ M
  A1 : D.wg1 + D.c1f ≤ M ∧ D.wa01 + D.c1f ≤ M ∧ D.wfa1 + D.c1f ≤ M
  A2 : D.wg2 + D.c2f ≤ M ∧ D.wa02 + D.c2f ≤ M ∧ D.wfa2 + D.c2f ≤ M

/-! ## Splicing a stylised settled past onto a run -/

/-- `s` from `B` on; before `B`, the settled state `P` with A0 low. -/
def splice (s : Sigs) (P : St) (B : Int) : Sigs where
  r1 t := if t < B then P.r1 else s.r1 t
  r2 t := if t < B then P.r2 else s.r2 t
  q t := if t < B then P.q else s.q t
  R0 t := if t < B then P.R0 else s.R0 t
  g1 t := if t < B then P.g1 else s.g1 t
  g2 t := if t < B then P.g2 else s.g2 t
  A0 t := if t < B then false else s.A0 t
  A1 t := if t < B then P.A1 else s.A1 t
  A2 t := if t < B then P.A2 else s.A2 t

section splice
variable {D : Dl} {s : Sigs} {P : St} {B M t : Int}

theorem sp_r1 (h : B ≤ t) : (splice s P B).r1 t = s.r1 t := by simp [splice, show ¬ t < B by omega]
theorem sp_r2 (h : B ≤ t) : (splice s P B).r2 t = s.r2 t := by simp [splice, show ¬ t < B by omega]
theorem sp_q (h : B ≤ t) : (splice s P B).q t = s.q t := by simp [splice, show ¬ t < B by omega]
theorem sp_R0 (h : B ≤ t) : (splice s P B).R0 t = s.R0 t := by simp [splice, show ¬ t < B by omega]
theorem sp_g1 (h : B ≤ t) : (splice s P B).g1 t = s.g1 t := by simp [splice, show ¬ t < B by omega]
theorem sp_g2 (h : B ≤ t) : (splice s P B).g2 t = s.g2 t := by simp [splice, show ¬ t < B by omega]
theorem sp_A0 (h : B ≤ t) : (splice s P B).A0 t = s.A0 t := by simp [splice, show ¬ t < B by omega]
theorem sp_A1 (h : B ≤ t) : (splice s P B).A1 t = s.A1 t := by simp [splice, show ¬ t < B by omega]
theorem sp_A2 (h : B ≤ t) : (splice s P B).A2 t = s.A2 t := by simp [splice, show ¬ t < B by omega]

/-- Quiet on `[B, B+M)`: requests and internals equal `P`. -/
def Quiet (s : Sigs) (P : St) (B M : Int) : Prop :=
  ∀ τ, B ≤ τ → τ < B + M → s.r1 τ = P.r1 ∧ s.r2 τ = P.r2 ∧ Q s P τ

theorem sp_lo (hq : Quiet s P B M) (τ : Int) (h : τ < B + M) :
    (splice s P B).r1 τ = P.r1 ∧ (splice s P B).r2 τ = P.r2 ∧ Q (splice s P B) P τ := by
  by_cases hb : τ < B
  · simp [splice, Q, hb]
  · obtain ⟨a, b, c, d, e, f, g, i⟩ := hq τ (by omega) h
    simp [splice, Q, hb, a, b, c, d, e, f, g, i]

theorem lo_r1 (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).r1 τ = P.r1 :=
  fun τ h => (sp_lo hq τ h).1
theorem lo_r2 (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).r2 τ = P.r2 :=
  fun τ h => (sp_lo hq τ h).2.1
theorem lo_q (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).q τ = P.q :=
  fun τ h => (sp_lo hq τ h).2.2.1
theorem lo_R0 (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).R0 τ = P.R0 :=
  fun τ h => (sp_lo hq τ h).2.2.2.1
theorem lo_g1 (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).g1 τ = P.g1 :=
  fun τ h => (sp_lo hq τ h).2.2.2.2.1
theorem lo_g2 (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).g2 τ = P.g2 :=
  fun τ h => (sp_lo hq τ h).2.2.2.2.2.1
theorem lo_A1 (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).A1 τ = P.A1 :=
  fun τ h => (sp_lo hq τ h).2.2.2.2.2.2.1
theorem lo_A2 (hq : Quiet s P B M) : ∀ τ, τ < B + M → (splice s P B).A2 τ = P.A2 :=
  fun τ h => (sp_lo hq τ h).2.2.2.2.2.2.2

/-- **Splice lemma.** If the run is quiet in `P` on `[B, B+M)`, `P` is a fixed
point of every gate (for either A0), and A0 last rose at `a ≤ B` and has been
high since with R0 high on `[a, B)`, then the spliced traces (stylised settled
past before `B`, A0 low there) satisfy every gate relation and the server
relation, for all t. -/
theorem splice_run (R : Run D s) (hM : MB D M) (hfix : FixA P) (hR0P : P.R0 = true)
    (hq : Quiet s P B M) {a : Int} (ha : a ≤ B) (ha0 : s.A0 (a - 1) = false)
    (hA0 : ∀ τ, a ≤ τ → τ < B + M → s.A0 τ = true)
    (hR0a : ∀ τ, a ≤ τ → τ < B → s.R0 τ = true) : Run D (splice s P B) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have hp := hM.pos; have := hM.q; have := hM.R0; have := hM.g1; have := hM.g2
  have := hM.A1; have := hM.A2
  have h1 := lo_r1 hq; have h2 := lo_r2 hq; have h3 := lo_q hq; have h4 := lo_R0 hq
  have h5 := lo_g1 hq; have h6 := lo_g2 hq; have h7 := lo_A1 hq; have h8 := lo_A2 hq
  have k1 : ∀ τ, B ≤ τ → (splice s P B).r1 τ = s.r1 τ := fun _ h => sp_r1 h
  have k2 : ∀ τ, B ≤ τ → (splice s P B).r2 τ = s.r2 τ := fun _ h => sp_r2 h
  have k3 : ∀ τ, B ≤ τ → (splice s P B).q τ = s.q τ := fun _ h => sp_q h
  have k4 : ∀ τ, B ≤ τ → (splice s P B).R0 τ = s.R0 τ := fun _ h => sp_R0 h
  have k5 : ∀ τ, B ≤ τ → (splice s P B).g1 τ = s.g1 τ := fun _ h => sp_g1 h
  have k6 : ∀ τ, B ≤ τ → (splice s P B).g2 τ = s.g2 τ := fun _ h => sp_g2 h
  have k7 : ∀ τ, B ≤ τ → (splice s P B).A0 τ = s.A0 τ := fun _ h => sp_A0 h
  have k8 : ∀ τ, B ≤ τ → (splice s P B).A1 τ = s.A1 τ := fun _ h => sp_A1 h
  have k9 : ∀ τ, B ≤ τ → (splice s P B).A2 τ = s.A2 τ := fun _ h => sp_A2 h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t < B + M
    · simp (disch := omega) only [h1, h2, h3]
      rw [(hfix _).1, (hfix _).1, Bool.or_self]
    · simp (disch := omega) only [k1, k2, k3, k7]; exact R.H_q t
  · intro t
    by_cases ht : t < B + M
    · simp (disch := omega) only [h1, h2, h3, h4]
      rw [(hfix false).2.1, Bool.or_self]
    · simp (disch := omega) only [k1, k2, k3, k4]; exact R.H_R0 t
  · intro t
    by_cases ht : t < B + M
    · simp (disch := omega) only [h1, h2, h3, h5]
      rw [(hfix false).2.2.1, Bool.or_self]
    · simp (disch := omega) only [k1, k2, k3, k5]; exact R.H_g1 t
  · intro t
    by_cases ht : t < B + M
    · simp (disch := omega) only [h1, h2, h3, h6]
      rw [(hfix false).2.2.2.1, Bool.or_self]
    · simp (disch := omega) only [k1, k2, k3, k6]; exact R.H_g2 t
  · intro t
    by_cases ht : t < B + M
    · simp (disch := omega) only [h5, h7]
      rw [(hfix _).2.2.2.2.1, (hfix _).2.2.2.2.1, Bool.or_self]
    · simp (disch := omega) only [k5, k7, k8]; exact R.H_A1 t
  · intro t
    by_cases ht : t < B + M
    · simp (disch := omega) only [h6, h8]
      rw [(hfix _).2.2.2.2.2, (hfix _).2.2.2.2.2, Bool.or_self]
    · simp (disch := omega) only [k6, k7, k9]; exact R.H_A2 t
  · intro t ht
    by_cases hlt : t < B
    · exfalso; apply ht
      simp [splice, hlt, show t - 1 < B by omega]
    · by_cases heq : t = B
      · subst heq
        refine ⟨t - D.smin, by omega, ?_, ?_⟩
        · rw [h4 _ (by omega), k7 t (by omega), hA0 t ha (by omega), hR0P]
        · intro v _ hv
          simp [splice, show v < t by omega, show t - 1 < t by omega]
      · have e0 := k7 t (by omega)
        have e1 := k7 (t - 1) (by omega)
        rw [e0, e1] at ht ⊢
        obtain ⟨u, hu, hR, hv⟩ := R.H_SRV t ht
        by_cases hub : B ≤ u
        · refine ⟨u, hu, by rw [k4 u hub]; exact hR, fun v h1 h2 => ?_⟩
          rw [k7 v (by omega)]; exact hv v h1 h2
        · exfalso
          by_cases hua : u < a
          · have x1 := hv (a - 1) (by omega) (by omega)
            have x2 := hv a (by omega) (by omega)
            rw [ha0] at x1; rw [hA0 a (Int.le_refl _) (by omega)] at x2
            rw [← x1] at x2; exact absurd x2 (by simp)
          · have x1 := hv u (Int.le_refl _) (by omega)
            rw [hR0a u (by omega) (by omega)] at hR
            rw [hA0 u (by omega) (by omega)] at x1
            exact ht (by rw [← hR, ← x1])

end splice

/-! ## Persistence of a settled state -/

theorem persist {D : Dl} {s : Sigs} {M : Int} (R : Run D s) (hM : MB D M) {P : St} {c : Bool}
    (hins : Ins P c) (X Y : Int)
    (hw1 : c = true → ∀ τ, X - M ≤ τ → τ < Y → s.r1 τ = true)
    (hw2 : c = false → ∀ τ, X - M ≤ τ → τ < Y → s.r2 τ = true)
    (hb : ∀ τ, X - M ≤ τ → τ < X → Q s P τ) : ∀ t, X - M ≤ t → t < Y → Q s P t := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have hp := hM.pos; have := hM.q; have := hM.R0; have := hM.g1; have := hM.g2
  have := hM.A1; have := hM.A2
  refine int_ind (fun t => X - M ≤ t → t < Y → Q s P t) X (fun t ht h1 _ => hb t h1 ht) ?_
  intro t htX ih h1 h2
  have IH : ∀ τ, X - M ≤ τ → τ < t → Q s P τ := fun τ a b => ih τ b a (by omega)
  have W : ∀ τ1 τ2 a, X - M ≤ τ1 → τ1 < Y → X - M ≤ τ2 → τ2 < Y →
      FS (s.r1 τ1) (s.r2 τ2) P.q a = P.q ∧ FR (s.r1 τ1) (s.r2 τ2) P.q = P.R0 ∧
      FG1 (s.r1 τ1) (s.r2 τ2) P.q = P.g1 ∧ FG2 (s.r1 τ1) (s.r2 τ2) P.q = P.g2 ∧
      CE P.g1 a P.A1 = P.A1 ∧ CE P.g2 a P.A2 = P.A2 :=
    fun τ1 τ2 a a1 a2 a3 a4 => hins _ _ a (fun hc => hw1 hc τ1 a1 a2) (fun hc => hw2 hc τ2 a3 a4)
  have eq : s.q t = P.q := by
    rw [R.H_q t, (IH _ (by omega) (by omega)).1, (IH _ (by omega) (by omega)).1,
      (W _ _ _ (by omega) (by omega) (by omega) (by omega)).1,
      (W _ _ _ (by omega) (by omega) (by omega) (by omega)).1, Bool.or_self]
  have hqv : ∀ τ, X - M ≤ τ → τ ≤ t → s.q τ = P.q := by
    intro τ a b
    by_cases e : τ = t
    · rw [e]; exact eq
    · exact (IH τ a (by omega)).1
  have eR : s.R0 t = P.R0 := by
    rw [R.H_R0 t, hqv _ (by omega) (by omega), hqv (t - D.wfb - D.Rfq) (by omega) (by omega),
      (W _ _ false (by omega) (by omega) (by omega) (by omega)).2.1,
      (W _ _ false (by omega) (by omega) (by omega) (by omega)).2.1, Bool.or_self]
  have eg1 : s.g1 t = P.g1 := by
    rw [R.H_g1 t, hqv _ (by omega) (by omega), hqv (t - D.wq - D.g1fq) (by omega) (by omega),
      (W _ _ false (by omega) (by omega) (by omega) (by omega)).2.2.1,
      (W _ _ false (by omega) (by omega) (by omega) (by omega)).2.2.1, Bool.or_self]
  have eg2 : s.g2 t = P.g2 := by
    rw [R.H_g2 t, hqv _ (by omega) (by omega), hqv (t - D.wq - D.g2f) (by omega) (by omega),
      (W _ _ false (by omega) (by omega) (by omega) (by omega)).2.2.2.1,
      (W _ _ false (by omega) (by omega) (by omega) (by omega)).2.2.2.1, Bool.or_self]
  have hg1v : ∀ τ, X - M ≤ τ → τ ≤ t → s.g1 τ = P.g1 := by
    intro τ a b
    by_cases e : τ = t
    · rw [e]; exact eg1
    · exact (IH τ a (by omega)).2.2.1
  have hg2v : ∀ τ, X - M ≤ τ → τ ≤ t → s.g2 τ = P.g2 := by
    intro τ a b
    by_cases e : τ = t
    · rw [e]; exact eg2
    · exact (IH τ a (by omega)).2.2.2.1
  have eA1 : s.A1 t = P.A1 := by
    rw [R.H_A1 t, hg1v _ (by omega) (by omega), hg1v (t - D.wg1 - D.c1f) (by omega) (by omega),
      (IH (t - D.wfa1 - D.c1r) (by omega) (by omega)).2.2.2.2.1,
      (IH (t - D.wfa1 - D.c1f) (by omega) (by omega)).2.2.2.2.1,
      (W t t _ (by omega) (by omega) (by omega) (by omega)).2.2.2.2.1,
      (W t t _ (by omega) (by omega) (by omega) (by omega)).2.2.2.2.1, Bool.or_self]
  have eA2 : s.A2 t = P.A2 := by
    rw [R.H_A2 t, hg2v _ (by omega) (by omega), hg2v (t - D.wg2 - D.c2f) (by omega) (by omega),
      (IH (t - D.wfa2 - D.c2r) (by omega) (by omega)).2.2.2.2.2,
      (IH (t - D.wfa2 - D.c2f) (by omega) (by omega)).2.2.2.2.2,
      (W t t _ (by omega) (by omega) (by omega) (by omega)).2.2.2.2.2,
      (W t t _ (by omega) (by omega) (by omega) (by omega)).2.2.2.2.2, Bool.or_self]
  exact ⟨eq, eR, eg1, eg2, eA1, eA2⟩

/-! ## Extra one-handover facts (7h / 7j scenarios): the settled end state -/

section ends
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

/-- 7h direction: R0 is high again from `RR` to the horizon (r2 high, q low at R0's rise view). -/
theorem R0_after (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, RR D TA ≤ t → t < Hz → s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  intro t h hz
  rw [R.H_R0 t, S.H_r2 (t - D.wr2s - D.Rr2) (by omega), q_eq R S (t - D.wfb - D.Rrq) (by omega)]
  have : ¬ (t - D.wfb - D.Rrq < QB D TA) := by unfold RR at h; omega
  simp [FR_eq, this]

/-- 7h direction: A2 is high from `max (G2 + wg2) (TA2 + wa02) + c2f` to the horizon. -/
theorem A2_after (R : Run D s) (S : Scn D s t0 ta TA TA2 Hz) :
    ∀ t, max (G2 D TA + D.wg2) (TA2 + D.wa02) + D.c2f ≤ t → t < Hz → s.A2 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  intro t h hz
  rw [R.H_A2 t, g2_eq R S (t - D.wg2 - D.c2r) (by omega),
    A0_hi2 S (t - D.wa02 - D.c2r) (by omega) (by omega)]
  have : G2 D TA ≤ t - D.wg2 - D.c2r := by omega
  simp [CE_eq, this]

/-- 7j direction: R0 is high again from `RRb` to the horizon. -/
theorem R0_after2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, RRb D TA ≤ t → t < Hz → s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  intro t h hz
  rw [R.H_R0 t, S.H_r1 (t - D.wr1s - D.Rr1) (by omega), q_eq2 R S (t - D.wfb - D.Rrq) (by omega)]
  have : QBb D TA ≤ t - D.wfb - D.Rrq := by unfold RRb at h; omega
  simp [FR_eq, this]

/-- 7j direction: A1 is high from `max (G1b + wg1) (TA2 + wa01) + c1f` to the horizon. -/
theorem A1_after2 (R : Run D s) (S : Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, max (G1b D TA + D.wg1) (TA2 + D.wa01) + D.c1f ≤ t → t < Hz → s.A1 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  intro t h hz
  rw [R.H_A1 t, g1_eq2 R S (t - D.wg1 - D.c1r) (by omega),
    A0_hi2b S (t - D.wa01 - D.c1r) (by omega) (by omega)]
  have : G1b D TA ≤ t - D.wg1 - D.c1r := by omega
  simp [CE_eq, this]

end ends

/-! ## One handover inside a multi-token run

`win1` (client 1 releases, 7h's direction) and `win2` (client 2 releases, 7j's)
take a run `s` that is settled in `P1` (resp. `P2`) on `[B - M, t0)`, splice the
stylised past of 7h's / 7j's scenario onto it at `B`, apply the ORIGINAL
one-handover theorems (`rt1_exclusion`, `q_eq`, `g1_eq`, `g2_eq`, `A1_low_after`,
`TA_ge`, `TA2_ge` and the 7j mirrors) to the spliced run, and transport the
results back to `s` on `[B, Hz)`. -/

/-! ## C's grant fields H_ARB1 / H_ARB2 at 1 ps ticks -/

/-- C's `H_ARB1` and `H_ARB2` (`OpsCM.AMerge`, verbatim shape) at the tick
`t → t+1`, with `x.req = r1`, `y.req = r2`, `z.ack = A0`. -/
def CArb (s : Sigs) (t : Int) : Prop :=
  (s.g1 (t + 1) ≠ s.g1 t → s.g1 (t + 1) = s.r1 t ∧
      (s.g1 (t + 1) = true → s.g2 t = false ∧ s.A0 t = false)) ∧
  (s.g2 (t + 1) ≠ s.g2 t → s.g2 (t + 1) = s.r2 t ∧
      (s.g2 (t + 1) = true → s.g1 t = false ∧ s.A0 t = false))

/-- Extra arc conditions for C's tick form (all named):
* `pos1`, `pos2` (H_TICK_CAUSAL): a request edge reaches its grant no sooner than one tick;
* `s1`, `s2` (RT1 / RT1b STRICT): the old grant falls at least one tick before the new
  one rises (C's rise clause reads the other grant one tick earlier);
* `a1`, `a2` (H_GRANT_IN_A0_LOW): the new grant rises inside A0's low phase: after A0's
  fall plus one tick, and no later than the earliest server re-rise (`RR + smin`). -/
structure CX (D : Dl) : Prop where
  pos1 : 1 ≤ D.wr1g + D.g1f1
  pos2 : 1 ≤ D.wr2g + D.g2f
  s1 : D.wr1g + D.g1f1 < D.wr1s + D.Rf1 + D.smin + D.wa0s + D.qf + D.wq + D.g2r ∨ D.g1fq < D.g2r
  s2 : D.wr2g + D.g2f < D.wr2s + D.Rf2 + D.smin + D.wa0s + D.qr + D.wq + D.g1rq ∨ D.g2f < D.g1rq
  a1 : 1 ≤ D.wa0s + D.qf + D.wq + D.g2r ∧ D.wq + D.g2r ≤ D.wfb + D.Rrq + D.smin
  a2 : 1 ≤ D.wa0s + D.qr + D.wq + D.g1rq ∧ D.wq + D.g1rq ≤ D.wfb + D.Rrq + D.smin

theorem carb_const {s : Sigs} {t : Int} (h1 : s.g1 (t + 1) = s.g1 t) (h2 : s.g2 (t + 1) = s.g2 t) :
    CArb s t := ⟨fun h => absurd h1 h, fun h => absurd h2 h⟩

section windows
variable {D : Dl} {s : Sigs} {M : Int}

theorem win1 (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D)
    {B t0 TA TA2 Hz a : Int}
    (hord : B + M ≤ t0 ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz) (ha : a ≤ B)
    (hpre : ∀ τ, B - M ≤ τ → τ < t0 → Q s P1 τ)
    (hr1 : ∀ τ, B - M ≤ τ → τ < Hz → s.r1 τ = decide (τ < t0))
    (hr2 : ∀ τ, B - M ≤ τ → τ < Hz → s.r2 τ = true)
    (hA0 : ∀ τ, B ≤ τ → τ < Hz → s.A0 τ = (decide (τ < TA) || decide (TA2 ≤ τ)))
    (ha0 : s.A0 (a - 1) = false) (hA0a : ∀ τ, a ≤ τ → τ < B → s.A0 τ = true)
    (hR0a : ∀ τ, a ≤ τ → τ < B → s.R0 τ = true) :
    (∀ t, B ≤ t → t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ t, TA2 + 3 * M ≤ t → t < Hz → Q s P2 t) ∧
    (∀ t, TA2 ≤ t → t < Hz → s.R0 t = true) ∧
    (CX D → ∀ t, B ≤ t → t + 1 < Hz → CArb s t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have hp := hM.pos; have := hM.q; have := hM.R0; have := hM.g1; have := hM.g2
  have := hM.A1; have := hM.A2
  obtain ⟨o1, o2, o3, o4⟩ := hord
  have hq : Quiet s P1 B M := by
    intro τ h1 h2
    exact ⟨by rw [hr1 τ (by omega) (by omega)]; simp [P1]; omega,
      by rw [hr2 τ (by omega) (by omega)]; rfl, hpre τ (by omega) (by omega)⟩
  have R' : Run D (splice s P1 B) :=
    splice_run R hM fix_P1 rfl hq ha ha0
      (fun τ h1 h2 => by
        by_cases hb : τ < B
        · exact hA0a τ h1 hb
        · rw [hA0 τ (by omega) (by omega)]; simp; omega)
      hR0a
  have S' : Scn D (splice s P1 B) t0 B TA TA2 Hz :=
    { H_ORDER := by omega
      H_r1 := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P1]; omega
        · rw [sp_r1 (by omega), hr1 t (by omega) ht]
      H_r2 := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P1]
        · rw [sp_r2 (by omega), hr2 t (by omega) ht]
      H_A0 := by intro t h1 h2; rw [sp_A0 h1, hA0 t h1 h2]
      H_A0_prev := by simp [splice]; intro h; omega
      H_q_init := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P1]
        · rw [sp_q (by omega), (hpre t (by omega) ht).1]; rfl
      H_A1_init := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P1]
        · rw [sp_A1 (by omega), (hpre t (by omega) ht).2.2.2.2.1]; rfl
      H_A2_init := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P1]
        · rw [sp_A2 (by omega), (hpre t (by omega) ht).2.2.2.2.2]; rfl
      H_SETTLED := by omega }
  have hTA := TA_ge R' S'
  have hTA2 := TA2_ge R' S'
  unfold TR at hTA; unfold RR QB at hTA2
  obtain ⟨p1, p2, _, _⟩ := hRT2
  have hRT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01 := by unfold T1 G1 QB; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t h1 h2
    have := rt1_exclusion R' S' hRT1 t h2
    rwa [sp_g1 h1, sp_g2 h1] at this
  · intro t h1 h2
    have hB : B ≤ t := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← sp_q (P := P1) hB, q_eq R' S' t h2]; simp [P2]; unfold QB; omega
    · rw [← sp_R0 (P := P1) hB, R0_after R' S' t (by unfold RR QB; omega) h2]; rfl
    · rw [← sp_g1 (P := P1) hB, g1_eq R' S' t h2]; simp [P2]; unfold G1 QB; omega
    · rw [← sp_g2 (P := P1) hB, g2_eq R' S' t h2]; simp [P2]; unfold G2 QB; omega
    · rw [← sp_A1 (P := P1) hB, A1_low_after R' S' hRT2a t (by unfold T1 G1 QB; omega) h2]; rfl
    · rw [← sp_A2 (P := P1) hB, A2_after R' S' t (by unfold G2 QB; omega) h2]; rfl
  · intro t h1 h2
    rw [← sp_R0 (P := P1) (B := B) (by omega), R0_after R' S' t (by unfold RR QB; omega) h2]
  · intro hx t h1 h2
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
    have g1t := g1_eq R' S' t (by omega)
    have g1u := g1_eq R' S' (t + 1) h2
    have g2t := g2_eq R' S' t (by omega)
    have g2u := g2_eq R' S' (t + 1) h2
    rw [sp_g1 h1] at g1t; rw [sp_g1 (by omega)] at g1u
    rw [sp_g2 h1] at g2t; rw [sp_g2 (by omega)] at g2u
    unfold CArb
    rw [g1t, g1u, g2t, g2u, hr1 t (by omega) (by omega), hr2 t (by omega) (by omega),
      hA0 t h1 (by omega)]
    have d1 : G1 D t0 TA = min (t0 + D.wr1g + D.g1f1) (TA + D.wa0s + D.qf + D.wq + D.g1fq) := rfl
    have d2 : G2 D TA = TA + D.wa0s + D.qf + D.wq + D.g2r := rfl
    refine ⟨fun hne => ?_, fun hne => ?_⟩
    · have e : G1 D t0 TA = t + 1 :=
        Classical.byContradiction fun hc => hne (by rw [decide_eq_decide]; omega)
      rw [@decide_eq_false _ _ (show ¬ t + 1 < G1 D t0 TA by omega),
        @decide_eq_false _ _ (show ¬ t < t0 by omega)]
      exact ⟨rfl, fun h => absurd h (by simp)⟩
    · have e : G2 D TA = t + 1 :=
        Classical.byContradiction fun hc => hne (by rw [decide_eq_decide]; omega)
      rw [@decide_eq_true _ _ (show G2 D TA ≤ t + 1 by omega)]
      refine ⟨rfl, fun _ => ⟨@decide_eq_false _ _ (by omega), ?_⟩⟩
      rw [@decide_eq_false _ _ (show ¬ t < TA by omega),
        @decide_eq_false _ _ (show ¬ TA2 ≤ t by omega)]; rfl

theorem win2 (R : Run D s) (hM : MB D M) (hRT1 : RT1b D) (hRT2 : RT2b D)
    {B t0 TA TA2 Hz a : Int}
    (hord : B + M ≤ t0 ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz) (ha : a ≤ B)
    (hpre : ∀ τ, B - M ≤ τ → τ < t0 → Q s P2 τ)
    (hr1 : ∀ τ, B - M ≤ τ → τ < Hz → s.r1 τ = true)
    (hr2 : ∀ τ, B - M ≤ τ → τ < Hz → s.r2 τ = decide (τ < t0))
    (hA0 : ∀ τ, B ≤ τ → τ < Hz → s.A0 τ = (decide (τ < TA) || decide (TA2 ≤ τ)))
    (ha0 : s.A0 (a - 1) = false) (hA0a : ∀ τ, a ≤ τ → τ < B → s.A0 τ = true)
    (hR0a : ∀ τ, a ≤ τ → τ < B → s.R0 τ = true) :
    (∀ t, B ≤ t → t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ t, TA2 + 3 * M ≤ t → t < Hz → Q s P1 t) ∧
    (∀ t, TA2 ≤ t → t < Hz → s.R0 t = true) ∧
    (CX D → ∀ t, B ≤ t → t + 1 < Hz → CArb s t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have hp := hM.pos; have := hM.q; have := hM.R0; have := hM.g1; have := hM.g2
  have := hM.A1; have := hM.A2
  obtain ⟨o1, o2, o3, o4⟩ := hord
  have hq : Quiet s P2 B M := by
    intro τ h1 h2
    exact ⟨by rw [hr1 τ (by omega) (by omega)]; rfl,
      by rw [hr2 τ (by omega) (by omega)]; simp [P2]; omega, hpre τ (by omega) (by omega)⟩
  have R' : Run D (splice s P2 B) :=
    splice_run R hM fix_P2 rfl hq ha ha0
      (fun τ h1 h2 => by
        by_cases hb : τ < B
        · exact hA0a τ h1 hb
        · rw [hA0 τ (by omega) (by omega)]; simp; omega)
      hR0a
  have S' : Scn2 D (splice s P2 B) t0 B TA TA2 Hz :=
    { H_ORDER := by omega
      H_r1 := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P2]
        · rw [sp_r1 (by omega), hr1 t (by omega) ht]
      H_r2 := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P2]; omega
        · rw [sp_r2 (by omega), hr2 t (by omega) ht]
      H_A0 := by intro t h1 h2; rw [sp_A0 h1, hA0 t h1 h2]
      H_A0_prev := by simp [splice]; intro h; omega
      H_q_init := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P2]
        · rw [sp_q (by omega), (hpre t (by omega) ht).1]; rfl
      H_A1_init := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P2]
        · rw [sp_A1 (by omega), (hpre t (by omega) ht).2.2.2.2.1]; rfl
      H_A2_init := by
        intro t ht
        by_cases hb : t < B
        · simp [splice, hb, P2]
        · rw [sp_A2 (by omega), (hpre t (by omega) ht).2.2.2.2.2]; rfl
      H_SETTLED := by omega }
  have hTA := TA_ge2 R' S'
  have hTA2 := TA2_ge2 R' S'
  unfold TRb at hTA; unfold RRb QBb at hTA2
  obtain ⟨p1, p2, _, _⟩ := hRT2
  have hRT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02 := by unfold T1b G2b QBb; omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t h1 h2
    have := rt1_exclusion2 R' S' hRT1 t h2
    rwa [sp_g1 h1, sp_g2 h1] at this
  · intro t h1 h2
    have hB : B ≤ t := by omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← sp_q (P := P2) hB, q_eq2 R' S' t h2]; simp [P1]; unfold QBb; omega
    · rw [← sp_R0 (P := P2) hB, R0_after2 R' S' t (by unfold RRb QBb; omega) h2]; rfl
    · rw [← sp_g1 (P := P2) hB, g1_eq2 R' S' t h2]; simp [P1]; unfold G1b QBb; omega
    · rw [← sp_g2 (P := P2) hB, g2_eq2 R' S' t h2]; simp [P1]; unfold G2b QBb; omega
    · rw [← sp_A1 (P := P2) hB, A1_after2 R' S' t (by unfold G1b QBb; omega) h2]; rfl
    · rw [← sp_A2 (P := P2) hB, A2_low_after2 R' S' hRT2a t (by unfold T1b G2b QBb; omega) h2]; rfl
  · intro t h1 h2
    rw [← sp_R0 (P := P2) (B := B) (by omega), R0_after2 R' S' t (by unfold RRb QBb; omega) h2]
  · intro hx t h1 h2
    obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hx
    have g1t := g1_eq2 R' S' t (by omega)
    have g1u := g1_eq2 R' S' (t + 1) h2
    have g2t := g2_eq2 R' S' t (by omega)
    have g2u := g2_eq2 R' S' (t + 1) h2
    rw [sp_g1 h1] at g1t; rw [sp_g1 (by omega)] at g1u
    rw [sp_g2 h1] at g2t; rw [sp_g2 (by omega)] at g2u
    unfold CArb
    rw [g1t, g1u, g2t, g2u, hr1 t (by omega) (by omega), hr2 t (by omega) (by omega),
      hA0 t h1 (by omega)]
    have d1 : G1b D TA = TA + D.wa0s + D.qr + D.wq + D.g1rq := rfl
    have d2 : G2b D t0 TA = min (t0 + D.wr2g) (TA + D.wa0s + D.qr + D.wq) + D.g2f := rfl
    refine ⟨fun hne => ?_, fun hne => ?_⟩
    · have e : G1b D TA = t + 1 := Classical.byContradiction fun hc => hne (by rw [decide_eq_decide]; omega)
      rw [@decide_eq_true _ _ (show G1b D TA ≤ t + 1 by omega)]
      refine ⟨rfl, fun _ => ⟨@decide_eq_false _ _ (by omega), ?_⟩⟩
      rw [@decide_eq_false _ _ (show ¬ t < TA by omega), @decide_eq_false _ _ (show ¬ TA2 ≤ t by omega)]; rfl
    · have e : G2b D t0 TA = t + 1 := Classical.byContradiction fun hc => hne (by rw [decide_eq_decide]; omega)
      rw [@decide_eq_false _ _ (show ¬ t + 1 < G2b D t0 TA by omega),
        @decide_eq_false _ _ (show ¬ t < t0 by omega)]
      exact ⟨rfl, fun h => absurd h (by simp)⟩

end windows

/-! ## The infinite run: schedule, hypotheses, induction over handovers -/

/-- The observable edges of an alternating-contention run. Handover `k` is
released by client 1 for even `k`, client 2 for odd `k`: the holder drops its
request at `t0 k`, the server drops A0 at `TA k` and re-raises it (for the other
client) at `TA2 k`, and the releasing client re-requests at `u k`. -/
structure Sched where
  t0 : Nat → Int
  TA : Nat → Int
  TA2 : Nat → Int
  u : Nat → Int
  B0 : Int
  a0 : Int

namespace Sched
/-- Splice point of handover `k`. -/
def Bk (S : Sched) (M : Int) : Nat → Int
  | 0 => S.B0
  | k + 1 => S.u k + M
/-- Last A0 rise before handover `k`. -/
def aK (S : Sched) : Nat → Int
  | 0 => S.a0
  | k + 1 => S.TA2 k
/-- Since when the releaser of handover `k` has been requesting. -/
def rq (S : Sched) (M : Int) : Nat → Int
  | 0 => S.B0 - M
  | 1 => S.B0 - M
  | k + 2 => S.u k
end Sched

/-- **The multi-token run hypotheses** (all named; every one is about the
environment or the observed edge times, none about the arbiter's internals
after `B0`):
* `H_ORD`: per handover, `t0 < TA < TA2`; **H_SLOW_REREQ** `TA2 + 4M ≤ u` (the
  releasing client re-requests only after the handover has settled at every
  gate input); **H_HOLD** `u + 2M ≤ t0 (k+1)` (the new holder keeps its request
  until the loser's re-request has settled: sustained contention);
* `H_A0`, `H_A0_PREV`: the server's A0 is `[aK k ≤ t < TA k]` high, `[TA k, TA2 k)`
  low (its response is otherwise constrained only by `Run`'s H_SERVER_MIN);
* `H_REQ1`, `H_REQ2`: four-phase clients without withdrawal: the releaser of
  handover `k` is high from its previous re-request until `t0 k`, low on
  `[t0 k, u k)`;
* `H_INIT`, `H_R0_INIT`: before `t0 0` the arbiter is settled with client 1
  holding (`P1`) on a window of length `M`, and R0 has been high since A0's last rise. -/
structure MTRun (D : Dl) (s : Sigs) (M : Int) (S : Sched) : Prop where
  H_ORD : ∀ k, S.t0 k < S.TA k ∧ S.TA k < S.TA2 k ∧ S.TA2 k + 3 * M ≤ S.u k ∧
    S.u k + 2 * M ≤ S.t0 (k + 1)
  H_B0 : S.B0 + M ≤ S.t0 0 ∧ S.a0 ≤ S.B0
  H_A0_PREV : s.A0 (S.a0 - 1) = false
  H_A0 : ∀ k τ, S.aK k ≤ τ → τ < S.TA2 k → s.A0 τ = decide (τ < S.TA k)
  H_REQ1 : ∀ j τ, S.rq M (2 * j) ≤ τ → τ < S.u (2 * j) → s.r1 τ = decide (τ < S.t0 (2 * j))
  H_REQ2 : ∀ j τ, S.rq M (2 * j + 1) ≤ τ → τ < S.u (2 * j + 1) →
    s.r2 τ = decide (τ < S.t0 (2 * j + 1))
  H_INIT : ∀ τ, S.B0 - M ≤ τ → τ < S.t0 0 → Q s P1 τ
  H_R0_INIT : ∀ τ, S.a0 ≤ τ → τ < S.B0 → s.R0 τ = true

section run
variable {D : Dl} {s : Sigs} {M : Int} {S : Sched}

theorem bk_t0 (Hr : MTRun D s M S) : ∀ k, S.Bk M k + M ≤ S.t0 k := by
  intro k; cases k with
  | zero => exact Hr.H_B0.1
  | succ k => have := Hr.H_ORD k; simp only [Sched.Bk]; omega

theorem ak_bk (Hr : MTRun D s M S) (hp : 1 ≤ M) : ∀ k, S.aK k ≤ S.Bk M k := by
  intro k; cases k with
  | zero => exact Hr.H_B0.2
  | succ k => have := Hr.H_ORD k; simp only [Sched.Bk, Sched.aK]; omega

theorem rq_bk (Hr : MTRun D s M S) (hp : 1 ≤ M) : ∀ k, S.rq M k ≤ S.Bk M k - M := by
  intro k
  match k with
  | 0 => simp only [Sched.rq, Sched.Bk]; omega
  | 1 => have := Hr.H_ORD 0; have := Hr.H_B0; simp only [Sched.rq, Sched.Bk]; omega
  | k + 2 => have := Hr.H_ORD k; have := Hr.H_ORD (k + 1); simp only [Sched.rq, Sched.Bk]; omega

theorem rq_next : ∀ k, S.rq M (k + 1) ≤ S.Bk M k - M := by
  intro k; cases k with
  | zero => simp only [Sched.rq, Sched.Bk]; omega
  | succ k => simp only [Sched.rq, Sched.Bk]; omega

theorem rq_u (Hr : MTRun D s M S) (hp : 1 ≤ M) : ∀ k, S.rq M (k + 1) ≤ S.u k - M := by
  intro k; cases k with
  | zero => have := Hr.H_ORD 0; have := Hr.H_B0; simp only [Sched.rq]; omega
  | succ k => have := Hr.H_ORD k; have := Hr.H_ORD (k + 1); simp only [Sched.rq]; omega

theorem a0_prev (Hr : MTRun D s M S) (hp : 1 ≤ M) : ∀ k, s.A0 (S.aK k - 1) = false := by
  intro k; cases k with
  | zero => exact Hr.H_A0_PREV
  | succ k =>
    have := Hr.H_ORD k; have := ak_bk Hr hp k; have := bk_t0 Hr k
    simp only [Sched.aK]
    rw [Hr.H_A0 k _ (by omega) (by omega)]; simp; omega

theorem a0_hi (Hr : MTRun D s M S) (hp : 1 ≤ M) :
    ∀ k τ, S.aK k ≤ τ → τ < S.Bk M k → s.A0 τ = true := by
  intro k τ h1 h2
  have := Hr.H_ORD k; have := bk_t0 Hr k
  rw [Hr.H_A0 k τ h1 (by omega)]; simp; omega

theorem a0_win (Hr : MTRun D s M S) (hp : 1 ≤ M) : ∀ k τ, S.Bk M k ≤ τ → τ < S.u k →
    s.A0 τ = (decide (τ < S.TA k) || decide (S.TA2 k ≤ τ)) := by
  intro k τ h1 h2
  have := Hr.H_ORD k; have := Hr.H_ORD (k + 1); have := ak_bk Hr hp k; have := bk_t0 Hr k
  by_cases hc : τ < S.TA2 k
  · rw [Hr.H_A0 k τ (by omega) hc]; simp; omega
  · rw [Hr.H_A0 (k + 1) τ (by show S.TA2 k ≤ τ; omega) (by omega)]
    rw [Bool.eq_iff_iff]; simp; omega

/-- The induction invariant at handover `k`: settled in `P` on `[Bk - M, t0 k)`,
R0 high since A0's last rise, and grant exclusion on `[B0, t0 k)`. -/
def Inv (s : Sigs) (M : Int) (S : Sched) (k : Nat) (P : St) : Prop :=
  (∀ τ, S.Bk M k - M ≤ τ → τ < S.t0 k → Q s P τ) ∧
  (∀ τ, S.aK k ≤ τ → τ < S.Bk M k → s.R0 τ = true) ∧
  (∀ τ, S.B0 ≤ τ → τ < S.t0 k → (s.g1 τ && s.g2 τ) = false)

theorem step1 (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D) (Hr : MTRun D s M S)
    (k : Nat)
    (hrel : ∀ τ, S.rq M k ≤ τ → τ < S.u k → s.r1 τ = decide (τ < S.t0 k))
    (hwait : ∀ τ, S.rq M (k + 1) ≤ τ → τ < S.u (k + 1) → s.r2 τ = decide (τ < S.t0 (k + 1)))
    (I : Inv s M S k P1) : Inv s M S (k + 1) P2 := by
  have hp := hM.pos
  obtain ⟨iQ, iR, iE⟩ := I
  have o := Hr.H_ORD k; have o' := Hr.H_ORD (k + 1)
  have b1 := bk_t0 Hr k; have b2 := rq_bk Hr hp k; have b3 := rq_next (S := S) (M := M) k
  have b4 := rq_u Hr hp k
  obtain ⟨E, Qe, Re, _⟩ := win1 R hM hRT1 hRT2 (B := S.Bk M k) (t0 := S.t0 k) (TA := S.TA k)
    (TA2 := S.TA2 k) (Hz := S.u k) (a := S.aK k) ⟨b1, o.1, o.2.1, by omega⟩ (ak_bk Hr hp k) iQ
    (fun τ h1 h2 => hrel τ (by omega) h2)
    (fun τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (a0_win Hr hp k) (a0_prev Hr hp k) (a0_hi Hr hp k) iR
  have Pq := persist R hM ins_P2 (S.u k) (S.t0 (k + 1)) (fun h => absurd h (by simp))
    (fun _ τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (fun τ h1 h2 => Qe τ (by omega) h2)
  refine ⟨?_, ?_, ?_⟩
  · intro τ h1 h2; simp only [Sched.Bk] at h1; exact Pq τ (by omega) h2
  · intro τ h1 h2
    simp only [Sched.Bk, Sched.aK] at h1 h2
    by_cases hc : τ < S.u k
    · exact Re τ h1 hc
    · exact (Pq τ (by omega) (by omega)).2.1
  · intro τ h1 h2
    by_cases c1 : τ < S.t0 k
    · exact iE τ h1 c1
    · by_cases c2 : τ < S.u k
      · exact E τ (by omega) c2
      · rw [(Pq τ (by omega) h2).2.2.1]; rfl

theorem step2 (R : Run D s) (hM : MB D M) (hRT1 : RT1b D) (hRT2 : RT2b D) (Hr : MTRun D s M S)
    (k : Nat)
    (hrel : ∀ τ, S.rq M k ≤ τ → τ < S.u k → s.r2 τ = decide (τ < S.t0 k))
    (hwait : ∀ τ, S.rq M (k + 1) ≤ τ → τ < S.u (k + 1) → s.r1 τ = decide (τ < S.t0 (k + 1)))
    (I : Inv s M S k P2) : Inv s M S (k + 1) P1 := by
  have hp := hM.pos
  obtain ⟨iQ, iR, iE⟩ := I
  have o := Hr.H_ORD k; have o' := Hr.H_ORD (k + 1)
  have b1 := bk_t0 Hr k; have b2 := rq_bk Hr hp k; have b3 := rq_next (S := S) (M := M) k
  have b4 := rq_u Hr hp k
  obtain ⟨E, Qe, Re, _⟩ := win2 R hM hRT1 hRT2 (B := S.Bk M k) (t0 := S.t0 k) (TA := S.TA k)
    (TA2 := S.TA2 k) (Hz := S.u k) (a := S.aK k) ⟨b1, o.1, o.2.1, by omega⟩ (ak_bk Hr hp k) iQ
    (fun τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (fun τ h1 h2 => hrel τ (by omega) h2)
    (a0_win Hr hp k) (a0_prev Hr hp k) (a0_hi Hr hp k) iR
  have Pq := persist R hM ins_P1 (S.u k) (S.t0 (k + 1))
    (fun _ τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (fun h => absurd h (by simp))
    (fun τ h1 h2 => Qe τ (by omega) h2)
  refine ⟨?_, ?_, ?_⟩
  · intro τ h1 h2; simp only [Sched.Bk] at h1; exact Pq τ (by omega) h2
  · intro τ h1 h2
    simp only [Sched.Bk, Sched.aK] at h1 h2
    by_cases hc : τ < S.u k
    · exact Re τ h1 hc
    · exact (Pq τ (by omega) (by omega)).2.1
  · intro τ h1 h2
    by_cases c1 : τ < S.t0 k
    · exact iE τ h1 c1
    · by_cases c2 : τ < S.u k
      · exact E τ (by omega) c2
      · rw [(Pq τ (by omega) h2).2.2.2.1]; simp [P1]

theorem inv_all (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D) (hRT1b : RT1b D)
    (hRT2b : RT2b D) (Hr : MTRun D s M S) : ∀ j, Inv s M S (2 * j) P1 := by
  intro j
  induction j with
  | zero =>
    refine ⟨fun τ h1 h2 => Hr.H_INIT τ (by simpa [Sched.Bk] using h1) h2, Hr.H_R0_INIT, ?_⟩
    intro τ h1 h2
    rw [(Hr.H_INIT τ (by have := hM.pos; omega) h2).2.2.2.1]; simp [P1]
  | succ j ih =>
    have I1 := step1 R hM hRT1 hRT2 Hr (2 * j) (Hr.H_REQ1 j) (Hr.H_REQ2 j) ih
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    rw [e]
    exact step2 R hM hRT1b hRT2b Hr (2 * j + 1) (Hr.H_REQ2 j)
      (fun τ h1 h2 => by
        have := Hr.H_REQ1 (j + 1) τ; rw [e] at this; exact this h1 h2) I1

theorem t0_ge (Hr : MTRun D s M S) (hp : 1 ≤ M) : ∀ k : Nat, S.t0 0 + k ≤ S.t0 k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => have := Hr.H_ORD k; push_cast; omega

/-- **Multi-token grant exclusion of the held `bd_arbiter`.** For every run of the
gate relations (`Run`: real INITs, rise-fast OR channel per LUT output, routed
pure delay per pin, server with minimum response `smin`) that follows an
alternating-contention schedule `S` (`MTRun`: four-phase clients, slow
re-request, sustained contention), under 7h's RT1 + RT2 and 7j's RT1b + RT2b
(arc forms, every handover) and H_M, the grants are never both high at any
`t ≥ B0`, over infinitely many handovers. -/
theorem mt_exclusion (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D)
    (hRT1b : RT1b D) (hRT2b : RT2b D) (Hr : MTRun D s M S) :
    ∀ t, S.B0 ≤ t → (s.g1 t && s.g2 t) = false := by
  intro t ht
  have hp := hM.pos
  have h := t0_ge Hr hp (2 * ((t - S.t0 0).toNat + 1))
  exact (inv_all R hM hRT1 hRT2 hRT1b hRT2b Hr ((t - S.t0 0).toNat + 1)).2.2 t ht (by omega)

/-- **C's H_ARB_EXCL** (`OpsCM.AMerge`, `IpowCells`, verbatim shape `∀ t, (g1 t && g2 t) = false`
on Nat-indexed traces), for the held arbiter's grants sampled at ANY times `σ n ≥ B0`
(for instance C's tick `n` at `B0 + n` ps). -/
theorem H_ARB_EXCL_of_mt (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D)
    (hRT1b : RT1b D) (hRT2b : RT2b D) (Hr : MTRun D s M S) (σ : Nat → Int)
    (hσ : ∀ n, S.B0 ≤ σ n) :
    ∀ n, ((fun n => s.g1 (σ n)) n && (fun n => s.g2 (σ n)) n) = false :=
  fun n => mt_exclusion R hM hRT1 hRT2 hRT1b hRT2b Hr (σ n) (hσ n)

/-! ### C's H_ARB1 / H_ARB2 over the whole run -/

/-- The C-field invariant: C's grant fields at every tick of `[B0, t0 k - 1)`. -/
def InvC (s : Sigs) (S : Sched) (k : Nat) : Prop :=
  ∀ τ, S.B0 ≤ τ → τ + 1 < S.t0 k → CArb s τ

theorem stepC1 (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D) (hx : CX D)
    (Hr : MTRun D s M S) (k : Nat)
    (hrel : ∀ τ, S.rq M k ≤ τ → τ < S.u k → s.r1 τ = decide (τ < S.t0 k))
    (hwait : ∀ τ, S.rq M (k + 1) ≤ τ → τ < S.u (k + 1) → s.r2 τ = decide (τ < S.t0 (k + 1)))
    (I : Inv s M S k P1) (IC : InvC s S k) : InvC s S (k + 1) := by
  have hp := hM.pos
  obtain ⟨iQ, iR, _⟩ := I
  have o := Hr.H_ORD k; have o' := Hr.H_ORD (k + 1)
  have b1 := bk_t0 Hr k; have b2 := rq_bk Hr hp k; have b3 := rq_next (S := S) (M := M) k
  have b4 := rq_u Hr hp k
  obtain ⟨_, Qe, _, C⟩ := win1 R hM hRT1 hRT2 (B := S.Bk M k) (t0 := S.t0 k) (TA := S.TA k)
    (TA2 := S.TA2 k) (Hz := S.u k) (a := S.aK k) ⟨b1, o.1, o.2.1, by omega⟩ (ak_bk Hr hp k) iQ
    (fun τ h1 h2 => hrel τ (by omega) h2)
    (fun τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (a0_win Hr hp k) (a0_prev Hr hp k) (a0_hi Hr hp k) iR
  have Pq := persist R hM ins_P2 (S.u k) (S.t0 (k + 1)) (fun h => absurd h (by simp))
    (fun _ τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (fun τ h1 h2 => Qe τ (by omega) h2)
  intro τ h1 h2
  by_cases c1 : τ + 1 < S.t0 k
  · exact IC τ h1 c1
  · by_cases c2 : τ + 1 < S.u k
    · exact C hx τ (by omega) c2
    · have q0 := Pq τ (by omega) (by omega)
      have q1 := Pq (τ + 1) (by omega) h2
      exact carb_const (q1.2.2.1.trans q0.2.2.1.symm) (q1.2.2.2.1.trans q0.2.2.2.1.symm)

theorem stepC2 (R : Run D s) (hM : MB D M) (hRT1 : RT1b D) (hRT2 : RT2b D) (hx : CX D)
    (Hr : MTRun D s M S) (k : Nat)
    (hrel : ∀ τ, S.rq M k ≤ τ → τ < S.u k → s.r2 τ = decide (τ < S.t0 k))
    (hwait : ∀ τ, S.rq M (k + 1) ≤ τ → τ < S.u (k + 1) → s.r1 τ = decide (τ < S.t0 (k + 1)))
    (I : Inv s M S k P2) (IC : InvC s S k) : InvC s S (k + 1) := by
  have hp := hM.pos
  obtain ⟨iQ, iR, _⟩ := I
  have o := Hr.H_ORD k; have o' := Hr.H_ORD (k + 1)
  have b1 := bk_t0 Hr k; have b2 := rq_bk Hr hp k; have b3 := rq_next (S := S) (M := M) k
  have b4 := rq_u Hr hp k
  obtain ⟨_, Qe, _, C⟩ := win2 R hM hRT1 hRT2 (B := S.Bk M k) (t0 := S.t0 k) (TA := S.TA k)
    (TA2 := S.TA2 k) (Hz := S.u k) (a := S.aK k) ⟨b1, o.1, o.2.1, by omega⟩ (ak_bk Hr hp k) iQ
    (fun τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (fun τ h1 h2 => hrel τ (by omega) h2)
    (a0_win Hr hp k) (a0_prev Hr hp k) (a0_hi Hr hp k) iR
  have Pq := persist R hM ins_P1 (S.u k) (S.t0 (k + 1))
    (fun _ τ h1 h2 => by rw [hwait τ (by omega) (by omega)]; simp; omega)
    (fun h => absurd h (by simp))
    (fun τ h1 h2 => Qe τ (by omega) h2)
  intro τ h1 h2
  by_cases c1 : τ + 1 < S.t0 k
  · exact IC τ h1 c1
  · by_cases c2 : τ + 1 < S.u k
    · exact C hx τ (by omega) c2
    · have q0 := Pq τ (by omega) (by omega)
      have q1 := Pq (τ + 1) (by omega) h2
      exact carb_const (q1.2.2.1.trans q0.2.2.1.symm) (q1.2.2.2.1.trans q0.2.2.2.1.symm)

theorem invC_all (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D) (hRT1b : RT1b D)
    (hRT2b : RT2b D) (hx : CX D) (Hr : MTRun D s M S) : ∀ j, InvC s S (2 * j) := by
  intro j
  induction j with
  | zero =>
    intro τ h1 h2
    simp only [Nat.mul_zero] at h2
    have q0 := Hr.H_INIT τ (by have := hM.pos; omega) (by omega)
    have q1 := Hr.H_INIT (τ + 1) (by have := hM.pos; omega) h2
    exact carb_const (q1.2.2.1.trans q0.2.2.1.symm) (q1.2.2.2.1.trans q0.2.2.2.1.symm)
  | succ j ih =>
    have I0 := inv_all R hM hRT1 hRT2 hRT1b hRT2b Hr j
    have I1 := step1 R hM hRT1 hRT2 Hr (2 * j) (Hr.H_REQ1 j) (Hr.H_REQ2 j) I0
    have C1 := stepC1 R hM hRT1 hRT2 hx Hr (2 * j) (Hr.H_REQ1 j) (Hr.H_REQ2 j) I0 ih
    have e : 2 * (j + 1) = 2 * j + 1 + 1 := by omega
    rw [e]
    exact stepC2 R hM hRT1b hRT2b hx Hr (2 * j + 1) (Hr.H_REQ2 j)
      (fun τ h1 h2 => by
        have := Hr.H_REQ1 (j + 1) τ; rw [e] at this; exact this h1 h2) I1 C1

/-- **C's H_ARB1 and H_ARB2, derived** for the held arbiter over the whole
multi-token run, at C's tick = 1 ps starting at `B0` (`x.req = r1`, `y.req = r2`,
`z.ack = A0`), under the hypotheses of `mt_exclusion` plus `CX` (strict RT1/RT1b,
one-tick causality, grant rise inside A0's low phase). -/
theorem H_ARB12_of_mt (R : Run D s) (hM : MB D M) (hRT1 : RT1 D) (hRT2 : RT2 D)
    (hRT1b : RT1b D) (hRT2b : RT2b D) (hx : CX D) (Hr : MTRun D s M S) :
    let g1 : Nat → Bool := fun n => s.g1 (S.B0 + n)
    let g2 : Nat → Bool := fun n => s.g2 (S.B0 + n)
    let xr : Nat → Bool := fun n => s.r1 (S.B0 + n)
    let yr : Nat → Bool := fun n => s.r2 (S.B0 + n)
    let za : Nat → Bool := fun n => s.A0 (S.B0 + n)
    (∀ t, g1 (t + 1) ≠ g1 t → g1 (t + 1) = xr t ∧ (g1 (t + 1) = true → g2 t = false ∧ za t = false)) ∧
    (∀ t, g2 (t + 1) ≠ g2 t → g2 (t + 1) = yr t ∧ (g2 (t + 1) = true → g1 t = false ∧ za t = false)) ∧
    (∀ t, (g1 t && g2 t) = false) := by
  have hp := hM.pos
  have key : ∀ τ, S.B0 ≤ τ → CArb s τ := by
    intro τ hτ
    have h := t0_ge Hr hp (2 * ((τ - S.t0 0).toNat + 2))
    exact invC_all R hM hRT1 hRT2 hRT1b hRT2b hx Hr ((τ - S.t0 0).toNat + 2) τ hτ (by omega)
  refine ⟨fun t => ?_, fun t => ?_, fun t => mt_exclusion R hM hRT1 hRT2 hRT1b hRT2b Hr _ (by omega)⟩
  · have := (key (S.B0 + t) (by omega)).1
    simp only [show S.B0 + ((t + 1 : Nat) : Int) = S.B0 + t + 1 by push_cast; omega]
    exact this
  · have := (key (S.B0 + t) (by omega)).2
    simp only [show S.B0 + ((t + 1 : Nat) : Int) = S.B0 + t + 1 by push_cast; omega]
    exact this

end run

/-! ## Non-vacuity: an infinite run with nonzero delays and infinitely many handovers

`Dw`: every route 1 ps, every arc 1 ps (rise = fall, one consistent corner),
server minimum response 3 ps; so every gate output is its function of its
inputs 2 ps earlier, and the server is the pure delay `A0 t = R0 (t - 3)`.
`Ww`: a periodic run (period 48 ps, two handovers per period). Per period
(`r = t mod 48`): client 1 drops at 0 and re-requests at 20, client 2 drops at
24 and re-requests at 44; A0 low on [5,12) and [29,36); q low on [7,31); R0
low on [2,9) and [26,33); g1 high on [33,48) ∪ [0,2); g2 high on [9,26); A1 high
on [38,48) ∪ [0,7); A2 high on [14,31). All values were derived by hand from the
instant formulas (TR = t0+2, TA = TR+3, QB = TA+2, G2 = RR = QB+2, TA2 = RR+3,
T1 = 7, A2 rise = 14, mirror +24) and cross-checked by a discrete simulation
(scratch, not part of the proof); the gate relations below are checked for ALL
t ∈ ℤ, so a wrong value would fail to check. Schedule `Sw`: `t0 k = 24k`,
`TA k = 24k+5`, `TA2 k = 24k+12`, `u k = 24k+20`, `B0 = -2`, `a0 = -12`, `M = 2`. -/

def Dw : Dl where
  wr1s := 1
  wr2s := 1
  wr1g := 1
  wr2g := 1
  wfb := 1
  wa0s := 1
  wq := 1
  wg1 := 1
  wa01 := 1
  wfa1 := 1
  wg2 := 1
  wa02 := 1
  wfa2 := 1
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := 1
  c2r := 1
  c2f := 1
  smin := 3
  H_NONNEG := by decide
  H_RISE_LE_FALL := by decide
  H_LOOP_POS := by decide

def Ww : Sigs where
  r1 := fun t => !decide (t % 48 < 20)
  r2 := fun t => !(decide (24 ≤ t % 48) && decide (t % 48 < 44))
  q := fun t => !(decide (7 ≤ t % 48) && decide (t % 48 < 31))
  R0 := fun t => !((decide (2 ≤ t % 48) && decide (t % 48 < 9)) ||
    (decide (26 ≤ t % 48) && decide (t % 48 < 33)))
  g1 := fun t => decide (33 ≤ t % 48) || decide (t % 48 < 2)
  g2 := fun t => decide (9 ≤ t % 48) && decide (t % 48 < 26)
  A0 := fun t => !((decide (5 ≤ t % 48) && decide (t % 48 < 12)) ||
    (decide (29 ≤ t % 48) && decide (t % 48 < 36)))
  A1 := fun t => decide (38 ≤ t % 48) || decide (t % 48 < 7)
  A2 := fun t => decide (14 ≤ t % 48) && decide (t % 48 < 31)

def Sw : Sched where
  t0 := fun k => 24 * (k : Int)
  TA := fun k => 24 * (k : Int) + 5
  TA2 := fun k => 24 * (k : Int) + 12
  u := fun k => 24 * (k : Int) + 20
  B0 := -2
  a0 := -12

theorem Ww_run : Run Dw Ww where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [Ww, Dw, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [Ww, Dw, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [Ww, Dw, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [Ww, Dw, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [Ww, Dw, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [Ww, Dw, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t % 48 = 5 ∨ t % 48 = 12 ∨ t % 48 = 29 ∨ t % 48 = 36 :=
      Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [Ww]; omega)
    refine ⟨t - 3, by simp [Dw], by rw [Bool.eq_iff_iff]; simp [Ww]; omega, ?_⟩
    intro v h1 h2
    rw [Bool.eq_iff_iff]; simp [Ww]; omega

theorem Dw_MB : MB Dw 2 := by
  refine ⟨by decide, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Dw]

theorem Dw_CX : CX Dw := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [Dw]

theorem Dw_rt : RT1 Dw ∧ RT2 Dw ∧ RT1b Dw ∧ RT2b Dw := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ⟨?_, ?_, ?_, ?_⟩⟩ <;> simp [RT1, RT1b, Dw]

theorem rq_ee (S : Sched) (M : Int) (j : Nat) : S.rq M (2 * (j + 1)) = S.u (2 * j) := by
  rw [show 2 * (j + 1) = 2 * j + 2 by omega]; rfl
theorem rq_oo (S : Sched) (M : Int) (j : Nat) : S.rq M (2 * (j + 1) + 1) = S.u (2 * j + 1) := by
  rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by omega]; rfl

theorem Ww_mt : MTRun Dw Ww 2 Sw where
  H_ORD := by intro k; simp [Sw]; omega
  H_B0 := by simp [Sw]
  H_A0_PREV := by decide
  H_A0 := by
    intro k τ h1 h2
    cases k with
    | zero =>
      simp only [Sched.aK, Sw] at h1 h2
      rw [Bool.eq_iff_iff]; simp [Ww, Sw]; omega
    | succ k =>
      simp only [Sched.aK, Sw] at h1 h2
      rw [Bool.eq_iff_iff]; simp [Ww, Sw]; push_cast at h1 h2 ⊢
      refine Iff.trans ?_ decide_eq_true_iff.symm
      have hc : τ / 48 = (k : Int) / 2 ∨ τ / 48 = (k : Int) / 2 + 1 := by omega
      have hk : (k : Int) % 2 = 0 ∨ (k : Int) % 2 = 1 := by omega
      rcases hc with hc | hc <;> rcases hk with hk | hk <;> omega
  H_REQ1 := by
    intro j τ h1 h2
    cases j with
    | zero =>
      simp only [Sched.rq, Sw] at h1 h2
      rw [Bool.eq_iff_iff]; simp [Ww, Sw] at h2 ⊢; omega
    | succ j =>
      rw [rq_ee] at h1
      simp only [Sw] at h1 h2
      rw [Bool.eq_iff_iff]; simp [Ww, Sw]; push_cast at h1 h2 ⊢
      refine Iff.trans ?_ decide_eq_true_iff.symm
      have hc : τ / 48 = j ∨ τ / 48 = j + 1 := by omega
      rcases hc with hc | hc <;> omega
  H_REQ2 := by
    intro j τ h1 h2
    cases j with
    | zero =>
      simp only [Sched.rq, Sw] at h1 h2
      rw [Bool.eq_iff_iff]; simp [Ww, Sw] at h2 ⊢; omega
    | succ j =>
      rw [rq_oo] at h1
      simp only [Sw] at h1 h2
      rw [Bool.eq_iff_iff]; simp [Ww, Sw]; push_cast at h1 h2 ⊢
      refine Iff.trans ?_ decide_eq_true_iff.symm
      have hc : τ / 48 = j ∨ τ / 48 = j + 1 := by omega
      rcases hc with hc | hc <;> omega
  H_INIT := by
    intro τ h1 h2
    simp only [Sw] at h1 h2
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (simp [Ww, P1]; omega)
  H_R0_INIT := by
    intro τ h1 h2
    simp only [Sw] at h1 h2
    simp [Ww]; omega

/-- **Non-vacuity of `mt_exclusion`**: one delay set with every route and arc
nonzero (1 ps) and a 3 ps server, and one run of the gate relations over all of
ℤ, satisfy H_M, RT1, RT2, RT1b, RT2b, `CX` and the multi-token schedule with infinitely
many handovers; the grants really alternate (g2 rises at 9, g1 at 33, g2 again at
57 ps: at least two handovers each way). -/
theorem mt_nonvacuous : ∃ (D : Dl) (s : Sigs) (M : Int) (S : Sched),
    Run D s ∧ MB D M ∧ RT1 D ∧ RT2 D ∧ RT1b D ∧ RT2b D ∧ CX D ∧ MTRun D s M S ∧
    0 < D.wr1s ∧ 0 < D.qr ∧ 0 < D.smin ∧
    s.g2 8 = false ∧ s.g2 9 = true ∧ s.g1 32 = false ∧ s.g1 33 = true ∧
    s.g2 56 = false ∧ s.g2 57 = true ∧ s.g1 80 = false ∧ s.g1 81 = true :=
  ⟨Dw, Ww, 2, Sw, Ww_run, Dw_MB, Dw_rt.1, Dw_rt.2.1, Dw_rt.2.2.1, Dw_rt.2.2.2, Dw_CX, Ww_mt,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

end Formal.Cells.ArbMultiToken
