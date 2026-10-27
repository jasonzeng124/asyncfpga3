import Formal.Net.HandshakeLive
import Formal.Net.HandshakeWitness

/-! Audit of shard C composition claims (Formal/Net/Handshake*.lean @ 71ee3e86).

Shard C's own witness (HandshakeWitness) has n = 1, so H_SEP / H_HOLD
(quantified over j + 1 < n) are vacuous there, and `muller_live` has no witness
at all. Here: a periodic 2-stage run satisfying ALL hypotheses of
`muller_pipeline` (with Sep 2 / Hold 4 exercised) and of `muller_live`, plus two
runs showing H_SRC_LIVE and H_CEL_FAIR cannot be dropped. -/

namespace Audit.C.HS
open Formal.Net Formal.Net.Handshake

def mkCh (r c0 c1 a : Trace) : Nat → Chan
  | 0 => { req := r, ack := c0, dat := fun _ => 42 }
  | 1 => { req := c0, ack := c1, dat := fun _ => 42 }
  | _ => { req := c1, ack := a, dat := fun _ => 42 }

/-! ## Periodic run, period 16, one event every 2 ticks:
    state k = (t % 16) / 2 : r c0 c1 a = 0000 1000 1100 1110 1111 0111 0011 0001 -/
def rf  (p : Nat) : Bool := decide (2 ≤ p ∧ p ≤ 9)
def c0f (p : Nat) : Bool := decide (4 ≤ p ∧ p ≤ 11)
def c1f (p : Nat) : Bool := decide (6 ≤ p ∧ p ≤ 13)
def af  (p : Nat) : Bool := decide (8 ≤ p ∧ p ≤ 15)
def R  : Trace := fun t => rf (t % 16)
def C0 : Trace := fun t => c0f (t % 16)
def C1 : Trace := fun t => c1f (t % 16)
def A  : Trace := fun t => af (t % 16)
def ch : Nat → Chan := mkCh R C0 C1 A

theorem msucc (t : Nat) : (t + 1) % 16 = (t % 16 + 1) % 16 := by omega
theorem mlt (t : Nat) : t % 16 < 16 := Nat.mod_lt _ (by decide)

theorem cel0_tab : ∀ p, p < 16 → c0f ((p+1)%16) = c0f p ∨ c0f ((p+1)%16) = celN (rf p) (c1f p) (c0f p) := by decide
theorem cel1_tab : ∀ p, p < 16 → c1f ((p+1)%16) = c1f p ∨ c1f ((p+1)%16) = celN (c0f p) (af p) (c1f p) := by decide
theorem src_tab : ∀ p, p < 16 → (rf ((p+1)%16) ≠ rf p → rf p = c0f p) := by decide
theorem snk_tab : ∀ p, p < 16 → (af ((p+1)%16) ≠ af p → af p ≠ c1f p) := by decide

theorem stage0 : MullerStage 2 4 (ch 0) (ch 1) where
  H_NODE := fun _ => rfl
  H_RESET := by decide
  H_CEL_SI := by intro t; show C0 (t+1) = C0 t ∨ C0 (t+1) = celN (R t) (C1 t) (C0 t)
                 have := cel0_tab _ (mlt t); rw [← msucc] at this; exact this
  H_LATCH := by intro _ _ _ _ _ _; rfl

theorem stage1 : MullerStage 2 4 (ch 1) (ch 2) where
  H_NODE := fun _ => rfl
  H_RESET := by decide
  H_CEL_SI := by intro t; show C1 (t+1) = C1 t ∨ C1 (t+1) = celN (C0 t) (A t) (C1 t)
                 have := cel1_tab _ (mlt t); rw [← msucc] at this; exact this
  H_LATCH := by intro _ _ _ _ _ _; rfl

theorem stages : ∀ j, j < 2 → MullerStage 2 4 (ch j) (ch (j + 1)) := by
  intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl
  · exact stage0
  · exact stage1

theorem srcOK : ∀ t, SendStep (ch 0) t := by
  intro t; show R (t+1) ≠ R t → R t = C0 t
  have := src_tab _ (mlt t); rw [← msucc] at this; exact this

theorem snkOK : ∀ t, RecvStep (ch 2) t := by
  intro t; show A (t+1) ≠ A t → A t ≠ C1 t
  have := snk_tab _ (mlt t); rw [← msucc] at this; exact this

theorem c0_fall : ∀ e, fallB C0 e = true → e % 16 = 11 := by
  intro e h
  have key : ∀ p, p < 16 → (c0f p && !c0f ((p+1)%16)) = true → p = 11 := by decide
  apply key _ (mlt e); simpa [fallB, C0, msucc] using h

theorem c1_fall : ∀ e, fallB C1 e = true → e % 16 = 13 := by
  intro e h
  have key : ∀ p, p < 16 → (c1f p && !c1f ((p+1)%16)) = true → p = 13 := by decide
  apply key _ (mlt e); simpa [fallB, C1, msucc] using h

/-- Sep 2 on the internal link: a real (non-trivial, m = 2 > 1) separation. -/
theorem sepOK : Sep 2 (ch 0) (ch 1) := by
  intro e e' he he' hlt _
  have h1 := c0_fall e he; have h2 := c1_fall e' he'; omega

theorem holdOK : Hold 4 (ch 0) (ch 1) := by
  intro e' s he' h1 h2
  have h := c1_fall e' he'
  show c0f (s % 16) = false
  have : s % 16 = 14 ∨ s % 16 = 15 ∨ s % 16 = 0 ∨ s % 16 = 1 := by omega
  rcases this with h | h | h | h <;> rw [h] <;> decide

theorem shOK : SetupHold 2 4 (ch 0) := by intro _ _ _ _ _; rfl

/-- ALL hypotheses of `muller_pipeline` at n = 2 (internal link obligations live). -/
theorem nv_muller_pipeline :
    (∀ j, j ≤ 2 → Protocol (ch j)) ∧ (∀ t, cnt (fallB (ch 2).ack) t ≤ cnt (fallB (ch 0).ack) t) ∧
    (∀ k e', TokAt (ch 2) k e' → ∃ e, e < e' ∧ TokAt (ch 0) k e ∧ (ch 2).dat e' = (ch 0).dat e) :=
  muller_pipeline (m := 2) (h := 4) (n := 2) (ch := ch) stages (by decide) (by decide)
    (fun t _ => srcOK t) (fun t _ => snkOK t) shOK
    (fun j hj => by rw [show j = 0 by omega]; exact sepOK)
    (fun j hj => by rw [show j = 0 by omega]; exact holdOK) (by decide)

theorem inf_change (f : Nat → Bool) (k : Nat) (hk : k < 16) (h : f ((k+1)%16) ≠ f k) :
    ∀ t, ∃ s, t ≤ s ∧ f ((s+1)%16) ≠ f (s%16) := by
  intro t
  refine ⟨t + (16 - t % 16) + k, by omega, ?_⟩
  rw [show (t + (16 - t % 16) + k + 1) % 16 = (k+1) % 16 by omega,
      show (t + (16 - t % 16) + k) % 16 = k by omega]
  exact h

/-- ALL hypotheses of `muller_live` at n = 2; the conclusion follows. -/
theorem nv_muller_live :
    (∀ j, j ≤ 2 → ∀ T, ∃ t, T ≤ t ∧ (ch j).ack (t+1) ≠ (ch j).ack t) ∧
    (∀ K, ∃ t, K ≤ cnt (fallB (ch 2).ack) t) :=
  muller_live (m := 2) (h := 4) (n := 2) (ch := ch) stages (by decide) (by decide)
    (fun t _ => srcOK t) (fun t _ => snkOK t)
    (fun t _ => inf_change rf 1 (by decide) (by decide) t)
    (fun t _ => inf_change af 7 (by decide) (by decide) t)
    (by
      intro j hj t _
      have : j = 0 ∨ j = 1 := by omega
      rcases this with rfl | rfl
      · exact inf_change c0f 3 (by decide) (by decide) t
      · exact inf_change c1f 5 (by decide) (by decide) t)

/-! ## Dropping a liveness hypothesis breaks the conclusion -/

def Z : Trace := fun _ => false
def chZ : Nat → Chan := mkCh Z Z Z Z

theorem stZ : ∀ j, j < 2 → MullerStage 2 4 (chZ j) (chZ (j + 1)) := by
  intro j hj
  have : j = 0 ∨ j = 1 := by omega
  rcases this with rfl | rfl <;>
  exact { H_NODE := fun _ => rfl, H_RESET := rfl, H_CEL_SI := fun _ => Or.inl rfl,
          H_LATCH := by intro _ _ _ _ _ _; rfl }

/-- All-zero run: every hypothesis of muller_live except H_SRC_LIVE holds
(H_SNK_LIVE and H_CEL_FAIR vacuously), and the conclusion is false. -/
theorem drop_src_live :
    (∀ t, (chZ 2).ack t ≠ (chZ 2).req t → ∃ s, t ≤ s ∧ (chZ 2).ack (s+1) ≠ (chZ 2).ack s) ∧
    (∀ j, j < 2 → ∀ t, celN ((chZ j).req t) ((chZ (j+1)).ack t) ((chZ j).ack t) ≠ (chZ j).ack t →
      ∃ s, t ≤ s ∧ (chZ j).ack (s+1) ≠ (chZ j).ack s) ∧
    ¬ (∀ K, ∃ t, K ≤ cnt (fallB (chZ 2).ack) t) := by
  refine ⟨fun t h => absurd rfl h, fun j hj t h => ?_, fun h => ?_⟩
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;> simp [chZ, mkCh, Z, celN_eq] at h
  · obtain ⟨t, ht⟩ := h 1
    have : ∀ t, cnt (fallB Z) t = 0 := by
      intro t; induction t with
      | zero => rfl
      | succ t ih => simp [cnt, ih, fallB, Z]
    have e : cnt (fallB (chZ 2).ack) t = 0 := this t
    omega

/-- Source raises once and holds; C-element of stage 0 excited forever but never fires:
all hypotheses except H_CEL_FAIR hold, conclusion false. -/
def R1 : Trace := fun t => decide (1 ≤ t)
def chS : Nat → Chan := mkCh R1 Z Z Z
theorem drop_cel_fair :
    (∀ j, j < 2 → MullerStage 2 4 (chS j) (chS (j + 1))) ∧
    (∀ t, SendStep (chS 0) t) ∧ (∀ t, RecvStep (chS 2) t) ∧
    (∀ t, (chS 0).req t = (chS 0).ack t → ∃ s, t ≤ s ∧ (chS 0).req (s+1) ≠ (chS 0).req s) ∧
    (∀ t, (chS 2).ack t ≠ (chS 2).req t → ∃ s, t ≤ s ∧ (chS 2).ack (s+1) ≠ (chS 2).ack s) ∧
    ¬ (∀ T, ∃ t, T ≤ t ∧ (chS 0).ack (t+1) ≠ (chS 0).ack t) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl <;>
    exact { H_NODE := fun _ => rfl, H_RESET := rfl, H_CEL_SI := fun _ => Or.inl rfl,
            H_LATCH := by intro _ _ _ _ _ _; rfl }
  · intro t h
    show R1 t = Z t
    cases t with
    | zero => rfl
    | succ t => exfalso; apply h; show R1 (t+1+1) = R1 (t+1); simp [R1]
  · intro t h; exact absurd rfl h
  · intro t h
    cases t with
    | zero => exact ⟨0, Nat.le_refl _, by decide⟩
    | succ t => exact absurd h (by show R1 (t+1) ≠ Z (t+1); simp [R1, Z])
  · intro t h; exact absurd rfl h
  · intro h; obtain ⟨t, _, ht⟩ := h 0; exact ht rfl

/-- ...and that stalled run really has stage 0's C-element excited (so H_CEL_FAIR fails). -/
example : celN ((chS 0).req 5) ((chS 1).ack 5) ((chS 0).ack 5) ≠ (chS 0).ack 5 := by decide

#print axioms nv_muller_pipeline
#print axioms nv_muller_live
#print axioms drop_src_live
#print axioms drop_cel_fair
#print axioms muller_pipeline
#print axioms muller_live
#print axioms pipeline_fifo
#print axioms Formal.Net.Handshake.Witness.witness

end Audit.C.HS
