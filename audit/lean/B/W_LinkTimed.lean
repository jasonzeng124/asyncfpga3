import Formal.Cells.LinkTimed
/-! Audit (shard B): non-vacuity of LinkTimed's stage contract (CtlEnv + DataPath).
A concrete periodic run (period 8 ps) of the real bd_c2n controller with dl = 1,
dw = 0, E = 1, and a one-bit latch whose token value ALTERNATES 1,0,1,0,... -/
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
open Formal.Cells Formal.Cells.LinkTimed

namespace AuditB.LT

def req : Trace := fun t => decide (t % 8 = 2 ∨ t % 8 = 3)
def ack : Trace := fun t => decide (t % 8 = 4 ∨ t % 8 = 5)
def O : Trace := fun t => decide (t % 8 = 3 ∨ t % 8 = 4)
def rst : Trace := fun t => decide (t = 0)
def ρ : Nat → Nat := fun k => 8 * k + 2
def φ : Nat → Nat := fun k => 8 * k + 4
def α : Nat → Nat := fun k => 8 * k + 4
def β : Nat → Nat := fun k => 8 * k + 6

theorem lut_step (s : Nat) :
    O (s + 1) = CElemTiming.exc CElemTiming.INIT_c2n (req s) (ack s) (O s) (rst s) := by
  rw [CElemTiming.c2n_eq]
  have h' : (s + 1) % 8 = (s % 8 + 1) % 8 := by omega
  have hr : rst s = true → s % 8 = 0 := by simp [rst]; omega
  simp only [O, req, ack, h']
  have h8 : s % 8 = 0 ∨ s % 8 = 1 ∨ s % 8 = 2 ∨ s % 8 = 3 ∨ s % 8 = 4 ∨ s % 8 = 5 ∨
      s % 8 = 6 ∨ s % 8 = 7 := by omega
  rcases h8 with h | h | h | h | h | h | h | h <;>
  · rw [h]
    cases hrs : rst s
    · simp
    · have := hr hrs; simp_all

theorem loop : CElemTiming.Loop CElemTiming.INIT_c2n req ack rst O O 1 1 0 0 where
  H_LUT := by
    intro t ht
    refine ⟨t - 1, by omega, by omega, ?_⟩
    have := lut_step (t - 1)
    rwa [show t - 1 + 1 = t by omega] at this
  H_FB := by intro t _; exact ⟨t, by omega, by omega, rfl⟩
  H_LOOP_POS := by decide

theorem cph_even (k : Nat) : cph ρ φ α β (2 * k) = 8 * k + 2 := by
  rw [cph_e]; cases k with
  | zero => simp [ρ, pb]
  | succ k => simp [ρ, pb, β]; omega

theorem cph_odd (k : Nat) : cph ρ φ α β (2 * k + 1) = 8 * k + 4 := by
  rw [cph_o]; simp [φ, α]

theorem ctlEnv : CtlEnv req ack rst O O ρ φ α β 1 1 0 0 1 0 where
  H_CTL := loop
  H_REQ_LOW0 := by intro t h; simp [req, ρ] at *; omega
  H_REQ_HIGH := by intro k t h1 h2; simp [req, ρ, φ] at *; omega
  H_REQ_LOW := by intro k t h1 h2; simp [req, ρ, φ] at *; omega
  H_ACK_LOW0 := by intro t h; simp [ack, α] at *; omega
  H_ACK_HIGH := by intro k t h1 h2; simp [ack, α, β] at *; omega
  H_ACK_LOW := by intro k t h1 h2; simp [ack, α, β] at *; omega
  H_SND_FALL := by
    intro k; refine ⟨8 * k + 3, by rw [cph_even]; omega, by simp [φ], ?_⟩; simp [O]
  H_RCV_RISE := by
    intro k; refine ⟨8 * k + 3, by rw [cph_even]; omega, by simp [α], ?_⟩; simp [O]
  H_SND_RISE := by
    intro k; refine ⟨8 * k + 5, by rw [cph_odd]; omega, by simp [ρ]; omega, ?_⟩; simp [O]
  H_RCV_FALL := by
    intro k; refine ⟨8 * k + 5, by rw [cph_odd]; omega, by simp [β], ?_⟩; simp [O]
  H_ENV_POS := by decide
  H_ENV_LATENCY := by decide
  H_RST_PULSE := by intro s h1 h2; simp [rst]; omega
  H_RST_OFF := by intro s h; simp [rst]; omega
  H_RST_EARLY := by decide

/-! ### the data path: one bit, alternating tokens -/

def val : Nat → Nat → Bool := fun k _ => decide (k % 2 = 0)
def dd : Nat → Bundling.Sig := fun _ t => decide ((t / 8) % 2 = 0)
def qq : Nat → Bundling.Sig := fun _ t => decide (((t + 5) / 8) % 2 = 1)
def dS : Nat → Nat := fun k => 8 * k
def dE : Nat → Nat := fun k => 8 * k + 8

theorem q_transport : Bundling.Transport Bundling.ODD [(dd 0, 0), (O, 0), (qq 0, 1),
    (Bundling.zero, 0), (Bundling.zero, 0), (Bundling.zero, 0)] (qq 0) := by
  intro t
  show qq 0 t = lutB Bundling.ODD [dd 0 (t - 0), O (t - 0), qq 0 (t - 1), false, false, false]
  rw [Bundling.odd_bin]
  simp only [qq, dd, O, Nat.sub_zero]
  have h8 : t % 8 = 0 ∨ t % 8 = 1 ∨ t % 8 = 2 ∨ t % 8 = 3 ∨ t % 8 = 4 ∨ t % 8 = 5 ∨
      t % 8 = 6 ∨ t % 8 = 7 := by omega
  by_cases ht : t = 0
  · subst ht; decide
  rcases h8 with h | h | h | h | h | h | h | h <;>
  · simp only [h]
    simp only [decide_eq_decide, Bool.decide_or, Bool.or_eq_true, decide_eq_true_eq]
    split <;> simp_all <;> omega

theorem latch_rel : Bundling.LatchRel (dd 0) O (qq 0) 0 0 0 0 1 1 :=
  Bundling.odd_latch (Bundling.transport_gate Bundling.ODD
    [(dd 0, 0, 0, 0), (O, 0, 0, 0), (qq 0, 1, 1, 1),
      (Bundling.zero, 0, 0, 0), (Bundling.zero, 0, 0, 0), (Bundling.zero, 0, 0, 0)] (qq 0)
    (by simp) q_transport)

theorem dataPath : DataPath O dd qq val dS dE (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 1) (fun _ => 1) 1 ρ φ α β 1 1 1 1 0 0 where
  H_LATCH := by intro i hi; have : i = 0 := by omega
                subst this; exact latch_rel
  H_WIN := by intro i _; exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩
  H_LATCH_LOOP_POS := by intro i _; exact Nat.le_refl _
  H_DATA_VALID := by intro k i t _ h1 h2; simp [dd, val, dS, dE] at *; omega
  H_DATA_LEAD := by intro k; simp [dS, ρ]
  H_DATA_REL := by
    intro k; refine ⟨8 * k + 5, by rw [cph_odd]; omega, by simp [dE], ?_⟩; simp [O]
  H_PULSE_WIDTH := by intro i _; decide
  H_DATA_SETUP := by intro i _; decide
  H_RULE_H := by intro i _; decide

/-- `stage_token` is thereby instantiated on a run where the token value
alternates, so its conclusion is not a constant-trace triviality. -/
theorem token_alternates (k : Nat) :
    qq 0 (8 * k + 3) = decide (k % 2 = 0) := by
  have := stage_token ctlEnv dataPath k 0 (by decide) (8 * k + 3)
    (by rw [cph_even]; simp [dS])
    (by rw [show 2 * k + 1 + 1 = 2 * (k + 1) by omega, cph_even]; omega)
  rw [this]; rfl

end AuditB.LT
