import Formal.Cells.PipeTimedN

/-!
# Audit P3: PipeTimedN non-vacuity, re-examined

1. `unit_tie`: in the shipped unit-delay witness `Wit.Pw N`, at every stage and
   every phase the request and the acknowledge reach the controller at the SAME
   tick (`Rin i j = Ain i j`). The C-element (bd_c2n = C(req, !ack)) therefore
   never sees its inputs disagree, so it never holds through its feedback:
   its excitation equals `req` at every instant (`unit_never_holds`).
   Shipped witness = degenerate tie run.

2. `Aud.witness_g`: an independent control-side witness for EVERY `N >= 1` with
   non-unit, UNEQUAL delays (LUT 2, request line 3, DACK 1, feedback 1,
   half-period 12, reset 6, Es = Er = 6). Request-dominated phases (ack
   arrives 4 ticks earlier), so the C-element HOLDS on [o+8, o+12) of each
   half period (`hold_exercised`). It satisfies GatesN, EnvN, TimingN jointly,
   and `pipe_ctl`/`nodes_clean`/`live` are applied to it.
-/

namespace Audit.P3
open Formal.Cells Formal.Cells.PipeTimed Formal.Cells.PipeTimedN

/-! ### 1. the shipped witness is a tie run -/

theorem unit_tie (N i j : Nat) (hi : i + 1 < N) (hi0 : 0 < i) :
    (Wit.Pw N).Rin i (j + 1) = (Wit.Pw N).Ain i (j + 1) := by
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  rw [PN.Ain_in _ _ _ hi]
  show (Ret.shift 1).fst ((Wit.Pw N).τ i' (j + 1)) = _
  rw [Wit.τ_w, Wit.τ_w, Wit.ackT_w _ _ _ _ (by omega), Wit.fst1 _ (by omega)]
  omega

/-- In the unit witness, `!ack = req` at every instant from reset on, so the
bd_c2n excitation never depends on the feedback pin. -/
theorem unit_never_holds (i t : Nat) (h1 : 4 + 2 * i ≤ t) :
    Wit.aW i t = !(Wit.rW i t) := by
  unfold Wit.aW Wit.rW PipeTimed.Wit.sq
  · by_cases h2 : 8 + 2 * i ≤ t
    · by_cases h3 : (t - (8 + 2 * i)) % 8 < 4
      · have : ¬ ((t - (4 + 2 * i)) % 8 < 4) := by omega
        simp [h1, h2, h3, this]
      · have : (t - (4 + 2 * i)) % 8 < 4 := by omega
        simp [h1, h2, h3, this]
    · have : (t - (4 + 2 * i)) % 8 < 4 := by omega
      simp [h1, h2, this]

/-! ### 2. an independent non-unit, non-tie witness -/

namespace Aud

def sqP (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 24 < 12)
def rst6 (t : Nat) : Bool := decide (t < 6)

theorem sqP_shift (o d t : Nat) : sqP (o + d) (t + d) = sqP o t := by
  unfold sqP
  have e : t + d - (o + d) = t - o := by omega
  rw [e]
  by_cases h : o ≤ t
  · simp [h, show o + d ≤ t + d by omega]
  · simp [h, show ¬ (o + d ≤ t + d) by omega]

theorem sqP_sub (o d t : Nat) (ht : d ≤ t) : sqP (o + d) t = sqP o (t - d) := by
  have := sqP_shift o d (t - d); rwa [Nat.sub_add_cancel ht] at this

/-- The real bd_c2n excitation on the generalized waves: req offset `o`,
ack offset `o + 8`, feedback offset `o + 3`, reset low from 6. -/
theorem keyG (o s : Nat) (ho : 6 ≤ o) :
    ex (sqP o) (sqP (o + 8)) (sqP (o + 3)) rst6 s = sqP o s := by
  unfold ex rst6
  rw [CElemTiming.c2n_eq]
  unfold sqP
  by_cases h0 : o ≤ s
  · have hr : ¬ (s < 6) := by omega
    by_cases hA : (s - o) % 24 < 8
    · have e2 : ¬ (o + 8 ≤ s ∧ (s - (o + 8)) % 24 < 12) := by omega
      simp [hr, h0, e2, show (s - o) % 24 < 12 by omega]
    · by_cases hB : (s - o) % 24 < 12
      · have e2 : (o + 8 ≤ s ∧ (s - (o + 8)) % 24 < 12) := by omega
        have e3 : (o + 3 ≤ s ∧ (s - (o + 3)) % 24 < 12) := by omega
        simp [hr, h0, hB, e2, e3]
      · by_cases hC : (s - o) % 24 < 20
        · have e2 : (o + 8 ≤ s ∧ (s - (o + 8)) % 24 < 12) := by omega
          simp [hr, h0, hB, e2]
        · have e2 : ¬ (o + 8 ≤ s ∧ (s - (o + 8)) % 24 < 12) := by omega
          have e3 : ¬ (o + 3 ≤ s ∧ (s - (o + 3)) % 24 < 12) := by omega
          simp [hr, h0, hB, e2, e3]
  · have e2 : ¬ (o + 8 ≤ s) := by omega
    have e3 : ¬ (o + 3 ≤ s) := by omega
    simp [h0, e2, e3]

/-- The hold state IS exercised: on `[o+8, o+12)` req = 1 and ack = 1, so
`C(req, !ack)` has disagreeing inputs and the output comes from the feedback. -/
theorem hold_exercised (o : Nat) :
    sqP o (o + 9) = true ∧ sqP (o + 8) (o + 9) = true ∧ sqP (o + 3) (o + 9) = true := by
  unfold sqP; simp

def Pg (N : Nat) : PN where
  N := N
  R := 6
  L _ := Ret.shift 2
  Rq _ := Ret.shift 3
  m _ := 0
  Ap _ _ := Ret.shift 1
  Ag _ := 1
  ρ j := 6 + 12 * j
  γ j := 14 + 5 * (N - 1) + 12 * j

theorem fs (d c : Nat) (h : 1 ≤ c) : (Ret.shift d).fst c = c + d := Ret.fst_shift d c h

theorem ackT_g (N b j τ : Nat) (h : 1 ≤ τ) : (Pg N).ackT b j τ = τ + 1 := by
  show (if j % 2 = 0 then (Ret.shift 1).fst τ else (Ret.shift 1).fst τ) = _
  rw [fs 1 τ h]; split <;> rfl

theorem row_g (N j : Nat) (α : Nat → Nat) (hα : ∀ i, α i ≤ 6 + 5 * i + 12 * j) :
    ∀ i, (Pg N).row j α i = 6 + 5 * i + 12 * j := by
  intro i
  induction i with
  | zero => show max (6 + 12 * j) (α 0) = _; have := hα 0; omega
  | succ i ih =>
    show max ((Ret.shift 3).fst ((Ret.shift 2).fst ((Pg N).row j α i))) (α (i + 1)) = _
    rw [ih, fs 2 _ (by omega), fs 3 _ (by omega)]
    have := hα (i + 1); omega

theorem cc_g (N : Nat) (hN : 1 ≤ N) : ∀ j i, (Pg N).cc j i = 6 + 5 * i + 12 * j := by
  intro j
  induction j with
  | zero => exact row_g N 0 (fun _ => 6) (fun i => by omega)
  | succ j ih =>
    apply row_g
    intro i
    show (if i + 1 < N then (Pg N).ackT (i + 1) j ((Ret.shift 2).fst ((Pg N).cc j (i + 1)))
      else 14 + 5 * (N - 1) + 12 * j) ≤ _
    split
    · rw [ih, fs 2 _ (by omega), ackT_g N _ _ _ (by omega)]; omega
    · omega

theorem τ_g (N : Nat) (hN : 1 ≤ N) (i j : Nat) : (Pg N).τ i j = 8 + 5 * i + 12 * j := by
  show (Ret.shift 2).fst ((Pg N).cc j i) = _
  rw [cc_g N hN, fs 2 _ (by omega)]; omega

/-- Not a tie: inside the pipe the acknowledge arrives 4 ticks BEFORE the request. -/
theorem no_tie (N i j : Nat) (hN : 1 ≤ N) (hi : i + 1 < N) :
    (Pg N).Ain i (j + 1) + 4 = (Pg N).Rin (i + 1) (j + 1) - 5 := by
  rw [PN.Ain_in _ _ _ hi]
  show (Pg N).ackT (i + 1) j ((Pg N).τ (i + 1) j) + 4 = (Ret.shift 3).fst ((Pg N).τ i (j + 1)) - 5
  rw [τ_g N hN, τ_g N hN, ackT_g _ _ _ _ (by omega), fs 3 _ (by omega)]; omega

def rG (i : Nat) : Trace := sqP (6 + 5 * i)
def OG (i : Nat) : Trace := sqP (8 + 5 * i)
def qG (i : Nat) : Trace := sqP (9 + 5 * i)
def aG (i : Nat) : Trace := sqP (14 + 5 * i)

theorem sqP_phase (o j t : Nat) (h1 : o + 12 * j ≤ t) (h2 : t < o + 12 * (j + 1)) :
    sqP o t = Vph j := by
  unfold sqP Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 24 < 12 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 24 < 12) := by omega
    simp [hj, this]

theorem gates_g (N : Nat) : GatesN (Pg N) rst6 rG aG OG qG (fun _ => 1) (fun _ => 1) where
  H_RST _ := rfl
  H_CTL i _ := {
    H_LUT_FIFO := fun t ht => by
      show sqP (8 + 5 * i) t = ex (sqP (6 + 5 * i)) (sqP (14 + 5 * i)) (sqP (9 + 5 * i)) rst6 (t - 2)
      have k := keyG (6 + 5 * i) (t - 2) (by omega)
      rw [show 6 + 5 * i + 8 = 14 + 5 * i by omega, show 6 + 5 * i + 3 = 9 + 5 * i by omega] at k
      rw [k, show 8 + 5 * i = 6 + 5 * i + 2 by omega]
      exact sqP_sub _ 2 t (by simpa [Pg, Ret.shift] using ht)
    H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
      (fun t => by
        show sqP (9 + 5 * i) (t + 1) = sqP (8 + 5 * i) t
        rw [show 9 + 5 * i = 8 + 5 * i + 1 by omega]; exact sqP_shift _ 1 t)
    H_LOOP_POS := by show 1 ≤ 2 + 1; decide }
  H_REQ_LINE i _ t ht := by
    show sqP (6 + 5 * (i + 1)) t = sqP (8 + 5 * i) (t - 3)
    rw [show 6 + 5 * (i + 1) = 8 + 5 * i + 3 by omega]
    exact sqP_sub _ 3 t (by simpa [Pg, Ret.shift] using ht)
  H_ACK_LINE i _ t ht := by
    show sqP (14 + 5 * i) t = sqP (8 + 5 * (i + 1)) (t - 1)
    rw [show 14 + 5 * i = 8 + 5 * (i + 1) + 1 by omega]
    exact sqP_sub _ 1 t (by simpa [Pg] using ht)

theorem env_g (N : Nat) (hN : 1 ≤ N) : EnvN (Pg N) (rG 0) (aG ((Pg N).N - 1)) 6 6 where
  H_REQ_LOW0 t h1 h2 := by simp only [Pg] at h1 h2; omega
  H_REQ j t h1 h2 := sqP_phase 6 j t (by simpa [Pg] using h1) (by simp only [Pg] at h2; omega)
  H_ACK_LOW0 t h1 h2 := by
    show sqP (14 + 5 * (N - 1)) t = false
    unfold sqP; simp only [Pg] at h2; simp; omega
  H_ACK j t h1 h2 := by
    show sqP (14 + 5 * (N - 1)) t = Vph j
    exact sqP_phase _ j t (by simp only [Pg] at h1; omega) (by simp only [Pg] at h2; omega)
  H_SND j := by rw [τ_g N hN]; show 8 + 5 * 0 + 12 * j + 6 ≤ 6 + 12 * (j + 1); omega
  H_RCV j := by rw [τ_g N hN]; show 8 + 5 * (N - 1) + 12 * j + 6 ≤ 14 + 5 * (N - 1) + 12 * j; omega
  H_RST_EARLY := by show 6 ≤ 6 + 12 * 0; omega

theorem ER_g (N i : Nat) : (Pg N).ER 6 i = 6 := by cases i <;> rfl
theorem EA_g (N i : Nat) : (Pg N).EA 6 i = 6 := by unfold PN.EA; split <;> rfl

theorem timing_g (N : Nat) (hN : 1 ≤ N) : TimingN (Pg N) (fun _ => 1) 6 6 where
  H_N_POS := hN
  H_R_POS := by show 1 ≤ 6; decide
  H_RST_LONG _ _ := by show 2 + 1 ≤ 6; decide
  H_RST_LINES _ _ := by show 2 + 3 ≤ 6 ∧ 2 + 1 ≤ 6 ∧ 1 ≤ 6; decide
  H_LAT i _ := by rw [ER_g, EA_g]; show 2 + 1 ≤ 2 + min 6 6; decide
  H_ACK_FLUSH i _ := by rw [ER_g, EA_g]; show 1 ≤ 2 + max 6 6 + 1; decide

/-- Joint non-vacuity with non-unit, unequal delays, every N >= 1, and the
headline theorems applied to it. -/
theorem witness_g (N : Nat) (hN : 1 ≤ N) :
    GatesN (Pg N) rst6 rG aG OG qG (fun _ => 1) (fun _ => 1) ∧
    EnvN (Pg N) (rG 0) (aG ((Pg N).N - 1)) 6 6 ∧ TimingN (Pg N) (fun _ => 1) 6 6 ∧
    (∀ i, i < N → ∀ j t, (Pg N).τ i j ≤ t → t < (Pg N).τ i (j + 1) → OG i t = Vph j) ∧
    (∀ i j, i < N → (Pg N).τ i j < (Pg N).τ i (j + 1)) := by
  refine ⟨gates_g N, env_g N hN, timing_g N hN, fun i hi => ?_, fun i j hi => ?_⟩
  · exact (nodes_clean (gates_g N) (env_g N hN) (timing_g N hN) i hi).2
  · exact live (env_g N hN) (timing_g N hN) i j hi (by show 1 ≤ 2 + 1; decide)

end Aud
end Audit.P3

#print axioms Audit.P3.unit_tie
#print axioms Audit.P3.Aud.witness_g
#print axioms Audit.P3.Aud.no_tie
#print axioms Formal.Cells.PipeTimedN.pipe_ctl
#print axioms Formal.Cells.PipeTimedN.nodes_clean
#print axioms Formal.Cells.PipeTimedN.pins_clean
#print axioms Formal.Cells.PipeTimedN.live
#print axioms Formal.Cells.PipeTimedN.token
#print axioms Formal.Cells.PipeTimedN.pipe_forward
#print axioms Formal.Cells.PipeTimedN.fastrise_or
#print axioms Formal.Cells.PipeTimedN.Wit.witness
#print axioms Formal.Cells.PipeTimedN.Wit.witness_data
#print axioms Formal.Cells.PipeTimedN.Wit.chain_w
