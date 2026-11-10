import Formal.Target.AssemblyPS
import Formal.Net.CViewPS.IslandPS

/-!
# Formal.Target.PlanPS — THE statement on THE target from ONE per-pair step (shard A, 2026-11-10)

**Problem, plainly.** `AssemblyPS.the_of_plan` reduces THE statement (`NetCorrectSeq` on the decoded gcd_ps
netlist) to a `Plan` per behaviour: an invariant `I`, a base (`I` holds at the end of reset with the circuit's
boundary outputs low), a quiet clause (while no pair is offered, the outputs stay low and `I` is kept), and a
step (from `I`, low, and a rising pair request, one whole pair episode -- acknowledges, one `out0` handshake
carrying the gcd, back to low and to `I`). Base and quiet are about the idle circuit, not about computing gcd.

**Proved here** (`the_of_step`): base and quiet hold for THE target with `I` = the *idle island* (shard C's 414
nodes, `CViewPS.memI`, which include `a.ack`, `b.ack`, `start.ack`, `out0.req`) low, together with the shared
input request and `end.ack`, over the last `M` ps (`Isl`), plus any extra invariant `J` the step's prover wants
that is true at reset end and kept by quiet steps. So THE statement follows from:
* the island's delay conditions for `p` (the same four as C's `correct_n0`: island starts and reset arrivals at
  most `A`, island pin delays at most `M`, forcing pins at least 1 ps, `A + 87·M + 1 ≤ R`); and
* **one per-pair hypothesis** (`StepHyp`): from any time `t ≥ R` at which the island has been low for `M` ps and
  `J` holds, a rising request is followed by one complete pair episode (`Assembly.StepCore`) that ends with the
  island low for `M` ps and `J` again.
Whatever the 4,185 unreset data latches and 9 arbiter states hold is left free by `Isl`: the step must work from
any of them (or the prover puts what it needs in `J`).

**Not shown.** `StepHyp` itself (the per-pair circuit argument: C's S4 instance for every pair); the delay
conditions for a concrete `p`. This file removes from THE statement's open list the base and the quiet clause of
the plan and the choice of invariant, nothing else.
-/

namespace Formal.Target.PlanPS
open Formal.Target Formal.Target.Assembly Formal.Target.DecodedPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman
  Formal.Timing.SpecLoop Formal.Timing.Island Formal.Net.CViewPS

/-! ## The island kept on a bounded interval (C's `island_forever`, with the environment bounded) -/

theorem island_upto {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (mem envm : Nat → Prop) (gate : Nat → Gate) (src : Nat → Nat → Nat)
    (arcs : Nat → Nat → List Arc) (S : Nat → Nat) (M T U : Nat) (val : Nat → Bool)
    (ps : Nat → List Nat)
    (hg : ∀ w, mem w → (gate w).out = w ∧ CGateOK p c (gate w) (src w) (arcs w) (S w) x)
    (hord : ∀ w, mem w → ∀ i, i < (gate w).k → ArcsOrd (arcs w i))
    (hF : ∀ w, mem w → ForcesP (gate w).k (gate w).init (asgOf src val w (ps w)) (val w) = true)
    (hps : ∀ w, mem w → ∀ j ∈ ps w, j < (gate w).k ∧ (mem (src w j) ∨ envm (src w j)) ∧
      1 ≤ sumMin p (arcs w j) ∧ sumMax p (arcs w j) ≤ M)
    (hS : ∀ w, mem w → S w ≤ T - M)
    (henv : ∀ e, envm e → ∀ t, T - M ≤ t → t ≤ U → x e t = val e)
    (hbase : ∀ w, mem w → ∀ t, T - M ≤ t → t ≤ T → x w t = val w) :
    ∀ w, mem w → ∀ t, T - M ≤ t → t ≤ U → x w t = val w := by
  intro w hw t
  induction t using Nat.strong_induction_on generalizing w with
  | _ t ih =>
    intro ht htU
    by_cases htT : t ≤ T
    · exact hbase w hw t ht htT
    obtain ⟨hout, F, -, hFt⟩ := hg w hw
    obtain ⟨hrd, ho⟩ := hFt t (by have := hS w hw; omega)
    suffices hv : ∀ e ∈ asgOf src val w (ps w), e.1 < (gate w).k ∧ x (src w e.1) (F e.1 t) = e.2 by
      have := forcesP_sound (hF w hw) (fun i => x (src w i) (F i t)) hv
      rw [hout] at ho; rw [ho]; exact this
    intro e he
    simp only [asgOf, List.mem_map] at he
    obtain ⟨j, hj, rfl⟩ := he
    dsimp only
    obtain ⟨hjk, hsrc, hmin, hmax⟩ := hps w hw j hj
    refine ⟨hjk, ?_⟩
    obtain ⟨r1, r2⟩ := hrd j hjk
    obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord w hw j hjk) r2
    rcases hsrc with hm | he'
    · exact ih _ (by omega) _ hm (by omega) (by omega)
    · exact henv _ he' _ (by omega) (by omega)

/-- The island's delay conditions for `p` (as in C's `correct_n0`). -/
structure IslDelay (p : DelayPar) (M A : Nat) : Prop where
  hS : ∀ w, memI w = true → startPS p w ≤ A
  hM : ∀ w, memI w = true → ∀ i, i < (gAt cs 2500 w).k → sumMax p (arcsPS w i) ≤ M
  hmin : ∀ w, memI w = true → ∀ j ∈ psI w, 1 ≤ sumMin p (arcsPS w j)
  hrs : ∀ r ∈ resetList, memI r.1 = true → sumMax p (arcsPS r.1 r.2.1) ≤ A

/-- **Reset, with the environment bounded:** C's `island_PS` with the shared request and `end.ack` low only on
`[0, U]` (`R - 1 ≤ U`); the island is low on `[R - 1 - M, U]`. Same proof, `island_upto` in place of
`island_forever`. -/
theorem island_reset_upto {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {R M A U : Nat} (hd : IslDelay p M A) (hR : ∀ t, t < R → x rstPS t = true) (hR0 : 0 < R)
    (hRU : R - 1 ≤ U) (hreq : ∀ t, t ≤ U → x 186985 t = false) (hpa : ∀ t, t ≤ U → x 104477 t = false)
    (hRA : A + 87 * M ≤ R - 1) :
    ∀ w, memI w = true → ∀ t, R - 1 - M ≤ t → t ≤ U → x w t = false := by
  obtain ⟨hS, hM, hmin, hrs⟩ := hd
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  have hgate : ∀ w, memI w = true → (gAt cs 2500 w).out = w ∧
      CGateOK p c (gAt cs 2500 w) (srcPS w) (arcsPS w) (startPS p w) x := fun w hw =>
    ⟨gAt_out_logic (entry_facts hw).1, hall _ (mem_view_logic (entry_facts hw).1)⟩
  have hordI : ∀ w, memI w = true → ∀ i, i < (gAt cs 2500 w).k → ArcsOrd (arcsPS w i) :=
    fun w hw => ord_logic (entry_facts hw).1
  have henv : ∀ e, envI e = true → ∀ t, t ≤ U → x e t = valI e := by
    intro e he t ht
    simp only [envI, Bool.or_eq_true, beq_iff_eq] at he
    rcases he with rfl | rfl
    · exact hreq t ht
    · exact hpa t ht
  have hstor : ∀ w, memI w = true → storI w = true → ∀ t, A ≤ t → t ≤ R - 1 → x w t = valI w := by
    intro w hw hs t h1 h2
    obtain ⟨r, hr, h1r, h2r⟩ := (entry_facts hw).2.2.2.1 hs
    have hok2 := List.all_eq_true.mp resetList_ok r hr
    simp only [resetOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok2
    obtain ⟨⟨⟨hl, hj⟩, hsrc⟩, hF⟩ := hok2
    have hwl := logicPS_of_B hl
    have hsA := hS w hw
    have hrA := hrs r hr (by rw [h1r]; exact hw)
    subst h1r
    have k := cgate_force_pin hp hc0 hc1 (ord_logic hwl) (hall _ (mem_view_logic hwl)) hj true r.2.2 hF 0 (R - 1)
      (fun t' _ b => by
        show x (srcPS r.1 r.2.1) t' = true
        rw [hsrc]; exact hR t' (by omega)) t (by dsimp only; simp only [startPS, pcsPS] at hsA; omega)
      (by simp only [arcsPS, pcsPS] at hrA ⊢; omega) (by omega)
    rw [gAt_out_logic hwl, h2r] at k
    exact k
  have hcomb := settle_partial hp hc0 hc1 (fun w => memI w = true ∧ storI w = false)
    (fun r => (memI r = true ∧ storI r = true) ∨ envI r = true) (fun w => (rkPS w).getD 0)
    (gAt cs 2500) srcPS arcsPS (startPS p) M A (R - 1) valI psI
    (fun w hw => hgate w hw.1) (fun w hw => hordI w hw.1) (fun w hw => (entry_facts hw.1).2.2.1)
    (by
      intro w hw j hj
      obtain ⟨hjk, hsrc⟩ := (entry_facts hw.1).2.1 j hj
      refine ⟨hjk, ?_⟩
      rcases hsrc with hm | he
      · rcases Bool.eq_false_or_eq_true (storI (srcPS w j)) with hst | hst
        · exact Or.inl (Or.inl ⟨hm, hst⟩)
        · exact Or.inr ⟨⟨hm, hst⟩, ((entry_facts hw.1).2.2.2.2 hw.2).2 j hj hm hst⟩
      · exact Or.inl (Or.inr he))
    (fun w hw => hM w hw.1) (fun w hw => hS w hw.1)
    (by
      intro r hr t h1 h2
      rcases hr with ⟨hm, hs⟩ | he
      · exact hstor r hm hs t h1 h2
      · exact henv r he t (by omega))
  have hfin := island_upto hp hc0 hc1 (fun w => memI w = true) (fun e => envI e = true) (gAt cs 2500) srcPS
    arcsPS (startPS p) M (R - 1) U valI psI hgate hordI (fun w hw => (entry_facts hw).2.2.1)
    (by
      intro w hw j hj
      obtain ⟨hjk, hsrc⟩ := (entry_facts hw).2.1 j hj
      exact ⟨hjk, hsrc, hmin w hw j hj, hM w hw j hjk⟩)
    (fun w hw => by have := hS w hw; omega)
    (fun e he t _ ht => henv e he t ht)
    (by
      intro w hw t h1 h2
      rcases Bool.eq_false_or_eq_true (storI w) with hst | hst
      · exact hstor w hw hst t (by omega) h2
      · have hr := ((entry_facts hw).2.2.2.2 hst).1
        have hmul : ((rkPS w).getD 0 + 1) * M ≤ 86 * M := Nat.mul_le_mul_right M (by omega)
        exact hcomb w ⟨hw, hst⟩ t (by omega) h2)
  exact hfin

/-! ## The invariant and the plan -/

/-- **The idle island over the last `M` ps**: on `[t - M, t]`, every island member, the shared input request and
`end.ack` are low. -/
def Isl (x : Beh) (M t : Nat) : Prop :=
  ∀ s, t - M ≤ s → s ≤ t → (∀ w, memI w = true → x w s = false) ∧ x 186985 s = false ∧ x 104477 s = false

theorem mem4 : memI 104576 = true ∧ memI 104695 = true ∧ memI 147972 = true ∧ memI 160957 = true := by
  decide +kernel

/-- **Quiet step of the island**: if the island and the two environment nodes have been low on `[t - M, t]`, the
environment nodes stay low at `t + 1`, and every island start is at most `t - M`, the island is low at `t + 1`. -/
theorem isl_next {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {M A t : Nat} (hd : IslDelay p M A) (hAt : A ≤ t - M) (hI : Isl x M t)
    (hq : x 186985 (t + 1) = false) (hpa : x 104477 (t + 1) = false) : Isl x M (t + 1) := by
  obtain ⟨hS, hM, hmin, -⟩ := hd
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  have hgate : ∀ w, memI w = true → (gAt cs 2500 w).out = w ∧
      CGateOK p c (gAt cs 2500 w) (srcPS w) (arcsPS w) (startPS p w) x := fun w hw =>
    ⟨gAt_out_logic (entry_facts hw).1, hall _ (mem_view_logic (entry_facts hw).1)⟩
  have henv : ∀ e, envI e = true → ∀ s, t - M ≤ s → s ≤ t + 1 → x e s = valI e := by
    intro e he s h1 h2
    simp only [envI, Bool.or_eq_true, beq_iff_eq] at he
    rcases Nat.lt_or_ge s (t + 1) with hs | hs
    · rcases he with rfl | rfl
      · exact (hI s h1 (by omega)).2.1
      · exact (hI s h1 (by omega)).2.2
    · have : s = t + 1 := by omega
      subst this
      rcases he with rfl | rfl
      · exact hq
      · exact hpa
  have hfin := island_upto hp hc0 hc1 (fun w => memI w = true) (fun e => envI e = true) (gAt cs 2500) srcPS
    arcsPS (startPS p) M t (t + 1) valI psI hgate (fun w hw => ord_logic (entry_facts hw).1)
    (fun w hw => (entry_facts hw).2.2.1)
    (by
      intro w hw j hj
      obtain ⟨hjk, hsrc⟩ := (entry_facts hw).2.1 j hj
      exact ⟨hjk, hsrc, hmin w hw j hj, hM w hw j hjk⟩)
    (fun w hw => by have := hS w hw; omega) henv
    (fun w hw s h1 h2 => (hI s h1 h2).1 w hw)
  intro s h1 h2
  rcases Nat.lt_or_ge s (t + 1) with hs | hs
  · exact hI s (by omega) (by omega)
  · have : s = t + 1 := by omega
    subst this
    exact ⟨fun w hw => hfin w hw (t + 1) (by omega) (le_refl _), hq, hpa⟩

/-- **The one remaining hypothesis**: from the idle island (plus `J`) at a rising pair request, one whole pair
episode that ends in the idle island (plus `J`). -/
def StepHyp (p : DelayPar) (T R su Δo M : Nat) (J : Beh → Nat → Prop) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit net boundary) x → ArbOK T arbs x →
    Env x boundary R su Δo n va vb → SeqEnv x boundary R →
    ∀ t, R ≤ t → Isl x M t → J x t → Low x boundary t → edge (x boundary.a.req) t →
      ∃ t2 t0, StepCore x boundary Δo (fun s => Isl x M s ∧ J x s) t t2 t0

/-- **THE statement on THE target from the per-pair step.** `J` is any extra invariant true at the end of reset
and kept by quiet steps (take `J := fun _ _ => True` for none: `the_of_step'`). -/
theorem the_of_step {p : DelayPar} {T R su Δo M A : Nat} (hp : Sane p) (hd : IslDelay p M A)
    (hRA : A + 87 * M + 1 ≤ R) (J : Beh → Nat → Prop)
    (hJ0 : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit net boundary) x →
      ArbOK T arbs x → Env x boundary R su Δo n va vb → SeqEnv x boundary R → J x R)
    (hJq : ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit net boundary) x →
      ArbOK T arbs x → Env x boundary R su Δo n va vb → SeqEnv x boundary R →
      ∀ t, R ≤ t → Isl x M t → J x t → Low x boundary t → x boundary.a.req (t + 1) = false → J x (t + 1))
    (hstep : StepHyp p T R su Δo M J) :
    NetCorrectSeq net boundary arbs p T R su Δo := by
  apply AssemblyPS.the_of_plan
  intro x n va vb hb harb he hseq
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := bnd_facts
  have he' := he
  obtain ⟨hrst, -, -, hEa, -, -, -, hEp⟩ := he'
  obtain ⟨hq0, -, -, -, -, -⟩ := hEa
  obtain ⟨hp0, hpm, -, -⟩ := hEp
  have hR0 : 0 < R := by omega
  -- the end acknowledge only moves when it differs from the shared request
  have hpa_next : ∀ t, R ≤ t → x 186985 t = false → x 104477 t = false → x 104477 (t + 1) = false := by
    intro t ht hq hpa
    by_contra hne
    have := hpm t ht (by rw [b11, hpa]; simpa using hne)
    rw [b11, b10, hpa, hq] at this; exact this rfl
  -- base: the island at the end of reset
  have hbase : Isl x M R := by
    have hisl := island_reset_upto hp hb hd (fun t ht => by rw [b12, ← b1]; exact hrst t ht) hR0
      (U := R) (by omega) (fun t ht => by rw [← b2]; exact hq0 t ht)
      (fun t ht => by rw [← b11]; exact hp0 t ht) (by omega)
    intro s h1 h2
    exact ⟨fun w hw => hisl w hw s (by omega) h2, by rw [← b2]; exact hq0 s h2, by rw [← b11]; exact hp0 s h2⟩
  refine ⟨fun t => Isl x M t ∧ J x t, ⟨⟨hbase, hJ0 x n va vb hb harb he hseq⟩, ?_, ?_, ?_⟩⟩
  · intro v hv
    simp only [couts, List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [b5, b6, b7, b8] at hv
    have hI := (hbase R (by omega) (le_refl _)).1
    rcases hv with rfl | rfl | rfl | rfl
    · exact hI _ mem4.1
    · exact hI _ mem4.2.1
    · exact hI _ mem4.2.2.1
    · exact hI _ mem4.2.2.2
  · intro t ht ⟨hI, hJ⟩ hlow hq
    have hq0t : x 186985 t = false := (hI t (by omega) (le_refl _)).2.1
    have hpat : x 104477 t = false := (hI t (by omega) (le_refl _)).2.2
    have hq' : x 186985 (t + 1) = false := by rw [← b2]; exact hq
    have hI' := isl_next hp hb hd (A := A) (by omega) hI hq' (hpa_next t ht hq0t hpat)
    refine ⟨?_, hI', hJq x n va vb hb harb he hseq t ht hI hJ hlow hq⟩
    intro v hv
    simp only [couts, List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [b5, b6, b7, b8] at hv
    have h1 := (hI' (t + 1) (by omega) (le_refl _)).1
    rcases hv with rfl | rfl | rfl | rfl
    · exact h1 _ mem4.1
    · exact h1 _ mem4.2.1
    · exact h1 _ mem4.2.2.1
    · exact h1 _ mem4.2.2.2
  · intro t ht ⟨hI, hJ⟩ hlow hedge
    exact hstep x n va vb hb harb he hseq t ht hI hJ hlow hedge

/-- The same with no extra invariant. -/
theorem the_of_step' {p : DelayPar} {T R su Δo M A : Nat} (hp : Sane p) (hd : IslDelay p M A)
    (hRA : A + 87 * M + 1 ≤ R) (hstep : StepHyp p T R su Δo M (fun _ _ => True)) :
    NetCorrectSeq net boundary arbs p T R su Δo :=
  the_of_step hp hd hRA (fun _ _ => True) (fun _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hstep

end Formal.Target.PlanPS
