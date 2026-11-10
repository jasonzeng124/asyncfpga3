import Formal.Target.PlanPS

/-!
# Formal.Target.PlanRPS — THE statement on THE target from the per-pair step alone (shard A, 2026-11-10)

**Problem, plainly.** `PlanPS.the_of_step` needed, besides the per-pair step, a quiet clause for a post-episode state
`J`, because the idle island cannot have been low for `M` ps when a fast sequential environment re-requests (out0.req,
an island member, falls 1-2 ps before). Is there one invariant that holds at the end of every episode AND whose quiet
clause is provable once and for all?

**Proved here** (`the_of_stepR`, `the_of_stepR_all`): yes, the *read island* `IslR`: every member `w` of C's
414-node idle island has a read map `F` (a witness of its routed gate relation `CGateOK`, monotone reads) and a set
`P` of its pins such that the pins of `P` alone force `w`'s LUT to 0 (Kleene: whatever the other pins read), each
pin of `P` reads an island member or one of the two environment nodes (shared request, `end.ack`) through a route
of minimum delay at least 1 ps, and at time `t` that source has been low ever since the time `F` reads it at `t`.
* `isl_islR`: the old invariant `Isl` (island and environment low for the last `M` ps) implies `IslR`;
* `islR_low`: `IslR` at `t` puts every member, so `a.ack`, `b.ack`, `start.ack`, `out0.req`, low at `t`;
* `islR_next`: `IslR` at `t` and the two environment nodes low at `t + 1` give `IslR` at `t + 1` (monotone reads:
  the same `F` and `P` keep reading low sources).
So THE statement (`NetCorrectSeq` on the decoded gcd_ps netlist), for every `g > 0`, `0 ≤ κ < 1` and reset
`R ≥ ⌈(1+κ)g⌉·(15,600 + 87·3,881) + 1` ps, follows from ONE hypothesis, `StepHypR`: from `IslR` at a rising pair
request, one complete pair episode (`Assembly.StepCore`) that ends in `IslR`.
Simulation (untrusted, JOURNAL 2026-11-10): at both re-requests of a run with the fastest sequential env (pairs
(12,18), (17,5), (8,12), corner 0.5, κ = 0), `IslR` holds with the simulator's delays while `Isl` fails (9 members
changed within the last 3.9 ns) and a per-pin-window version fails on out0.req's last causal step.

Also (`the_on_of_stepR_all`): the same restricted to environments whose every offered pair satisfies a predicate
`Q` (`NetCorrectSeqOn Q`; `on_true_iff`: `Q = True` is THE statement), from the step on those pairs only; so a
step proof for one pair gives correctness for any number of repetitions of that pair.

**Not shown.** `StepHypR` (the per-pair circuit argument, C's S4/S6 instance for every pair).
-/

namespace Formal.Target.PlanRPS
open Formal.Target Formal.Target.Assembly Formal.Target.DecodedPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman
  Formal.Timing.SpecLoop Formal.Timing.Island Formal.Net.CViewPS Formal.Target.PlanPS

/-- **The read island at `t`** (see the module doc). -/
def IslR (p : DelayPar) (x : Beh) (t : Nat) : Prop :=
  ∀ w, memI w = true → ∃ (c : ℚ) (F : Nat → Nat → Nat), 0 ≤ c ∧ c ≤ 1 ∧
    (∀ i, i < (gAt cs 2500 w).k → Monotone (F i)) ∧
    (∀ s, startPS p w ≤ s →
      (∀ i, i < (gAt cs 2500 w).k → F i s ≤ s ∧ SumAdm p c (arcsPS w i) (s - F i s)) ∧
      x (gAt cs 2500 w).out s = (gAt cs 2500 w).init.testBit (addr (gAt cs 2500 w).k fun i => x (srcPS w i) (F i s))) ∧
    startPS p w ≤ t ∧
    ∃ P : List Nat, ForcesP (gAt cs 2500 w).k (gAt cs 2500 w).init (asgOf srcPS valI w P) false = true ∧
      ∀ j ∈ P, j < (gAt cs 2500 w).k ∧ (memI (srcPS w j) = true ∨ envI (srcPS w j) = true) ∧
        1 ≤ sumMin p (arcsPS w j) ∧ ∀ s, F j t ≤ s → s ≤ t → x (srcPS w j) s = false

/-- Forcing from reads: if every pin of `P` reads `false`, the LUT outputs `false`. -/
theorem forced_low {w : Nat} {P : List Nat} {v : Nat → Bool}
    (hF : ForcesP (gAt cs 2500 w).k (gAt cs 2500 w).init (asgOf srcPS valI w P) false = true)
    (hv : ∀ j ∈ P, j < (gAt cs 2500 w).k ∧ v j = false) :
    (gAt cs 2500 w).init.testBit (addr (gAt cs 2500 w).k v) = false := by
  apply forcesP_sound hF v
  intro e he
  simp only [asgOf, List.mem_map] at he
  obtain ⟨j, hj, rfl⟩ := he
  exact ⟨(hv j hj).1, by simpa [valI] using (hv j hj).2⟩

/-- `IslR` at `t` puts every island member low at `t`. -/
theorem islR_low {p : DelayPar} (hp : Sane p) {x : Beh} {t : Nat} (h : IslR p x t) :
    ∀ w, memI w = true → x w t = false := by
  intro w hw
  obtain ⟨c, F, hc0, hc1, -, hgt, hst, P, hF, hP⟩ := h w hw
  obtain ⟨hrd, ho⟩ := hgt t hst
  rw [← gAt_out_logic (entry_facts hw).1, ho]
  exact forced_low hF fun j hj => ⟨(hP j hj).1, (hP j hj).2.2.2 _ (le_refl _) (hrd j (hP j hj).1).1⟩

/-- **Quiet step of the read island.** -/
theorem islR_next {p : DelayPar} (hp : Sane p) {x : Beh} {t : Nat} (h : IslR p x t)
    (hq : x 186985 (t + 1) = false) (hpa : x 104477 (t + 1) = false) :
    IslR p x (t + 1) ∧ ∀ w, memI w = true → x w (t + 1) = false := by
  -- every member is low at t + 1
  have hlow : ∀ w, memI w = true → x w (t + 1) = false := by
    intro w hw
    obtain ⟨c, F, hc0, hc1, hmono, hgt, hst, P, hF, hP⟩ := h w hw
    obtain ⟨hrd, ho⟩ := hgt (t + 1) (by omega)
    rw [← gAt_out_logic (entry_facts hw).1, ho]
    refine forced_low hF fun j hj => ⟨(hP j hj).1, ?_⟩
    obtain ⟨hjk, -, hmin, hlo⟩ := hP j hj
    obtain ⟨r1, r2⟩ := hrd j hjk
    have hb := (sumAdm_bounds hp hc0 hc1 _ _ (ord_logic (entry_facts hw).1 j hjk) r2).1
    exact hlo _ (hmono j hjk (Nat.le_succ t)) (by omega)
  refine ⟨fun w hw => ?_, hlow⟩
  obtain ⟨c, F, hc0, hc1, hmono, hgt, hst, P, hF, hP⟩ := h w hw
  refine ⟨c, F, hc0, hc1, hmono, hgt, by omega, P, hF, fun j hj => ?_⟩
  obtain ⟨hjk, hsrc, hmin, hlo⟩ := hP j hj
  refine ⟨hjk, hsrc, hmin, fun s h1 h2 => ?_⟩
  rcases Nat.lt_or_ge s (t + 1) with hs | hs
  · exact hlo s (le_trans (hmono j hjk (Nat.le_succ t)) h1) (by omega)
  · have : s = t + 1 := by omega
    subst this
    rcases hsrc with hm | he
    · exact hlow _ hm
    · simp only [envI, Bool.or_eq_true, beq_iff_eq] at he
      rcases he with he | he <;> rw [he]
      · exact hq
      · exact hpa

/-- **`Isl` implies `IslR`** (in a behaviour, once every island start is at most `t - M`). -/
theorem isl_islR {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    {M A t : Nat} (hd : IslDelay p M A) (hAt : A ≤ t - M) (hI : Isl x M t) : IslR p x t := by
  obtain ⟨hS, hM, hmin, -⟩ := hd
  obtain ⟨c, hc0, hc1, hall⟩ := collapsed hp hb
  intro w hw
  have hg : CGateOK p c (gAt cs 2500 w) (srcPS w) (arcsPS w) (startPS p w) x :=
    hall _ (mem_view_logic (entry_facts hw).1)
  obtain ⟨F, hmono, hgt⟩ := hg
  have hSw := hS w hw
  refine ⟨c, F, hc0, hc1, hmono, hgt, by omega, psI w, (entry_facts hw).2.2.1, fun j hj => ?_⟩
  obtain ⟨hjk, hsrc⟩ := (entry_facts hw).2.1 j hj
  refine ⟨hjk, hsrc, hmin w hw j hj, fun s h1 h2 => ?_⟩
  obtain ⟨r1, r2⟩ := (hgt t (by omega)).1 j hjk
  have hb2 := (sumAdm_bounds hp hc0 hc1 _ _ (ord_logic (entry_facts hw).1 j hjk) r2).2
  have hMj := hM w hw j hjk
  have hIs := hI s (by omega) h2
  rcases hsrc with hm | he
  · exact hIs.1 _ hm
  · simp only [envI, Bool.or_eq_true, beq_iff_eq] at he
    rcases he with he | he <;> rw [he]
    · exact hIs.2.1
    · exact hIs.2.2

/-- **The one remaining hypothesis**: from the read island at a rising pair request, one whole pair episode that
ends in the read island. -/
def StepHypR (p : DelayPar) (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit net boundary) x → ArbOK T arbs x →
    Env x boundary R su Δo n va vb → SeqEnv x boundary R →
    ∀ t, R ≤ t → IslR p x t → Low x boundary t → edge (x boundary.a.req) t →
      ∃ t2 t0, StepCore x boundary Δo (IslR p x) t t2 t0

/-- **The plan for one behaviour**, from that behaviour's per-pair step (base and quiet proved here). -/
theorem plan_R {p : DelayPar} {Δo M A R su : Nat} (hp : Sane p) (hd : IslDelay p M A) (hRA : A + 87 * M + 1 ≤ R)
    {x : Beh} {n : Option Nat} {va vb : Nat → Nat} (hb : Behaves p (circuit net boundary) x)
    (he : Env x boundary R su Δo n va vb)
    (hstep : ∀ t, R ≤ t → IslR p x t → Low x boundary t → edge (x boundary.a.req) t →
      ∃ t2 t0, StepCore x boundary Δo (IslR p x) t t2 t0) :
    Plan x boundary R Δo (IslR p x) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12⟩ := bnd_facts
  obtain ⟨hrst, -, -, hEa, -, -, -, hEp⟩ := he
  obtain ⟨hq0, -, -, -, -, -⟩ := hEa
  obtain ⟨hp0, hpm, -, -⟩ := hEp
  have hR0 : 0 < R := by omega
  have couts_of : ∀ s, (∀ w, memI w = true → x w s = false) → ∀ v ∈ couts boundary, x v s = false := by
    intro s hI v hv
    simp only [couts, List.mem_cons, List.not_mem_nil, or_false] at hv
    rw [b5, b6, b7, b8] at hv
    rcases hv with rfl | rfl | rfl | rfl
    · exact hI _ mem4.1
    · exact hI _ mem4.2.1
    · exact hI _ mem4.2.2.1
    · exact hI _ mem4.2.2.2
  have hbase : Isl x M R := by
    have hisl := island_reset_upto hp hb hd (fun t ht => by rw [b12, ← b1]; exact hrst t ht) hR0
      (U := R) (by omega) (fun t ht => by rw [← b2]; exact hq0 t ht)
      (fun t ht => by rw [← b11]; exact hp0 t ht) (by omega)
    intro s h1 h2
    exact ⟨fun w hw => hisl w hw s (by omega) h2, by rw [← b2]; exact hq0 s h2, by rw [← b11]; exact hp0 s h2⟩
  have hbaseR : IslR p x R := isl_islR hp hb hd (by omega) hbase
  refine ⟨hbaseR, couts_of R (islR_low hp hbaseR), ?_, hstep⟩
  intro t ht hI hlow hq
  have hq0t : x 186985 t = false := by
    have := hlow boundary.a.req (by simp [bnodes]); rw [b2] at this; exact this
  have hpat : x 104477 t = false := by
    have := hlow boundary.pend.ack (by simp [bnodes]); rw [b11] at this; exact this
  have hq' : x 186985 (t + 1) = false := by rw [← b2]; exact hq
  have hpa' : x 104477 (t + 1) = false := by
    by_contra hne
    have := hpm t ht (by rw [b11, hpat]; simpa using hne)
    rw [b11, b10, hpat, hq0t] at this; exact this rfl
  obtain ⟨hI', hl'⟩ := islR_next hp hI hq' hpa'
  exact ⟨couts_of (t + 1) hl', hI'⟩

/-- **THE statement on THE target from the per-pair step alone.** -/
theorem the_of_stepR {p : DelayPar} {T R su Δo M A : Nat} (hp : Sane p) (hd : IslDelay p M A)
    (hRA : A + 87 * M + 1 ≤ R) (hstep : StepHypR p T R su Δo) :
    NetCorrectSeq net boundary arbs p T R su Δo := by
  apply AssemblyPS.the_of_plan
  intro x n va vb hb harb he hseq
  exact ⟨IslR p x, plan_R hp hd hRA hb he (hstep x n va vb hb harb he hseq)⟩

/-! ## Restricted to the pairs a predicate allows (a one-pair certificate gives this for its pair, any number of times) -/

/-- THE statement for environments whose every offered pair satisfies `Q`. -/
def NetCorrectSeqOn (Q : Nat → Nat → Prop) (p : DelayPar) (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat),
    Behaves p (circuit net boundary) x → ArbOK T arbs x → Env x boundary R su Δo n va vb → SeqEnv x boundary R →
      (∀ k, Offered n k → Q (va k) (vb k)) → Correct x boundary R Δo n va vb

theorem on_true_iff {p : DelayPar} {T R su Δo : Nat} :
    NetCorrectSeqOn (fun _ _ => True) p T R su Δo ↔ NetCorrectSeq net boundary arbs p T R su Δo :=
  ⟨fun h x n va vb hb ha he hs => h x n va vb hb ha he hs (fun _ _ => trivial),
   fun h x n va vb hb ha he hs _ => h x n va vb hb ha he hs⟩

/-- `StepHypR` for environments offering only pairs allowed by `Q`. -/
def StepHypROn (Q : Nat → Nat → Prop) (p : DelayPar) (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat), Behaves p (circuit net boundary) x → ArbOK T arbs x →
    Env x boundary R su Δo n va vb → SeqEnv x boundary R → (∀ k, Offered n k → Q (va k) (vb k)) →
    ∀ t, R ≤ t → IslR p x t → Low x boundary t → edge (x boundary.a.req) t →
      ∃ t2 t0, StepCore x boundary Δo (IslR p x) t t2 t0

/-- **THE statement restricted to `Q`'s pairs, from the per-pair step on those pairs**, every `g > 0`, `κ < 1`.
With `Q a b := a = 12 ∧ b = 18`: a step proof for the pair (12, 18) alone gives correctness for every environment
offering (12, 18) any number of times (n = none included). -/
theorem the_on_of_stepR_all {Q : Nat → Nat → Prop} {p : DelayPar} {T R su Δo : Nat} (hp : Sane p) (hk : p.κ < 1)
    (hR : Cp p * A1 + 87 * (Cp p * M1) + 1 ≤ R) (hstep : StepHypROn Q p T R su Δo) :
    NetCorrectSeqOn Q p T R su Δo := by
  intro x n va vb hb ha he hs hQ
  exact correct_of_plan AssemblyPS.oneReq_PS he
    (plan_R hp (islDelay_all hp hk) hR hb he (hstep x n va vb hb ha he hs hQ))

/-- **For every `g > 0`, `0 ≤ κ < 1`**, with a reset of at least `⌈(1+κ)g⌉·(15,600 + 87·3,881) + 1` ps. -/
theorem the_of_stepR_all {p : DelayPar} {T R su Δo : Nat} (hp : Sane p) (hk : p.κ < 1)
    (hR : Cp p * A1 + 87 * (Cp p * M1) + 1 ≤ R) (hstep : StepHypR p T R su Δo) :
    NetCorrectSeq net boundary arbs p T R su Δo :=
  the_of_stepR hp (islDelay_all hp hk) hR hstep

end Formal.Target.PlanRPS
