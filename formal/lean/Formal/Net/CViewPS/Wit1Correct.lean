import Formal.Net.CViewPS.Wit1Env

/-!
# A run of THE target that meets THE statement's hypotheses and its conclusion (shard C)

**Proved** (`w1_hyps_and_correct`): the Lean-checked run `xW1` (decoded gcd_ps circuit, operands 12
and 18, every pin at FAST_MIN; Wit1.lean) satisfies every hypothesis of `NetCorrectSeq` at
`p1 = (g = 1, κ = 0)`, `R = 400000`, any `su`, `Δo = 3000`, `n = some 1`, any `T ≥ 220` (Behaves,
ArbOK, Env, SeqEnv; `w1_all_hyps'`) **and** its conclusion `Correct`: the handshakes follow the
protocol and complete, out0's data from `Δo` after its request until its acknowledge is
`Nat.gcd 12 18`, and the boundary ends idle with out0 and end having risen once. One run: a
consistency check of the statement on the real netlist, not a proof for all runs.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS

theorem busVal_after (d : List Nat) (L : Nat) (h : (d.all fun n => (thrL (encW1 n)).all fun θ => decide (θ ≤ L)) = true)
    (t : Nat) (ht : L ≤ t) : busVal xW1 d t = busVal xW1 d L := by
  unfold busVal
  congr 1
  apply List.map_congr_left
  intro p hp
  have hn : p.1 ∈ d := List.fst_mem_of_mem_zipIdx hp
  have := List.all_eq_true.mp h p.1 hn
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  have e : xW1 p.1 t = xW1 p.1 L := sigL_eq _ _ _ (fun θ hθ => by have := this θ hθ; omega)
  simp only [e]

theorem w1_out_data : (boundary.out0.data.all fun n => (thrL (encW1 n)).all fun θ => decide (θ ≤ 768160)) = true ∧
    busVal xW1 boundary.out0.data 768160 = Nat.gcd 12 18 := by
  decide +kernel

theorem w1_correct : Correct xW1 boundary 400000 3000 (some 1) (fun _ => 12) (fun _ => 18) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -⟩ := bnd_facts
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := w1_codes
  have hp : ∀ {n a b : Nat}, encW1 n = some (false, [a, b]) → a < b → xW1 n = pls a b :=
    fun h hab => funext fun t => w1_sig h hab t
  have rq := hp c2 (by omega)
  have cin : ∀ (ch : InCh) (p q : Nat), ch.req = 186985 → 401000 < p → p ≤ 499366 → 499367 < q →
      xW1 ch.ack = pls p q → CircIn xW1 ch 400000 := by
    intro ch p q hq h1 h2 h3 ha
    refine ⟨by rw [ha, pls_false]; omega, fun t ht hne => ?_, fun t ht hne => ?_⟩
    · rw [ha] at hne ⊢; rw [hq, rq]
      rcases pls_change hne with h | h
      · rw [(pls_false.mpr (by omega) : pls p q t = false), (pls_true.mpr (by omega) : pls 401000 499367 t = true)]; simp
      · rw [(pls_true.mpr (by omega) : pls p q t = true), (pls_false.mpr (by omega) : pls 401000 499367 t = false)]; simp
    · rw [ha, hq, rq] at hne
      by_cases e1 : 401000 ≤ t ∧ t < p
      · exact ⟨p, by omega, by rw [ha, hq, rq, (pls_true.mpr (by omega) : pls p q p = true),
          (pls_true.mpr (by omega) : pls 401000 499367 p = true)]⟩
      · by_cases e2 : 499367 ≤ t ∧ t < q
        · exact ⟨q, by omega, by rw [ha, hq, rq, (pls_false.mpr (by omega) : pls p q q = false),
            (pls_false.mpr (by omega) : pls 401000 499367 q = false)]⟩
        · exfalso; apply hne
          by_cases e3 : p ≤ t ∧ t < 499367
          · rw [(pls_true.mpr (by omega) : pls p q t = true), (pls_true.mpr (by omega) : pls 401000 499367 t = true)]
          · rw [(pls_false.mpr (by omega) : pls p q t = false), (pls_false.mpr (by omega) : pls 401000 499367 t = false)]
  have cout : ∀ (ch : OutCh) (a1 b1' : Nat), xW1 ch.req = pls a1 b1' → xW1 ch.ack = pls (a1 + 4000) (b1' + 4000) →
      400000 < a1 → a1 + 4000 < b1' → CircOut xW1 ch 400000 (some 1) := by
    intro ch a1 b1' hr ha h0 h1
    have rs : ∀ t, rises (xW1 ch.req) 400000 t = if a1 ≤ t then 1 else 0 :=
      rises_pulse _ 400000 a1 b1' (by omega) (by omega) (fun t => by rw [hr]; rfl)
    refine ⟨by rw [hr, pls_false]; omega, fun t ht hne => ?_, fun t ht he hc => ?_, fun t ht hx => ?_⟩
    · rw [hr] at hne ⊢; rw [ha]
      rcases pls_change hne with h | h
      · rw [(pls_false.mpr (by omega) : pls a1 b1' t = false), (pls_false.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) t = false)]
      · rw [(pls_true.mpr (by omega) : pls a1 b1' t = true), (pls_true.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) t = true)]
    · rw [rs, hr] at hc; rw [hr, ha] at he
      by_cases e1 : t < a1
      · exact ⟨a1, by omega, by rw [hr, ha, (pls_true.mpr (by omega) : pls a1 b1' a1 = true),
          (pls_false.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) a1 = false)]; simp⟩
      · by_cases e2 : t < b1'
        · exact ⟨b1', by omega, by rw [hr, ha, (pls_false.mpr (by omega) : pls a1 b1' b1' = false),
            (pls_true.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) b1' = true)]; simp⟩
        · exfalso
          rw [(pls_false.mpr (by omega) : pls a1 b1' t = false)] at hc
          simp only [Bool.false_eq_true, false_or, Offered] at hc
          have : (if a1 ≤ t then 1 else 0) = 1 := by simp; omega
          rw [this] at hc; omega
    · rw [rs]; rw [hr, pls_true] at hx
      simp only [Offered]; split <;> omega
  obtain ⟨d1, d2⟩ := w1_out_data
  have orq := hp c6 (by omega)
  have ors : ∀ t, rises (xW1 160957) 400000 t = if 771456 ≤ t then 1 else 0 :=
    rises_pulse _ 400000 771456 781729 (by omega) (by omega) (fun t => by rw [orq]; rfl)
  have rrs : ∀ t, rises (xW1 186985) 400000 t = if 401000 ≤ t then 1 else 0 :=
    rises_pulse _ 400000 401000 499367 (by omega) (by omega) (fun t => by rw [rq]; rfl)
  refine ⟨cin _ 436429 513860 b2 (by omega) (by omega) (by omega) (by rw [b5]; exact hp c3 (by omega)),
    cin _ 436885 514175 b3 (by omega) (by omega) (by omega) (by rw [b6]; exact hp c4 (by omega)),
    cin _ 499366 537972 b4 (by omega) (by omega) (by omega) (by rw [b7]; exact hp c5 (by omega)),
    cout _ 771456 781729 (by rw [b8]; exact orq) (by rw [b9]; exact hp c7 (by omega)) (by omega) (by omega),
    cout _ 401000 499367 (by rw [b10]; exact rq) (by rw [b11]; exact hp c8 (by omega)) (by omega) (by omega),
    fun t0 t ht0 h1 h2 h3 h4 => ?_, fun m hm => ?_⟩
  · rw [b8, orq, pls_false] at h1; rw [b8, orq, pls_true] at h2
    have e : t0 = 771455 := by omega
    subst e
    rw [b8, ors]
    simp only [show 771456 ≤ 771455 + 1 by omega, ite_true, Nat.sub_self]
    rw [busVal_after _ 768160 d1 t (by omega), d2]
  · simp only [Option.some.injEq] at hm; subst hm
    refine ⟨785729, fun t ht => ⟨?_, ?_, ?_⟩⟩
    · intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rw [b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [rq, pls_false]; omega
      · rw [hp c3 (by omega), pls_false]; omega
      · rw [rq, pls_false]; omega
      · rw [hp c4 (by omega), pls_false]; omega
      · rw [rq, pls_false]; omega
      · rw [hp c5 (by omega), pls_false]; omega
      · rw [orq, pls_false]; omega
      · rw [hp c7 (by omega), pls_false]; omega
      · rw [rq, pls_false]; omega
      · rw [hp c8 (by omega), pls_false]; omega
    · rw [b8, ors]; simp; omega
    · rw [b10, rrs]; simp; omega

theorem w1_hyps_and_correct (su T : Nat) (hT : 220 ≤ T) :
    (Behaves p1 (circuit net boundary) xW1 ∧ ArbOK T arbs xW1 ∧
      Env xW1 boundary 400000 su 3000 (some 1) (fun _ => 12) (fun _ => 18) ∧ SeqEnv xW1 boundary 400000) ∧
    Correct xW1 boundary 400000 3000 (some 1) (fun _ => 12) (fun _ => 18) :=
  ⟨w1_all_hyps' su T hT, w1_correct⟩

end Formal.Net.CViewPS
