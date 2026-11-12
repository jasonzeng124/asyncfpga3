import Formal.Net.CexRg16.Wit

/-!
# THE headline statement `NetCorrectSeqRunt 20` is false at g = 8/5, κ = 0 (shard C, 2026-11-07)

**Problem, plainly.** Does THE target satisfy the owner's headline statement (sequential env, H_RUNT(20 ps)) when
every arc may take any delay in its fast-corner window widened by the guard g = 8/5 (no scatter, κ = 0)?

**Proved.** No. `Wit.behavesRunt_r` is a behaviour under `BehavesRunt 20`: `r_hyps` (Env with reset 400 ns, one pair
(1071, 462), any `su`, `Δo ≤ 3000`; SeqEnv), `r_arbOK` (ArbOK T for every T ≥ 137), `r_not_correct` (out0's request
never rises). **`not_netCorrectSeqRunt20`**: for every `T ≥ 137`, `su`, `Δo ≤ 3000`,
`¬ NetCorrectSeqRunt 20 DecodedPS.net DecodedPS.boundary DecodedPS.arbs ⟨8/5, 0⟩ T 400000 su Δo`.
The environment proofs are shard C's (`CexPS72/Refute.lean`, as re-run by shard A in `CexRunt72`) on this run's codes.

**What it does NOT say.** Nothing about g < 8/5 (simulation: this adversary is correct at g = 1.58), other
corners, or other reset lengths. The deadlock is the race of shard B's binding RaceTablePS row (SLICE_X32Y45.A:
acknowledge path vs the node's own feedback loop), not a runt mechanism.
-/

namespace Formal.Net.CexRg16
open Formal.Target Formal.Target.DecodedPS Formal.Net.CViewPS

theorem pulse_val (a b t : Nat) (hab : a < b) :
    sigL (some (false, [a, b])) t = (decide (a ≤ t) && !decide (b ≤ t)) := by
  simp only [sigL, List.countP_cons, List.countP_nil]
  by_cases h1 : a ≤ t <;> by_cases h2 : b ≤ t <;> simp [h1, h2] <;> omega

theorem step_val (a t : Nat) : sigL (some (true, [a])) t = !decide (a ≤ t) := by
  simp only [sigL, List.countP_cons, List.countP_nil]
  by_cases h1 : a ≤ t <;> simp [h1]

theorem rises_pulse (s : Sig) (R a b : Nat) (hRa : R < a) (hab : a < b)
    (hs : ∀ t, s t = (decide (a ≤ t) && !decide (b ≤ t))) : ∀ t, rises s R t = if a ≤ t then 1 else 0
  | 0 => by simp [rises]; omega
  | t + 1 => by
    simp only [rises, rises_pulse s R a b hRa hab hs t, hs]
    by_cases h1 : a ≤ t
    · have : a ≤ t + 1 := by omega
      simp [h1, this]; intro _ _; omega
    · by_cases h2 : a = t + 1
      · subst h2; simp; omega
      · have : ¬ a ≤ t + 1 := by omega
        simp [h1, this]

theorem rises_false (s : Sig) (R : Nat) (h : ∀ t, s t = false) : ∀ t, rises s R t = 0
  | 0 => rfl
  | t + 1 => by simp only [rises, rises_false s R h t, h]; simp

theorem bnd_facts : boundary.rst = 186905 ∧ boundary.a.req = 186985 ∧ boundary.b.req = 186985 ∧
    boundary.start.req = 186985 ∧ boundary.a.ack = 104576 ∧ boundary.b.ack = 104695 ∧
    boundary.start.ack = 147972 ∧ boundary.out0.req = 160957 ∧ boundary.out0.ack = 154859 ∧
    boundary.pend.req = 186985 ∧ boundary.pend.ack = 104477 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem r_codes : encR 186905 = some (true, [400000]) ∧ encR 186985 = some (false, [401000, 461903]) ∧
    encR 104576 = some (false, [423300, 470887]) ∧ encR 104695 = some (false, [423571, 471172]) ∧
    encR 147972 = some (false, [461902, 484862]) ∧ encR 160957 = none ∧
    encR 154859 = none ∧ encR 104477 = some (false, [404000, 464903]) := by
  decide +kernel

theorem r_data : (boundary.a.data.all fun n => (thrL (encR n)).isEmpty) = true ∧
    (boundary.b.data.all fun n => (thrL (encR n)).isEmpty) = true ∧
    busVal xR boundary.a.data 0 = 1071 ∧ busVal xR boundary.b.data 0 = 462 := by
  decide +kernel

theorem busVal_const (d : List Nat) (h : (d.all fun n => (thrL (encR n)).isEmpty) = true) (t : Nat) :
    busVal xR d t = busVal xR d 0 := by
  unfold busVal
  congr 1
  apply List.map_congr_left
  intro p hp
  have hn : p.1 ∈ d := List.fst_mem_of_mem_zipIdx hp
  have := List.all_eq_true.mp h p.1 hn
  simp only [List.isEmpty_iff] at this
  have e : xR p.1 t = xR p.1 0 := sigL_eq _ _ _ (by rw [this]; simp)
  simp only [e]

/-- A pulse is `true` exactly on `[a, b)`. -/
def pls (a b : Nat) : Sig := fun t => decide (a ≤ t) && !decide (b ≤ t)

theorem pls_true {a b t : Nat} : pls a b t = true ↔ a ≤ t ∧ t < b := by
  simp [pls]

theorem pls_false {a b t : Nat} : pls a b t = false ↔ ¬ (a ≤ t ∧ t < b) := by
  rw [← Bool.not_eq_true, pls_true]

theorem pls_change {a b t : Nat} (h : pls a b (t + 1) ≠ pls a b t) : t + 1 = a ∨ t + 1 = b := by
  by_contra hc
  apply h
  cases h1 : pls a b t
  · rw [pls_false] at h1 ⊢; omega
  · rw [pls_true] at h1 ⊢; omega

theorem r_sig {n a b : Nat} (h : encR n = some (false, [a, b])) (hab : a < b) : xR n = pls a b :=
  funext fun t => by simp only [xR, h]; exact pulse_val a b t hab

theorem r_none {n : Nat} (h : encR n = none) : xR n = fun _ => false :=
  funext fun t => by simp only [xR, h, sigL]

theorem r_hyps (su Δo : Nat) (hΔ : Δo ≤ 3000) :
    Env xR boundary 400000 su Δo (some 1) (fun _ => 1071) (fun _ => 462) ∧ SeqEnv xR boundary 400000 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := bnd_facts
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := r_codes
  obtain ⟨d1, d2, d3, d4⟩ := r_data
  have rq := r_sig c2 (by omega)
  have rs : ∀ t, rises (xR 186985) 400000 t = if 401000 ≤ t then 1 else 0 :=
    rises_pulse _ 400000 401000 461903 (by omega) (by omega) (fun t => by rw [rq]; rfl)
  have ein : ∀ (ch : InCh) (vals : Nat → Nat) (p q : Nat), ch.req = 186985 → 401000 < p → p ≤ 461902 →
      461903 < q → xR ch.ack = pls p q → (∀ t, busVal xR ch.data t = vals 0) →
      EnvIn xR ch 400000 su (some 1) vals := by
    intro ch vals p q hq hp1 hp2 hq2 hack hdat
    have r1 : ∀ t, rises (xR ch.req) 400000 t - 1 = 0 := fun t => by rw [hq, rs]; split <;> rfl
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht he hc => ?_, fun t ht hr => ?_,
      fun t ht _ _ s _ _ => by rw [r1]; exact hdat s, fun t ht _ _ => by rw [r1]; exact hdat t⟩
    · rw [hq, rq, pls_false]; omega
    · rw [hq, rq] at hne ⊢; rw [hack]
      rcases pls_change hne with h | h
      · have e1 : pls 401000 461903 t = false := pls_false.mpr (by omega)
        have e2 : pls p q t = false := pls_false.mpr (by omega)
        rw [e1, e2]
      · have e1 : pls 401000 461903 t = true := pls_true.mpr (by omega)
        have e2 : pls p q t = true := pls_true.mpr (by omega)
        rw [e1, e2]
    · rw [hq, rq, hack] at he; rw [hq, rs, rq] at hc; rw [hq]
      by_cases h1 : t < 401000
      · exact ⟨401000, by omega, by rw [rq, hack, (pls_true.mpr (by omega) : pls 401000 461903 401000 = true),
          (pls_false.mpr (by omega) : pls p q 401000 = false)]; simp⟩
      · by_cases h2 : t < 461903
        · exact ⟨461903, by omega, by rw [rq, hack, (pls_false.mpr (by omega) : pls 401000 461903 461903 = false),
            (pls_true.mpr (by omega) : pls p q 461903 = true)]; simp⟩
        · exfalso
          have e1 : pls 401000 461903 t = false := pls_false.mpr (by omega)
          rw [e1] at hc
          simp only [Bool.false_eq_true, false_or, Offered] at hc
          have : (if 401000 ≤ t then 1 else 0) = 1 := by simp; omega
          rw [this] at hc; omega
    · rw [hq, rs]; rw [hq, rq, pls_true] at hr
      simp only [Offered]; split <;> omega
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [b1]; simp only [xR, c1]; rw [step_val]; simp; omega
  · rw [b1]; simp only [xR, c1]; rw [step_val]; simp; omega
  · simp only [Offered] at hk; have : k = 0 := by omega
    subst this; decide
  · exact ein _ _ 423300 470887 b2 (by omega) (by omega) (by omega) (by rw [b5]; exact r_sig c3 (by omega))
      (fun t => by rw [busVal_const _ d1 t]; exact d3)
  · exact ein _ _ 423571 471172 b3 (by omega) (by omega) (by omega) (by rw [b6]; exact r_sig c4 (by omega))
      (fun t => by rw [busVal_const _ d2 t]; exact d4)
  · exact ein _ _ 461902 484862 b4 (by omega) (by omega) (by omega) (by rw [b7]; exact r_sig c5 (by omega))
      (fun t => by rw [show boundary.start.data = [] from rfl]; rfl)
  · -- out0: request and acknowledge never move
    rw [show boundary.out0 = ⟨160957, 154859, boundary.out0.data⟩ from rfl]
    refine ⟨fun t _ => ?_, fun t _ hne => ?_, fun t _ hne => ?_, fun t _ _ h5 _ _ _ => ?_⟩
    · simp only [r_none c7]
    · simp only [r_none c7] at hne; exact absurd rfl hne
    · simp only [r_none c7, r_none c6] at hne; exact absurd rfl hne
    · simp only [r_none c7] at h5; exact absurd h5 (by simp)
  · -- pend: the shared request, acknowledged 3 ns after each of its moves
    rw [show boundary.pend = ⟨186985, 104477, boundary.pend.data⟩ from rfl]
    have ha := r_sig c8 (by omega)
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht hne => ?_, fun t ht h4 h5 s hs1 hs2 => ?_⟩
    · show xR 104477 t = false
      rw [ha, pls_false]; omega
    · show xR 104477 t ≠ xR 186985 t
      change xR 104477 (t + 1) ≠ xR 104477 t at hne
      rw [ha] at hne ⊢; rw [rq]
      rcases pls_change hne with h | h
      · rw [(pls_false.mpr (by omega) : pls 404000 464903 t = false),
          (pls_true.mpr (by omega) : pls 401000 461903 t = true)]; simp
      · rw [(pls_true.mpr (by omega) : pls 404000 464903 t = true),
          (pls_false.mpr (by omega) : pls 401000 461903 t = false)]; simp
    · change xR 104477 t ≠ xR 186985 t at hne
      rw [ha, rq] at hne
      by_cases e1 : 401000 ≤ t ∧ t < 404000
      · exact ⟨404000, by omega, by
          show xR 104477 404000 = xR 186985 404000
          rw [ha, rq, (pls_true.mpr (by omega) : pls 404000 464903 404000 = true),
            (pls_true.mpr (by omega) : pls 401000 461903 404000 = true)]⟩
      · by_cases e2 : 461903 ≤ t ∧ t < 464903
        · exact ⟨464903, by omega, by
            show xR 104477 464903 = xR 186985 464903
            rw [ha, rq, (pls_false.mpr (by omega) : pls 404000 464903 464903 = false),
              (pls_false.mpr (by omega) : pls 401000 461903 464903 = false)]⟩
        · exfalso; apply hne
          by_cases e3 : 404000 ≤ t ∧ t < 461903
          · rw [(pls_true.mpr (by omega) : pls 404000 464903 t = true), (pls_true.mpr (by omega) : pls 401000 461903 t = true)]
          · rw [(pls_false.mpr (by omega) : pls 404000 464903 t = false), (pls_false.mpr (by omega) : pls 401000 461903 t = false)]
    · change xR 104477 t = false at h4; change xR 104477 (t + 1) = true at h5
      show xR 186985 s = true
      rw [ha, pls_false] at h4; rw [ha, pls_true] at h5; rw [rq, pls_true]; omega
  · intro ch hch t ht h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    have hq : ch.req = 186985 := by rcases hch with rfl | rfl | rfl <;> assumption
    rw [hq, rq, pls_false] at h1; rw [hq, rq, pls_true] at h2
    have : t = 400999 := by omega
    subst this
    rw [hq, rs, b8, b9, r_none c6, r_none c7]
    refine ⟨by simp, rfl, rfl⟩

def arbChk (T : Nat) (a : ArbNodes) : Bool :=
  (thrL (encR a.q)).all fun τ => a.ins.any fun n =>
    (thrL (encR n)).any fun θ => decide (τ < θ + T) && decide (θ ≤ τ) && decide (1 ≤ θ)

def incr (n : Nat) : Bool := match encR n with
  | some (_, ts) => decide (ts.Pairwise (· < ·))
  | none => true

theorem arbs_quick : (arbs.all fun a => arbChk 137 a && a.ins.all incr) = true := by decide +kernel

/-- **H_ARB(T) for every `T ≥ 137` ps** in the run: every arbiter-state toggle comes less than 137 ps after a
toggle of one of its state LUT's other inputs. -/
theorem r_arbOK (T : Nat) (hT : 137 ≤ T) : ArbOK T arbs xR := by
  intro a ha t1 t2 hin t ht1 ht2
  have hk := List.all_eq_true.mp arbs_quick a ha
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hchk, hinc⟩ := hk
  apply sigL_eq
  intro θ hθ
  constructor
  · intro h; by_contra h'
    simp only [arbChk, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨n, hn, θ', hθ', ⟨⟨h1, h2⟩, h3⟩⟩ := hchk θ hθ
    have hi := List.all_eq_true.mp hinc n hn
    have hc := hin n hn
    cases he : encR n with
    | none => simp [thrL, he] at hθ'
    | some pr =>
      obtain ⟨b, ts⟩ := pr
      simp only [thrL, he] at hθ'
      simp only [incr, he, decide_eq_true_eq] at hi
      have tog := sigL_toggles b ts hi θ' hθ' h3
      have e1 := hc (θ' - 1) (by omega) (by omega)
      have e2 := hc θ' (by omega) (by omega)
      simp only [xR, he] at e1 e2
      exact tog (e1.trans e2.symm)
  · intro h; omega

/-- **The conclusion fails**: out0's request never rises, so it has not risen once by any time. -/
theorem r_not_correct (Δo : Nat) :
    ¬ Correct xR boundary 400000 Δo (some 1) (fun _ => 1071) (fun _ => 462) := by
  intro h
  obtain ⟨T, hT⟩ := h.2.2.2.2.2.2 1 rfl
  have h1 := (hT T (le_refl _)).2.1
  have hz : rises (xR boundary.out0.req) 400000 T = 0 :=
    rises_false _ _ (fun t => by rw [show boundary.out0.req = 160957 from rfl, r_none r_codes.2.2.2.2.2.1]) T
  omega

/-- **THE headline statement under H_RUNT(20 ps) is false at g = 8/5, κ = 0**, for reset 400 ns, every
`T ≥ 137` ps, every `su` and every `Δo ≤ 3 ns`. -/
theorem not_netCorrectSeqRunt20 (T su Δo : Nat) (hT : 137 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt 20 net boundary arbs pK T 400000 su Δo := by
  intro h
  obtain ⟨he, hs⟩ := r_hyps su Δo hΔ
  exact r_not_correct Δo (h xR (some 1) (fun _ => 1071) (fun _ => 462) behavesRunt_r (r_arbOK T hT) he hs)

end Formal.Net.CexRg16
