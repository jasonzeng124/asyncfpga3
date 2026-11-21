import Formal.Net.CViewPS.Wit1

/-!
# THE statement's hypotheses are satisfiable for one pair (shard C)

**Problem, plainly.** `NetCorrectSeq` quantifies over behaviours that satisfy `Behaves`, `Env` (here
one pair, `n = some 1`), `SeqEnv` and `ArbOK T`. If no behaviour satisfied them, the statement would be
vacuous for `n = 1`. **Proved** (`w1_hyps`): the run `xW1` (Wit1.lean, which computes gcd(12, 18))
satisfies `Behaves p1 (circuit DecodedPS.net DecodedPS.boundary)`, `Env` with `R = 400000`, any `su`,
`Δo = 3000` (the run's acknowledges follow after 4 ns), `n = some 1`, `va = fun _ => 12`, `vb = fun _ => 18`, and `SeqEnv`; and `ArbOK T` for every `T ≥ 220` (`w1_all_hyps'`). Every boundary signal of the run is a single pulse; the Env clauses are proved from
the pulse shapes (`pulse_val`, `rises_pulse`).
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS

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

theorem w1_codes : encW1 186905 = some (true, [400000]) ∧ encW1 186985 = some (false, [401000, 499367]) ∧
    encW1 104576 = some (false, [436429, 513860]) ∧ encW1 104695 = some (false, [436885, 514175]) ∧
    encW1 147972 = some (false, [499366, 537972]) ∧ encW1 160957 = some (false, [771456, 781729]) ∧
    encW1 154859 = some (false, [775456, 785729]) ∧ encW1 104477 = some (false, [405000, 503367]) := by
  decide +kernel

theorem w1_data : (boundary.a.data.all fun n => (thrL (encW1 n)).isEmpty) = true ∧
    (boundary.b.data.all fun n => (thrL (encW1 n)).isEmpty) = true ∧
    busVal xW1 boundary.a.data 0 = 12 ∧ busVal xW1 boundary.b.data 0 = 18 := by
  decide +kernel

theorem busVal_const (d : List Nat) (h : (d.all fun n => (thrL (encW1 n)).isEmpty) = true) (t : Nat) :
    busVal xW1 d t = busVal xW1 d 0 := by
  unfold busVal
  congr 1
  apply List.map_congr_left
  intro p hp
  have hn : p.1 ∈ d := (List.mem_zipIdx hp).1 |> fun _ => List.fst_mem_of_mem_zipIdx hp
  have := List.all_eq_true.mp h p.1 hn
  simp only [List.isEmpty_iff] at this
  have e : xW1 p.1 t = xW1 p.1 0 := sigL_eq _ _ _ (by rw [this]; simp)
  simp only [e]

/-- A pulse signal of the run, as a function. -/
theorem w1_sig {n a b : Nat} (h : encW1 n = some (false, [a, b])) (hab : a < b) (t : Nat) :
    xW1 n t = (decide (a ≤ t) && !decide (b ≤ t)) := by
  simp only [xW1, h]; exact pulse_val a b t hab

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

theorem w1_hyps (su : Nat) :
    Behaves p1 (circuit net boundary) xW1 ∧
    Env xW1 boundary 400000 su 3000 (some 1) (fun _ => 12) (fun _ => 18) ∧ SeqEnv xW1 boundary 400000 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, -⟩ := bnd_facts
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := w1_codes
  obtain ⟨d1, d2, d3, d4⟩ := w1_data
  have hp : ∀ {n a b : Nat}, encW1 n = some (false, [a, b]) → a < b → xW1 n = pls a b :=
    fun h hab => funext fun t => w1_sig h hab t
  have rq := hp c2 (by omega)
  have rs : ∀ t, rises (xW1 186985) 400000 t = if 401000 ≤ t then 1 else 0 :=
    rises_pulse _ 400000 401000 499367 (by omega) (by omega) (fun t => by rw [rq]; rfl)
  have ein : ∀ (ch : InCh) (vals : Nat → Nat) (p q : Nat), ch.req = 186985 → 401000 < p → p ≤ 499366 →
      499367 < q → xW1 ch.ack = pls p q → (∀ t, busVal xW1 ch.data t = vals 0) →
      EnvIn xW1 ch 400000 su (some 1) vals := by
    intro ch vals p q hq hp1 hp2 hq2 hack hdat
    have r1 : ∀ t, rises (xW1 ch.req) 400000 t - 1 = 0 := fun t => by rw [hq, rs]; split <;> rfl
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht he hc => ?_, fun t ht hr => ?_,
      fun t ht _ _ s _ _ => by rw [r1]; exact hdat s, fun t ht _ _ => by rw [r1]; exact hdat t⟩
    · rw [hq, rq, pls_false]; omega
    · rw [hq, rq] at hne ⊢; rw [hack]
      rcases pls_change hne with h | h
      · have e1 : pls 401000 499367 t = false := pls_false.mpr (by omega)
        have e2 : pls p q t = false := pls_false.mpr (by omega)
        rw [e1, e2]
      · have e1 : pls 401000 499367 t = true := pls_true.mpr (by omega)
        have e2 : pls p q t = true := pls_true.mpr (by omega)
        rw [e1, e2]
    · rw [hq, rq, hack] at he; rw [hq, rs, rq] at hc; rw [hq]
      by_cases h1 : t < 401000
      · exact ⟨401000, by omega, by rw [rq, hack, (pls_true.mpr (by omega) : pls 401000 499367 401000 = true),
          (pls_false.mpr (by omega) : pls p q 401000 = false)]; simp⟩
      · by_cases h2 : t < 499367
        · exact ⟨499367, by omega, by rw [rq, hack, (pls_false.mpr (by omega) : pls 401000 499367 499367 = false),
            (pls_true.mpr (by omega) : pls p q 499367 = true)]; simp⟩
        · exfalso
          have e1 : pls 401000 499367 t = false := pls_false.mpr (by omega)
          rw [e1] at hc
          simp only [Bool.false_eq_true, false_or, Offered] at hc
          have : (if 401000 ≤ t then 1 else 0) = 1 := by simp; omega
          rw [this] at hc; omega
    · rw [hq, rs]; rw [hq, rq, pls_true] at hr
      simp only [Offered]; split <;> omega
  have eout : ∀ (ch : OutCh) (a1 b1' : Nat), xW1 ch.req = pls a1 b1' → xW1 ch.ack = pls (a1 + 4000) (b1' + 4000) →
      400000 < a1 → a1 + 4000 < b1' → EnvOut xW1 ch 400000 3000 := by
    intro ch a1 b1' hr ha h0 h1
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht hne => ?_, fun t ht h4 h5 s hs1 hs2 => ?_⟩
    · rw [ha, pls_false]; omega
    · rw [ha] at hne ⊢; rw [hr]
      rcases pls_change hne with h | h
      · rw [(pls_false.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) t = false),
          (pls_true.mpr (by omega) : pls a1 b1' t = true)]; simp
      · rw [(pls_true.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) t = true),
          (pls_false.mpr (by omega) : pls a1 b1' t = false)]; simp
    · rw [ha, hr] at hne
      by_cases e1 : a1 ≤ t ∧ t < a1 + 4000
      · exact ⟨a1 + 4000, by omega, by rw [ha, hr, (pls_true.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) (a1 + 4000) = true),
          (pls_true.mpr (by omega) : pls a1 b1' (a1 + 4000) = true)]⟩
      · by_cases e2 : b1' ≤ t ∧ t < b1' + 4000
        · exact ⟨b1' + 4000, by omega, by rw [ha, hr, (pls_false.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) (b1' + 4000) = false),
            (pls_false.mpr (by omega) : pls a1 b1' (b1' + 4000) = false)]⟩
        · exfalso; apply hne
          by_cases e3 : a1 + 4000 ≤ t ∧ t < b1'
          · rw [(pls_true.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) t = true), (pls_true.mpr (by omega) : pls a1 b1' t = true)]
          · rw [(pls_false.mpr (by omega) : pls (a1 + 4000) (b1' + 4000) t = false), (pls_false.mpr (by omega) : pls a1 b1' t = false)]
    · rw [ha, pls_false] at h4; rw [ha, pls_true] at h5; rw [hr, pls_true]; omega
  refine ⟨behaves_w1, ⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [b1]; simp only [xW1, c1]; rw [step_val]; simp; omega
  · rw [b1]; simp only [xW1, c1]; rw [step_val]; simp; omega
  · simp only [Offered] at hk; have : k = 0 := by omega
    subst this; decide
  · exact ein _ _ 436429 513860 b2 (by omega) (by omega) (by omega) (by rw [b5]; exact hp c3 (by omega))
      (fun t => by rw [busVal_const _ d1 t]; exact d3)
  · exact ein _ _ 436885 514175 b3 (by omega) (by omega) (by omega) (by rw [b6]; exact hp c4 (by omega))
      (fun t => by rw [busVal_const _ d2 t]; exact d4)
  · exact ein _ _ 499366 537972 b4 (by omega) (by omega) (by omega) (by rw [b7]; exact hp c5 (by omega))
      (fun t => by rw [show boundary.start.data = [] from rfl]; rfl)
  · exact eout _ 771456 781729 (by rw [b8]; exact hp c6 (by omega)) (by rw [b9]; exact hp c7 (by omega))
      (by omega) (by omega)
  · exact eout _ 401000 499367 (by rw [b10]; exact rq) (by rw [b11]; exact hp c8 (by omega))
      (by omega) (by omega)
  · intro ch hch t ht h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    have hq : ch.req = 186985 := by rcases hch with rfl | rfl | rfl <;> assumption
    rw [hq, rq, pls_false] at h1; rw [hq, rq, pls_true] at h2
    have : t = 400999 := by omega
    subst this
    rw [hq, rs, b8, b9, hp c6 (by omega), hp c7 (by omega)]
    refine ⟨by simp, pls_false.mpr (by omega), pls_false.mpr (by omega)⟩


theorem arbs_late : (arbs.all fun a => (thrL (encW1 a.q)).all fun θ => decide (θ < 787000)) = true := by
  decide +kernel

/-- **All of `NetCorrectSeq`'s hypotheses hold of the run**, for every `T ≥ 787,000` ps (H_ARB(T) is
met because every arbiter state is constant after the run's last transition; a weak `T`). -/
theorem w1_all_hyps (su T : Nat) (hT : 787000 ≤ T) :
    Behaves p1 (circuit net boundary) xW1 ∧ ArbOK T arbs xW1 ∧
    Env xW1 boundary 400000 su 3000 (some 1) (fun _ => 12) (fun _ => 18) ∧ SeqEnv xW1 boundary 400000 := by
  obtain ⟨h1, h2, h3⟩ := w1_hyps su
  refine ⟨h1, ?_, h2, h3⟩
  intro a ha t1 t2 _ t ht1 ht2
  have hl := List.all_eq_true.mp arbs_late a ha
  simp only [List.all_eq_true, decide_eq_true_eq] at hl
  exact sigL_eq _ _ _ (fun θ hθ => by have := hl θ hθ; constructor <;> intro <;> omega)


theorem countP_le_split (θ : Nat) (hθ : 1 ≤ θ) : ∀ ts : List Nat,
    ts.countP (fun x => decide (x ≤ θ)) = ts.countP (fun x => decide (x ≤ θ - 1)) + ts.count θ
  | [] => rfl
  | x :: ts => by
    rw [List.countP_cons, List.countP_cons, List.count_cons, countP_le_split θ hθ ts]
    by_cases h1 : x = θ
    · subst h1
      have : ¬ (x ≤ x - 1) := by omega
      simp [this]; omega
    · by_cases h2 : x ≤ θ - 1
      · have : x ≤ θ := by omega
        simp [h2, this, h1]; try omega
      · have : ¬ x ≤ θ := by omega
        simp [h2, this, h1]; try omega

/-- In a strictly increasing transition list, every listed time is a real toggle. -/
theorem sigL_toggles (b : Bool) (ts : List Nat) (hs : ts.Pairwise (· < ·)) (θ : Nat) (hθ : θ ∈ ts) (h1 : 1 ≤ θ) :
    sigL (some (b, ts)) (θ - 1) ≠ sigL (some (b, ts)) θ := by
  simp only [sigL]
  rw [countP_le_split θ h1 ts]
  have hc : ts.count θ = 1 := List.Nodup.count_of_mem (hs.imp (fun h => Nat.ne_of_lt h)) hθ
  rw [hc]
  cases b <;> cases h : (ts.countP fun x => decide (x ≤ θ - 1)) % 2 == 1 <;> simp_all <;> omega

def arbChk (T : Nat) (a : ArbNodes) : Bool :=
  (thrL (encW1 a.q)).all fun τ => a.ins.any fun n =>
    (thrL (encW1 n)).any fun θ => decide (τ < θ + T) && decide (θ ≤ τ) && decide (1 ≤ θ)

def incr (n : Nat) : Bool := match encW1 n with
  | some (_, ts) => decide (ts.Pairwise (· < ·))
  | none => true

theorem arbs_quick : (arbs.all fun a => arbChk 220 a && a.ins.all incr) = true := by decide +kernel

/-- **H_ARB(T) for every `T ≥ 220` ps**: in the run every arbiter-state toggle comes at most 219 ps
after a toggle of one of the state LUT's other inputs. -/
theorem w1_arbOK (T : Nat) (hT : 220 ≤ T) : ArbOK T arbs xW1 := by
  intro a ha t1 t2 hin t ht1 ht2
  have hk := List.all_eq_true.mp arbs_quick a ha
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hchk, hinc⟩ := hk
  apply sigL_eq
  intro θ hθ
  constructor
  · intro h; by_contra h'
    -- a toggle of q at θ in (t1 + T, t]: some input toggled shortly before
    simp only [arbChk, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hchk
    obtain ⟨n, hn, θ', hθ', ⟨⟨h1, h2⟩, h3⟩⟩ := hchk θ hθ
    have hi := List.all_eq_true.mp hinc n hn
    have hc := hin n hn
    cases he : encW1 n with
    | none => simp [thrL, he] at hθ'
    | some pr =>
      obtain ⟨b, ts⟩ := pr
      simp only [thrL, he] at hθ'
      simp only [incr, he, decide_eq_true_eq] at hi
      have tog := sigL_toggles b ts hi θ' hθ' h3
      have e1 := hc (θ' - 1) (by omega) (by omega)
      have e2 := hc θ' (by omega) (by omega)
      simp only [xW1, he] at e1 e2
      exact tog (e1.trans e2.symm)
  · intro h; omega

theorem w1_all_hyps' (su T : Nat) (hT : 220 ≤ T) :
    Behaves p1 (circuit net boundary) xW1 ∧ ArbOK T arbs xW1 ∧
    Env xW1 boundary 400000 su 3000 (some 1) (fun _ => 12) (fun _ => 18) ∧ SeqEnv xW1 boundary 400000 := by
  obtain ⟨h1, h2, h3⟩ := w1_hyps su
  exact ⟨h1, w1_arbOK T hT, h2, h3⟩

end Formal.Net.CViewPS
