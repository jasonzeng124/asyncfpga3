import Formal.Target.CexQ36.Refute
import Formal.Target.CexRuntQ.QStretch

/-!
# The κ = 9/25 livelock for EVERY reset length R ≥ 400 ns (shard A, 2026-11-09)

**Problem, plainly.** `CexQ36.not_netCorrectSeqRunt20` refutes the headline statement with a 400 ns reset; `Env`
fixes the reset length. The run is quiet from 299,999 to 399,999 ps, so waiting longer changes nothing.

**Proved.** For every `Δ`, the run with every transition after 399,999 ps (prefix and periodic part) delayed by `Δ`
(`xS Δ = stutB 399999 Δ xR`, `CexRuntQ.xQ_shift`) is a `BehavesRunt 20` behaviour at ⟨1, 9/25⟩ (stutter lemma),
meets Env with reset `400,000 + Δ` and SeqEnv, ArbOK for every `T ≥ 140`, and out0 never rises.
**`not_netCorrectSeqRunt20_R`**: for every `R ≥ 400,000`, `T ≥ 140`, `su`, `Δo ≤ 3000`:
`¬ NetCorrectSeqRunt 20 net boundary arbs ⟨1, 9/25⟩ T R su Δo`. The proof text is `CexRunt44.AnyR`'s with this
run's codes and the periodic part carried along.

**Assumptions used.** Only the Spec's definitions; standard axioms.
-/

namespace Formal.Target.CexQ36.AnyR
open Formal.Target Formal.Target.DecodedPS Formal.Net.CViewPS Formal.Net.CexPS72 Formal.Target.CexRuntP
open Formal.Target.CexQ36 Formal.Target.Stutter Formal.Target.StutterCodes Formal.Target.CexRuntQ

/-- The stretched run's codes: every transition after `399,999` ps delayed by `Δ`. -/
def encS (Δ : Nat) (n : Nat) : Option (Bool × List Nat) := shiftE 399999 Δ (encR n)

/-- The stretched run's periods: every periodic transition (all after 491,000 ps) delayed by `Δ`. -/
def perS (Δ : Nat) (n : Nat) : List Nat := (perR n).map (· + Δ)

def xS (Δ : Nat) : Beh := xQ 79 (encS Δ) (perS Δ)

def perP (l : List Nat) : Bool := l.all fun p => decide (399999 < p)

theorem per_trees : BTN.allLeaves perP perT = true := by decide +kernel

theorem per_late (n : Nat) : ∀ p ∈ perR n, 399999 < p := by
  have := BTN.get_all perP rfl perT 18 n per_trees
  intro p hp
  simpa using List.all_eq_true.mp this p hp

theorem xS_eq (Δ : Nat) : xS Δ = stutB 399999 Δ xR := xQ_shift 79 399999 Δ encR perR per_late

/-! ## The run is quiet on [299,999, 399,999] and every arc is short -/

def quietP (e : Option (Bool × List Nat)) : Bool := (thrL e).all fun θ => decide (θ ≤ 299999) || decide (399999 < θ)

theorem quiet_trees : llR.all (StutterCodes.BTL.allLeaves quietP) = true := by decide +kernel

theorem quiet_codes (n : Nat) : ∀ θ ∈ thrL (encR n), θ ≤ 399999 - 100000 ∨ 399999 < θ := by
  have := lookL_all quietP rfl llR 2500 12 quiet_trees n
  intro θ hθ
  have h := List.all_eq_true.mp this θ hθ
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h
  omega

theorem quiet_r : Quiet xR 399999 100000 := by
  intro n u h1 h2
  have e : ∀ t, t ≤ 399999 → xR n t = sigL (encR n) t := by
    intro t ht
    simp only [xR, xQ, Formal.Net.Periodic.sigQ]
    have hz : ((perR n).map fun p => Formal.Net.Periodic.cnt1 79 p t).sum = 0 := by
      apply List.sum_eq_zero
      intro a ha
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
      have := per_late n p hp
      simp only [Formal.Net.Periodic.cnt1]; rw [if_neg (by omega)]
    rw [hz, Nat.add_zero]
    cases e : encR n with
    | none => simp [pre, sigL]
    | some p => obtain ⟨b, ts⟩ := p; simp [pre, sigL]
  rw [e u (by omega), e 399999 le_rfl]
  apply sigL_eq
  intro θ hθ
  rcases quiet_codes n θ hθ with h3 | h3 <;> omega

theorem arcs_chunks : gR.all (fun l => l.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698) && decide (e.fmax ≤ e.smax)) =
    true := by decide +kernel

theorem arcs_ok (g : Gate) (hg : g ∈ (circuit net boundary).gates) : ∀ e ∈ g.arcs, e.smax ≤ 698 ∧ e.fmax ≤ e.smax := by
  rw [circuit_gates, gates_eq, List.mem_filter, List.mem_flatten] at hg
  obtain ⟨⟨l, hl, hgl⟩, _⟩ := hg
  have := List.all_eq_true.mp (List.all_eq_true.mp arcs_chunks l hl) g hgl
  intro e he
  have := List.all_eq_true.mp this e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  exact this

theorem arc_getD (g : Gate) (h : ∀ e ∈ g.arcs, e.smax ≤ 698 ∧ e.fmax ≤ e.smax) (i : Nat) :
    (g.arcs.getD i default).smax ≤ 698 ∧ (g.arcs.getD i default).fmax ≤ (g.arcs.getD i default).smax := by
  rw [List.getD_eq_getElem?_getD]
  cases h' : g.arcs[i]? with
  | none => simp only [Option.getD_none]; exact ⟨Nat.zero_le _, le_refl _⟩
  | some e => exact h e (List.mem_of_getElem? h')

theorem adm_le (c : ℚ) (h0 : 0 ≤ c) (h1 : c ≤ 1) (e : Arc) (he : e.smax ≤ 698 ∧ e.fmax ≤ e.smax) (d : Nat)
    (ha : Adm (pP 9) c e d) : d ≤ 100000 := by
  obtain ⟨_, hhi⟩ := ha
  simp only [pP, lerp, mul_one] at hhi
  have hs : (e.smax : ℚ) ≤ 698 := by exact_mod_cast he.1
  have hf : (e.fmax : ℚ) ≤ e.smax := by exact_mod_cast he.2
  have hl : (1 - c) * (e.fmax : ℚ) + c * e.smax ≤ e.smax := by nlinarith
  have hd : (d : ℚ) ≤ 100000 := by
    have : (1 + (9 : ℚ) / 25) * ((1 - c) * (e.fmax : ℚ) + c * e.smax) ≤ (1 + (9 : ℚ) / 25) * 698 := by
      apply mul_le_mul_of_nonneg_left (le_trans hl hs); norm_num
    push_cast at hhi; linarith
  exact_mod_cast hd

theorem foldr_max_le (l : List Arc) (f : Arc → Nat) (B : Nat) (h : ∀ e ∈ l, f e ≤ B) : (l.map f).foldr max 0 ≤ B := by
  induction l with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le (h e List.mem_cons_self) (ih fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem start_le (g : Gate) (h : ∀ e ∈ g.arcs, e.smax ≤ 698 ∧ e.fmax ≤ e.smax) : g.start (pP 9) ≤ 399999 := by
  unfold Gate.start
  apply foldr_max_le
  intro e he
  have hs : (e.smax : ℚ) ≤ 698 := by exact_mod_cast (h e he).1
  have : (Rat.ceil ((1 + (pP 9).κ) * e.smax * (pP 9).g)) ≤ 399999 := by
    rw [rat_ceil_eq', Int.ceil_le]
    simp only [pP, mul_one]; push_cast; nlinarith
  omega

/-- **The stretched run is a behaviour under H_RUNT(20)** at ⟨1, 9/25⟩. -/
theorem behavesRunt_s (Δ : Nat) : BehavesRunt 20 (pP 9) (circuit net boundary) (xS Δ) := by
  rw [xS_eq]
  exact behavesRuntOn_stut behavesRunt_r quiet_r (by norm_num) (by norm_num)
    (fun g hg => start_le g (arcs_ok g hg))
    (fun c h0 h1 g hg i _ d ha => adm_le c h0 h1 _ (arc_getD g (arcs_ok g hg) i) d ha)

/-! ## The environment, the arbiters and the missing result, with reset 400,000 + Δ -/

theorem shift_pair (Δ a b : Nat) (v : Bool) (ha : 399999 < a) (hb : 399999 < b) :
    shiftE 399999 Δ (some (v, [a, b])) = some (v, [a + Δ, b + Δ]) := by
  simp only [shiftE, List.map_cons, List.map_nil, sh, if_neg (show ¬ a ≤ 399999 by omega),
    if_neg (show ¬ b ≤ 399999 by omega)]

theorem shift_one (Δ a : Nat) (v : Bool) (ha : 399999 < a) :
    shiftE 399999 Δ (some (v, [a])) = some (v, [a + Δ]) := by
  simp only [shiftE, List.map_cons, List.map_nil, sh, if_neg (show ¬ a ≤ 399999 by omega)]

theorem s_codes (Δ : Nat) : encS Δ 186905 = some (true, [400000 + Δ]) ∧
    encS Δ 186985 = some (false, [401000 + Δ, 464710 + Δ]) ∧
    encS Δ 104576 = some (false, [423916 + Δ, 474089 + Δ]) ∧ encS Δ 104695 = some (false, [424206 + Δ, 474289 + Δ]) ∧
    encS Δ 147972 = some (false, [464709 + Δ, 489770 + Δ]) ∧ encS Δ 160957 = none ∧
    encS Δ 154859 = none ∧ encS Δ 104477 = some (false, [404000 + Δ, 467710 + Δ]) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := r_codes
  simp only [encS, c1, c2, c3, c4, c5, c6, c7, c8]
  refine ⟨shift_one _ _ _ (by norm_num), shift_pair _ _ _ _ (by norm_num) (by norm_num),
    shift_pair _ _ _ _ (by norm_num) (by norm_num), shift_pair _ _ _ _ (by norm_num) (by norm_num),
    shift_pair _ _ _ _ (by norm_num) (by norm_num), rfl, rfl, shift_pair _ _ _ _ (by norm_num) (by norm_num)⟩

theorem s_per (Δ : Nat) : perS Δ 186905 = [] ∧ perS Δ 186985 = [] ∧ perS Δ 104576 = [] ∧ perS Δ 104695 = [] ∧
    perS Δ 147972 = [] ∧ perS Δ 160957 = [] ∧ perS Δ 154859 = [] ∧ perS Δ 104477 = [] := by
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := r_per
  simp only [perS, p1, p2, p3, p4, p5, p6, p7, p8, List.map_nil, and_self]

theorem xS_zero (Δ n : Nat) : xS Δ n 0 = xR n 0 := by
  rw [xS_eq]; rfl

theorem s_data (Δ : Nat) : (boundary.a.data.all fun n => (thrL (encS Δ n)).isEmpty && (perS Δ n).isEmpty) = true ∧
    (boundary.b.data.all fun n => (thrL (encS Δ n)).isEmpty && (perS Δ n).isEmpty) = true ∧
    busVal (xS Δ) boundary.a.data 0 = 1240057368 ∧ busVal (xS Δ) boundary.b.data 0 = 901749038 := by
  obtain ⟨d1, d2, d3, d4⟩ := r_data
  have hb : ∀ d, busVal (xS Δ) d 0 = busVal xR d 0 := by
    intro d; unfold busVal; simp only [xS_zero]
  refine ⟨?_, ?_, by rw [hb]; exact d3, by rw [hb]; exact d4⟩
  · simp only [encS, perS, thrL_shift, List.isEmpty_map]; exact d1
  · simp only [encS, perS, thrL_shift, List.isEmpty_map]; exact d2

theorem busVal_constS (Δ : Nat) (d : List Nat) (h : (d.all fun n => (thrL (encS Δ n)).isEmpty && (perS Δ n).isEmpty) = true) (t : Nat) :
    busVal (xS Δ) d t = busVal (xS Δ) d 0 := by
  unfold busVal
  congr 1
  apply List.map_congr_left
  intro p hp
  have hn : p.1 ∈ d := List.fst_mem_of_mem_zipIdx hp
  have := List.all_eq_true.mp h p.1 hn
  simp only [Bool.and_eq_true, List.isEmpty_iff] at this
  have e : xS Δ p.1 t = xS Δ p.1 0 := by
    simp only [xS]; rw [xQ_fin this.2]; exact sigL_eq _ _ _ (by rw [this.1]; simp)
  simp only [e]

theorem encS_def (Δ : Nat) : encS Δ = fun n => shiftE 399999 Δ (encR n) := rfl

attribute [irreducible] encS

theorem s_sig (Δ : Nat) {n a b : Nat} (hp : perS Δ n = []) (h : encS Δ n = some (false, [a, b])) (hab : a < b) :
    xS Δ n = pls a b :=
  funext fun t => by simp only [xS]; rw [xQ_fin hp, h]; exact pulse_val a b t hab

theorem s_none (Δ : Nat) {n : Nat} (hp : perS Δ n = []) (h : encS Δ n = none) : xS Δ n = fun _ => false :=
  funext fun t => by simp only [xS]; rw [xQ_fin hp, h]; rfl

theorem s_hyps (Δ su Δo : Nat) (hΔ : Δo ≤ 3000) :
    Env (xS Δ) boundary (400000 + Δ) su Δo (some 1) (fun _ => 1240057368) (fun _ => 901749038) ∧ SeqEnv (xS Δ) boundary (400000 + Δ) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := bnd_facts
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := (s_codes Δ)
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := (s_per Δ)
  obtain ⟨d1, d2, d3, d4⟩ := (s_data Δ)
  have rq := (s_sig Δ) p2 c2 (by omega)
  have rs : ∀ t, rises ((xS Δ) 186985) (400000 + Δ) t = if (401000 + Δ) ≤ t then 1 else 0 :=
    rises_pulse _ (400000 + Δ) (401000 + Δ) (464710 + Δ) (by omega) (by omega) (fun t => by rw [rq]; rfl)
  have ein : ∀ (ch : InCh) (vals : Nat → Nat) (p q : Nat), ch.req = 186985 → (401000 + Δ) < p → p ≤ (464709 + Δ) →
      (464710 + Δ) < q → (xS Δ) ch.ack = pls p q → (∀ t, busVal (xS Δ) ch.data t = vals 0) →
      EnvIn (xS Δ) ch (400000 + Δ) su (some 1) vals := by
    intro ch vals p q hq hp1 hp2 hq2 hack hdat
    have r1 : ∀ t, rises ((xS Δ) ch.req) (400000 + Δ) t - 1 = 0 := fun t => by rw [hq, rs]; split <;> rfl
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht he hc => ?_, fun t ht hr => ?_,
      fun t ht _ _ s _ _ => by rw [r1]; exact hdat s, fun t ht _ _ => by rw [r1]; exact hdat t⟩
    · rw [hq, rq, pls_false]; omega
    · rw [hq, rq] at hne ⊢; rw [hack]
      rcases pls_change hne with h | h
      · have e1 : pls (401000 + Δ) (464710 + Δ) t = false := pls_false.mpr (by omega)
        have e2 : pls p q t = false := pls_false.mpr (by omega)
        rw [e1, e2]
      · have e1 : pls (401000 + Δ) (464710 + Δ) t = true := pls_true.mpr (by omega)
        have e2 : pls p q t = true := pls_true.mpr (by omega)
        rw [e1, e2]
    · rw [hq, rq, hack] at he; rw [hq, rs, rq] at hc; rw [hq]
      by_cases h1 : t < (401000 + Δ)
      · exact ⟨(401000 + Δ), by omega, by rw [rq, hack, (pls_true.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) (401000 + Δ) = true),
          (pls_false.mpr (by omega) : pls p q (401000 + Δ) = false)]; simp⟩
      · by_cases h2 : t < (464710 + Δ)
        · exact ⟨(464710 + Δ), by omega, by rw [rq, hack, (pls_false.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) (464710 + Δ) = false),
            (pls_true.mpr (by omega) : pls p q (464710 + Δ) = true)]; simp⟩
        · exfalso
          have e1 : pls (401000 + Δ) (464710 + Δ) t = false := pls_false.mpr (by omega)
          rw [e1] at hc
          simp only [Bool.false_eq_true, false_or, Offered] at hc
          have : (if (401000 + Δ) ≤ t then 1 else 0) = 1 := by simp; omega
          rw [this] at hc; omega
    · rw [hq, rs]; rw [hq, rq, pls_true] at hr
      simp only [Offered]; split <;> omega
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [b1]; simp only [xS]; rw [xQ_fin p1, c1, step_val]; simp; omega
  · rw [b1]; simp only [xS]; rw [xQ_fin p1, c1, step_val]; simp; omega
  · simp only [Offered] at hk; have : k = 0 := by omega
    subst this; decide
  · exact ein _ _ (423916 + Δ) (474089 + Δ) b2 (by omega) (by omega) (by omega) (by rw [b5]; exact (s_sig Δ) p3 c3 (by omega))
      (fun t => by rw [busVal_constS Δ _ d1 t]; exact d3)
  · exact ein _ _ (424206 + Δ) (474289 + Δ) b3 (by omega) (by omega) (by omega) (by rw [b6]; exact (s_sig Δ) p4 c4 (by omega))
      (fun t => by rw [busVal_constS Δ _ d2 t]; exact d4)
  · exact ein _ _ (464709 + Δ) (489770 + Δ) b4 (by omega) (by omega) (by omega) (by rw [b7]; exact (s_sig Δ) p5 c5 (by omega))
      (fun t => by rw [show boundary.start.data = [] from rfl]; rfl)
  · -- out0: request and acknowledge never move
    rw [show boundary.out0 = ⟨160957, 154859, boundary.out0.data⟩ from rfl]
    refine ⟨fun t _ => ?_, fun t _ hne => ?_, fun t _ hne => ?_, fun t _ _ h5 _ _ _ => ?_⟩
    · simp only [(s_none Δ) p7 c7]
    · simp only [(s_none Δ) p7 c7] at hne; exact absurd rfl hne
    · simp only [(s_none Δ) p7 c7, (s_none Δ) p6 c6] at hne; exact absurd rfl hne
    · simp only [(s_none Δ) p7 c7] at h5; exact absurd h5 (by simp)
  · -- pend: the shared request, acknowledged 3 ns after each of its moves
    rw [show boundary.pend = ⟨186985, 104477, boundary.pend.data⟩ from rfl]
    have ha := (s_sig Δ) p8 c8 (by omega)
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht hne => ?_, fun t ht h4 h5 s hs1 hs2 => ?_⟩
    · show (xS Δ) 104477 t = false
      rw [ha, pls_false]; omega
    · show (xS Δ) 104477 t ≠ (xS Δ) 186985 t
      change (xS Δ) 104477 (t + 1) ≠ (xS Δ) 104477 t at hne
      rw [ha] at hne ⊢; rw [rq]
      rcases pls_change hne with h | h
      · rw [(pls_false.mpr (by omega) : pls (404000 + Δ) (467710 + Δ) t = false),
          (pls_true.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) t = true)]; simp
      · rw [(pls_true.mpr (by omega) : pls (404000 + Δ) (467710 + Δ) t = true),
          (pls_false.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) t = false)]; simp
    · change (xS Δ) 104477 t ≠ (xS Δ) 186985 t at hne
      rw [ha, rq] at hne
      by_cases e1 : (401000 + Δ) ≤ t ∧ t < (404000 + Δ)
      · exact ⟨(404000 + Δ), by omega, by
          show (xS Δ) 104477 (404000 + Δ) = (xS Δ) 186985 (404000 + Δ)
          rw [ha, rq, (pls_true.mpr (by omega) : pls (404000 + Δ) (467710 + Δ) (404000 + Δ) = true),
            (pls_true.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) (404000 + Δ) = true)]⟩
      · by_cases e2 : (464710 + Δ) ≤ t ∧ t < (467710 + Δ)
        · exact ⟨(467710 + Δ), by omega, by
            show (xS Δ) 104477 (467710 + Δ) = (xS Δ) 186985 (467710 + Δ)
            rw [ha, rq, (pls_false.mpr (by omega) : pls (404000 + Δ) (467710 + Δ) (467710 + Δ) = false),
              (pls_false.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) (467710 + Δ) = false)]⟩
        · exfalso; apply hne
          by_cases e3 : (404000 + Δ) ≤ t ∧ t < (464710 + Δ)
          · rw [(pls_true.mpr (by omega) : pls (404000 + Δ) (467710 + Δ) t = true), (pls_true.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) t = true)]
          · rw [(pls_false.mpr (by omega) : pls (404000 + Δ) (467710 + Δ) t = false), (pls_false.mpr (by omega) : pls (401000 + Δ) (464710 + Δ) t = false)]
    · change (xS Δ) 104477 t = false at h4; change (xS Δ) 104477 (t + 1) = true at h5
      show (xS Δ) 186985 s = true
      rw [ha, pls_false] at h4; rw [ha, pls_true] at h5; rw [rq, pls_true]; omega
  · intro ch hch t ht h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    have hq : ch.req = 186985 := by rcases hch with rfl | rfl | rfl; exacts [b2, b3, b4]
    rw [hq, rq, pls_false] at h1; rw [hq, rq, pls_true] at h2
    have : t = (400999 + Δ) := by omega
    subst this
    rw [hq, rs, b8, b9, (s_none Δ) p6 c6, (s_none Δ) p7 c7]
    refine ⟨by simp, rfl, rfl⟩


/-- The prefix codes of the nodes that do not oscillate (an oscillating node is coded `none` here). -/
def encN (n : Nat) : Option (Bool × List Nat) := if (perR n).isEmpty then encR n else none

theorem arbs_chkR : (arbs.all fun a => (perR a.q).isEmpty && arbChkE encN 140 a &&
    a.ins.all fun n => decide ((thrL (encR n)).Pairwise (· < ·))) = true := by decide +kernel

/-- **H_ARB(T) for every `T ≥ 140` ps** in the stretched run. -/
theorem s_arbOK (Δ T : Nat) (hT : 140 ≤ T) : ArbOK T arbs (xS Δ) := by
  intro a ha t1 t2 hin t ht1 ht2
  have hk := List.all_eq_true.mp arbs_chkR a ha
  simp only [Bool.and_eq_true] at hk
  obtain ⟨⟨hq0, hchk0⟩, hinc0⟩ := hk
  simp only [List.isEmpty_iff] at hq0
  have hN : ∀ n, thrL (encN n) ≠ [] → perR n = [] ∧ encN n = encR n := by
    intro n hn
    by_cases h : (perR n).isEmpty
    · simp only [List.isEmpty_iff] at h; exact ⟨h, by simp [encN, h]⟩
    · exact absurd (by simp [encN, h, thrL]) hn
  have hchk : arbChkE (fun n => shiftE 399999 Δ (encN n)) 140 a = true := by
    apply arbChkE_shift encN 140 399999 Δ a hchk0
    intro n _ θ hθ
    have hne : thrL (encN n) ≠ [] := List.ne_nil_of_mem hθ
    rw [(hN n hne).2] at hθ
    rcases quiet_codes n θ hθ with h | h <;> omega
  have hqS : perS Δ a.q = [] := by simp [perS, hq0]
  have hxq : xS Δ a.q = sigL (encS Δ a.q) := by simp only [xS]; exact xQ_fin hqS
  have hqN : encN a.q = encR a.q := by simp [encN, hq0]
  rw [hxq]
  apply sigL_eq
  intro θ hθ
  constructor
  · intro h; by_contra h'
    simp only [arbChkE, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hchk
    rw [encS_def] at hθ; simp only at hθ; rw [← hqN] at hθ
    obtain ⟨n, hn, θ', hθ', ⟨⟨h1, h2⟩, h3⟩⟩ := hchk θ hθ
    have hne : thrL (encN n) ≠ [] := by
      intro h0; rw [thrL_shift, h0] at hθ'; simp at hθ'
    obtain ⟨hpn, hen⟩ := hN n hne
    rw [hen] at hθ'
    have hpS : perS Δ n = [] := by simp [perS, hpn]
    have hi := List.all_eq_true.mp hinc0 n hn
    simp only [decide_eq_true_eq] at hi
    have hc := hin n hn
    cases he : encR n with
    | none => simp [thrL, he, shiftE] at hθ'
    | some pr =>
      obtain ⟨b, ts⟩ := pr
      have hes : encS Δ n = some (b, ts.map (sh 399999 Δ)) := by rw [encS_def]; simp only [he, shiftE]
      rw [he] at hθ'; simp only [shiftE, thrL] at hθ'
      simp only [thrL, he] at hi
      have tog := sigL_toggles b _ (incr_shift 399999 Δ ts hi) θ' hθ' h3
      have e1 := hc (θ' - 1) (by omega) (by omega)
      have e2 := hc θ' (by omega) (by omega)
      have hxn : xS Δ n = sigL (encS Δ n) := by simp only [xS]; exact xQ_fin hpS
      rw [hxn, hes] at e1 e2
      exact tog (e1.trans e2.symm)
  · intro h; omega

/-- **The conclusion fails**: out0's request never rises. -/
theorem s_not_correct (Δ Δo : Nat) :
    ¬ Correct (xS Δ) boundary (400000 + Δ) Δo (some 1) (fun _ => 1240057368) (fun _ => 901749038) := by
  intro h
  obtain ⟨T, hT⟩ := h.2.2.2.2.2.2 1 rfl
  have h1 := (hT T (le_refl _)).2.1
  have hz : rises (xS Δ boundary.out0.req) (400000 + Δ) T = 0 :=
    rises_false _ _ (fun t => by rw [show boundary.out0.req = 160957 from rfl, s_none Δ (s_per Δ).2.2.2.2.2.1 (s_codes Δ).2.2.2.2.2.1]) T
  omega

/-- **THE headline statement under H_RUNT(20 ps) is false at g = 1, κ = 9/25 (a livelock) for every reset length
`R ≥ 400 ns`**, every `T ≥ 140` ps, every `su` and every `Δo ≤ 3 ns`. -/
theorem not_netCorrectSeqRunt20_R (R T su Δo : Nat) (hR : 400000 ≤ R) (hT : 140 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt 20 net boundary arbs (pP 9) T R su Δo := by
  obtain ⟨Δ, rfl⟩ : ∃ Δ, R = 400000 + Δ := ⟨R - 400000, by omega⟩
  intro h
  obtain ⟨he, hs⟩ := s_hyps Δ su Δo hΔ
  exact s_not_correct Δ Δo (h (xS Δ) (some 1) (fun _ => 1240057368) (fun _ => 901749038) (behavesRunt_s Δ) (s_arbOK Δ T hT) he hs)

end Formal.Target.CexQ36.AnyR
