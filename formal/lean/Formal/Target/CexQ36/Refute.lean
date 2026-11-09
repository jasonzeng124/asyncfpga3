import Formal.Target.CexQ36.Wit

/-!
# THE headline statement `NetCorrectSeqRunt 20` is false at g = 1, κ = 9/25 = 0.36, by a LIVELOCK (shard A, 2026-11-09)

**Problem, plainly.** Does THE target satisfy the owner's headline statement (sequential env, H_RUNT(20 ps)) when
every arc may take any delay in its fast-corner window widened by within-die scatter κ = 0.36, for the full-width
operand pair (0x49e9c618, 0x35bf992e)?

**Proved (if this file checks).** No. `Wit.behavesRunt_r` is a behaviour under `BehavesRunt 20` at `pP 9 = ⟨1, 9/25⟩`
that never goes quiet: from 491 ns on, 140 nodes (around SLICE_X8-9Y14 and the C-element SLICE_X16Y21.A6) oscillate
with period 79 ps for ever, and out0's request never rises. `r_hyps` (Env with reset 400 ns, one pair (1240057368,
901749038), any `su`, `Δo ≤ 3000`; SeqEnv), `r_arbOK` (ArbOK T for every T ≥ 140: every arbiter state toggle is
within 140 ps of a toggle of a non-oscillating input), `r_not_correct` (out0's request never rises).
**`not_netCorrectSeqRunt20`**: for every `T ≥ 140`, `su`, `Δo ≤ 3000`,
`¬ NetCorrectSeqRunt 20 DecodedPS.net DecodedPS.boundary DecodedPS.arbs ⟨1, 9/25⟩ T 400000 su Δo`.
The proof text is shard B's `Formal/Cells/CexX16/Refute.lean` (itself C's CexR44) with this run's codes and the
eventually periodic behaviour substituted (`x_fin`: a node that does not oscillate follows its prefix code).

**What it does NOT say.** Nothing about κ < 9/25 (B's simulation: this adversary is correct at 0.35), other
corners, other reset lengths (not stretched here), other pairs. The failure is a liveness failure (no answer, the
circuit never stops switching), not a deadlock and not a wrong value.
-/

namespace Formal.Target.CexQ36
open Formal.Target Formal.Target.DecodedPS Formal.Net.CViewPS Formal.Net.CexPS72 Formal.Target.CexRuntP Formal.Target.CexRuntQ

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

theorem r_codes : encR 186905 = some (true, [400000]) ∧ encR 186985 = some (false, [401000, 464710]) ∧
    encR 104576 = some (false, [423916, 474089]) ∧ encR 104695 = some (false, [424206, 474289]) ∧
    encR 147972 = some (false, [464709, 489770]) ∧ encR 160957 = none ∧
    encR 154859 = none ∧ encR 104477 = some (false, [404000, 467710]) := by
  decide +kernel

/-- None of the boundary nodes oscillates in the tail. -/
theorem r_per : perR 186905 = [] ∧ perR 186985 = [] ∧ perR 104576 = [] ∧ perR 104695 = [] ∧ perR 147972 = [] ∧
    perR 160957 = [] ∧ perR 154859 = [] ∧ perR 104477 = [] := by
  decide +kernel

/-- A node that does not oscillate in the tail follows its prefix code. -/
theorem x_fin {n : Nat} (h : perR n = []) : xR n = sigL (encR n) := by
  funext t
  simp only [xR, xQ, Formal.Net.Periodic.sigQ, h, List.map_nil, List.sum_nil, Nat.add_zero]
  cases e : encR n with
  | none => simp [pre, sigL]
  | some p => obtain ⟨b, ts⟩ := p; simp [pre, sigL]

theorem r_data : (boundary.a.data.all fun n => (thrL (encR n)).isEmpty && (perR n).isEmpty) = true ∧
    (boundary.b.data.all fun n => (thrL (encR n)).isEmpty && (perR n).isEmpty) = true ∧
    busVal xR boundary.a.data 0 = 1240057368 ∧ busVal xR boundary.b.data 0 = 901749038 := by
  decide +kernel

theorem busVal_const (d : List Nat) (h : (d.all fun n => (thrL (encR n)).isEmpty && (perR n).isEmpty) = true) (t : Nat) :
    busVal xR d t = busVal xR d 0 := by
  unfold busVal
  congr 1
  apply List.map_congr_left
  intro p hp
  have hn : p.1 ∈ d := List.fst_mem_of_mem_zipIdx hp
  have := List.all_eq_true.mp h p.1 hn
  simp only [Bool.and_eq_true, List.isEmpty_iff] at this
  have e : xR p.1 t = xR p.1 0 := by
    rw [x_fin this.2]; exact sigL_eq _ _ _ (by rw [this.1]; simp)
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

theorem r_sig {n a b : Nat} (hp : perR n = []) (h : encR n = some (false, [a, b])) (hab : a < b) : xR n = pls a b :=
  funext fun t => by rw [x_fin hp, h]; exact pulse_val a b t hab

theorem r_none {n : Nat} (hp : perR n = []) (h : encR n = none) : xR n = fun _ => false :=
  funext fun t => by rw [x_fin hp, h]; rfl

theorem r_hyps (su Δo : Nat) (hΔ : Δo ≤ 3000) :
    Env xR boundary 400000 su Δo (some 1) (fun _ => 1240057368) (fun _ => 901749038) ∧ SeqEnv xR boundary 400000 := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := bnd_facts
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8⟩ := r_codes
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩ := r_per
  obtain ⟨d1, d2, d3, d4⟩ := r_data
  have rq := r_sig p2 c2 (by omega)
  have rs : ∀ t, rises (xR 186985) 400000 t = if 401000 ≤ t then 1 else 0 :=
    rises_pulse _ 400000 401000 464710 (by omega) (by omega) (fun t => by rw [rq]; rfl)
  have ein : ∀ (ch : InCh) (vals : Nat → Nat) (p q : Nat), ch.req = 186985 → 401000 < p → p ≤ 464709 →
      464710 < q → xR ch.ack = pls p q → (∀ t, busVal xR ch.data t = vals 0) →
      EnvIn xR ch 400000 su (some 1) vals := by
    intro ch vals p q hq hp1 hp2 hq2 hack hdat
    have r1 : ∀ t, rises (xR ch.req) 400000 t - 1 = 0 := fun t => by rw [hq, rs]; split <;> rfl
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht he hc => ?_, fun t ht hr => ?_,
      fun t ht _ _ s _ _ => by rw [r1]; exact hdat s, fun t ht _ _ => by rw [r1]; exact hdat t⟩
    · rw [hq, rq, pls_false]; omega
    · rw [hq, rq] at hne ⊢; rw [hack]
      rcases pls_change hne with h | h
      · have e1 : pls 401000 464710 t = false := pls_false.mpr (by omega)
        have e2 : pls p q t = false := pls_false.mpr (by omega)
        rw [e1, e2]
      · have e1 : pls 401000 464710 t = true := pls_true.mpr (by omega)
        have e2 : pls p q t = true := pls_true.mpr (by omega)
        rw [e1, e2]
    · rw [hq, rq, hack] at he; rw [hq, rs, rq] at hc; rw [hq]
      by_cases h1 : t < 401000
      · exact ⟨401000, by omega, by rw [rq, hack, (pls_true.mpr (by omega) : pls 401000 464710 401000 = true),
          (pls_false.mpr (by omega) : pls p q 401000 = false)]; simp⟩
      · by_cases h2 : t < 464710
        · exact ⟨464710, by omega, by rw [rq, hack, (pls_false.mpr (by omega) : pls 401000 464710 464710 = false),
            (pls_true.mpr (by omega) : pls p q 464710 = true)]; simp⟩
        · exfalso
          have e1 : pls 401000 464710 t = false := pls_false.mpr (by omega)
          rw [e1] at hc
          simp only [Bool.false_eq_true, false_or, Offered] at hc
          have : (if 401000 ≤ t then 1 else 0) = 1 := by simp; omega
          rw [this] at hc; omega
    · rw [hq, rs]; rw [hq, rq, pls_true] at hr
      simp only [Offered]; split <;> omega
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [b1, x_fin p1, c1, step_val]; simp; omega
  · rw [b1, x_fin p1, c1, step_val]; simp; omega
  · simp only [Offered] at hk; have : k = 0 := by omega
    subst this; decide
  · exact ein _ _ 423916 474089 b2 (by omega) (by omega) (by omega) (by rw [b5]; exact r_sig p3 c3 (by omega))
      (fun t => by rw [busVal_const _ d1 t]; exact d3)
  · exact ein _ _ 424206 474289 b3 (by omega) (by omega) (by omega) (by rw [b6]; exact r_sig p4 c4 (by omega))
      (fun t => by rw [busVal_const _ d2 t]; exact d4)
  · exact ein _ _ 464709 489770 b4 (by omega) (by omega) (by omega) (by rw [b7]; exact r_sig p5 c5 (by omega))
      (fun t => by rw [show boundary.start.data = [] from rfl]; rfl)
  · -- out0: request and acknowledge never move
    rw [show boundary.out0 = ⟨160957, 154859, boundary.out0.data⟩ from rfl]
    refine ⟨fun t _ => ?_, fun t _ hne => ?_, fun t _ hne => ?_, fun t _ _ h5 _ _ _ => ?_⟩
    · simp only [r_none p7 c7]
    · simp only [r_none p7 c7] at hne; exact absurd rfl hne
    · simp only [r_none p7 c7, r_none p6 c6] at hne; exact absurd rfl hne
    · simp only [r_none p7 c7] at h5; exact absurd h5 (by simp)
  · -- pend: the shared request, acknowledged 3 ns after each of its moves
    rw [show boundary.pend = ⟨186985, 104477, boundary.pend.data⟩ from rfl]
    have ha := r_sig p8 c8 (by omega)
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht hne => ?_, fun t ht h4 h5 s hs1 hs2 => ?_⟩
    · show xR 104477 t = false
      rw [ha, pls_false]; omega
    · show xR 104477 t ≠ xR 186985 t
      change xR 104477 (t + 1) ≠ xR 104477 t at hne
      rw [ha] at hne ⊢; rw [rq]
      rcases pls_change hne with h | h
      · rw [(pls_false.mpr (by omega) : pls 404000 467710 t = false),
          (pls_true.mpr (by omega) : pls 401000 464710 t = true)]; simp
      · rw [(pls_true.mpr (by omega) : pls 404000 467710 t = true),
          (pls_false.mpr (by omega) : pls 401000 464710 t = false)]; simp
    · change xR 104477 t ≠ xR 186985 t at hne
      rw [ha, rq] at hne
      by_cases e1 : 401000 ≤ t ∧ t < 404000
      · exact ⟨404000, by omega, by
          show xR 104477 404000 = xR 186985 404000
          rw [ha, rq, (pls_true.mpr (by omega) : pls 404000 467710 404000 = true),
            (pls_true.mpr (by omega) : pls 401000 464710 404000 = true)]⟩
      · by_cases e2 : 464710 ≤ t ∧ t < 467710
        · exact ⟨467710, by omega, by
            show xR 104477 467710 = xR 186985 467710
            rw [ha, rq, (pls_false.mpr (by omega) : pls 404000 467710 467710 = false),
              (pls_false.mpr (by omega) : pls 401000 464710 467710 = false)]⟩
        · exfalso; apply hne
          by_cases e3 : 404000 ≤ t ∧ t < 464710
          · rw [(pls_true.mpr (by omega) : pls 404000 467710 t = true), (pls_true.mpr (by omega) : pls 401000 464710 t = true)]
          · rw [(pls_false.mpr (by omega) : pls 404000 467710 t = false), (pls_false.mpr (by omega) : pls 401000 464710 t = false)]
    · change xR 104477 t = false at h4; change xR 104477 (t + 1) = true at h5
      show xR 186985 s = true
      rw [ha, pls_false] at h4; rw [ha, pls_true] at h5; rw [rq, pls_true]; omega
  · intro ch hch t ht h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    have hq : ch.req = 186985 := by rcases hch with rfl | rfl | rfl <;> assumption
    rw [hq, rq, pls_false] at h1; rw [hq, rq, pls_true] at h2
    have : t = 400999 := by omega
    subst this
    rw [hq, rs, b8, b9, r_none p6 c6, r_none p7 c7]
    refine ⟨by simp, rfl, rfl⟩

/-- Every toggle of the arbiter's state node comes less than `T` after a toggle of one of its other inputs that does
not oscillate in the tail; the state node does not oscillate either. -/
def arbChk (T : Nat) (a : ArbNodes) : Bool :=
  (perR a.q).isEmpty && (thrL (encR a.q)).all fun τ => a.ins.any fun n =>
    (perR n).isEmpty && (thrL (encR n)).any fun θ => decide (τ < θ + T) && decide (θ ≤ τ) && decide (1 ≤ θ)

def incr (n : Nat) : Bool := match encR n with
  | some (_, ts) => decide (ts.Pairwise (· < ·))
  | none => true

theorem arbs_quick : (arbs.all fun a => arbChk 140 a && a.ins.all incr) = true := by decide +kernel

/-- **H_ARB(T) for every `T ≥ 140` ps** in the run: every arbiter-state toggle comes less than 140 ps after a
toggle of one of its state LUT's other inputs. -/
theorem r_arbOK (T : Nat) (hT : 140 ≤ T) : ArbOK T arbs xR := by
  intro a ha t1 t2 hin t ht1 ht2
  have hk := List.all_eq_true.mp arbs_quick a ha
  simp only [Bool.and_eq_true] at hk
  obtain ⟨hchk, hinc⟩ := hk
  simp only [arbChk, Bool.and_eq_true, List.isEmpty_iff] at hchk
  obtain ⟨hq, hchk⟩ := hchk
  rw [x_fin hq, x_fin hq]
  apply sigL_eq
  intro θ hθ
  constructor
  · intro h; by_contra h'
    simp only [List.all_eq_true, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.isEmpty_iff] at hchk
    obtain ⟨n, hn, hpn, θ', hθ', ⟨⟨h1, h2⟩, h3⟩⟩ := hchk θ hθ
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
      rw [x_fin hpn, he] at e1 e2
      exact tog (e1.trans e2.symm)
  · intro h; omega

/-- **The conclusion fails**: out0's request never rises, so it has not risen once by any time. -/
theorem r_not_correct (Δo : Nat) :
    ¬ Correct xR boundary 400000 Δo (some 1) (fun _ => 1240057368) (fun _ => 901749038) := by
  intro h
  obtain ⟨T, hT⟩ := h.2.2.2.2.2.2 1 rfl
  have h1 := (hT T (le_refl _)).2.1
  have hz : rises (xR boundary.out0.req) 400000 T = 0 :=
    rises_false _ _ (fun t => by rw [show boundary.out0.req = 160957 from rfl, r_none r_per.2.2.2.2.2.1 r_codes.2.2.2.2.2.1]) T
  omega

/-- **THE headline statement under H_RUNT(20 ps) is false at g = 1, κ = 10/25**, for reset 400 ns, every
`T ≥ 140` ps, every `su` and every `Δo ≤ 3 ns`. -/
theorem not_netCorrectSeqRunt20 (T su Δo : Nat) (hT : 140 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt 20 net boundary arbs (pP 9) T 400000 su Δo := by
  intro h
  obtain ⟨he, hs⟩ := r_hyps su Δo hΔ
  exact r_not_correct Δo (h xR (some 1) (fun _ => 1240057368) (fun _ => 901749038) behavesRunt_r (r_arbOK T hT) he hs)

end Formal.Target.CexQ36
