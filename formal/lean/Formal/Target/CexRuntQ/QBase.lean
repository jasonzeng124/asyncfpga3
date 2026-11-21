import Formal.Target.CexRuntP.RBase
import Formal.Target.SpecPeriodic

/-!
# Livelock witnesses under H_RUNT(w): the per-gate finite check for eventually periodic runs (shard A, 2026-11-09)

**Problem, plainly.** A run of THE target that oscillates for ever (a livelock) is described by, for every node, an
initial value, its transitions before `t0` (`A`) and one period of transitions in `[t0, t0 + Q)` (`B`), repeated
for ever (`sigQ`, shard C's `Formal.Net.Periodic`). To show it is a `BehavesRunt w` behaviour at `pP P = ⟨1, P/25⟩`,
corner 0, every gate must satisfy Spec's gate relation at every time. This file gives a finite check per gate.

**The check `gateQ`.** With the run unrolled `m` periods (finite codes `encU`, equal to the periodic run below
`H = t0 + m·Q`): shard A's `gateWR` check (`CexRuntP.RBase`: per-arc delays, jump reads that skip narrow-pulse chains
on LUT pins) restricted to breakpoints before `U = V + Q` (`gateWRU`); `V` past the gate's start and past `t0`;
`U + w ≤ H`; each read map's *seam* `rd (V + Q - 1) ≤ rd V + Q` and *floor* `t0 + w ≤ rd V`; and the gate's output and
input nodes eventually periodic (`nodeQ`).

**Proved.** `gateOKRunt_of_gateQ`: `gateQ … g = true → GateOKRunt w (pP P) 0 g (xQ …)`, for the periodic behaviour
`xQ`. Via `SpecPeriodic.gateOKRunt_of_window` (periodic extension of the read maps) and `condAt_transfer`.

**Not shown here.** Any particular run (data), nor the environment, arbiter and conclusion clauses.
-/

namespace Formal.Target.CexRuntQ
open Formal.Target Formal.Net.CexPS72 Formal.Target.CexRuntP Formal.Target.SpecPeriodic Formal.Net.Periodic

/-! ## Codes -/

/-- Trees with `List Nat` leaves (sparse per-node periods; a leaf stands for every index below it). -/
inductive BTN
  | lf (v : List Nat)
  | nd (l r : BTN)

def BTN.get : BTN → Nat → Nat → List Nat
  | .lf v, _, _ => v
  | .nd _ _, 0, _ => []
  | .nd l r, d + 1, i => if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

/-- Prefix code (initial value, transitions before `t0`); `none` is a node that is always low. -/
def pre (e : Option (Bool × List Nat)) : Bool × List Nat := match e with
  | some p => p
  | none => (false, [])

/-- The eventually periodic behaviour: prefix codes `enc`, one period `per n` of transitions in `[t0, t0 + Q)`. -/
def xQ (Q : Nat) (enc : Nat → Option (Bool × List Nat)) (per : Nat → List Nat) : Beh :=
  fun n => sigQ Q (pre (enc n)).1 (pre (enc n)).2 (per n)

/-- The finite code unrolled `m` periods. -/
def encU (Q m : Nat) (enc : Nat → Option (Bool × List Nat)) (per : Nat → List Nat) (n : Nat) :
    Option (Bool × List Nat) :=
  some ((pre (enc n)).1, (pre (enc n)).2 ++ unr Q (per n) m)

/-- A node is eventually periodic from `t0` with period `Q`. -/
def nodeQ (Q t0 : Nat) (enc : Nat → Option (Bool × List Nat)) (per : Nat → List Nat) (n : Nat) : Bool :=
  (pre (enc n)).2.all (fun a => decide (a < t0)) && (per n).all (fun p => decide (t0 ≤ p) && decide (p < t0 + Q)) &&
    decide ((per n).length % 2 = 0)

theorem nodeQ_periodic {Q t0 : Nat} (hQ : 0 < Q) {enc : Nat → Option (Bool × List Nat)} {per : Nat → List Nat}
    {n : Nat} (h : nodeQ Q t0 enc per n = true) : ∀ t, t0 ≤ t → xQ Q enc per n (t + Q) = xQ Q enc per n t := by
  simp only [nodeQ, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  intro t ht
  exact sigQ_periodic hQ h1 h2 h3 ht

theorem xQ_eq_encU {Q t0 m : Nat} (hQ : 0 < Q) {enc : Nat → Option (Bool × List Nat)} {per : Nat → List Nat}
    (n : Nat) (h : (per n).all (fun p => decide (t0 ≤ p)) = true) (t : Nat) (ht : t < t0 + m * Q) :
    xQ Q enc per n t = sigL (encU Q m enc per n) t := by
  simp only [List.all_eq_true, decide_eq_true_eq] at h
  simp only [xQ, encU, sigL]
  exact sigQ_eq_unr hQ _ _ _ h m t ht

/-! ## The windowed finite check -/

/-- `gateWR` (CexRuntP) with the gate equation checked only at breakpoints before `U`. -/
def gateWRU (P w U : Nat) (enc : Nat → Option (Bool × List Nat)) (chs : Nat → List (Nat × Nat)) (sl : List Nat)
    (g : Gate) : Bool :=
  arcsOKR P w sl g &&
    (!lutGate g || (List.range g.k).all fun i =>
      pinOK w (enc (g.ins.getD i 0)) (chs (g.ins.getD i 0)) (dR P w sl g i) (startKP P g - dR P w sl g i)
        ((25 + P) * (g.arcs.getD i default).fmax)) &&
    (startKP P g :: bpsR P w enc sl g).all fun τ => decide (τ < startKP P g) || decide (U ≤ τ) || eqAtR P w enc chs sl g τ

/-- Soundness of the windowed check: monotone read maps, and every clause of the gate relation before `U`. -/
theorem condAt_of_gateWRU (P : Nat) (hP25 : P ≤ 25) (w : Nat) (hw : 1 ≤ w) (U : Nat)
    (enc : Nat → Option (Bool × List Nat)) (chs : Nat → List (Nat × Nat)) (sl : List Nat) (g : Gate)
    (hc : gateWRU P w U enc chs sl g = true) :
    (∀ i, i < g.k → Monotone (rd P w chs sl g i)) ∧
      ∀ t, g.start (pP P) ≤ t → t < U →
        CondAt lutGate w (pP P) 0 g (fun n => sigL (enc n)) (rd P w chs sl g) t := by
  simp only [gateWRU, Bool.and_eq_true] at hc
  obtain ⟨⟨harc, hpin⟩, hc⟩ := hc
  have hA : ∀ i, i < g.k → (25 - P) * (g.arcs.getD i default).fmin ≤ 25 * dR P w sl g i ∧
      25 * dR P w sl g i ≤ (25 + P) * (g.arcs.getD i default).fmax ∧ dR P w sl g i ≤ startKP P g := by
    intro i hi
    have := List.all_eq_true.mp harc i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have hP : lutGate g = true → ∀ i, i < g.k →
      pinOK w (enc (g.ins.getD i 0)) (chs (g.ins.getD i 0)) (dR P w sl g i) (startKP P g - dR P w sl g i)
        ((25 + P) * (g.arcs.getD i default).fmax) = true := by
    intro hl i hi
    simp only [hl, Bool.not_true, Bool.false_or] at hpin
    exact List.all_eq_true.mp hpin i (List.mem_range.mpr hi)
  refine ⟨fun i hi a b hab => ?_, fun t ht htU => ?_⟩
  · simp only [rd]
    split
    · rename_i hl
      have hs := hP hl i hi
      simp only [pinOK, Bool.and_eq_true] at hs
      exact jr_mono _ hs.1.1.1.1.2 _ _ (by omega)
    · omega
  have ht' : startKP P g ≤ t := le_trans (startKP_le P g) ht
  refine ⟨fun i hi => ⟨?_, ?_, fun hl => ?_⟩, ?_⟩
  · simp only [rd]; split
    · exact le_trans (jr_le _ _) (by omega)
    · omega
  · obtain ⟨h1, h2, h3⟩ := hA i hi
    simp only [rd]; split
    · rename_i hl
      have hlag := lag_of_pinOK w _ _ _ _ _ (hP hl i hi) t (by omega) (by omega) h2
      have hle := jr_le (chs (g.ins.getD i 0)) (t - dR P w sl g i)
      exact adm_of_int P hP25 _ _ (by omega) hlag
    · rw [show t - (t - dR P w sl g i) = dR P w sl g i by omega]
      exact adm_of_int P hP25 _ _ h1 h2
  · simp only [rd, hl, if_true]
    exact noRunt_of_pinOK w hw _ _ _ _ _ (hP hl i hi) _ (by have := (hA i hi).2.2; omega)
  · obtain ⟨a, b, c, d⟩ := lastBp_spec (startKP P g) t ht' (bpsR P w enc sl g)
    set τ := lastBp (startKP P g) t (bpsR P w enc sl g)
    have hτ : eqAtR P w enc chs sl g τ = true := by
      have hm : τ ∈ startKP P g :: bpsR P w enc sl g := by
        rcases c with c | c
        · rw [c]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ c
      have := List.all_eq_true.mp hc τ hm
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with (h | h) | h
      · omega
      · omega
      · exact h
    simp only [eqAtR, beq_iff_eq] at hτ
    have hout : sigL (enc g.out) t = sigL (enc g.out) τ := by
      apply sigL_eq; intro θ hθ
      exact d θ (by simp only [bpsR, List.mem_append]; exact Or.inl hθ)
    show sigL (enc g.out) t = g.init.testBit (addr g.k fun i => sigL (enc (g.ins.getD i 0)) (rd P w chs sl g i t))
    rw [hout, hτ]
    congr 1
    apply Formal.Timing.SpecSettle.addr_congr
    intro i hi
    have hdi := (hA i hi).2.2
    have hno : ∀ θ ∈ thrL (enc (g.ins.getD i 0)), (θ ≤ t - dR P w sl g i ↔ θ ≤ τ - dR P w sl g i) := by
      intro θ hθ
      have := d (θ + dR P w sl g i) (by
        simp only [bpsR, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
        exact Or.inr ⟨i, hi, θ, hθ, rfl⟩)
      constructor
      · intro h; have := this.mp (by omega); omega
      · intro h; have := this.mpr (by omega); omega
    simp only [rd]
    split
    · rename_i hl
      have hs := hP hl i hi
      simp only [pinOK, Bool.and_eq_true, List.all_eq_true] at hs
      have hends := hs.1.1.1.2
      have hcg : ∀ c ∈ chs (g.ins.getD i 0), (c.1 ≤ τ - dR P w sl g i ∧ τ - dR P w sl g i < c.2) ↔
          (c.1 ≤ t - dR P w sl g i ∧ t - dR P w sl g i < c.2) := by
        intro c hc
        have he := hends c hc
        have h1 := hno c.1 (contains_mem he.1)
        have h2 := hno c.2 (contains_mem he.2)
        constructor
        · intro ⟨x, y⟩; exact ⟨h1.mpr x, by by_contra hh; exact absurd (h2.mp (by omega)) (by omega)⟩
        · intro ⟨x, y⟩; exact ⟨h1.mp x, by by_contra hh; exact absurd (h2.mpr (by omega)) (by omega)⟩
      rcases jr_congr _ _ _ hcg with h | ⟨h1, h2⟩
      · rw [h]
      · rw [h1, h2]; exact sigL_eq _ _ _ (fun θ hθ => (hno θ hθ).symm)
    · exact sigL_eq _ _ _ (fun θ hθ => (hno θ hθ).symm)

/-! ## An upper bound of the gate's start -/

/-- An upper bound of `Gate.start (pP P) g`. -/
def startUB (P : Nat) (g : Gate) : Nat := (g.arcs.map fun e => ((25 + P) * e.smax + 24) / 25).foldr max 0

theorem ceil_le_ub (P s : Nat) : (Rat.ceil ((1 + (P : ℚ) / 25) * (s : ℚ) * 1)).toNat ≤ ((25 + P) * s + 24) / 25 := by
  rw [rat_ceil_eq']
  have h1 : (1 + (P : ℚ) / 25) * (s : ℚ) * 1 ≤ ((((25 + P) * s + 24) / 25 : Nat) : ℚ) := by
    have : (25 + P) * s ≤ ((25 + P) * s + 24) / 25 * 25 := by omega
    have h' : (25 + (P : ℚ)) * (s : ℚ) ≤ ((((25 + P) * s + 24) / 25 : Nat) : ℚ) * 25 := by exact_mod_cast this
    nlinarith
  have h3 : ⌈(1 + (P : ℚ) / 25) * (s : ℚ) * 1⌉ ≤ ((((25 + P) * s + 24) / 25 : Nat) : ℤ) := by
    rw [Int.ceil_le]; exact_mod_cast h1
  omega

theorem start_le_ub (P : Nat) (g : Gate) : g.start (pP P) ≤ startUB P g := by
  unfold startUB Gate.start
  apply foldr_max_mono
  intro e _
  simp only [pP]
  exact ceil_le_ub P e.smax

/-! ## The per-gate check for an eventually periodic run -/

/-- The finite check of one gate of an eventually periodic run (see the module doc). -/
def gateQ (P w Q t0 m V : Nat) (enc : Nat → Option (Bool × List Nat)) (per : Nat → List Nat)
    (chs : Nat → List (Nat × Nat)) (sl : List Nat) (g : Gate) : Bool :=
  gateWRU P w (V + Q) (encU Q m enc per) chs sl g &&
    decide (startUB P g ≤ V) && decide (t0 ≤ V) && decide (V + Q + w ≤ t0 + m * Q) &&
    nodeQ Q t0 enc per g.out &&
    (List.range g.k).all fun i =>
      nodeQ Q t0 enc per (g.ins.getD i 0) &&
        decide (rd P w chs sl g i (V + Q - 1) ≤ rd P w chs sl g i V + Q) &&
        decide (t0 + w ≤ rd P w chs sl g i V)

theorem gateOKRunt_of_gateQ (P : Nat) (hP25 : P ≤ 25) (w : Nat) (hw : 1 ≤ w) (Q t0 m V : Nat) (hQ : 0 < Q)
    (enc : Nat → Option (Bool × List Nat)) (per : Nat → List Nat) (chs : Nat → List (Nat × Nat)) (sl : List Nat)
    (g : Gate) (hc : gateQ P w Q t0 m V enc per chs sl g = true) :
    GateOKRunt w (pP P) 0 g (xQ Q enc per) := by
  simp only [gateQ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hc
  obtain ⟨⟨⟨⟨⟨hwr, hub⟩, ht0⟩, hH⟩, hout⟩, hins⟩ := hc
  obtain ⟨hmono, hwin⟩ := condAt_of_gateWRU P hP25 w hw (V + Q) _ chs sl g hwr
  have hnode : ∀ n, nodeQ Q t0 enc per n = true → ∀ t, t < t0 + m * Q →
      xQ Q enc per n t = sigL (encU Q m enc per n) t := by
    intro n hn t ht
    simp only [nodeQ, Bool.and_eq_true] at hn
    have : (per n).all (fun p => decide (t0 ≤ p)) = true := by
      simp only [List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hn ⊢
      exact fun p hp => (hn.1.2 p hp).1
    exact xQ_eq_encU hQ n this t ht
  -- periodicity and agreement on the gate's own nodes, through a behaviour that equals `xQ` there
  set z : Beh := fun n => if nodeQ Q t0 enc per n then xQ Q enc per n else sigL (encU Q m enc per n) with hz
  have hzx : ∀ n, nodeQ Q t0 enc per n = true → z n = xQ Q enc per n := fun n hn => by simp only [hz, hn, if_true]
  have hzper : ∀ n, nodeQ Q t0 enc per n = true → ∀ t, t0 ≤ t → z n (t + Q) = z n t := fun n hn t ht => by
    rw [hzx n hn]; exact nodeQ_periodic hQ hn t ht
  -- the window clauses for `z`
  have hwinz : ∀ t, g.start (pP P) ≤ t → t < V + Q → CondAt lutGate w (pP P) 0 g z (rd P w chs sl g) t := by
    intro t h1 h2
    refine condAt_transfer (H := t0 + m * Q) (U := V + Q) (fun n t' ht' => ?_) hH h2 (hwin t h1 h2)
    by_cases hn : nodeQ Q t0 enc per n = true
    · rw [hzx n hn]; exact hnode n hn t' ht'
    · simp only [hz, hn]; rfl
  -- the gate relation only reads the gate's own nodes: restrict periodicity to them
  have hz' : GateOKRunt w (pP P) 0 g z := by
    -- periodicity is needed only at the output and the input nodes
    have key : ∀ t, g.start (pP P) ≤ t → t < V + Q → CondAt lutGate w (pP P) 0 g z (rd P w chs sl g) t := hwinz
    clear hwinz
    exact gateOKRunt_of_window hQ (hzper _ hout) (fun i hi => hzper _ (hins i hi).1.1) hmono
      (le_trans (start_le_ub P g) hub) ht0 key (fun i hi => (hins i hi).1.2) (fun i hi => (hins i hi).2)
  -- `z` and `xQ` agree on every node the gate reads or drives
  obtain ⟨f, hm, hf⟩ := hz'
  refine ⟨f, hm, fun t ht => ?_⟩
  obtain ⟨h1, h2⟩ := hf t ht
  have ein : ∀ i, i < g.k → z (g.ins.getD i 0) = xQ Q enc per (g.ins.getD i 0) := fun i hi => hzx _ (hins i hi).1.1
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [← ein i hi]; exact h1 i hi
  · rw [← hzx _ hout, h2]; congr 1
    apply Formal.Timing.SpecSettle.addr_congr
    intro i hi; rw [ein i hi]

end Formal.Target.CexRuntQ
