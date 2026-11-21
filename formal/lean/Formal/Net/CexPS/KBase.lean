import Formal.Net.CViewPS.Base
import Formal.Timing.SpecSettle

/-!
# Witness behaviours with per-arc delays, at g = 1, κ = 21/25 (shard C, counterexample work)

**Problem.** A candidate counterexample to THE statement (JOURNAL-C 2026-11-06, FOR-RESEARCH C2) is a run of
THE target's circuit in which a few gates (a set `sl` of output nodes) read their pins at the slow end of the
κ = 21/25 window and every other gate at the fast end. To make it a theorem, its gate relations must be
kernel-checked. This file gives the finite check and proves it sound.

**Proved.** `gateOK_of_gateWK`: if `gateWK enc sl g` holds (the gate equation at the gate's start and at every
breakpoint: its output's transitions and each input transition shifted by that pin's delay; plus, per arc,
`4·fmin ≤ 25·d ≤ 46·fmax` and `d ≤ startK g`), then `Spec.GateOK pK 0 g` holds for the behaviour coded by
`enc`, where `pK = ⟨1, 21/25⟩` and pin `i` is read at `t - dK sl g i` with
`dK = ⌊46·FAST_MAX/25⌋` for gates in `sl`, `⌈4·FAST_MIN/25⌉` otherwise (both inside `Adm pK 0`).

**Not shown here.** That any particular run passes (data, per chunk), nor the environment clauses.
-/

namespace Formal.Net.CexPS
open Formal.Target Formal.Timing.SpecSettle

/-- The delay parameters of the counterexample: no guard, scatter κ = 21/25. -/
def pK : DelayPar := ⟨1, 21 / 25⟩

/-- Trees with `Option (Bool × List Nat)` leaves (node codes: initial value, transition times). -/
inductive BTL
  | lf (v : Option (Bool × List Nat))
  | nd (l r : BTL)

def BTL.get : BTL → Nat → Nat → Option (Bool × List Nat)
  | .lf v, _, _ => v
  | .nd _ _, 0, _ => none
  | .nd l r, d + 1, i => if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

def lookL (tl : List BTL) (C d w : Nat) : Option (Bool × List Nat) := (tl.getD (w / C) (.lf none)).get d (w % C)

/-- The signal coded by a leaf: the initial value, toggled at each listed time. -/
def sigL : Option (Bool × List Nat) → Sig
  | none => fun _ => false
  | some (b, ts) => fun t => b != ((ts.countP fun x => decide (x ≤ t)) % 2 == 1)

def thrL : Option (Bool × List Nat) → List Nat
  | some (_, ts) => ts
  | none => []

theorem sigL_eq (e : Option (Bool × List Nat)) (s s' : Nat) (h : ∀ θ ∈ thrL e, (θ ≤ s ↔ θ ≤ s')) :
    sigL e s = sigL e s' := by
  cases e with
  | none => rfl
  | some p =>
    obtain ⟨b, ts⟩ := p
    simp only [sigL]
    congr 3
    apply List.countP_congr
    intro x hx
    simp only [decide_eq_true_eq]
    exact h x hx

/-- Pin `i`'s read delay: slow end for gates driving a node in `sl`, fast end otherwise. -/
def dK (sl : List Nat) (g : Gate) (i : Nat) : Nat :=
  if sl.contains g.out then 46 * (g.arcs.getD i default).fmax / 25 else (4 * (g.arcs.getD i default).fmin + 24) / 25

/-- A lower bound of `Gate.start pK g` (`startK_le`). -/
def startK (g : Gate) : Nat := (g.arcs.map fun e => 46 * e.smax / 25).foldr max 0

def bpsK (enc : Nat → Option (Bool × List Nat)) (sl : List Nat) (g : Gate) : List Nat :=
  thrL (enc g.out) ++ (List.range g.k).flatMap fun i => (thrL (enc (g.ins.getD i 0))).map (· + dK sl g i)

def eqAtK (enc : Nat → Option (Bool × List Nat)) (sl : List Nat) (g : Gate) (τ : Nat) : Bool :=
  sigL (enc g.out) τ == g.init.testBit (addr g.k fun i => sigL (enc (g.ins.getD i 0)) (τ - dK sl g i))

/-- Per-arc conditions: the delay is in `Adm pK 0` (as integers) and below the check's start. -/
def arcsOK (sl : List Nat) (g : Gate) : Bool :=
  (List.range g.k).all fun i =>
    decide (4 * (g.arcs.getD i default).fmin ≤ 25 * dK sl g i) && decide (25 * dK sl g i ≤ 46 * (g.arcs.getD i default).fmax) &&
      decide (dK sl g i ≤ startK g)

/-- The finite check of one gate. -/
def gateWK (enc : Nat → Option (Bool × List Nat)) (sl : List Nat) (g : Gate) : Bool :=
  arcsOK sl g && (startK g :: bpsK enc sl g).all fun τ => decide (τ < startK g) || eqAtK enc sl g τ

/-- The last checkpoint not after `t`. -/
def lastBp (st t : Nat) : List Nat → Nat
  | [] => st
  | θ :: Θ => if θ ≤ t then max θ (lastBp st t Θ) else lastBp st t Θ

theorem lastBp_spec (st t : Nat) (hst : st ≤ t) : ∀ Θ : List Nat,
    st ≤ lastBp st t Θ ∧ lastBp st t Θ ≤ t ∧ (lastBp st t Θ = st ∨ lastBp st t Θ ∈ Θ) ∧
      ∀ θ ∈ Θ, (θ ≤ t ↔ θ ≤ lastBp st t Θ)
  | [] => by simp [lastBp, hst]
  | θ :: Θ => by
    obtain ⟨a, b, c, d⟩ := lastBp_spec st t hst Θ
    simp only [lastBp]
    split
    · rename_i h
      refine ⟨le_trans a (le_max_right _ _), max_le h b, ?_, ?_⟩
      · rcases le_total θ (lastBp st t Θ) with hl | hl
        · rw [max_eq_right hl]; rcases c with c | c
          · exact Or.inl c
          · exact Or.inr (List.mem_cons_of_mem _ c)
        · rw [max_eq_left hl]; exact Or.inr List.mem_cons_self
      · intro θ' hθ'
        rcases List.mem_cons.mp hθ' with rfl | hm
        · exact ⟨fun _ => le_max_left _ _, fun _ => h⟩
        · rw [d θ' hm]; constructor
          · intro h'; exact le_trans h' (le_max_right _ _)
          · intro h'; rcases le_total θ (lastBp st t Θ) with hl | hl
            · rw [max_eq_right hl] at h'; exact h'
            · rw [max_eq_left hl] at h'
              exact (d θ' hm).mp (le_trans h' h)
    · rename_i h
      refine ⟨a, b, ?_, ?_⟩
      · rcases c with c | c
        · exact Or.inl c
        · exact Or.inr (List.mem_cons_of_mem _ c)
      · intro θ' hθ'
        rcases List.mem_cons.mp hθ' with rfl | hm
        · exact ⟨fun h' => absurd h' h, fun h' => absurd (le_trans h' b) h⟩
        · exact d θ' hm

theorem rat_ceil_eq' (q : ℚ) : Rat.ceil q = ⌈q⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]; rfl

theorem div_le_ceil (s : Nat) : 46 * s / 25 ≤ (Rat.ceil ((1 + 21 / 25 : ℚ) * (s : ℚ) * 1)).toNat := by
  rw [rat_ceil_eq']
  have h1 : ((46 * s / 25 : Nat) : ℚ) ≤ (1 + 21 / 25 : ℚ) * (s : ℚ) * 1 := by
    have : (46 * s / 25 : Nat) * 25 ≤ 46 * s := Nat.div_mul_le_self _ _
    have h' : ((46 * s / 25 : Nat) : ℚ) * 25 ≤ 46 * (s : ℚ) := by exact_mod_cast this
    linarith
  have h3 : ((46 * s / 25 : Nat) : ℤ) ≤ ⌈(1 + 21 / 25 : ℚ) * (s : ℚ) * 1⌉ := by
    have := Int.ceil_mono h1
    rwa [Int.ceil_natCast] at this
  omega

theorem foldr_max_mono (l : List Arc) (f g : Arc → Nat) (h : ∀ e ∈ l, f e ≤ g e) :
    (l.map f).foldr max 0 ≤ (l.map g).foldr max 0 := by
  induction l with
  | nil => simp
  | cons e l ih =>
    simp only [List.map_cons, List.foldr_cons]
    exact max_le_max (h e List.mem_cons_self) (ih fun e' he' => h e' (List.mem_cons_of_mem _ he'))

theorem startK_le (g : Gate) : startK g ≤ g.start pK := by
  unfold startK Gate.start
  apply foldr_max_mono
  intro e _
  simp only [pK]
  exact div_le_ceil e.smax

theorem gateOK_of_gateWK (enc : Nat → Option (Bool × List Nat)) (sl : List Nat) (g : Gate)
    (hc : gateWK enc sl g = true) : GateOK pK 0 g (fun n => sigL (enc n)) := by
  simp only [gateWK, Bool.and_eq_true] at hc
  obtain ⟨harc, hc⟩ := hc
  have hA : ∀ i, i < g.k → 4 * (g.arcs.getD i default).fmin ≤ 25 * dK sl g i ∧
      25 * dK sl g i ≤ 46 * (g.arcs.getD i default).fmax ∧ dK sl g i ≤ startK g := by
    intro i hi
    have := List.all_eq_true.mp harc i (List.mem_range.mpr hi)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨fun i t => t - dK sl g i, fun i _ a b hab => by dsimp only; omega, fun t ht => ?_⟩
  have ht' : startK g ≤ t := le_trans (startK_le g) ht
  refine ⟨fun i hi => ⟨by dsimp only; omega, ?_⟩, ?_⟩
  all_goals dsimp only
  · obtain ⟨h1, h2, h3⟩ := hA i hi
    rw [show t - (t - dK sl g i) = dK sl g i by omega]
    simp only [Adm, pK, lerp, sub_zero, one_mul, zero_mul, add_zero, div_one, mul_one]
    constructor
    · have : ((4 * (g.arcs.getD i default).fmin : Nat) : ℚ) ≤ ((25 * dK sl g i : Nat) : ℚ) := by exact_mod_cast h1
      push_cast at this; linarith
    · have : ((25 * dK sl g i : Nat) : ℚ) ≤ ((46 * (g.arcs.getD i default).fmax : Nat) : ℚ) := by exact_mod_cast h2
      push_cast at this; linarith
  · obtain ⟨a, b, c, d⟩ := lastBp_spec (startK g) t ht' (bpsK enc sl g)
    set τ := lastBp (startK g) t (bpsK enc sl g)
    have hτ : eqAtK enc sl g τ = true := by
      have hm : τ ∈ startK g :: bpsK enc sl g := by
        rcases c with c | c
        · rw [c]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ c
      have := List.all_eq_true.mp hc τ hm
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · omega
      · exact h
    simp only [eqAtK, beq_iff_eq] at hτ
    have hout : sigL (enc g.out) t = sigL (enc g.out) τ := by
      apply sigL_eq; intro θ hθ
      exact d θ (by simp only [bpsK, List.mem_append]; exact Or.inl hθ)
    rw [hout, hτ]
    congr 1
    apply addr_congr
    intro i hi
    apply sigL_eq
    intro θ hθ
    have hdi := (hA i hi).2.2
    have := d (θ + dK sl g i) (by
      simp only [bpsK, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
      exact Or.inr ⟨i, hi, θ, hθ, rfl⟩)
    constructor
    · intro h; have := this.mp (by omega); omega
    · intro h; have := this.mpr (by omega); omega

end Formal.Net.CexPS
