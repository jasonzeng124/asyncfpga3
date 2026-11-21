import Formal.Net.CViewPS.WitBase

/-!
# Witness behaviours with lists of transitions (shard C)

**Problem.** The zero-pair theorems are implications from `Behaves`. Are their hypotheses satisfiable
for THE target? A witness is a concrete behaviour. Here: every node is described by an `Option Nat`
code (`sig1`): `none` is constant 0; `some b` with `b < 2` is constant `b`; `some (2·(T+1) + b)` is
`b` before `T` and `¬b` from `T` on. Every pin is read at its `FAST_MIN` (read time `t - fmin`,
admissible at `p1`, corner 0). `gateW` checks a gate's equation at its start and at every
breakpoint (its output's transition, each input transition shifted by the pin delay);
`gateOK_of_gateW` proves that this finite check gives `Spec.GateOK p1 0` for all time.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecLoop

/-- Trees with `Option (Bool × List Nat)` leaves (node codes: initial value, transition times). -/
inductive BTL
  | lf (v : Option (Bool × List Nat))
  | nd (l r : BTL)

def BTL.get : BTL → Nat → Nat → Option (Bool × List Nat)
  | .lf v, _, _ => v
  | .nd _ _, 0, _ => none
  | .nd l r, d + 1, i => if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

def lookL (tl : List BTL) (C d w : Nat) : Option (Bool × List Nat) := (tl.getD (w / C) (.lf none)).get d (w % C)

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

/-- The breakpoints of a gate: its output's transition and each input transition plus the pin's
`fmin`. -/
def bpsL (enc : Nat → Option (Bool × List Nat)) (g : Gate) : List Nat :=
  thrL (enc g.out) ++
  (List.range g.k).flatMap fun i => (thrL (enc (g.ins.getD i 0))).map (· + (g.arcs.getD i default).fmin)

/-- The gate equation at time `τ` with reads at `τ - fmin`. -/
def eqAtL (enc : Nat → Option (Bool × List Nat)) (g : Gate) (τ : Nat) : Bool :=
  sigL (enc g.out) τ == g.init.testBit (addr g.k fun i => sigL (enc (g.ins.getD i 0)) (τ - (g.arcs.getD i default).fmin))

/-- The finite check: at the gate's start and at every breakpoint past it. -/
def gateWL (enc : Nat → Option (Bool × List Nat)) (g : Gate) : Bool :=
  (startN g :: bpsL enc g).all fun τ => decide (τ < startN g) || eqAtL enc g τ

theorem gateOK_of_gateWL (enc : Nat → Option (Bool × List Nat)) (g : Gate)
    (harc : ∀ i, i < g.k → (g.arcs.getD i default).fmin ≤ (g.arcs.getD i default).fmax)
    (hd : ∀ i, i < g.k → (g.arcs.getD i default).fmin ≤ startN g)
    (hc : gateWL enc g = true) : GateOK p1 0 g (fun n => sigL (enc n)) := by
  refine ⟨fun i t => t - (g.arcs.getD i default).fmin, fun i _ a b hab => by dsimp only; omega, fun t ht => ?_⟩
  rw [start_p1] at ht
  change startN g ≤ t at ht
  refine ⟨fun i hi => ⟨by dsimp only; omega, ?_⟩, ?_⟩
  all_goals dsimp only
  · have hdi := hd i hi
    rw [show t - (t - (g.arcs.getD i default).fmin) = (g.arcs.getD i default).fmin by omega]
    simp only [Adm, p1, sub_zero, add_zero, one_mul, div_one, mul_one, lerp, zero_mul, add_zero]
    refine ⟨by simp, ?_⟩
    exact_mod_cast harc i hi
  · obtain ⟨a, b, c, d⟩ := lastBp_spec (startN g) t ht (bpsL enc g)
    set τ := lastBp (startN g) t (bpsL enc g)
    have hτ : eqAtL enc g τ = true := by
      have hm : τ ∈ startN g :: bpsL enc g := by
        rcases c with c | c
        · rw [c]; exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ c
      have := List.all_eq_true.mp hc τ hm
      simp only [Bool.or_eq_true, decide_eq_true_eq] at this
      rcases this with h | h
      · omega
      · exact h
    simp only [eqAtL, beq_iff_eq] at hτ
    have hout : sigL (enc g.out) t = sigL (enc g.out) τ := by
      apply sigL_eq; intro θ hθ
      exact d θ (by simp only [bpsL, List.mem_append]; exact Or.inl hθ)
    rw [hout, hτ]
    congr 1
    apply addr_congr
    intro i hi
    apply sigL_eq
    intro θ hθ
    have hdi := hd i hi
    have := d (θ + (g.arcs.getD i default).fmin) (by
      simp only [bpsL, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_map]
      exact Or.inr ⟨i, hi, θ, hθ, rfl⟩)
    constructor
    · intro h; have := this.mp (by omega); omega
    · intro h; have := this.mpr (by omega); omega

end Formal.Net.CViewPS
