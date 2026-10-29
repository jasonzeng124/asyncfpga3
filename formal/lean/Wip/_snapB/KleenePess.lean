import Formal.Cells.MuxTree
import Formal.Cells.ArbKleene
import Formal.Cells.Latch
import Formal.Cells.LibGapLatch

/-!
# KleenePess: pessimistic LUT models below H_KLEENE_LUT, and which cell results survive

Probe Bpess (shard B; audit row 88, `audit/findings/P8.md` section 2).
`Prelim.lutK` (Core's mux tree, `K3.mux` at every node: an `x` select passes a
value iff both legs carry it) is the EXACT hazard-free ternary closure
(`MuxTree.lutK_eq_closure`): the optimistic end. This file puts a family of
pessimistic models below it and re-checks the key shard-B cell results.

## The family (one 2:1 pass-transistor mux, select `x`)

A policy `Pol = ⟨p0, p1⟩` says which equal-leg value an `x`-select mux passes
(output-referred: an inverting buffer between the mux and the LUT output is
folded into the policy):
* `kle  = ⟨1,1⟩`: both (H_KLEENE_LUT; `muxP_kle`: it IS `K3.mux`).
* `weak1 = ⟨1,0⟩`: NMOS pass tree whose weak level (an NMOS passes 1 only to
  `V_G - V_t`, see `notes/B-muxtree-fidelity.md` §3) is the output's 1: equal
  0 legs pass, equal 1 legs may give a runt / mid-rail level (`x`).
* `weak0 = ⟨0,1⟩`: the same tree behind an inverting output stage (weak level
  is the output's 0). Which of the two the 7-series LUT is, is not public.
* `strict = ⟨0,0⟩`: an `x` select gives `x` whatever the legs (P1).
A policy is attached PER PIN (`pol : Nat → Pol`, the level that pin's buffer
drives; re-buffering inside the tree may flip the polarity between levels), and
the tree may split on the pins in ANY order (`MuxTree.build`, e.g. A6 at the
output mux as on silicon).

Retention variant (`lutR`, H_RETAIN): a LUT output that already shows the
closure value keeps it (the level restorer holds a node that is not driven
away; the note's case "legs both 1, node already 1"). It sits between `lutM`
and `lutK`.

## Results

* `muxP_mono`, `evalP_mono`, `bracket`: strict ⊑ any per-pin policy ⊑ Kleene,
  in the information order, for every read-once tree in any order and every
  K3 input (and monotone in the inputs).
* `lutP_definite` (**exactness**): for ANY per-pin policy and ANY split order
  (permutation), the LUT output is definite `v` iff the Kleene closure is `v`
  AND every pin that reads `x` has a level that passes `v`. Consequences:
  `lutP_eq_lutM` (the model depends neither on the order nor on the tree,
  only on which (pin, value) pairs pass), `strict_iff` (strict: definite iff no
  pin is `x`).
* `transfer`: a definite model value is the Kleene value. So every SAFETY
  result of the form "never a definite wrong value / never both 1" transfers
  to every model (e.g. `excl_M`, `arb_run_le`), and every `x` of the Kleene
  simulation stays `x`.
* Cells: `c2M_restore`, `c2M_hold_qx`, `c2nM_restore`, `c2M_rst`, `oddM_*`,
  `rstM_*`, arbiter `g1M_qx`, `hold_shields_M`, `arb_restore_M`, the nine
  ternary-simulation scenarios of `ArbKleene` under each model, KleeneBox
  pointwise lemmas `outKM_sel_weak1` (survives) and the counter-runs
  `steer_fails_M`, `join_fails_weak1`, `join_fails_weak0`, `latch_fails_M`.

Assumed: only the definitions (each model is a hypothesis about one 2:1 mux,
plus "a LUT is a full read-once mux tree", as in MuxTree). NOT covered: which
model silicon follows (that is the experiment of `notes/B-kleene-pess.md`);
timing of the runt (a model `x` means "may be a runt or mid-rail", not "is");
internal-node state (H_RETAIN is at the LUT output only).

Core Lean only.
-/

namespace Formal.Cells
namespace KleenePess

open MuxTree

local infix:50 " ⊑ " => Formal.Core.K3.Le

/-! ## 1. Policies and the 2:1 mux -/

/-- Which equal-leg value an `x`-select mux passes (output-referred). -/
structure Pol where
  p0 : Bool
  p1 : Bool
  deriving DecidableEq, Repr

namespace Pol
def pass (p : Pol) : K3 → Bool
  | .zero => p.p0
  | .one => p.p1
  | .X => false
/-- Pointwise order on policies (more values passed = more optimistic). -/
def Le (p q : Pol) : Prop := (p.p0 = true → q.p0 = true) ∧ (p.p1 = true → q.p1 = true)
end Pol

/-- H_KLEENE_LUT. -/
def kle : Pol := ⟨true, true⟩
/-- NMOS tree, weak level = output 1: only equal-0 legs pass. -/
def weak1 : Pol := ⟨true, false⟩
/-- NMOS tree behind an inverting stage, weak level = output 0. -/
def weak0 : Pol := ⟨false, true⟩
/-- P1: an `x` select gives `x`. -/
def strict : Pol := ⟨false, false⟩

/-- The 2:1 mux under policy `p`. -/
def muxP (p : Pol) (s a b : K3) : K3 :=
  match s with
  | .zero => a
  | .one => b
  | .X => if a = b ∧ p.pass a = true then a else .X

theorem muxP_kle (s a b : K3) : muxP kle s a b = K3.mux s a b := by
  cases s <;> cases a <;> cases b <;> rfl

theorem muxP_mono_all : ∀ (p0 p1 q0 q1 : Bool) (s s' a a' b b' : K3),
    ((p0 = true → q0 = true) ∧ (p1 = true → q1 = true)) → s ⊑ s' → a ⊑ a' → b ⊑ b' →
      muxP ⟨p0, p1⟩ s a b ⊑ muxP ⟨q0, q1⟩ s' a' b' := by
  decide

theorem muxP_mono {p q : Pol} (h : p.Le q) {s s' a a' b b' : K3}
    (hs : s ⊑ s') (ha : a ⊑ a') (hb : b ⊑ b') : muxP p s a b ⊑ muxP q s' a' b' := by
  rcases p with ⟨p0, p1⟩; rcases q with ⟨q0, q1⟩
  exact muxP_mono_all p0 p1 q0 q1 s s' a a' b b' h hs ha hb

theorem muxP_X_ofBool (p : Pol) (a b : K3) (v : Bool) :
    muxP p .X a b = K3.ofBool v ↔ a = K3.ofBool v ∧ b = K3.ofBool v ∧ p.pass (K3.ofBool v) = true := by
  rcases p with ⟨p0, p1⟩
  cases p0 <;> cases p1 <;> cases a <;> cases b <;> cases v <;> decide

theorem mux_X_ofBool (a b : K3) (v : Bool) :
    K3.mux .X a b = K3.ofBool v ↔ a = K3.ofBool v ∧ b = K3.ofBool v := by
  cases a <;> cases b <;> cases v <;> decide

theorem Pol.le_kle (p : Pol) : p.Le kle := ⟨fun _ => rfl, fun _ => rfl⟩
theorem Pol.strict_le (p : Pol) : strict.Le p := ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
theorem Pol.le_refl (p : Pol) : p.Le p := ⟨id, id⟩

/-! ## 2. Trees under a per-pin policy -/

/-- Evaluation of a mux tree with the policy `pol i` at every mux selected by pin `i`. -/
def evalP (pol : Nat → Pol) (ins : List K3) : Tree → K3
  | .leaf b => K3.ofBool b
  | .node i lo hi => muxP (pol i) (ins.getD i .X) (evalP pol ins lo) (evalP pol ins hi)

theorem evalP_kle (ins : List K3) (T : Tree) : evalP (fun _ => kle) ins T = T.evalK ins := by
  induction T with
  | leaf b => rfl
  | node i lo hi ihl ihh => simp only [evalP, Tree.evalK, ihl, ihh, muxP_kle]

/-- Monotone in the policy and in the inputs. -/
theorem evalP_mono {pol pol' : Nat → Pol} (hp : ∀ i, (pol i).Le (pol' i))
    {ins ins' : List K3} (hi : ∀ i, ins.getD i .X ⊑ ins'.getD i .X) (T : Tree) :
    evalP pol ins T ⊑ evalP pol' ins' T := by
  induction T with
  | leaf b => exact Formal.Core.K3.le_refl _
  | node i lo hi' ihl ihh => exact muxP_mono (hp i) (hi i) ihl ihh

/-- The LUT as the tree that splits on `order` (head = output mux). -/
def lutP (pol : Nat → Pol) (order : List Nat) (init : Nat) (ins : List K3) : K3 :=
  evalP pol ins (build (lutB init) order (List.replicate ins.length false))

/-- Uniform policy. -/
abbrev U (p : Pol) : Nat → Pol := fun _ => p

/-- **Bracket.** For every permutation `order` and every per-pin policy:
strict ⊑ model ⊑ Kleene (`lutK`, H_KLEENE_LUT). -/
theorem bracket (pol : Nat → Pol) (order : List Nat) (init : Nat) (ins : List K3)
    (hnd : order.Nodup) (hcov : ∀ j, j ∈ order ↔ j < ins.length) :
    lutP (U strict) order init ins ⊑ lutP pol order init ins ∧
      lutP pol order init ins ⊑ lutK init ins := by
  unfold lutP
  refine ⟨evalP_mono (fun i => Pol.strict_le _) (fun _ => Formal.Core.K3.le_refl _) _, ?_⟩
  rw [← build_evalK_eq_lutK init ins order hnd hcov, ← evalP_kle]
  exact evalP_mono (fun i => Pol.le_kle _) (fun _ => Formal.Core.K3.le_refl _) _

/-! ## 3. Exactness: which outputs stay definite -/

theorem evalP_build_def (pol : Nat → Pol) (ins : List K3) (G : List Bool → Bool) (v : Bool) :
    ∀ (o : List Nat) (acc : List Bool),
      evalP pol ins (build G o acc) = K3.ofBool v ↔
        (build G o acc).evalK ins = K3.ofBool v ∧
          ∀ j ∈ o, ins.getD j .X = .X → (pol j).pass (K3.ofBool v) = true := by
  intro o
  induction o with
  | nil => intro acc; simp [build, evalP, Tree.evalK]
  | cons j o ih =>
    intro acc
    simp only [build, evalP, Tree.evalK, List.forall_mem_cons]
    generalize hs : ins.getD j .X = s
    cases s with
    | zero =>
      simp only [muxP, K3.mux]
      rw [ih]; simp
    | one =>
      simp only [muxP, K3.mux]
      rw [ih]; simp
    | X =>
      rw [muxP_X_ofBool, mux_X_ofBool, ih, ih]
      simp only [forall_const]
      constructor
      · rintro ⟨⟨h1, h2⟩, ⟨h3, _⟩, h5⟩; exact ⟨⟨h1, h3⟩, h5, h2⟩
      · rintro ⟨⟨h1, h3⟩, h5, h2⟩; exact ⟨⟨h1, h2⟩, ⟨h3, h2⟩, h5⟩

/-- **Exactness (any per-pin policy, any split order).** The model output is
the definite value `v` iff the Kleene closure is `v` and every pin reading `x`
sits on a level that passes `v`. -/
theorem lutP_definite (pol : Nat → Pol) (order : List Nat) (init : Nat) (ins : List K3)
    (hnd : order.Nodup) (hcov : ∀ j, j ∈ order ↔ j < ins.length) (v : Bool) :
    lutP pol order init ins = K3.ofBool v ↔
      lutK init ins = K3.ofBool v ∧
        ∀ j, j < ins.length → ins.getD j .X = .X → (pol j).pass (K3.ofBool v) = true := by
  unfold lutP
  rw [evalP_build_def, build_evalK_eq_lutK init ins order hnd hcov]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj => h2 j ((hcov j).2 hj)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj => h2 j ((hcov j).1 hj)⟩

/-- The closed form: Kleene value if every `x` pin passes it, else `x`. -/
def lutM (pol : Nat → Pol) (init : Nat) (ins : List K3) : K3 :=
  if lutK init ins ≠ .X ∧ ∀ j, j < ins.length → ins.getD j .X = .X → (pol j).pass (lutK init ins) = true
  then lutK init ins else .X

theorem lutM_definite (pol : Nat → Pol) (init : Nat) (ins : List K3) (v : Bool) :
    lutM pol init ins = K3.ofBool v ↔
      lutK init ins = K3.ofBool v ∧
        ∀ j, j < ins.length → ins.getD j .X = .X → (pol j).pass (K3.ofBool v) = true := by
  unfold lutM
  generalize lutK init ins = k
  split
  · rename_i hc
    constructor
    · intro h; subst h; exact ⟨rfl, hc.2⟩
    · rintro ⟨h1, _⟩; exact h1
  · rename_i hc
    constructor
    · intro h; exact absurd h.symm (Formal.Core.K3.ofBool_ne_X v)
    · rintro ⟨h1, h2⟩
      subst h1
      exact absurd ⟨Formal.Core.K3.ofBool_ne_X v, h2⟩ hc

theorem k3_ext {a b : K3} (h : ∀ v : Bool, a = K3.ofBool v ↔ b = K3.ofBool v) : a = b := by
  have h0 := h false; have h1 := h true
  cases a <;> cases b <;> simp_all [K3.ofBool]

/-- The model does not depend on the tree order: it is `lutM`. -/
theorem lutP_eq_lutM (pol : Nat → Pol) (order : List Nat) (init : Nat) (ins : List K3)
    (hnd : order.Nodup) (hcov : ∀ j, j ∈ order ↔ j < ins.length) :
    lutP pol order init ins = lutM pol init ins :=
  k3_ext fun v => (lutP_definite pol order init ins hnd hcov v).trans (lutM_definite pol init ins v).symm

theorem range_cov (n : Nat) : ∀ j, j ∈ List.range n ↔ j < n := fun j => by simp

theorem lutM_eq_lutP (pol : Nat → Pol) (init : Nat) (ins : List K3) :
    lutM pol init ins = lutP pol (List.range ins.length) init ins :=
  (lutP_eq_lutM pol _ init ins (List.nodup_range) (range_cov _)).symm

/-- Kleene IS the `kle` model. -/
theorem lutM_kle (init : Nat) (ins : List K3) : lutM (U kle) init ins = lutK init ins := by
  rw [lutM_eq_lutP, lutP, evalP_kle,
    build_evalK_eq_lutK init ins _ List.nodup_range (range_cov _)]

/-- Bracket for the closed form, with monotonicity in the inputs (same length). -/
theorem lutM_mono {pol pol' : Nat → Pol} (hp : ∀ i, (pol i).Le (pol' i)) (init : Nat)
    {ins ins' : List K3} (hl : ins.length = ins'.length)
    (hi : ∀ i, ins.getD i .X ⊑ ins'.getD i .X) :
    lutM pol init ins ⊑ lutM pol' init ins' := by
  rw [lutM_eq_lutP, lutM_eq_lutP, lutP, lutP, hl]
  exact evalP_mono hp hi _

theorem lutM_le_lutK (pol : Nat → Pol) (init : Nat) (ins : List K3) :
    lutM pol init ins ⊑ lutK init ins := by
  rw [← lutM_kle]
  exact lutM_mono (fun i => Pol.le_kle _) init rfl (fun _ => Formal.Core.K3.le_refl _)

theorem lutK_mono (init : Nat) {ins ins' : List K3} (hl : ins.length = ins'.length)
    (hi : ∀ i, ins.getD i .X ⊑ ins'.getD i .X) : lutK init ins ⊑ lutK init ins' := by
  rw [← lutM_kle, ← lutM_kle]; exact lutM_mono (fun _ => Pol.le_refl _) init hl hi

/-- **Transfer.** A definite model value is the Kleene value. -/
theorem transfer {pol : Nat → Pol} {init : Nat} {ins : List K3} {v : Bool}
    (h : lutM pol init ins = K3.ofBool v) : lutK init ins = K3.ofBool v :=
  ((lutM_definite pol init ins v).1 h).1

/-- Strict (P1): definite iff the closure is definite and NO pin reads `x`. -/
theorem strict_iff (init : Nat) (ins : List K3) (v : Bool) :
    lutM (U strict) init ins = K3.ofBool v ↔
      lutK init ins = K3.ofBool v ∧ ∀ j, j < ins.length → ins.getD j .X ≠ .X := by
  rw [lutM_definite]
  constructor
  · rintro ⟨h1, h2⟩; refine ⟨h1, fun j hj hx => ?_⟩
    have := h2 j hj hx; cases v <;> simp [U, strict, Pol.pass, K3.ofBool] at this
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun j hj hx => absurd hx (h2 j hj)⟩

/-- Retention (H_RETAIN): a LUT whose output `prev` already shows the closure keeps it. -/
def lutR (pol : Nat → Pol) (init : Nat) (ins : List K3) (prev : K3) : K3 :=
  if lutK init ins = prev then prev else lutM pol init ins

theorem lutR_between (pol : Nat → Pol) (init : Nat) (ins : List K3) (prev : K3) :
    lutM pol init ins ⊑ lutR pol init ins prev ∧ lutR pol init ins prev ⊑ lutK init ins := by
  unfold lutR
  by_cases h : lutK init ins = prev
  · simp only [h, ite_true]; rw [← h]; exact ⟨lutM_le_lutK _ _ _, Formal.Core.K3.le_refl _⟩
  · simp only [h, ite_false]; exact ⟨Formal.Core.K3.le_refl _, lutM_le_lutK _ _ _⟩

end KleenePess
end Formal.Cells
