-- Bsa4 mutant M03 of Formal/Cells/KleenePess.lean: one change, 'def C2N_INIT : Nat := 0x00B200B200B200B2' -> 'def C2N_INIT : Nat := 0x00B300B300B300B3'. Expected: FAIL.
import Formal.Cells.MuxTree
import Formal.Cells.ArbKleene
import Formal.Cells.Latch
import Formal.Cells.KleeneBox

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
* Cells (each over ALL four uniform policies; `p = kle` is the shard-B lemma):
  C-element `c2M_restore`, `c2M_11x`, `c2M_hold_xin`, `c2M_rst`,
  `c2nM_restore`; latch `oddM_hold`, `oddM_transp`, `oddM_enx`, `rstM_reset`;
  arbiter `excl_M` and `arb_x_held_M` (survive every per-pin model),
  `g1M_qx`, `hold_shields_M`, `arb_restore_M` (new exact conditions),
  `arb_run_le` / `arb_acks_safe` (network bracket), `scen_weak1`, `scen_weak0`,
  `scen_strict`, `scen_weak1r`, `scen_weak0r`, `scen_strictr` (the nine
  `ArbKleene` scenarios under each model; `scen_kle` / `scen_kle_matches` the
  control).
* KleeneBox `+w`: `steer_edges_weak1` (the steer iff holds verbatim under
  `weak1`), `steer_fails_M` (fails without pass-0), `join_fails_weak1`,
  `join_fails_weak0` (the join iff fails under every pessimistic uniform model:
  right side true, model left side false), `latch_pin_ok_M` (latch sufficient
  half iff the token value passes) and `latch_fails_M` (counter-run otherwise).
* Non-vacuity: `bracket_strict_witness`, `steer_witness_weak1`,
  `latch_witness_weak1`, `arb_acks_safe_witness`.

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


/-! ## 4. Cells: `bd_c2`, `bd_c2n`, `bd_latch` (uniform policy `p`; per-pin forms follow from
`lutM_definite` the same way)

Every statement is over ALL policies `p` (all four `⟨p0, p1⟩`); `p = kle` gives
back the shard-B Kleene lemma it is named after. -/

open ArbKleene (ST_INIT GR_INIT CS_INIT C2_INIT)

/-- `bd_c2n` (C(a,~b), comes up at 0), `cells/rtl/bd_ce.v`: I0=a I1=b I2=q I3=rst. -/
def C2N_INIT : Nat := 0x00B300B300B300B3

def c2M (p : Pol) (a b q rst : K3) : K3 := lutM (U p) C2_INIT [a, b, q, rst, .f, .f]
def c2nM (p : Pol) (a b q rst : K3) : K3 := lutM (U p) C2N_INIT [a, b, q, rst, .f, .f]

/-- `ArbKleene.c_restore_iff` under `p`: with an `x` on its own feedback the
C-element is definite iff both inputs are equal and definite AND that value
passes. -/
theorem c2M_restore (p : Pol) (a b : K3) :
    c2M p a b .x .f ≠ .x ↔ (a = b ∧ a ≠ .x ∧ p.pass a = true) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases a <;> cases b <;> decide

/-- The audit's example: `C2(1,1,X) = 1` holds iff equal-1 legs pass. -/
theorem c2M_11x (p : Pol) : c2M p .t .t .x .f = (if p.p1 then .t else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide

/-- `ArbKleene.c_x_left` under `p`: X on input `a`, the held value survives iff
it equals `b` and passes. -/
theorem c2M_hold_xin (p : Pol) (b q : K3) :
    c2M p .x b q .f = (if q = b ∧ b ≠ .x ∧ p.pass q = true then q else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases b <;> cases q <;> decide

/-- `ArbKleene.c_rst` under `p`: reset forces 0 under X elsewhere iff 0 passes. -/
theorem c2M_rst (p : Pol) (a b q : K3) :
    c2M p a b q .t = (if p.p0 = true ∨ (a ≠ .x ∧ b ≠ .x ∧ q ≠ .x) then .f else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases a <;> cases b <;> cases q <;> decide

/-- `bd_c2n` restore under `p`. -/
theorem c2nM_restore (p : Pol) (a b : K3) :
    c2nM p a b .x .f ≠ .x ↔ (a = K3.not b ∧ a ≠ .x ∧ p.pass a = true) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases a <;> cases b <;> decide

/-- `bd_latch` odd bit (`Latch.ODD`, I0=d I1=en I2=q). -/
def oddM (p : Pol) (d e q : K3) : K3 := lutM (U p) Latch.ODD [d, e, q, .f, .f, .f]
/-- `bd_latch_rst` (`Latch.RST0`/`RST1`, I3=rst). -/
def rstM (p : Pol) (init : Nat) (d e q rst : K3) : K3 := lutM (U p) init [d, e, q, rst, .f, .f]

/-- Hold (en = 0): the stored value survives an X on d iff it passes. -/
theorem oddM_hold (p : Pol) (d q : K3) :
    oddM p d .f q = (if q ≠ .x ∧ (d ≠ .x ∨ p.pass q = true) then q else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases d <;> cases q <;> decide

/-- Transparent (en = 1): d is passed with an X on the feedback iff it passes. -/
theorem oddM_transp (p : Pol) (d q : K3) :
    oddM p d .t q = (if d ≠ .x ∧ (q ≠ .x ∨ p.pass d = true) then d else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases d <;> cases q <;> decide

/-- X on en with d = q: definite iff the value passes. -/
theorem oddM_enx (p : Pol) (v : Bool) :
    oddM p (K3.ofBool v) .x (K3.ofBool v) = (if p.pass (K3.ofBool v) then K3.ofBool v else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases v <;> decide

/-- Reset of `bd_latch_rst` with X on d, en, q: the reset value survives iff it passes. -/
theorem rstM_reset (p : Pol) (d e q : K3) :
    rstM p Latch.RST0 d e q .t = (if p.p0 = true ∨ (d ≠ .x ∧ e ≠ .x ∧ q ≠ .x) then .f else .x) ∧
    rstM p Latch.RST1 d e q .t = (if p.p1 = true ∨ (d ≠ .x ∧ e ≠ .x ∧ q ≠ .x) then .t else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases d <;> cases e <;> cases q <;> decide

/-! ## 5. Arbiter (`bd_arbiter`: `ustate` FFF0_FFB2_ACAC_ACAC, `ugrant` 0C0C_0C0C_A0A0_A0A0) -/

def o5M (pol : Nat → Pol) (init : Nat) (ins : List K3) : K3 := lutM pol (init % 2 ^ 32) (ins.take 5)

def g1M (pol : Nat → Pol) (r1 r2 q : K3) : K3 := o5M pol GR_INIT [r1, r2, q, .f, .f, .t]
def g2M (pol : Nat → Pol) (r1 r2 q : K3) : K3 := lutM pol GR_INIT [r1, r2, q, .f, .f, .t]
def qArbM (pol : Nat → Pol) (r1 r2 q rst a0 : K3) : K3 := lutM pol ST_INIT [r1, r2, q, rst, a0, .t]

/-- **Exclusion survives every model** (any per-pin policy, any tree order):
never both grants definite 1. -/
theorem excl_M (pol : Nat → Pol) (r1 r2 q : K3) : ¬ (g1M pol r1 r2 q = .t ∧ g2M pol r1 r2 q = .t) := by
  rintro ⟨h1, h2⟩
  exact ArbKleene.kleene_exclusion r1 r2 q ⟨transfer (v := true) h1, transfer (v := true) h2⟩

/-- `ArbKleene.arb_x_held` survives every model: x on q stays x on every hold input. -/
theorem arb_x_held_M (pol : Nat → Pol) (r1 r2 a0 : K3) (h : a0 = .t ∨ r1 = r2) :
    qArbM pol r1 r2 .x .f a0 = .x := by
  have hK := ArbKleene.arb_x_held r1 r2 a0 h
  have hle := lutM_le_lutK pol ST_INIT [r1, r2, .x, .f, a0, .t]
  rcases hle with hle | hle
  · exact hle
  · exact hle.trans hK

/-- `ArbKleene.g1_qx` under `p`: x on q reaches g1 unless r1 = 0 AND 0 passes. -/
theorem g1M_qx (p : Pol) (r1 r2 : K3) :
    g1M (U p) r1 r2 .x = (if r1 = .f ∧ p.p0 = true then .f else .x) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases r1 <;> cases r2 <;> decide

/-- `ArbKleene.hold_shields` under `p` (A0 = 1, q definite): x on a request
leaves q alone iff q's value passes. -/
theorem hold_shields_M (p : Pol) (r1 r2 q : K3) (hq : q ≠ .x) :
    qArbM (U p) r1 r2 q .f .t = (if (r1 ≠ .x ∧ r2 ≠ .x) ∨ p.pass q = true then q else .x) := by
  revert hq
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> cases r1 <;> cases r2 <;> cases q <;> decide

/-- `ArbKleene.arb_restore_iff` under `p`: from q = x the state is restored to 1
only if 1 passes, to 0 only if 0 passes (q itself is the x pin). -/
theorem arb_restore_M (p : Pol) (r1 r2 rst a0 : K3) :
    qArbM (U p) r1 r2 .x rst a0 ≠ .x ↔
      (((rst = .t ∨ (a0 = .f ∧ r1 = .t ∧ r2 = .f)) ∧ p.p1 = true) ∨
        (rst = .f ∧ a0 = .f ∧ r1 = .f ∧ r2 = .t ∧ p.p0 = true)) := by
  rcases p with ⟨p0, p1⟩
  cases p0 <;> cases p1 <;> cases r1 <;> cases r2 <;> cases rst <;> cases a0 <;> decide

/-! ### The arbiter network under any LUT evaluator below Kleene

`E init ins prev` is a LUT semantics (`prev` = the LUT's present output, for
the retention model). `stepE` is `ArbKleene.step` with every LUT replaced by
`E`, same pins, same Jacobi unit-delay iteration. -/

open ArbKleene (Net Inp I idle1 own1 served1 done1)

def stepE (E : Nat → List K3 → K3 → K3) (i : Inp) (s : Net) : Net where
  q := E ST_INIT [i.r1, i.r2, s.q, i.rst, i.a0, .t] s.q
  r0 := E (ST_INIT % 2 ^ 32) [i.r1, i.r2, s.q, i.rst, i.a0] s.r0
  g1 := E (GR_INIT % 2 ^ 32) [i.r1, i.r2, s.q, .f, .f] s.g1
  g2 := E GR_INIT [i.r1, i.r2, s.q, .f, .f, .t] s.g2
  a1 := E C2_INIT [s.g1, i.a0c, s.a1, i.rst, .f, .f] s.a1
  a2 := E C2_INIT [s.g2, i.a0c, s.a2, i.rst, .f, .f] s.a2

def settleE (E : Nat → List K3 → K3 → K3) : Nat → Inp → Net → Net
  | 0, _, s => s
  | n + 1, i, s => settleE E n i (stepE E i s)

def runE (E : Nat → List K3 → K3 → K3) (k : Nat) : List Inp → Net → Net
  | [], s => s
  | i :: is, s => runE E k is (settleE E k i s)

/-- Kleene, static model, retention model. -/
def EK : Nat → List K3 → K3 → K3 := fun init ins _ => lutK init ins
def EM (p : Pol) : Nat → List K3 → K3 → K3 := fun init ins _ => lutM (U p) init ins
def ER (p : Pol) : Nat → List K3 → K3 → K3 := fun init ins prev => lutR (U p) init ins prev

theorem stepE_EK (i : Inp) (s : Net) : stepE EK i s = ArbKleene.step i s := rfl

theorem settleE_EK (n : Nat) (i : Inp) (s : Net) : settleE EK n i s = ArbKleene.settle n i s := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => exact ih _

theorem runE_EK (k : Nat) (is : List Inp) (s : Net) : runE EK k is s = ArbKleene.run k is s := by
  induction is generalizing s with
  | nil => rfl
  | cons i is ih => simp only [runE, ArbKleene.run, settleE_EK, ih]

def NetLe (s s' : Net) : Prop :=
  s.q ⊑ s'.q ∧ s.g1 ⊑ s'.g1 ∧ s.g2 ⊑ s'.g2 ∧ s.r0 ⊑ s'.r0 ∧ s.a1 ⊑ s'.a1 ∧ s.a2 ⊑ s'.a2

/-- A LUT semantics below Kleene. -/
def Below (E : Nat → List K3 → K3 → K3) : Prop := ∀ init ins prev, E init ins prev ⊑ lutK init ins

theorem below_EM (p : Pol) : Below (EM p) := fun init ins _ => lutM_le_lutK _ init ins
theorem below_ER (p : Pol) : Below (ER p) := fun init ins prev => (lutR_between _ init ins prev).2

theorem getD_le5 {a b c d e a' b' c' d' e' : K3} (ha : a ⊑ a') (hb : b ⊑ b') (hc : c ⊑ c')
    (hd : d ⊑ d') (he : e ⊑ e') :
    ∀ i, [a, b, c, d, e].getD i .X ⊑ [a', b', c', d', e'].getD i .X
  | 0 => ha | 1 => hb | 2 => hc | 3 => hd | 4 => he
  | _ + 5 => Formal.Core.K3.le_refl _

theorem getD_le6 {a b c d e g a' b' c' d' e' g' : K3} (ha : a ⊑ a') (hb : b ⊑ b') (hc : c ⊑ c')
    (hd : d ⊑ d') (he : e ⊑ e') (hg : g ⊑ g') :
    ∀ i, [a, b, c, d, e, g].getD i .X ⊑ [a', b', c', d', e', g'].getD i .X
  | 0 => ha | 1 => hb | 2 => hc | 3 => hd | 4 => he | 5 => hg
  | _ + 6 => Formal.Core.K3.le_refl _

theorem step_le {E : Nat → List K3 → K3 → K3} (hE : Below E) (i : Inp) {s s' : Net}
    (h : NetLe s s') : NetLe (stepE E i s) (ArbKleene.step i s') := by
  obtain ⟨hq, hg1, hg2, _, ha1, ha2⟩ := h
  have r := Formal.Core.K3.le_refl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Formal.Core.K3.le_trans (hE _ _ _) (lutK_mono _ rfl (getD_le6 (r _) (r _) hq (r _) (r _) (r _)))
  · exact Formal.Core.K3.le_trans (hE _ _ _) (lutK_mono _ rfl (getD_le5 (r _) (r _) hq (r _) (r _)))
  · exact Formal.Core.K3.le_trans (hE _ _ _) (lutK_mono _ rfl (getD_le6 (r _) (r _) hq (r _) (r _) (r _)))
  · exact Formal.Core.K3.le_trans (hE _ _ _) (lutK_mono _ rfl (getD_le5 (r _) (r _) hq (r _) (r _)))
  · exact Formal.Core.K3.le_trans (hE _ _ _) (lutK_mono _ rfl (getD_le6 hg1 (r _) ha1 (r _) (r _) (r _)))
  · exact Formal.Core.K3.le_trans (hE _ _ _) (lutK_mono _ rfl (getD_le6 hg2 (r _) ha2 (r _) (r _) (r _)))

theorem settle_le {E : Nat → List K3 → K3 → K3} (hE : Below E) (n : Nat) (i : Inp) {s s' : Net}
    (h : NetLe s s') : NetLe (settleE E n i s) (ArbKleene.settle n i s') := by
  induction n generalizing s s' with
  | zero => exact h
  | succ n ih => exact ih (step_le hE i h)

/-- **Network bracket.** Under any LUT semantics below Kleene (every static
model, every retention model), the ternary simulation of `bd_arbiter` is below
the Kleene simulation, step by step from any states below. So every `x` of
`ArbKleene`'s scenarios stays `x`, and every definite model value is the
Kleene value. -/
theorem arb_run_le {E : Nat → List K3 → K3 → K3} (hE : Below E) (k : Nat) (is : List Inp)
    {s s' : Net} (h : NetLe s s') : NetLe (runE E k is s) (ArbKleene.run k is s') := by
  induction is generalizing s s' with
  | nil => exact h
  | cons i is ih => exact ih (settle_le hE k i h)

/-- Consequence: no model run ever has both acks definite 1 where Kleene does not. -/
theorem arb_acks_safe {E : Nat → List K3 → K3 → K3} (hE : Below E) (k : Nat) (is : List Inp) (s : Net)
    (hK : ¬ ((ArbKleene.run k is s).a1 = .t ∧ (ArbKleene.run k is s).a2 = .t)) :
    ¬ ((runE E k is s).a1 = .t ∧ (runE E k is s).a2 = .t) := by
  have h := arb_run_le hE k is (s := s) (s' := s) ⟨Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl, Or.inr rfl⟩
  obtain ⟨_, _, _, _, h5, h6⟩ := h
  rintro ⟨e1, e2⟩
  apply hK
  rw [e1] at h5; rw [e2] at h6
  exact ⟨(h5.resolve_left (by decide)).symm, (h6.resolve_left (by decide)).symm⟩

/-! ### The nine `ArbKleene` scenarios under each model (same input sequences) -/

def allX : Net := ⟨.x, .x, .x, .x, .x, .x⟩

def scReset (E : Nat → List K3 → K3 → K3) : Net := settleE E 4 (I .f .f .f .t) allX
def scRuntOppA (E : Nat → List K3 → K3 → K3) : Net := settleE E 3 (I .x .x .f .f) own1
def scRuntOppB (E : Nat → List K3 → K3 → K3) : Net := runE E 3 [I .x .x .f .f, I .f .t .f .f] own1
def scRuntHeld (E : Nat → List K3 → K3 → K3) : Net := settleE E 3 (I .x .x .t .f) served1
def scTieRising (E : Nat → List K3 → K3 → K3) : Net := runE E 3 [I .x .x .f .f, I .t .t .f .f] idle1
def scTieAcked (E : Nat → List K3 → K3 → K3) : Net :=
  runE E 3 [I .x .x .f .f, I .t .t .f .f, I .t .t .x .f, I .t .t .t .f] idle1
def scA0Skewed (E : Nat → List K3 → K3 → K3) : Net := runE E 3 [I .f .t .x .f, I .f .t .f .f] done1
def scA0Ordered (E : Nat → List K3 → K3 → K3) : Net :=
  runE E 3 [⟨.f, .t, .t, .x, .f⟩, ⟨.f, .t, .t, .f, .f⟩, ⟨.f, .t, .x, .f, .f⟩, ⟨.f, .t, .f, .f, .f⟩] done1
def scA0Runt (E : Nat → List K3 → K3 → K3) : Net :=
  runE E 3 [⟨.f, .t, .t, .x, .f⟩, ⟨.f, .t, .t, .f, .f⟩, ⟨.x, .t, .x, .f, .f⟩, ⟨.t, .t, .f, .f, .f⟩] done1

set_option maxRecDepth 20000

theorem scen_weak1 :
    scReset (EM weak1) = ⟨.x, .f, .f, .f, .f, .f⟩ ∧
    scRuntOppA (EM weak1) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scRuntOppB (EM weak1) = ⟨.f, .f, .t, .t, .f, .f⟩ ∧
    scRuntHeld (EM weak1) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scTieRising (EM weak1) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scTieAcked (EM weak1) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Skewed (EM weak1) = ⟨.f, .f, .t, .t, .f, .x⟩ ∧
    scA0Ordered (EM weak1) = ⟨.f, .f, .t, .t, .f, .f⟩ ∧
    scA0Runt (EM weak1) = ⟨.x, .x, .x, .x, .f, .f⟩ := by decide

theorem scen_weak0 :
    scReset (EM weak0) = ⟨.t, .f, .f, .f, .x, .x⟩ ∧
    scRuntOppA (EM weak0) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scRuntOppB (EM weak0) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scRuntHeld (EM weak0) = ⟨.t, .x, .x, .x, .t, .x⟩ ∧
    scTieRising (EM weak0) = ⟨.x, .x, .x, .t, .x, .x⟩ ∧
    scTieAcked (EM weak0) = ⟨.x, .x, .x, .t, .x, .x⟩ ∧
    scA0Skewed (EM weak0) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Ordered (EM weak0) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Runt (EM weak0) = ⟨.x, .x, .x, .t, .x, .x⟩ := by decide

theorem scen_strict :
    scReset (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scRuntOppA (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scRuntOppB (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scRuntHeld (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scTieRising (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scTieAcked (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Skewed (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Ordered (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Runt (EM strict) = ⟨.x, .x, .x, .x, .x, .x⟩ := by decide

theorem scen_kle :
    scReset (EM kle) = ⟨.t, .f, .f, .f, .f, .f⟩ ∧
    scRuntOppA (EM kle) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scRuntOppB (EM kle) = ⟨.f, .f, .t, .t, .f, .f⟩ ∧
    scRuntHeld (EM kle) = ⟨.t, .x, .f, .x, .t, .f⟩ ∧
    scTieRising (EM kle) = ⟨.x, .x, .x, .t, .f, .f⟩ ∧
    scTieAcked (EM kle) = ⟨.x, .x, .x, .t, .x, .x⟩ ∧
    scA0Skewed (EM kle) = ⟨.f, .f, .t, .t, .f, .x⟩ ∧
    scA0Ordered (EM kle) = ⟨.f, .f, .t, .t, .f, .f⟩ ∧
    scA0Runt (EM kle) = ⟨.x, .x, .x, .t, .f, .f⟩ := by decide

theorem scen_weak1r :
    scReset (ER weak1) = ⟨.x, .f, .f, .f, .f, .f⟩ ∧
    scRuntOppA (ER weak1) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scRuntOppB (ER weak1) = ⟨.f, .f, .t, .t, .f, .f⟩ ∧
    scRuntHeld (ER weak1) = ⟨.t, .x, .f, .x, .t, .f⟩ ∧
    scTieRising (ER weak1) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scTieAcked (ER weak1) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Skewed (ER weak1) = ⟨.f, .f, .t, .t, .f, .x⟩ ∧
    scA0Ordered (ER weak1) = ⟨.f, .f, .t, .t, .f, .f⟩ ∧
    scA0Runt (ER weak1) = ⟨.x, .x, .x, .x, .f, .f⟩ := by decide

theorem scen_weak0r :
    scReset (ER weak0) = ⟨.t, .f, .f, .f, .x, .x⟩ ∧
    scRuntOppA (ER weak0) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scRuntOppB (ER weak0) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scRuntHeld (ER weak0) = ⟨.t, .x, .f, .x, .t, .f⟩ ∧
    scTieRising (ER weak0) = ⟨.x, .x, .x, .t, .f, .f⟩ ∧
    scTieAcked (ER weak0) = ⟨.x, .x, .x, .t, .x, .x⟩ ∧
    scA0Skewed (ER weak0) = ⟨.x, .f, .x, .x, .x, .x⟩ ∧
    scA0Ordered (ER weak0) = ⟨.x, .f, .x, .x, .x, .f⟩ ∧
    scA0Runt (ER weak0) = ⟨.x, .x, .x, .t, .x, .f⟩ := by decide

theorem scen_strictr :
    scReset (ER strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scRuntOppA (ER strict) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scRuntOppB (ER strict) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scRuntHeld (ER strict) = ⟨.t, .x, .f, .x, .t, .f⟩ ∧
    scTieRising (ER strict) = ⟨.x, .x, .x, .x, .f, .f⟩ ∧
    scTieAcked (ER strict) = ⟨.x, .x, .x, .x, .x, .x⟩ ∧
    scA0Skewed (ER strict) = ⟨.x, .f, .x, .x, .x, .x⟩ ∧
    scA0Ordered (ER strict) = ⟨.x, .f, .x, .x, .x, .f⟩ ∧
    scA0Runt (ER strict) = ⟨.x, .x, .x, .x, .x, .f⟩ := by decide


/-- Control: `EM kle` reproduces `ArbKleene`'s end states (e.g. `sc_runt_held`). -/
theorem scen_kle_matches :
    scRuntHeld (EM kle) = ArbKleene.settle 3 (I .x .x .t .f) served1 ∧
    scTieAcked (EM kle) = ArbKleene.run 3 [I .x .x .f .f, I .t .t .f .f, I .t .t .x .f, I .t .t .t .f] idle1 := by
  decide


/-! ## 6. KleeneBox setup/hold `+w` under the models

`bd_steer` (`8888_8888_2222_2222`, I0=req I1=s I5=1), `bd_mux` joins
(`uj0`/`uj1`), `bd_latch` (ODD). Same traces, read maps and spec as
`KleeneBox`; only the LUT semantics changes. -/

open Formal.Cells.LibGapSteer (Rd Rd.const outK outK_def)
open Formal.Cells.LibCtlMergeMux (INIT_steer steerPinsK INIT_j0 INIT_j1 cK)
open Formal.Cells.KleeneBox (kb kb_inj kgate kgate_kb ReqEdge StabK SpecK SteerSafeB rX sX
  rX_edge sX_stab rX_lo reqEdge_pulse reqEdge_supp stabK_of RestK JSpecK steer_edges_K join_edges_K)

/-- Steer branch `b` under `p` (O5 = req0 when `b = false`, O6 = req1). -/
def outKM (p : Pol) (b : Bool) (r s : K3) : K3 :=
  if b then lutM (U p) INIT_steer (steerPinsK r s) else o5M (U p) INIT_steer (steerPinsK r s)

theorem outKM_kb (p : Pol) : ∀ b r s : Bool, outKM p b (kb r) (kb s) = outK b (kb r) (kb s) := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide

/-- **Steer survives `weak1`** pointwise (`KleeneBox.outK_sel` with `weak1`):
every definite spec value reached with an x pin is a 0. -/
theorem outKM_sel_weak1 : ∀ (b v : Bool) (r s : K3), (r ≠ .f → s = kb v) →
    outKM weak1 b r s = kgate r (v == b) := by decide

/-- ... and fails under every policy that does not pass 0 (`weak0`, `strict`):
request in transit, select definite, UNSELECTED branch. -/
theorem outKM_sel_fails (p : Pol) (hp : p.p0 = false) :
    outKM p false .x (kb true) = .x ∧ kgate .x (true == false) = .f := by
  rcases p with ⟨p0, p1⟩; simp at hp; subst hp; cases p1 <;> decide

def SpecKM (p : Pol) (b v : Bool) (pr ps : Rd) (r s : Int → K3) : Prop :=
  ∀ t, outKM p b (r (pr.σ t)) (s (ps.σ t)) = kgate (r (pr.σ t)) (v == b)

/-- **`KleeneBox.steer_edges_K` holds verbatim under `weak1`** (same right side, `+w`). -/
theorem steer_edges_weak1 (b v : Bool) (Rlo Rhi Slo Shi R F S0 S1 a c : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R < F) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
      ∀ r s, ReqEdge R F a c r → StabK v (S0 + c) (S1 - a) s → SpecKM weak1 b v pr ps r s) ↔
    (S0 + Shi + (a + c) ≤ R + Rlo ∧ F + Rhi + (a + c) ≤ S1 + Slo) := by
  constructor
  · intro h
    have hB : SteerSafeB b v Rlo Rhi Slo Shi (R - a) (F + c) (S0 + c) (S1 - a) := by
      intro pr ps a1 a2 a3 a4 s hs t
      have := h pr ps a1 a2 a3 a4 _ _ (reqEdge_pulse R F a c ha hc) (stabK_of v _ _ s hs) t
      rw [outKM_kb, outK_def, kgate_kb] at this
      exact kb_inj _ _ this
    have := (LibGapSteer.steer_box_exact b v Rlo Rhi Slo Shi (R - a) (F + c) (S0 + c) (S1 - a)
      hR hS (by omega)).mp hB
    omega
  · rintro ⟨h1, h2⟩ pr ps a1 a2 a3 a4 r s hr hs t
    apply outKM_sel_weak1
    intro hrt
    obtain ⟨e1, e2⟩ := reqEdge_supp hr _ hrt
    have := pr.ge t; have := pr.le t; have := ps.ge t; have := ps.le t
    exact hs _ (by omega) (by omega)

/-- **Steer fails under `weak0` / `strict`**: on `KleeneBox.steer_witness_K`'s
own traces (strict margins, X on every edge), where Kleene's spec holds, the
unselected O5 reads x at 1299 (request in its rise window, select definite 1). -/
theorem steer_fails_M (p : Pol) (hp : p.p0 = false) :
    ((500 : Int) + 450 + (1 + 0) ≤ 1000 + 300 ∧ (3000 : Int) + 300 + (1 + 0) ≤ 4000 + 450) ∧
    ReqEdge 1000 3000 1 0 (rX 1000 3000) ∧ StabK true (500 + 0) (4000 - 1) (sX 500 4000) ∧
    SpecK false true (Rd.const 300) (Rd.const 450) (rX 1000 3000) (sX 500 4000) ∧
    ¬ SpecKM p false true (Rd.const 300) (Rd.const 450) (rX 1000 3000) (sX 500 4000) := by
  refine ⟨by decide, rX_edge _ _ (by decide), sX_stab _ _, KleeneBox.steer_witness_K.2.2.2.2.1, ?_⟩
  intro h
  have := h 1299
  revert this
  rcases p with ⟨p0, p1⟩; simp at hp; subst hp; cases p1 <;> decide

/-- Join under `p` (`KleeneBox`'s `jK`, rst read 0). -/
def jKM (p : Pol) (b : Bool) (r c s q : K3) : K3 :=
  if b then lutM (U p) INIT_j1 [r, c, s, q, .f, .f] else lutM (U p) INIT_j0 [r, c, s, q, .f, .f]

def LutEqKM (p : Pol) (b : Bool) (pr pc ps pq : Rd) (r c s j : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → j t = jKM p b (r (pr.σ t)) (c (pc.σ t)) (s (ps.σ t)) (j (pq.σ t))

/-- The left side of `KleeneBox.join_edges_K` with the LUT under `p`. -/
def JoinEdgesM (p : Pol) (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf S0 S1 xa xc : Int) : Prop :=
  ∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
    Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
    ∀ r c s j : Int → K3, ReqEdge Cr Cf xa xc c → StabK v (S0 + xc) (S1 - xa) s →
      LutEqKM p b pr pc ps pq r c s j → RestK j → JSpecK b v pr pc pq r c j

/-- The counter-run's join trace: 0, then x from the ctl_req rise window on. -/
def jW (t : Int) : K3 := if t < 999 then .f else .x

theorem jKM_x_stays (p : Pol) : ∀ b : Bool, ∀ c : K3, (b = true → p.p1 = false) →
    jKM p b .t c .t .x = .x := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide

theorem jKM_low (p : Pol) : ∀ b : Bool, jKM p b .t .f .t .f = .f := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide

theorem jW_run (p : Pol) (b : Bool) (h999 : jKM p b .t .x .t .f = .x)
    (hst : ∀ c : K3, jKM p b .t c .t .x = .x) :
    LutEqKM p b (Rd.const 0) (Rd.const 0) (Rd.const 0) (Rd.const 1) (fun _ => .t) (rX 1000 3000)
      (fun _ => .t) jW := by
  intro t ht
  simp only [Rd.const]
  by_cases h1 : t < 999
  · have e1 : jW t = .f := by simp [jW, h1]
    have e2 : jW (t - 1) = .f := by simp [jW]; omega
    have e3 : rX 1000 3000 (t - 0) = .f := rX_lo (by decide) (by omega)
    rw [e1, e2, e3, jKM_low]
  · by_cases h2 : t = 999
    · subst h2; rw [show (999 : Int) - 0 = 999 by rfl, show (999 : Int) - 1 = 998 by rfl]
      have e1 : jW 999 = .x := by decide
      have e2 : jW 998 = .f := by decide
      have e3 : rX 1000 3000 999 = .x := by decide
      rw [e1, e2, e3, h999]
    · have e1 : jW t = .x := by simp [jW]; omega
      have e2 : jW (t - 1) = .x := by simp [jW]; omega
      rw [e1, e2, hst]

theorem jW_rest : RestK jW := fun t ht => by simp [jW]; omega

theorem const_stab : StabK true (0 + 0) (5000 - 1) (fun _ => .t) := fun _ _ _ => rfl

/-- **Join fails under `weak1`** (selected `uj1`, x_req waiting): after the
ctl_req rise window the C-element must restore 1 with its own feedback pin
reading x (`C2(1,1,X)`), which `weak1` does not pass. The binary-edge margins
hold (so Kleene's `join_edges_K` gives safety), the model's left side fails. -/
theorem join_fails_weak1 :
    ((0 : Int) + 0 + (1 + 0) ≤ 1000 + 0 ∧ (3000 : Int) + 0 + (1 + 0) ≤ 5000 + 0) ∧
    (∀ pr pc ps pq : Rd, 0 ≤ pr.lo → pr.hi ≤ 0 → 0 ≤ pc.lo → pc.hi ≤ 0 →
      0 ≤ ps.lo → ps.hi ≤ 0 → 1 ≤ pq.lo → pq.hi ≤ 1 →
      ∀ r c s j : Int → K3, ReqEdge 1000 3000 1 0 c → StabK true (0 + 0) (5000 - 1) s →
        KleeneBox.LutEqK true pr pc ps pq r c s j → RestK j → JSpecK true true pr pc pq r c j) ∧
    ¬ JoinEdgesM weak1 true true 0 0 0 0 0 0 1 1 1000 3000 0 5000 1 0 := by
  refine ⟨by decide, (join_edges_K true true 0 0 0 0 0 0 1 1 1000 3000 0 5000 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).mpr (by decide), ?_⟩
  intro h
  have hs := h (Rd.const 0) (Rd.const 0) (Rd.const 0) (Rd.const 1) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (fun _ => .t) (rX 1000 3000)
    (fun _ => .t) jW (rX_edge _ _ (by decide)) const_stab
    (jW_run weak1 true (by decide) (fun c => jKM_x_stays weak1 true c (fun _ => rfl))) jW_rest
  have := hs 1000 (by decide)
  revert this; decide

/-- **Join fails under every policy that does not pass 0** (`weak0`, `strict`):
UNSELECTED `uj0`, x_req waiting, the ctl_req rise window puts x on its pin while
the spec is a definite 0. -/
theorem join_fails_weak0 (p : Pol) (hp : p.p0 = false) :
    ((0 : Int) + 0 + (1 + 0) ≤ 1000 + 0 ∧ (3000 : Int) + 0 + (1 + 0) ≤ 5000 + 0) ∧
    ¬ JoinEdgesM p false true 0 0 0 0 0 0 1 1 1000 3000 0 5000 1 0 := by
  refine ⟨by decide, ?_⟩
  intro h
  have h999 : jKM p false .t .x .t .f = .x := by
    rcases p with ⟨p0, p1⟩; simp at hp; subst hp; cases p1 <;> decide
  have hs := h (Rd.const 0) (Rd.const 0) (Rd.const 0) (Rd.const 1) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (fun _ => .t) (rX 1000 3000)
    (fun _ => .t) jW (rX_edge _ _ (by decide)) const_stab
    (jW_run p false h999 (fun c => jKM_x_stays p false c (fun h => nomatch h))) jW_rest
  have := hs 999 (by decide)
  revert this; decide

/-! ### `bd_latch` (ODD) -/

def LutEqM (p : Pol) (pd pe pq : Rd) (d e q : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → q t = oddM p (d (pd.σ t)) (e (pe.σ t)) (q (pq.σ t))

/-- `LibGapLatch.SafeBox` with the LUT under `p`. -/
def SafeBoxM (p : Pol) (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int) : Prop :=
  ∀ pd pe pq : Rd, Dlo ≤ pd.lo → pd.hi ≤ Dhi → Elo ≤ pe.lo → pe.hi ≤ Ehi →
    Qlo ≤ pq.lo → pq.hi ≤ Qhi →
    ∀ d e q, LibGapLatch.DStab v Td Tn d → LibGapLatch.EnTok A B C e → LutEqM p pd pe pq d e q →
      LibGapLatch.Capt v B pe q

theorem mM_t (p : Pol) : ∀ (v : Bool) (q : K3), p.pass (kb v) = true → oddM p (kb v) .t q = kb v := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide
theorem mM_same (p : Pol) : ∀ (v : Bool) (s : K3), p.pass (kb v) = true → oddM p (kb v) s (kb v) = kb v := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide
theorem mM_f (p : Pol) : ∀ (v : Bool) (d : K3), p.pass (kb v) = true → oddM p d .f (kb v) = kb v := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide
theorem mM_dead (p : Pol) : ∀ (v : Bool) (d e : K3), p.pass (kb v) = false → (d = kb v ∨ d = .x) →
    oddM p d e .x = .x := by
  rcases p with ⟨p0, p1⟩; cases p0 <;> cases p1 <;> decide

/-- **Latch, sufficient under `p` when the token value passes**
(`LibGapLatch.latch_pin_ok`, same three inequalities). -/
theorem latch_pin_ok_M (p : Pol) (v : Bool) (hv : p.pass (kb v) = true)
    (A B C Td Tn : Int) (pd pe pq : Rd) (d e q : Int → K3)
    (hq1 : 1 ≤ pq.lo) (hBC : B ≤ C) (H_T0 : 0 ≤ A + pe.lo)
    (H_EN_TOKEN : LibGapLatch.EnTok A B C e) (H_D_STABLE : LibGapLatch.DStab v Td Tn d)
    (H_PIN_READ : LutEqM p pd pe pq d e q)
    (H_SETUP_PULSE : A + pe.hi + pq.hi ≤ B + pe.lo)
    (H_SETUP_DATA : Td + pd.hi + pq.hi ≤ B + pe.lo)
    (H_HOLD : C + pe.hi ≤ Tn + pd.lo) :
    LibGapLatch.Capt v B pe q := by
  have e1 := LibGapLatch.Rd.lo_le_hi pe; have e2 := LibGapLatch.Rd.lo_le_hi pq
  have e3 := LibGapLatch.Rd.lo_le_hi pd
  intro t
  refine Formal.Cells.LibGapMux.int_ind (fun t => 0 ≤ t → B ≤ pe.σ t → q t = kb v)
    (fun t ht h0 => absurd h0 (by omega)) ?_ t
  intro t ht ih _ hB
  have hfb : q (pq.σ t) = kb v := by
    have h0 : 0 ≤ pq.σ t := by have := pe.le t; have := pq.ge t; omega
    have hlt : pq.σ t < t := by have := pq.le t; omega
    by_cases hu : B ≤ pe.σ (pq.σ t)
    · exact ih _ hlt h0 hu
    · rw [H_PIN_READ _ h0]
      have hA : A ≤ pe.σ (pq.σ t) := by
        have := pe.le t; have := pq.ge t; have := pe.ge (pq.σ t); omega
      rw [H_EN_TOKEN.1 _ hA (by omega)]
      have hd1 : Td ≤ pd.σ (pq.σ t) := by
        have := pe.le t; have := pq.ge t; have := pd.ge (pq.σ t); omega
      have hd2 : pd.σ (pq.σ t) < Tn := by
        have := pe.ge (pq.σ t); have := pd.le (pq.σ t); omega
      rw [H_D_STABLE _ hd1 hd2]
      exact mM_t p v _ hv
  rw [H_PIN_READ t ht, hfb]
  by_cases hc : pe.σ t < C
  · have hd1 : Td ≤ pd.σ t := by have := pe.le t; have := pd.ge t; omega
    have hd2 : pd.σ t < Tn := by have := pe.ge t; have := pd.le t; omega
    rw [H_D_STABLE _ hd1 hd2]; exact mM_same p v _ hv
  · rw [H_EN_TOKEN.2 _ (by omega)]; exact mM_f p v _ hv

/-- **Latch fails under `p` for a token value that does not pass**: numbers
`A=0, B=2, C=3, Td=0, Tn=3`, pins 0/0/1 ps, where all three inequalities of
`LibGapLatch.box_exact` hold (so the Kleene box is safe), the model has the
run `q ≡ x` (transparent phase with an x feedback cannot restore `v`). -/
theorem latch_fails_M (p : Pol) (v : Bool) (hv : p.pass (kb v) = false) :
    ((0 : Int) + 0 + 1 ≤ 2 + 0 ∧ (0 : Int) + 0 + 1 ≤ 2 + 0 ∧ (3 : Int) + 0 ≤ 3 + 0) ∧
    LibGapLatch.SafeBox v 0 2 3 0 3 0 0 0 0 1 1 ∧
    ¬ SafeBoxM p v 0 2 3 0 3 0 0 0 0 1 1 := by
  refine ⟨by decide, (LibGapLatch.box_exact v 0 2 3 0 3 0 0 0 0 1 1 (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide), ?_⟩
  intro h
  have hs := h (Rd.const 0) (Rd.const 0) (Rd.const 1) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (fun x => if 0 ≤ x ∧ x < 3 then kb v else .x) (fun x => if 0 ≤ x ∧ x < 2 then .t else .f)
    (fun _ => .x)
    (fun x h1 h2 => by simp [h1, h2])
    ⟨fun x h1 h2 => by simp [h1, h2], fun x h1 => by
      have : ¬ (0 ≤ x ∧ x < 2) := by omega
      simp [this]⟩
    (fun t _ => by
      symm; apply mM_dead p v _ _ hv
      have hd : ∀ x : Int, (if 0 ≤ x ∧ x < 3 then kb v else K3.x) = kb v ∨
          (if 0 ≤ x ∧ x < 3 then kb v else K3.x) = .x := by
        intro x; split <;> simp
      exact hd _)
  have := hs 2 (by decide) (by decide)
  revert this; cases v <;> decide


/-! ## 7. Non-vacuity witnesses -/

/-- The bracket is strict: on the silicon split order (A6 = I5 at the output
mux) the C-element `C2(1,1,X)` is `x` under `weak1` and `strict`, `t` under Kleene. -/
theorem bracket_strict_witness :
    lutP (U weak1) [5, 4, 3, 2, 1, 0] C2_INIT [.t, .t, .x, .f, .f, .f] = .x ∧
    lutP (U strict) [5, 4, 3, 2, 1, 0] C2_INIT [.t, .t, .x, .f, .f, .f] = .x ∧
    lutP (U weak0) [5, 4, 3, 2, 1, 0] C2_INIT [.t, .t, .x, .f, .f, .f] = .t ∧
    lutK C2_INIT [.t, .t, .x, .f, .f, .f] = .t := by decide

/-- `steer_edges_weak1`'s left side is inhabited: `steer_witness_K`'s traces. -/
theorem steer_witness_weak1 :
    SpecKM weak1 false true (Rd.const 300) (Rd.const 450) (rX 1000 3000) (sX 500 4000) ∧
    SpecKM weak1 true true (Rd.const 300) (Rd.const 450) (rX 1000 3000) (sX 500 4000) := by
  have h := fun b => (steer_edges_weak1 b true 300 300 450 450 1000 3000 500 4000 1 0
    (by decide) (by decide) (by decide) (by decide) (by decide)).mpr (by decide)
    (Rd.const 300) (Rd.const 450) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const]) (rX 1000 3000) (sX 500 4000) (rX_edge _ _ (by decide)) (sX_stab _ _)
  exact ⟨h false, h true⟩

/-- `latch_pin_ok_M`'s hypotheses are jointly satisfiable (`weak1`, token 0,
the stored 1 is overwritten by 0 at t = 0). -/
theorem latch_witness_weak1 :
    let d : Int → K3 := fun _ => .f
    let e : Int → K3 := fun x => if 0 ≤ x ∧ x < 2 then .t else .f
    let q : Int → K3 := fun x => if x < 0 then .t else .f
    LibGapLatch.EnTok 0 2 3 e ∧ LibGapLatch.DStab false 0 3 d ∧
      LutEqM weak1 (Rd.const 0) (Rd.const 0) (Rd.const 1) d e q ∧
      LibGapLatch.Capt false 2 (Rd.const 0) q := by
  intro d e q
  have hE : LibGapLatch.EnTok 0 2 3 e :=
    ⟨fun x h1 h2 => by simp [e, h1, h2], fun x h1 => by
      have : ¬ (0 ≤ x ∧ x < 2) := by omega
      simp [e, this]⟩
  have hD : LibGapLatch.DStab false 0 3 d := fun _ _ _ => rfl
  have hL : LutEqM weak1 (Rd.const 0) (Rd.const 0) (Rd.const 1) d e q := by
    intro t ht
    have hq : q t = .f := by simp [q]; omega
    rw [hq]
    simp only [Rd.const, d]
    by_cases h0 : t = 0
    · subst h0; decide
    · have hq' : q (t - 1) = .f := by simp [q]; omega
      rw [hq']
      by_cases he : 0 ≤ t - 0 ∧ t - 0 < 2
      · have : e (t - 0) = .t := by simp only [e]; exact ite_eq_left_iff.mpr (fun h => absurd he h)
        rw [this]; decide
      · have : e (t - 0) = .f := by simp only [e]; exact ite_eq_right_iff.mpr (fun h => absurd h he)
        rw [this]; decide
  exact ⟨hE, hD, hL, latch_pin_ok_M weak1 false rfl 0 2 3 0 3 _ _ _ d e q
    (by simp [Rd.const]) (by decide) (by simp [Rd.const]) hE hD hL
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])⟩

/-- `arb_acks_safe`'s hypothesis is met on `sc_tie_acked` (both acks x, not 1). -/
theorem arb_acks_safe_witness (E : Nat → List K3 → K3 → K3) (hE : Below E) :
    ¬ ((runE E 3 [I .x .x .f .f, I .t .t .f .f, I .t .t .x .f, I .t .t .t .f] idle1).a1 = .t ∧
       (runE E 3 [I .x .x .f .f, I .t .t .f .f, I .t .t .x .f, I .t .t .t .f] idle1).a2 = .t) :=
  arb_acks_safe hE _ _ _ (by decide)

end KleenePess
end Formal.Cells
