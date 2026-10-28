import Formal.Core.Kleene
/-!
# Formal.Core.Prims.SeqNext — the next-state functions of the slice flops, in Kleene logic

Shard A, probe PrimsSeq. Core Lean only (no Mathlib). Notes: `formal/notes/A-prims-seq.md`.

What a 7-series slice flop computes at a clock edge (UG474, prjxray fuzzer 011):

* FDRE / FDCE: `R` (or `CLR`) wins and gives 0; otherwise `CE` selects `D` or the old state.
* FDSE / FDPE: the same with the set value 1.

One function covers all four: `bnext rv r ce d s = if r then rv else if ce then d else s`
(`rv` is the reset/set value, `r` the SR pin read at the edge). Whether SR is synchronous
(FDRE/FDSE) or asynchronous (FDCE/FDPE) is a matter of *when* it is read; that is the timed
model in `Formal.Core.Prims.Flop`.

## Kleene extension

`kmux s a b` is the exact Kleene extension of `if s then a else b` on three independent
inputs: `s = X` gives `merge a b`. `knext rv r ce d s = kmux r rv (kmux ce d s)`. Because the
formula is read-once (each of `r ce d s` occurs once), the composition of exact muxes is the
exact extension: `knext_exact` proves that `knext` is defined (= `b`) **iff** every Boolean
completion of the inputs gives `b`. So an `X` on `R` or `CE` reaches the next state exactly
when the completions disagree.

## The research GLS hides X on SR and CE (proved counterexample)

`origin/claude/research:cells/gls/prims.v` `SLICE_FFX` does
`else if (SR) Q <= SRVAL; else if (CE) Q <= D;` (and the `GLS_FID` variant `SR === 1'b1`).
Verilog's `if (x)` takes the else branch, so X on SR or CE is read as 0. `glsNext` is that
code. `gls_unsound` proves it is not a sound ternary abstraction of the flop: there are inputs
where it returns a defined value and a Boolean completion of those inputs gives the other
value. `gls_hides_X_R` and `gls_hides_X_CE` are the two concrete cases (the same as
`formal/tools-A/glsdiff/tb_seq_x.v` F1/F2, `formal/notes/A-gls-compare-2.md`).
-/

namespace Formal.Core.Prims.Seq

open Formal.Core Formal.Core.K3

/-! ## The exact Kleene mux -/

/-- Exact Kleene extension of `if s then a else b` (a 2:1 pass-transistor mux with an X
select passes `merge a b`). -/
def kmux : K3 → K3 → K3 → K3
  | one, a, _ => a
  | zero, _, b => b
  | X, a, b => merge a b

@[simp] theorem kmux_one (a b : K3) : kmux one a b = a := rfl
@[simp] theorem kmux_zero (a b : K3) : kmux zero a b = b := rfl
@[simp] theorem kmux_X (a b : K3) : kmux X a b = merge a b := rfl

theorem kmux_ofBool (s : Bool) (a b : K3) : kmux (ofBool s) a b = if s then a else b := by
  cases s <;> rfl

theorem kmux_mono {s a b s' a' b' : K3} (hs : s ⊑ s') (ha : a ⊑ a') (hb : b ⊑ b') :
    kmux s a b ⊑ kmux s' a' b' := by
  cases s <;> cases s' <;> simp only [kmux] <;>
    first
    | exact ha
    | exact hb
    | exact merge_mono ha hb
    | exact le_trans (merge_le_left a b) ha
    | exact le_trans (merge_le_right a b) hb
    | exact absurd hs (by decide)

/-- `kmux s a a = a`: an X select with equal data does not produce X (the Kleene-exact
pass-gate reading, same hypothesis as the LUT's `H_mux_kleene`). -/
@[simp] theorem kmux_same (s a : K3) : kmux s a a = a := by cases s <;> simp [kmux]

/-! ## The flop's next-state function -/

/-- Boolean next state at a clock edge: `R` (reset/set value `rv`) wins, then `CE`. -/
def bnext (rv r ce d s : Bool) : Bool := if r then rv else if ce then d else s

/-- Kleene next state. -/
def knext (rv : Bool) (r ce d s : K3) : K3 := kmux r (ofBool rv) (kmux ce d s)

theorem knext_ofBool (rv r ce d s : Bool) :
    knext rv (ofBool r) (ofBool ce) (ofBool d) (ofBool s) = ofBool (bnext rv r ce d s) := by
  cases r <;> cases ce <;> rfl

theorem knext_mono (rv : Bool) {r ce d s r' ce' d' s' : K3}
    (hr : r ⊑ r') (hce : ce ⊑ ce') (hd : d ⊑ d') (hs : s ⊑ s') :
    knext rv r ce d s ⊑ knext rv r' ce' d' s' :=
  kmux_mono hr (le_refl _) (kmux_mono hce hd hs)

/-- Soundness: the Kleene next state is below the Boolean next state of every completion. -/
theorem knext_sound (rv : Bool) {r ce d s : K3} {r' ce' d' s' : Bool}
    (hr : r ⊑ ofBool r') (hce : ce ⊑ ofBool ce') (hd : d ⊑ ofBool d') (hs : s ⊑ ofBool s') :
    knext rv r ce d s ⊑ ofBool (bnext rv r' ce' d' s') := by
  rw [← knext_ofBool]; exact knext_mono rv hr hce hd hs

/-- All Boolean completions of the four inputs give `b`. -/
def AllGive (rv : Bool) (r ce d s : K3) (b : Bool) : Prop :=
  ∀ r' ce' d' s' : Bool, r ⊑ ofBool r' → ce ⊑ ofBool ce' → d ⊑ ofBool d' → s ⊑ ofBool s' →
    bnext rv r' ce' d' s' = b

instance (rv : Bool) (r ce d s : K3) (b : Bool) : Decidable (AllGive rv r ce d s b) := by
  unfold AllGive; exact inferInstance

/-- Exactness: `knext` is defined and equal to `b` iff every completion gives `b`. -/
theorem knext_exact (rv : Bool) (r ce d s : K3) (b : Bool) :
    knext rv r ce d s = ofBool b ↔ AllGive rv r ce d s b := by
  cases rv <;> cases b <;> cases r <;> cases ce <;> cases d <;> cases s <;> decide

/-- So `knext = X` iff two completions disagree. -/
theorem knext_eq_X_iff (rv : Bool) (r ce d s : K3) :
    knext rv r ce d s = X ↔ ¬ AllGive rv r ce d s true ∧ ¬ AllGive rv r ce d s false := by
  rw [← knext_exact, ← knext_exact]
  cases h : knext rv r ce d s <;> simp

/-- X on R reaches the next state whenever the unreset next state differs from `rv`. -/
theorem knext_X_R (rv : Bool) (ce d s : K3) (h : kmux ce d s ≠ ofBool rv) :
    knext rv X ce d s = X := by
  cases rv <;> cases ce <;> cases d <;> cases s <;> simp_all [knext, kmux, merge] <;> decide

/-- X on CE reaches the next state whenever `D` and the held state differ (R = 0). -/
theorem knext_X_CE (rv : Bool) (d s : K3) (h : d ≠ s) :
    knext rv zero X d s = X := by
  cases rv <;> cases d <;> cases s <;> simp_all [knext, kmux, merge]

/-! ## The research GLS's flop: X on SR or CE read as 0 -/

/-- `SLICE_FFX` in `cells/gls/prims.v` (research): `if (SR) Q <= SRVAL; else if (CE) Q <= D;`
(`GLS_FID`: `SR === 1'b1`). An X condition takes the else branch. -/
def glsNext (rv : Bool) (r ce d s : K3) : K3 :=
  if r = one then ofBool rv else if ce = one then d else s

/-- R = X, CE = 1, D = 1, Q = 0 (FDRE): the GLS gives 1, the flop can give 0 (R = 1). -/
theorem gls_hides_X_R :
    glsNext false X one one zero = one ∧ knext false X one one zero = X ∧
      X ⊑ ofBool true ∧ bnext false true true true false = false := by decide

/-- CE = X, D = 0, Q = 1, R = 0: the GLS gives 1, the flop can give 0 (CE = 1). -/
theorem gls_hides_X_CE :
    glsNext false zero X zero one = one ∧ knext false zero X zero one = X ∧
      X ⊑ ofBool true ∧ bnext false false true false true = false := by decide

/-- The GLS's X-as-0 is optimistic: it is NOT a sound ternary abstraction of the flop's
next-state function (it returns a defined value that some completion contradicts). -/
theorem gls_unsound :
    ¬ ∀ (rv : Bool) (r ce d s : K3) (r' ce' d' s' : Bool),
      r ⊑ ofBool r' → ce ⊑ ofBool ce' → d ⊑ ofBool d' → s ⊑ ofBool s' →
        glsNext rv r ce d s ⊑ ofBool (bnext rv r' ce' d' s') := by
  intro h
  have := h false X one one zero true true true false (X_le _) (le_refl _) (le_refl _) (le_refl _)
  exact absurd this (by decide)

/-- On Boolean inputs the GLS agrees with the flop (the defect is only on X). -/
theorem glsNext_ofBool (rv r ce d s : Bool) :
    glsNext rv (ofBool r) (ofBool ce) (ofBool d) (ofBool s) = ofBool (bnext rv r ce d s) := by
  cases rv <;> cases r <;> cases ce <;> cases d <;> cases s <;> decide

/-- `knext` is the greatest sound value: any ternary value `v` is sound for the flop at an
input (below the next state of every completion) iff `v ⊑ knext`. So a ternary flop model is
sound exactly where it returns `X` or `knext`'s value. -/
theorem sound_iff_le_knext (rv : Bool) (r ce d s v : K3) :
    (∀ r' ce' d' s' : Bool, r ⊑ ofBool r' → ce ⊑ ofBool ce' → d ⊑ ofBool d' → s ⊑ ofBool s' →
        v ⊑ ofBool (bnext rv r' ce' d' s')) ↔ v ⊑ knext rv r ce d s := by
  cases rv <;> cases v <;> cases r <;> cases ce <;> cases d <;> cases s <;> decide

end Formal.Core.Prims.Seq
