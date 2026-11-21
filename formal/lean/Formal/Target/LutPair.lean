import Formal.Target.RoundTrip

/-!
# Formal.Target.LutPair — LUT5 (O5) gates agree with their LUT6 (O6) gate

Shard A, 2026-11-01. Part of S1 (H_DECODE). The round trip (`RoundTrip.feats`) re-encodes the O6 gates' INIT
bits; an O5 output has no FASM feature of its own: its function is INIT[31:0] of the same LUT on the same first
five pins. `o5_of_ok`: if `o5ok default l` holds, every O5 gate of `l` has an O6 gate in `l` with the same
`<site>.<L>LUT.` name, the O6's first five pins as its pins, and INIT = the O6's INIT mod 2^32.
-/

namespace Formal.Target.RT
open Formal.Target

/-! ## LUT5 outputs agree with their LUT6 (O5 = INIT[31:0] on the O6's first five pins)

Not covered by `feats` (an O5 output has no FASM feature of its own; its function is the low half of the LUT's
one INIT). `o5ok prev l`: every O5 gate of `l` directly follows its O6 gate (same `<site>.<L>LUT.` name), reads the
O6's first five pins, and has INIT = the O6's INIT mod 2^32. -/

def isO5 (g : Gate) : Bool := g.k == 5 && g.name.endsWith ".O5"

def o5match (p g : Gate) : Bool :=
  p.k == 6 && p.name.endsWith ".O6" && eqB (bl p.name).dropLast.dropLast (bl g.name).dropLast.dropLast &&
    g.ins == p.ins.take 5 && g.init == p.init % 2 ^ 32

def o5ok : Gate → List Gate → Bool
  | _, [] => true
  | p, g :: l => (!isO5 g || o5match p g) && o5ok g l

theorem getLastD_ne {α : Type} (l : List α) (h : l ≠ []) (x y : α) : l.getLast?.getD x = l.getLast?.getD y := by
  rw [List.getLast?_eq_some_getLast h]; rfl

theorem o5ok_append (p : Gate) : ∀ l1 l2 : List Gate,
    o5ok p (l1 ++ l2) = (o5ok p l1 && o5ok (l1.getLast?.getD p) l2)
  | [], l2 => by simp [o5ok]
  | [g], l2 => by simp [o5ok]
  | g :: h :: l1, l2 => by
    have := o5ok_append g (h :: l1) l2
    simp only [List.cons_append, o5ok] at this ⊢
    rw [this, getLastD_ne (h :: l1) (by simp) g p]; simp [Bool.and_assoc]


theorem o5ok_sound : ∀ (p : Gate) (l : List Gate), o5ok p l = true →
    ∀ g ∈ l, isO5 g = true → o5match p g = true ∨ ∃ q ∈ l, o5match q g = true
  | _, [], _, g, hg, _ => by cases hg
  | p, x :: l, h, g, hg, h5 => by
    simp only [o5ok, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
    rcases List.mem_cons.1 hg with rfl | hm
    · rcases h.1 with h1 | h1
      · rw [h5] at h1; cases h1
      · exact Or.inl h1
    · rcases o5ok_sound x l h.2 g hm h5 with h1 | ⟨q, hq, h2⟩
      · exact Or.inr ⟨x, List.mem_cons_self, h1⟩
      · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, h2⟩

/-- From the check with no predecessor: every O5 gate has its O6 gate in the list. -/
theorem o5_of_ok (l : List Gate) (h : o5ok default l = true) :
    ∀ g ∈ l, isO5 g = true → ∃ q ∈ l, o5match q g = true := fun g hg h5 =>
  (o5ok_sound default l h g hg h5).resolve_left (by
    have hk : (default : Gate).k = 0 := rfl
    simp [o5match, hk])

end Formal.Target.RT
