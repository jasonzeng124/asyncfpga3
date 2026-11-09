import Formal.Net.AO.Timed

/-!
# Formal.Cells.UnionUp — joining claim phases by an UPPER bound (shard B, 2026-11-09)

## Problem, plainly
Shard C's data layer proves a latch's value across its phases (transparent, enable uncertain, hold, ...) as a chain
of claims (`TimedU.ChainOK`). Two consecutive claims `c1`, `c2` are joined when `c1` lasts until `c2` starts, and the
only way `ChainOK` can say so is a LOWER bound: a separation `Sep(c2.A → c1.B) = d` ("`c1`'s end event comes at
least `d` after `c2`'s start event"). On THE target, pair (12,18), this fails for the bulk of the truncated latch
holds (B's tracing, JOURNAL-B 2026-11-09, class A): the claim on the latch's data input ends at an event `c1.B` that
comes causally BEFORE the latch's close `c2.A` (often the latch's own opening), with a large offset `c1.b`. Then
`Sep(c2.A → c1.B)` cannot exist (it is a natural number), and the right statement is an UPPER bound: the close
happens at most `u` after `c1.B`, and `c2.a + u ≤ c1.b`.

## Proved (core Lean, no Mathlib)
* `UpSoundT x t0 Up T`: "every `Up e0 e = some d` entry is a true upper bound up to horizon `T`" (the conclusion
  shape of C's `AO.up_sound`); `upSoundT_of_up_sound`: C's `up_sound` gives it, under exactly `up_sound`'s
  hypotheses.
* `UnionUpOK`, `union_holds_up`: if `c1.B = e1`, `c2.A = e2`, `Up e1 e2 = some u`, `c2.a + u ≤ c1.b` and `0 ≤ c2.a`,
  then at every `t ≤ T` where both claims hold, their union holds (same value, `c1`'s start, `c2`'s end).
* `ChainUpOK`, `chain_holds_up`: chains whose links are joined by either rule (`Sep` as in `ChainOK`, `Up`, or `JoinAnc`: a `Sep` from a common ancestor `e0` to `c1`'s
  end and an `Up` from `e0` to `c2`'s start, `c2.a + u ≤ c1.b + s`; `union_holds_anc`);
  `chainOK_up_of_chainOK`: every `ChainOK` chain is a `ChainUpOK` chain, so this is a strict generalisation.

## Not shown
The wiring into C's main induction (`TimedU.timedU_follows` / `AO.timedA_follows` take `ChainOK`; using `ChainUpOK`
there needs `UpSoundT` at the induction's horizon, which `up_sound` supplies from the same induction hypotheses: this
is a change to C's files, proposed in JOURNAL-B). Class B (claim end and close causally unordered) is the
shape `JoinAnc` covers when C's Up/Sep tables reach a common ancestor; whether they do is measured, not shown. Class C (re-open setup; a claim-builder artefact) is not addressed here. No instance.
-/

namespace Formal.Cells.UnionUp
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR
  Formal.Net.OccNet.TimedU

variable {α : Type} [DecidableEq α]

/-- Upper bounds are sound up to horizon `T`: if `e0` has happened by `τ` and `τ + d ≤ T`, `e` has happened by
`τ + d`. -/
def UpSoundT (x : α → Nat → Bool) (t0 : Nat) (Up : α × Nat → α × Nat → Option Nat) (T : Nat) : Prop :=
  ∀ (e0 e : α × Nat) (d τ : Nat), Up e0 e = some d → e0.2 < cnt x t0 e0.1 τ → τ + d ≤ T →
    e.2 < cnt x t0 e.1 (τ + d)

/-- Two consecutive claims joined by an upper bound: `c2` starts at most `u` after `c1`'s end event, early enough. -/
def UnionUpOK (Up : α × Nat → α × Nat → Option Nat) (c c1 c2 : Claim α) : Prop :=
  c1.z = c.z ∧ c2.z = c.z ∧ c1.val = c.val ∧ c2.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c2.B = c.B ∧ c2.b = c.b ∧
  (match c1.B, c2.A with
    | some e1, some e2 => ∃ u, Up e1 e2 = some u ∧ 0 ≤ c2.a ∧ c2.a + u ≤ (c1.b : Int)
    | none, _ => True
    | some _, none => True)

theorem union_holds_up {x : α → Nat → Bool} {t0 H T : Nat} {Up : α × Nat → α × Nat → Option Nat}
    (hUS : UpSoundT x t0 Up T) (c c1 c2 : Claim α) (hu : UnionUpOK Up c c1 c2) (t : Nat) (ht : t ≤ T)
    (h1 : Holds x t0 H c1 t) (h2 : Holds x t0 H c2 t) : Holds x t0 H c t := by
  obtain ⟨hz1, hz2, hv1, hv2, hA1, ha1, hB2, hb2, hj⟩ := hu
  intro hH hA hBn
  by_cases hend : ∃ e1, c1.B = some e1 ∧ hbI x t0 e1 ((t : Int) - c1.b)
  · obtain ⟨e1, he1, hhb⟩ := hend
    rw [← hz2, ← hv2]
    apply h2 hH
    · cases hA2 : c2.A with
      | none => trivial
      | some e2 =>
        rw [he1, hA2] at hj
        obtain ⟨u, hU, ha0, hle⟩ := hj
        obtain ⟨h0, hc⟩ := hhb
        have hτ := hUS e1 e2 u ((t : Int) - c1.b).toNat hU hc (by omega)
        refine ⟨by omega, ?_⟩
        have : ((t : Int) - c2.a).toNat ≥ ((t : Int) - c1.b).toNat + u := by omega
        exact Nat.lt_of_lt_of_le hτ (cnt_mono e2.1 _ _ this)
    · rw [hB2, hb2]; exact hBn
  · rw [← hz1, ← hv1]
    apply h1 hH
    · rw [hA1, ha1]; exact hA
    · cases hB1 : c1.B with
      | none => trivial
      | some e1 => exact fun hh => hend ⟨e1, hB1, hh⟩

/-- The join through a common ancestor `e0`: `c1`'s end event comes at least `s` after `e0` (a `Sep` entry) and
`c2`'s start event at most `u` after it (an `Up` entry), with `c2.a + u ≤ c1.b + s`. -/
def JoinAnc (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat) (c1 c2 : Claim α) : Prop :=
  match c1.B, c2.A with
  | some e1, some e2 => ∃ e0 s u, Sep e0.1 e0.2 e1.1 e1.2 = some s ∧ Up e0 e2 = some u ∧ 0 ≤ c2.a ∧
      c2.a + u ≤ (c1.b : Int) + s
  | none, _ => True
  | some _, none => True

theorem union_holds_anc {x : α → Nat → Bool} {t0 H T : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {Up : α × Nat → α × Nat → Option Nat}
    (hSS : SepSound x t0 Sep T) (hUS : UpSoundT x t0 Up T) (c c1 c2 : Claim α)
    (hz1 : c1.z = c.z) (hz2 : c2.z = c.z) (hv1 : c1.val = c.val) (hv2 : c2.val = c.val) (hA1 : c1.A = c.A)
    (ha1 : c1.a = c.a) (hB2 : c2.B = c.B) (hb2 : c2.b = c.b) (hj : JoinAnc Sep Up c1 c2)
    (t : Nat) (ht : t ≤ T)
    (h1 : Holds x t0 H c1 t) (h2 : Holds x t0 H c2 t) : Holds x t0 H c t := by
  intro hH hA hBn
  by_cases hend : ∃ e1, c1.B = some e1 ∧ hbI x t0 e1 ((t : Int) - c1.b)
  · obtain ⟨e1, he1, hhb⟩ := hend
    rw [← hz2, ← hv2]
    apply h2 hH
    · cases hA2 : c2.A with
      | none => trivial
      | some e2 =>
        unfold JoinAnc at hj
        rw [he1, hA2] at hj
        obtain ⟨e0, s, u, hS, hU, ha0, hle⟩ := hj
        have h0 := hSS e1.1 e0.1 e1.2 e0.2 s hS ((t : Int) - c1.b) (by omega) hhb
        obtain ⟨h00, hc0⟩ := h0
        have hτ := hUS e0 e2 u (((t : Int) - c1.b) - s).toNat hU hc0 (by omega)
        refine ⟨by omega, ?_⟩
        have : ((t : Int) - c2.a).toNat ≥ (((t : Int) - c1.b) - s).toNat + u := by omega
        exact Nat.lt_of_lt_of_le hτ (cnt_mono e2.1 _ _ this)
    · rw [hB2, hb2]; exact hBn
  · rw [← hz1, ← hv1]
    apply h1 hH
    · rw [hA1, ha1]; exact hA
    · cases hB1 : c1.B with
      | none => trivial
      | some e1 => exact fun hh => hend ⟨e1, hB1, hh⟩

/-- Chains whose consecutive claims are joined by a separation (as `ChainOK`) or by an upper bound. -/
def ChainUpOK (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat) (c : Claim α) :
    List (Claim α) → Prop
  | [] => False
  | [c1] => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c1.B = c.B ∧ c1.b = c.b
  | c1 :: c2 :: cs => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧
      ((match c1.B, c2.A with
        | some e1, some e2 => ∃ d, Sep e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d
        | none, _ => True
        | some _, none => True) ∨
       (match c1.B, c2.A with
        | some e1, some e2 => ∃ u, Up e1 e2 = some u ∧ 0 ≤ c2.a ∧ c2.a + u ≤ (c1.b : Int)
        | none, _ => True
        | some _, none => True) ∨
       JoinAnc Sep Up c1 c2) ∧
      ChainUpOK Sep Up ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩ (c2 :: cs)

theorem chain_holds_up {x : α → Nat → Bool} {t0 H T : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {Up : α × Nat → α × Nat → Option Nat}
    (hSS : SepSound x t0 Sep T) (hUS : UpSoundT x t0 Up T) (t : Nat) (ht : t ≤ T) :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainUpOK Sep Up c cs → (∀ c' ∈ cs, Holds x t0 H c' t) →
      Holds x t0 H c t
  | [], c, h, _ => h.elim
  | [c1], c, h, hh => by
    obtain ⟨hz, hv, hA, ha, hB, hb⟩ := h
    have h1 := hh c1 (by simp)
    intro hH hA' hB'
    rw [← hz, ← hv]
    exact h1 hH (by rw [hA, ha]; exact hA') (by rw [hB, hb]; exact hB')
  | c1 :: c2 :: cs, c, h, hh => by
    obtain ⟨hz, hv, hA, ha, hj, hrest⟩ := h
    let c' : Claim α := ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩
    have hc' := chain_holds_up hSS hUS t ht (c2 :: cs) c' hrest (fun d hd => hh d (by simp [hd]))
    have h1 := hh c1 (by simp)
    rcases hj with hj | hj | hj
    · exact union_holds hSS c c1 c' ⟨hz, rfl, hv, rfl, hA, ha, rfl, rfl, hj⟩ t ht h1 hc'
    · exact union_holds_up hUS c c1 c' ⟨hz, rfl, hv, rfl, hA, ha, rfl, rfl, hj⟩ t ht h1 hc'
    · exact union_holds_anc hSS hUS c c1 c' hz rfl hv rfl hA ha rfl rfl hj t ht h1 hc'

omit [DecidableEq α] in
/-- Every `ChainOK` chain is a `ChainUpOK` chain (the new rule only adds the upper-bound join). -/
theorem chainOK_up_of_chainOK {Sep : α → Nat → α → Nat → Option Nat} {Up : α × Nat → α × Nat → Option Nat} :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainOK Sep c cs → ChainUpOK Sep Up c cs
  | [], _, h => h
  | [_], _, h => h
  | _ :: c2 :: cs, _, h => by
    obtain ⟨hz, hv, hA, ha, hj, hrest⟩ := h
    exact ⟨hz, hv, hA, ha, Or.inl hj, chainOK_up_of_chainOK (c2 :: cs) _ hrest⟩

section bridge
open Formal.Net.AO
variable {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {x : α → Nat → Bool}
  {r : α → α → Nat → Nat} {t0 H : Nat} {CF CP : Formal.Net.AO.Cert α} {L : α → α → Nat → α → Nat} {D : α → List α}
  {Sep : α → Nat → α → Nat → Option Nat} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
  {Up : α × Nat → α × Nat → Option Nat}

/-- C's `AO.up_sound`, under its own hypotheses at horizon `T`, gives `UpSoundT` at `T`: the upper-bound join of
`union_holds_up` can be used wherever C's induction already has `up_sound`. -/
theorem upSoundT_of_up_sound (hb : TBehX N dat envEn x r t0 H) (hTP : TmOK CP) (hLs : ∀ v, LSound CF (L v))
    (hSE : ∀ b m a k d, Sep b m a k = some d → dat a = false)
    (hTO : TOA N CF CP L D Sep) (hDE : ∀ v u, u ∈ D v → dat u = false)
    (hloc : ∀ v, N.gate v = true → dat v = false → LCheckXA N dat envEn (fun w => x w t0) CP (L v) D cl gd v)
    (hEnvE : ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal CF (fun u => cntE dat x t0 u (s - 1)) → Enabled CP (fun w => cnt x t0 w (s - 1)) v)
    (hlenEq : ∀ u, CP.len u = CF.len u)
    (hgdF : ∀ v z, N.gate v = false → gd v z = [])
    (hGd : ∀ v z, N.gate v = true → z ∈ N.pins v → ∀ g ∈ gd v z, ∃ c, cl[g.ci]? = some c ∧ c.z = z ∧
      GuardTime N Sep v z c g)
    (hUp : UpOKA N dat CP Sep Up) (hS : SepOKA N CP Sep Up)
    (T : Nat) (hI : ∀ τ, τ ≤ T → Ideal CF (fun u => cntE dat x t0 u τ))
    (hB : ∀ v s, dat v = false → t0 < s → s ≤ T → x v s ≠ x v (s - 1) → ChangeOKA N CP x t0 r v s)
    (hC : ∀ c ∈ cl, ∀ s, s ≤ T → Holds x t0 H c s) (hSS : SepSound x t0 Sep T) :
    UpSoundT x t0 Up T := by
  intro e0 e d τ hU h0 hT
  exact up_sound hb hTP hLs hSE hTO hDE hloc hEnvE hlenEq hgdF hGd hUp hS T hI hB hC hSS e0 τ h0
    (CP.tm e.1 e.2) e d (Nat.le_refl _) hU hT

end bridge

end Formal.Cells.UnionUp
