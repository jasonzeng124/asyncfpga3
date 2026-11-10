import Formal.Net.TimedOccU

/-!
# Union claims joined by an UPPER bound (shard C, 2026-11-10; B's "UnionUpOK")

**Problem, plainly.** `TimedOccU.UnionOK`/`ChainOK` join two claims `c1` (until event `e1`) and `c2` (from event `e2`)
of the same node and value only when `e2` is no later than `e1` by a separation (`Sep e2 → e1`). The one-pair data
layer at corner c = 0 (tools/tocc/r1h) has 40 joins where `e2` is causally AFTER `e1`, so no such separation exists;
what exists there is an upper bound `Up e1 e2 = u` (`e2` follows `e1` within `u`). Is the union still sound when
`c2.a + u ≤ c1.b`?

**Proved** (`unionUp_holds`, `chainU_holds`): yes, given that the upper-bound table is sound up to time `T`
(`UpSoundI`: if `e1` has happened by `σ` then `e2` has by `σ + u`, for `σ + u ≤ T`): at `t ≤ T`, either `e1` has not
happened by `t - c1.b`, so `c1` holds, or it has, so `e2` has happened by `t - c1.b + u ≤ t - c2.a`, so `c2` holds (the join also asks `0 ≤ c2.a`, so that
time is at most `t ≤ T`).
`ChainUOK` is `ChainOK` with this second way to join consecutive claims.

**Not shown here:** using `chainU_holds` inside the timed induction (`AO/Timed.timedA_follows`'s `hGC`): there the
table's soundness (`AO/Timed.up_sound`) is available only up to the current time, so a join at the induction's new
time step needs the join's target strictly inside (e.g. `1 ≤ c2.a`); that integration is open.
-/

namespace Formal.Net.OccNet.TimedU
open Formal.Net.OccNet Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR

variable {α : Type} [DecidableEq α]

/-- The upper-bound table is sound up to `T`, in claim (integer) time. -/
def UpSoundI (x : α → Nat → Bool) (t0 : Nat) (Up : α × Nat → α × Nat → Option Nat) (T : Nat) : Prop :=
  ∀ e1 e2 u, Up e1 e2 = some u → ∀ σ : Int, σ + u ≤ T → hbI x t0 e1 σ → hbI x t0 e2 (σ + u)

/-- `UnionOK` with a second way to join: an upper bound from `c1`'s end to `c2`'s start. -/
def UnionUpOK (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat)
    (c c1 c2 : Claim α) : Prop :=
  c1.z = c.z ∧ c2.z = c.z ∧ c1.val = c.val ∧ c2.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c2.B = c.B ∧ c2.b = c.b ∧
  (match c1.B, c2.A with
    | some e1, some e2 => (∃ d, Sep e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d) ∨
        (∃ u, Up e1 e2 = some u ∧ 0 ≤ c2.a ∧ c2.a + (u : Int) ≤ c1.b)
    | none, _ => True
    | some _, none => True)

theorem unionUp_holds {x : α → Nat → Bool} {t0 H T : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {Up : α × Nat → α × Nat → Option Nat}
    (hSS : SepSound x t0 Sep T) (hUS : UpSoundI x t0 Up T) (c c1 c2 : Claim α) (hu : UnionUpOK Sep Up c c1 c2)
    (t : Nat) (ht : t ≤ T) (h1 : Holds x t0 H c1 t) (h2 : Holds x t0 H c2 t) : Holds x t0 H c t := by
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
        rcases hj with ⟨d, hd, hle⟩ | ⟨u, hU, h0, hle⟩
        · have := hSS e1.1 e2.1 e1.2 e2.2 d hd _ (by omega) hhb
          exact hbI_mono this (by omega)
        · have := hUS e1 e2 u hU ((t : Int) - c1.b) (by omega) hhb
          exact hbI_mono this (by omega)
    · rw [hB2, hb2]; exact hBn
  · rw [← hz1, ← hv1]
    apply h1 hH
    · rw [hA1, ha1]; exact hA
    · cases hB1 : c1.B with
      | none => trivial
      | some e1 => exact fun hh => hend ⟨e1, hB1, hh⟩

/-- `ChainOK` with the upper-bound join. -/
def ChainUOK (Sep : α → Nat → α → Nat → Option Nat) (Up : α × Nat → α × Nat → Option Nat) (c : Claim α) :
    List (Claim α) → Prop
  | [] => False
  | [c1] => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧ c1.B = c.B ∧ c1.b = c.b
  | c1 :: c2 :: cs => c1.z = c.z ∧ c1.val = c.val ∧ c1.A = c.A ∧ c1.a = c.a ∧
      (match c1.B, c2.A with
        | some e1, some e2 => (∃ d, Sep e2.1 e2.2 e1.1 e1.2 = some d ∧ c2.a ≤ (c1.b : Int) + d) ∨
            (∃ u, Up e1 e2 = some u ∧ 0 ≤ c2.a ∧ c2.a + (u : Int) ≤ c1.b)
        | none, _ => True
        | some _, none => True) ∧
      ChainUOK Sep Up ⟨c.z, c.val, c2.A, c2.a, c.B, c.b⟩ (c2 :: cs)

/-- **A chain of claims joined by separations or upper bounds covers its union.** -/
theorem chainU_holds {x : α → Nat → Bool} {t0 H T : Nat} {Sep : α → Nat → α → Nat → Option Nat}
    {Up : α × Nat → α × Nat → Option Nat} (hSS : SepSound x t0 Sep T) (hUS : UpSoundI x t0 Up T)
    (t : Nat) (ht : t ≤ T) :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainUOK Sep Up c cs → (∀ c' ∈ cs, Holds x t0 H c' t) → Holds x t0 H c t
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
    have hc' := chainU_holds hSS hUS t ht (c2 :: cs) c' hrest (fun d hd => hh d (by simp [hd]))
    have h1 := hh c1 (by simp)
    exact unionUp_holds hSS hUS c c1 c' ⟨hz, rfl, hv, rfl, hA, ha, rfl, rfl, hj⟩ t ht h1 hc'

/-- Every `ChainOK` chain is a `ChainUOK` chain (the new rule only adds joins). -/
theorem chainUOK_of_chainOK {Sep : α → Nat → α → Nat → Option Nat} (Up : α × Nat → α × Nat → Option Nat) :
    ∀ (cs : List (Claim α)) (c : Claim α), ChainOK Sep c cs → ChainUOK Sep Up c cs
  | [], _, h => h.elim
  | [_], _, h => h
  | c1 :: c2 :: cs, c, h => by
    obtain ⟨hz, hv, hA, ha, hj, hrest⟩ := h
    refine ⟨hz, hv, hA, ha, ?_, chainUOK_of_chainOK Up (c2 :: cs) _ hrest⟩
    revert hj
    cases c1.B <;> cases c2.A <;> simp_all

end Formal.Net.OccNet.TimedU
