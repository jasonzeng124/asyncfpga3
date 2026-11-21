import Formal.Net.AO.Window

/-!
# Coverage of the local check by two-window certificates (shard C, all-pairs route; notes/C-allpairs.md)

**Problem, plainly.** `Window.lcheckXA_of_windows` derives the long certificate's local check at a reader `v` from a
family of window certificates, given *coverage*: every count vector the long check ranges over lies in the box of
some window. For the all-pairs route the long certificate is cut at window boundaries `O j u` (the number of events
of node `u` before window `j`), and the window certificates are *two-window* certificates (windows `j` and `j + 1`,
plus one overhanging event per node). When does every count vector lie in such a box?

**Proved** (`box_exists`, `lcheckXA_of_twoWindows`): if the boundaries start at 0, are monotone, reach the long
certificate's length at window `m`, and the per-reader bounds `L` *spread* the windows (`Spread`: the first event of
window `j + 2` of any dependency node `a` waits, through `L`, for every dependency node `b` to have entered window
`j + 1`), then every count vector that satisfies the bounds lies in the box `[O j, O (j+2)]` of some `j ≤ m`. With
a window certificate for every `j ≤ m` at offsets `O j` that reaches at least `O (j+2)` on the dependency set (and no
further than the long certificate) and holds the reader's next event after `O (j+2) v` when there is one, the long
local check at `v` holds.

The spread condition is finitely checkable per window boundary (an instance property; it holds when every
boundary event is causally after the previous window's start events on the dependency set, through `L`).

**Not shown here:** the instance; coverage for the timing tables (`WindowT` lifts each entry; that the long tables
consist of shifted window entries is also an instance property); the unrolled certificate's construction from a
word of kinds.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]

/-- Window boundaries: `O j u` events of `u` lie before window `j`; `O 0 = 0`, monotone, `O j = len` from `m` on. -/
structure Bounds (C : Cert α) (O : Nat → α → Nat) (m : Nat) : Prop where
  zero : ∀ u, O 0 u = 0
  mono : ∀ j u, O j u ≤ O (j + 1) u
  top : ∀ j u, m ≤ j → O j u = C.len u

/-- The bounds `L` of the dependency set `Dv` spread the windows. -/
def Spread (C : Cert α) (L : α → Nat → α → Nat) (Dv : List α) (O : Nat → α → Nat) : Prop :=
  ∀ a ∈ Dv, ∀ b ∈ Dv, ∀ j, O (j + 2) a < C.len a → O (j + 1) b ≤ L a (O (j + 2) a) b

theorem Bounds.mono_le {C : Cert α} {O : Nat → α → Nat} {m : Nat} (hB : Bounds C O m) (u : α) :
    ∀ i j, i ≤ j → O i u ≤ O j u := by
  intro i j hij
  induction j with
  | zero => have : i = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j ih =>
    rcases Nat.lt_or_ge i (j + 1) with h | h
    · exact Nat.le_trans (ih (by omega)) (hB.mono j u)
    · have : i = j + 1 := by omega
      subst this; exact Nat.le_refl _

/-- The largest `j ≤ m` such that every dependency node has passed `O j`. -/
theorem exists_max (P : Nat → Prop) [DecidablePred P] (m : Nat) (h0 : P 0) :
    ∃ j, j ≤ m ∧ P j ∧ (j < m → ¬ P (j + 1)) := by
  induction m with
  | zero => exact ⟨0, Nat.le_refl _, h0, fun h => absurd h (Nat.lt_irrefl _)⟩
  | succ m ih =>
    obtain ⟨j, hjm, hj, hmax⟩ := ih
    by_cases hP : P (m + 1)
    · exact ⟨m + 1, Nat.le_refl _, hP, fun h => absurd h (Nat.lt_irrefl _)⟩
    · refine ⟨j, by omega, hj, fun _ => ?_⟩
      rcases Nat.lt_or_ge j m with h | h
      · exact hmax h
      · have : j = m := by omega
        subst this; exact hP

/-- **Every bounded count vector lies in a two-window box.** -/
theorem box_exists {C : Cert α} {L : α → Nat → α → Nat} {Dv : List α} {O : Nat → α → Nat} {m : Nat}
    (hB : Bounds C O m) (hS : Spread C L Dv O) (n : α → Nat) (hlen : ∀ u ∈ Dv, n u ≤ C.len u)
    (hcons : ∀ a ∈ Dv, ∀ b ∈ Dv, ∀ k, k < n a → L a k b ≤ n b) :
    ∃ j, j ≤ m ∧ ∀ u ∈ Dv, O j u ≤ n u ∧ n u ≤ O (j + 2) u := by
  classical
  obtain ⟨j, hjm, hP, hmax⟩ := exists_max (fun j => ∀ u ∈ Dv, O j u ≤ n u) m
    (fun u _ => by rw [hB.zero u]; exact Nat.zero_le _)
  refine ⟨j, hjm, fun u hu => ⟨hP u hu, ?_⟩⟩
  rcases Nat.lt_or_ge j m with hj | hj
  · -- some dependency node `u0` has not passed `O (j+1)`
    have hn := hmax hj
    have : ∃ u0 ∈ Dv, n u0 < O (j + 1) u0 := by
      apply Classical.byContradiction
      intro hne
      apply hn
      intro w hw
      apply Classical.byContradiction
      intro hlt
      exact hne ⟨w, hw, Nat.lt_of_not_le hlt⟩
    obtain ⟨u0, hu0, hlt⟩ := this
    apply Classical.byContradiction
    intro hc
    have hc' : O (j + 2) u < n u := Nat.lt_of_not_le hc
    have h1 := hS u hu u0 hu0 j (Nat.lt_of_lt_of_le hc' (hlen u hu))
    have h2 := hcons u hu u0 hu0 (O (j + 2) u) hc'
    omega
  · have e : O (j + 2) u = C.len u := hB.top (j + 2) u (by omega)
    rw [e]; exact hlen u hu

/-- **The long local check from two-window certificates.** If the window boundaries `O` are `Bounds` with top `m`,
the reader's bounds spread the windows, and for every `j ≤ m` there is a window certificate at offsets `O j` that
reaches at least `O (j+2)` on every dependency node and no further than the long certificate (`hWlen`), and that
holds the reader's next event after `O (j+2) v` whenever there is one (`hWv`), then the long certificate's local
check at `v` holds. (Two-window certificates plus one overhanging event of `v`; how the overhang's causes are
covered is the instance's business: e.g. a three-window certificate when `v` has an event in window `j + 2`.) -/
theorem lcheckXA_of_twoWindows {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {C : Cert α} {L : α → Nat → α → Nat} {D : α → List α} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
    {v : α} (hv : v ∈ D v)
    (hT : ∀ s s' : α → Bool, (∀ u ∈ D v, s u = s' u) → (∀ u, dat u = true → s u = s' u) →
      tEn N envEn v s = tEn N envEn v s')
    {O : Nat → α → Nat} {m : Nat} (hB : Bounds C O m) (hS : Spread C L (D v) O)
    (W : Nat → WinAt N dat envEn s0 C L D cl gd v)
    (hWo : ∀ j, j ≤ m → (W j).o = O j)
    (hWlen : ∀ j, j ≤ m → ∀ u ∈ D v, O (j + 2) u ≤ O j u + (W j).C'.len u ∧ O j u + (W j).C'.len u ≤ C.len u)
    (hWv : ∀ j, j ≤ m → O (j + 2) v < C.len v → O (j + 2) v < O j v + (W j).C'.len v) :
    LCheckXA N dat envEn s0 C L D cl gd v := by
  apply lcheckXA_of_windows hv hT
  intro n hlen hcons
  obtain ⟨j, hjm, hbox⟩ := box_exists hB hS n hlen hcons
  refine ⟨W j, fun u hu => ?_, ?_⟩
  · rw [hWo j hjm]
    have h1 := hbox u hu
    have h2 := hWlen j hjm u hu
    exact ⟨h1.1, by omega⟩
  · rw [hWo j hjm]
    have h1 := hbox v hv
    have h2 := hWlen j hjm v hv
    constructor
    · intro h
      rcases Nat.lt_or_ge (n v) (O (j + 2) v) with h3 | h3
      · omega
      · have h4 := hWv j hjm (by omega)
        omega
    · intro h
      omega

end Formal.Net.AO
