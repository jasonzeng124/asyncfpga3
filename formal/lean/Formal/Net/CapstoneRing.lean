import Formal.Net.CapstoneLinks

/-!
# Probe C-8l (3, structural half): every cycle of the gcd_hw circuit carries >= 3 link stages

`ringG` (generated, `Formal.Net.CapstoneLinks`) is the graph of the circuit bdc emits for
gcd_hw at the granularity of `Formal.Net.GcdHw.Gcd.rules` (one node per fused firing rule,
one edge per channel from its producer rule to its consumer rule), weighted by the number of
`bd_link` stages bdc's `Emitter` puts on that channel (`linked`, `depth`).

* `gcdhw_ring_ge3`: every closed walk carries at least 3 link stages (C-9b's verified
  checker `RingCheck`, certificate re-checked by the kernel in 20 chunks). With
  `RingCheckSimple.allCyclesGe_iff_simple` this is CLAUDE.md's rule ("three storage stages
  per simple cycle") on the fused graph.
* `gcdhw_cycle_linked`: hence every cycle passes through a link: the deadlock C-8j found on
  the hand-drawn graph (a data loop with no storage, `OpsLive.gcd_loop_stuck`) has no
  counterpart in the graph bdc emits.
* `gcdhw_has_cycle`: non-vacuity, the graph does have cycles (an explicit closed walk).
-/

namespace Formal.Net.GcdHw.Gcd
open Formal.Net.RingCheck

theorem ring_n : numNodes ringG = 158 := by decide +kernel

set_option maxRecDepth 20000 in
theorem ring_B0 : certCheckFrom ringG 3 ringCert (List.range' 0 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B1 : certCheckFrom ringG 3 ringCert (List.range' 8 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B2 : certCheckFrom ringG 3 ringCert (List.range' 16 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B3 : certCheckFrom ringG 3 ringCert (List.range' 24 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B4 : certCheckFrom ringG 3 ringCert (List.range' 32 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B5 : certCheckFrom ringG 3 ringCert (List.range' 40 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B6 : certCheckFrom ringG 3 ringCert (List.range' 48 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B7 : certCheckFrom ringG 3 ringCert (List.range' 56 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B8 : certCheckFrom ringG 3 ringCert (List.range' 64 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B9 : certCheckFrom ringG 3 ringCert (List.range' 72 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B10 : certCheckFrom ringG 3 ringCert (List.range' 80 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B11 : certCheckFrom ringG 3 ringCert (List.range' 88 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B12 : certCheckFrom ringG 3 ringCert (List.range' 96 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B13 : certCheckFrom ringG 3 ringCert (List.range' 104 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B14 : certCheckFrom ringG 3 ringCert (List.range' 112 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B15 : certCheckFrom ringG 3 ringCert (List.range' 120 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B16 : certCheckFrom ringG 3 ringCert (List.range' 128 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B17 : certCheckFrom ringG 3 ringCert (List.range' 136 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B18 : certCheckFrom ringG 3 ringCert (List.range' 144 8) = true := by decide +kernel
set_option maxRecDepth 20000 in
theorem ring_B19 : certCheckFrom ringG 3 ringCert (List.range' 152 6) = true := by decide +kernel

theorem ring_G19 : certCheckFrom ringG 3 ringCert (List.range' 152 6) = true := ring_B19
theorem ring_G18 : certCheckFrom ringG 3 ringCert (List.range' 144 14) = true :=
  certCheckFrom_append (m := 8) (b := 6) ring_B18 ring_G19
theorem ring_G17 : certCheckFrom ringG 3 ringCert (List.range' 136 22) = true :=
  certCheckFrom_append (m := 8) (b := 14) ring_B17 ring_G18
theorem ring_G16 : certCheckFrom ringG 3 ringCert (List.range' 128 30) = true :=
  certCheckFrom_append (m := 8) (b := 22) ring_B16 ring_G17
theorem ring_G15 : certCheckFrom ringG 3 ringCert (List.range' 120 38) = true :=
  certCheckFrom_append (m := 8) (b := 30) ring_B15 ring_G16
theorem ring_G14 : certCheckFrom ringG 3 ringCert (List.range' 112 46) = true :=
  certCheckFrom_append (m := 8) (b := 38) ring_B14 ring_G15
theorem ring_G13 : certCheckFrom ringG 3 ringCert (List.range' 104 54) = true :=
  certCheckFrom_append (m := 8) (b := 46) ring_B13 ring_G14
theorem ring_G12 : certCheckFrom ringG 3 ringCert (List.range' 96 62) = true :=
  certCheckFrom_append (m := 8) (b := 54) ring_B12 ring_G13
theorem ring_G11 : certCheckFrom ringG 3 ringCert (List.range' 88 70) = true :=
  certCheckFrom_append (m := 8) (b := 62) ring_B11 ring_G12
theorem ring_G10 : certCheckFrom ringG 3 ringCert (List.range' 80 78) = true :=
  certCheckFrom_append (m := 8) (b := 70) ring_B10 ring_G11
theorem ring_G9 : certCheckFrom ringG 3 ringCert (List.range' 72 86) = true :=
  certCheckFrom_append (m := 8) (b := 78) ring_B9 ring_G10
theorem ring_G8 : certCheckFrom ringG 3 ringCert (List.range' 64 94) = true :=
  certCheckFrom_append (m := 8) (b := 86) ring_B8 ring_G9
theorem ring_G7 : certCheckFrom ringG 3 ringCert (List.range' 56 102) = true :=
  certCheckFrom_append (m := 8) (b := 94) ring_B7 ring_G8
theorem ring_G6 : certCheckFrom ringG 3 ringCert (List.range' 48 110) = true :=
  certCheckFrom_append (m := 8) (b := 102) ring_B6 ring_G7
theorem ring_G5 : certCheckFrom ringG 3 ringCert (List.range' 40 118) = true :=
  certCheckFrom_append (m := 8) (b := 110) ring_B5 ring_G6
theorem ring_G4 : certCheckFrom ringG 3 ringCert (List.range' 32 126) = true :=
  certCheckFrom_append (m := 8) (b := 118) ring_B4 ring_G5
theorem ring_G3 : certCheckFrom ringG 3 ringCert (List.range' 24 134) = true :=
  certCheckFrom_append (m := 8) (b := 126) ring_B3 ring_G4
theorem ring_G2 : certCheckFrom ringG 3 ringCert (List.range' 16 142) = true :=
  certCheckFrom_append (m := 8) (b := 134) ring_B2 ring_G3
theorem ring_G1 : certCheckFrom ringG 3 ringCert (List.range' 8 150) = true :=
  certCheckFrom_append (m := 8) (b := 142) ring_B1 ring_G2
theorem ring_G0 : certCheckFrom ringG 3 ringCert (List.range' 0 158) = true :=
  certCheckFrom_append (m := 8) (b := 150) ring_B0 ring_G1

/-- Every closed walk of the gcd_hw circuit graph carries at least 3 bd_link stages. -/
theorem gcdhw_ring_ge3 : AllCyclesGe ringG 3 := certCheckFrom_sound ring_n ring_G0

/-- Every cycle passes through at least one link. -/
theorem gcdhw_cycle_linked : AllCyclesGe ringG 1 := fun s c hw => by
  have := gcdhw_ring_ge3 s c hw; omega

/-! ## Non-vacuity: the graph has cycles -/

/-- Follow a list of edge indices from node `v`, adding the weights. -/
def follow (g : Graph) : List Nat → Nat → Nat → Option (Nat × Nat)
  | [], v, c => some (v, c)
  | i :: is, v, c => match g[i]? with
    | some e => if e.src = v then follow g is e.dst (c + e.w) else none
    | none => none

theorem follow_walk (g : Graph) (s : Nat) : ∀ (is : List Nat) (v c : Nat), Walk g s v c →
    ∀ v' c', follow g is v c = some (v', c') → Walk g s v' c' := by
  intro is
  induction is with
  | nil => intro v c hw v' c' h; simp [follow] at h; obtain ⟨rfl, rfl⟩ := h; exact hw
  | cons i is ih =>
    intro v c hw v' c' h
    simp only [follow] at h
    split at h
    · rename_i e he
      split at h
      · rename_i hs
        have hm : e ∈ g := List.mem_of_getElem? he
        rw [← hs] at hw
        exact ih _ _ (Walk.snoc hw hm) v' c' h
      · simp at h
    · simp at h

theorem follow_start (g : Graph) (s : Nat) (i : Nat) (is : List Nat) (v' c' : Nat)
    (h : follow g (i :: is) s 0 = some (v', c')) : Walk g s v' c' := by
  simp only [follow] at h
  split at h
  · rename_i e he
    split at h
    · rename_i hs
      have hm : e ∈ g := List.mem_of_getElem? he
      have w0 : Walk g s e.dst e.w := Walk.edge hm hs
      have := follow_walk g s is e.dst e.w w0 v' c'
      rw [Nat.zero_add] at h
      exact this h
    · simp at h
  · simp at h

theorem aCycle_follow : follow ringG aCycle aCycleStart 0 = some (aCycleStart, 7) := by
  decide +kernel

/-- The circuit graph does have cycles, so `gcdhw_ring_ge3` is not vacuous. -/
theorem gcdhw_has_cycle : ∃ s c, Walk ringG s s c := by
  have h := aCycle_follow
  refine ⟨aCycleStart, 7, ?_⟩
  unfold aCycle at h
  exact follow_start _ _ _ _ _ _ h

end Formal.Net.GcdHw.Gcd
