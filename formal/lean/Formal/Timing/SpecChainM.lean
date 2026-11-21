import Formal.Timing.SpecChain

/-!
# Copy chains given by a copy map (shard C)

`SpecChain` collapses a chain given as a list of gates. For a netlist of 187k nodes the chains
are better given as data the kernel can check cheaply: a **copy map** `cm` (node `w` ↦ the input
of the copy gate driving `w`, if any), the gate driving each node (`ga`), and per pin only the
source node and the chain length. `CmSound` says the map is the netlist's; then following the
map `r` times from a pin node to its claimed source yields a `chainOK` chain of the netlist's
gates (`follow_chain`), and `collapse_net_m` gives the collapsed relation for every listed gate.

Problem statement and limits: as in `SpecChain`. Nothing here is about a particular netlist.
-/

namespace Formal.Timing.SpecChainM
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain

/-- Follow the copy map `r` times. -/
def follow (cm : Nat → Option Nat) : Nat → Nat → Option Nat
  | v, 0 => some v
  | v, r + 1 => (cm v).bind fun y => follow cm y r

/-- The gates of the chain followed from `v`, `r` steps (the driver of `v` first). -/
def chainGates (cm : Nat → Option Nat) (ga : Nat → Gate) : Nat → Nat → List Gate
  | _, 0 => []
  | v, r + 1 => ga v :: (match cm v with | some y => chainGates cm ga y r | none => [])

/-- The copy map and driver map are the netlist's. -/
def CmSound (N : Net) (cm : Nat → Option Nat) (ga : Nat → Gate) : Prop :=
  ∀ w y, cm w = some y →
    ga w ∈ N.gates ∧ (ga w).out = w ∧ (ga w).k = 1 ∧ (ga w).init = 2 ∧ (ga w).ins.getD 0 0 = y

theorem follow_chain {N : Net} {cm : Nat → Option Nat} {ga : Nat → Gate} (hs : CmSound N cm ga) :
    ∀ (r v u : Nat), follow cm v r = some u →
      chainOK v (chainGates cm ga v r) u = true ∧ ∀ g ∈ chainGates cm ga v r, g ∈ N.gates
  | 0, v, u, h => by
    simp only [follow, Option.some.injEq] at h
    subst h
    exact ⟨by simp [chainOK, chainGates], by simp [chainGates]⟩
  | r + 1, v, u, h => by
    simp only [follow] at h
    cases hc : cm v with
    | none => rw [hc] at h; cases h
    | some y =>
      rw [hc] at h
      simp only [Option.bind_some] at h
      obtain ⟨h1, h2, h3, h4, h5⟩ := hs v y hc
      obtain ⟨i1, i2⟩ := follow_chain hs r y u h
      refine ⟨?_, ?_⟩
      · simp only [chainGates, hc, chainOK, h2, h3, h4, h5, beq_self_eq_true, Bool.and_self,
          Bool.true_and]
        exact i1
      · intro g hg
        simp only [chainGates, hc, List.mem_cons] at hg
        rcases hg with rfl | hg
        · exact h1
        · exact i2 g hg

/-- Per-pin data: (source node, chain length). -/
abbrev PinData := List (Nat × Nat)

/-- The pin chains these data stand for. -/
def toPCs (cm : Nat → Option Nat) (ga : Nat → Gate) (g : Gate) (pv : PinData) : List PinChain :=
  (List.range g.k).map fun i =>
    ⟨(pv.getD i (0, 0)).1, chainGates cm ga (g.ins.getD i 0) (pv.getD i (0, 0)).2⟩

/-- The per-gate check, through the copy map. -/
def pinsOKm (cm : Nat → Option Nat) (g : Gate) (pv : PinData) : Bool :=
  (List.range g.k).all fun i => follow cm (g.ins.getD i 0) (pv.getD i (0, 0)).2 == some (pv.getD i (0, 0)).1

theorem toPCs_getD (cm : Nat → Option Nat) (ga : Nat → Gate) (g : Gate) (pv : PinData) {i : Nat}
    (hi : i < g.k) :
    (toPCs cm ga g pv).getD i ⟨0, []⟩ =
      ⟨(pv.getD i (0, 0)).1, chainGates cm ga (g.ins.getD i 0) (pv.getD i (0, 0)).2⟩ := by
  simp [toPCs, List.getD_eq_getElem?_getD, hi]

theorem pinsOK_of_m {N : Net} {cm : Nat → Option Nat} {ga : Nat → Gate} (hs : CmSound N cm ga)
    {g : Gate} {pv : PinData} (h : pinsOKm cm g pv = true) :
    pinsOK g (toPCs cm ga g pv) = true ∧
      ∀ i, i < g.k → ∀ g' ∈ ((toPCs cm ga g pv).getD i ⟨0, []⟩).chain, g' ∈ N.gates := by
  simp only [pinsOKm, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  refine ⟨?_, fun i hi g' hg' => ?_⟩
  · simp only [pinsOK, List.all_eq_true, List.mem_range]
    intro i hi
    rw [toPCs_getD cm ga g pv hi]
    exact (follow_chain hs _ _ _ (h i hi)).1
  · rw [toPCs_getD cm ga g pv hi] at hg'
    exact (follow_chain hs _ _ _ (h i hi)).2 g' hg'

/-- **On a netlist, through a copy map.** -/
theorem collapse_net_m {p : DelayPar} {N : Net} {x : Beh} (hp : Sane p) (hN : N.WF) (hb : Behaves p N x)
    {cm : Nat → Option Nat} {ga : Nat → Gate} (hs : CmSound N cm ga)
    (L : List (Gate × PinData)) (hL : ∀ e ∈ L, e.1 ∈ N.gates ∧ pinsOKm cm e.1 e.2 = true) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ e ∈ L,
      CGateOK p c e.1 (fun i => ((toPCs cm ga e.1 e.2).getD i ⟨0, []⟩).src)
        (pinArcs e.1 (toPCs cm ga e.1 e.2)) (cStart p e.1 (toPCs cm ga e.1 e.2)) x := by
  have := collapse_net hp hN hb (L.map fun e => (e.1, toPCs cm ga e.1 e.2)) (by
    intro e he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    obtain ⟨h1, h2⟩ := hL e' he'
    obtain ⟨k1, k2⟩ := pinsOK_of_m hs h2
    exact ⟨h1, k1, k2⟩)
  obtain ⟨c, hc0, hc1, hall⟩ := this
  exact ⟨c, hc0, hc1, fun e he => hall _ (List.mem_map.mpr ⟨e, he, rfl⟩)⟩

end Formal.Timing.SpecChainM
