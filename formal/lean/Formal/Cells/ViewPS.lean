import Formal.Cells.RaceLinkPS.Defs
import Formal.Net.CViewPS.Base

/-!
# Formal.Cells.ViewPS — listed gates of THE target read their sources through checked copy chains, in every behaviour

Shard B, THE goal, S3 (the netlist side of the per-cell theorems).

## Problem, plainly
`SpecCElem.celem_forced'` and `SpecLatch.latch_close` take the collapsed relation `CGateOK` of one gate as a premise.
For a gate of THE target's circuit, does every behaviour (`Behaves p (circuit net boundary) x`) give it, with the pin
sources and copy chains that B's generated tables list? Shard C proved the same for its own generated view
(`CViewPS.collapsed`); this is the version for an arbitrary list of (gate index, per-pin (chain, source)) data, so that
B's rows carry their own chains and the bridge is a row check.

## Results
* `gateAt_mem`: every index below `nGates` names a gate of `net` (chunk lookup = list membership).
* `viewOK q pins` (Bool): gate `q` and every listed chain gate are gates of the circuit (index in range, not driving an
  environment node), and every pin's listed chain leads from the pin node back to its listed source (`pinsOK`).
* `view_collapse`: for every behaviour of the circuit with `0 ≤ κ ≤ 1`, `0 < g`, at its one corner `c`, every listed
  `(q, pins)` passing `viewOK` satisfies `CGateOK` with sources `src i` = the listed source of pin `i` and composite
  arcs `pinArcs` (pin arc, then the chain's arcs), from `cStart`.
* `const_hold`: a constant gate (k = 0) of the circuit drives its INIT bit 0 at every time, in every behaviour.

## Not covered
What the gates compute together; anything before `cStart` (power-up).
-/

namespace Formal.Cells.ViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Cells.RaceLinkPS Formal.Timing.SpecSettle
  Formal.Timing.SpecChain Formal.Net.CViewPS

theorem chunks_length : chunks.length = 75 := rfl

theorem g074_length : g074.length = 1873 := by decide +kernel

theorem getD_dropLast_mem {α : Type} : ∀ (l : List α) (i : Nat) (d : α), i + 1 < l.length →
    l.getD i d ∈ l.dropLast
  | [], _, _, h => by simp at h
  | [_], _, _, h => by simp at h
  | a :: b :: l, 0, d, _ => by simp
  | a :: b :: l, i + 1, d, h => by
    have := getD_dropLast_mem (b :: l) i d (by simp at h ⊢; omega)
    simp only [List.getD_cons_succ, List.dropLast_cons₂]
    exact List.mem_cons_of_mem _ this

/-- Every index below `nGates` names a gate of the netlist. -/
theorem gateAt_mem {c : Nat} (hc : c < 186873) : gateAt c ∈ net.gates := by
  have hcat := cat_get 2500 (by decide) chunks chunks_full chunks_last c
  have hlen : c % 2500 < (chunks.getD (c / 2500) []).length := by
    by_cases h : c / 2500 < 74
    · have hm := getD_dropLast_mem chunks (c / 2500) [] (by rw [chunks_length]; omega)
      rw [chunks_full _ hm]; omega
    · have h74 : c / 2500 = 74 := by omega
      rw [h74]
      show c % 2500 < g074.length
      rw [g074_length]; omega
  have hsome : (chunks.getD (c / 2500) [])[c % 2500]? = some (gateAt c) := by
    unfold gateAt
    generalize chunks.getD (c / 2500) [] = l at hlen ⊢
    rw [List.getD_eq_getElem?_getD]
    cases h : l[c % 2500]? with
    | none => rw [List.getElem?_eq_none_iff] at h; omega
    | some y => rfl
  rw [hsome] at hcat
  show gateAt c ∈ gates
  rw [gates_cat]
  exact List.mem_of_getElem? hcat

theorem gateAt_mem_circuit {c : Nat} (hc : c < 186873) (hk : keepPS (gateAt c) = true) :
    gateAt c ∈ (circuit net boundary).gates := by
  rw [circuit_gates]
  exact List.mem_filter.mpr ⟨gateAt_mem hc, hk⟩

/-- Per-pin data: (chain gate indices, nearest first; source node). -/
abbrev Pins := List (List Nat × Nat)

def pcsOf (pins : Pins) : List PinChain := pins.map fun e => ⟨e.2, e.1.map gateAt⟩

/-- The view check of one gate. -/
def viewOK (q : Nat) (pins : Pins) : Bool :=
  decide (q < 186873) && keepPS (gateAt q) && pinsOK (gateAt q) (pcsOf pins) &&
  pins.all fun e => e.1.all fun c => decide (c < 186873) && keepPS (gateAt c)

theorem viewOK_sound {q : Nat} {pins : Pins} (h : viewOK q pins = true) :
    gateAt q ∈ (circuit net boundary).gates ∧ pinsOK (gateAt q) (pcsOf pins) = true ∧
      ∀ i, i < (gateAt q).k → ∀ g' ∈ ((pcsOf pins).getD i ⟨0, []⟩).chain, g' ∈ (circuit net boundary).gates := by
  simp only [viewOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨gateAt_mem_circuit h1 h2, h3, fun i _ g' hg' => ?_⟩
  simp only [pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map] at hg'
  cases he : pins[i]? with
  | none => simp [he] at hg'
  | some e =>
    simp only [he, Option.map_some, Option.getD_some, List.mem_map] at hg'
    obtain ⟨c, hc, rfl⟩ := hg'
    have := h4 e (List.mem_of_getElem? he) c hc
    exact gateAt_mem_circuit this.1 this.2

/-- **Every listed gate is collapsed, in every behaviour of THE circuit.** -/
theorem view_collapse {p : DelayPar} (hp : Sane p) {x : Beh} (hb : Behaves p (circuit net boundary) x)
    (L : List (Nat × Pins)) (hL : L.all (fun e => viewOK e.1 e.2) = true) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ e ∈ L,
      CGateOK p c (gateAt e.1) (fun i => ((pcsOf e.2).getD i ⟨0, []⟩).src) (pinArcs (gateAt e.1) (pcsOf e.2))
        (cStart p (gateAt e.1) (pcsOf e.2)) x := by
  have hL' : ∀ e ∈ L.map (fun e => (gateAt e.1, pcsOf e.2)), e.1 ∈ (circuit net boundary).gates ∧
      pinsOK e.1 e.2 = true ∧ ∀ i, i < e.1.k → ∀ g' ∈ (e.2.getD i ⟨0, []⟩).chain, g' ∈ (circuit net boundary).gates := by
    intro e he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    simp only [List.all_eq_true] at hL
    exact viewOK_sound (hL e0 he0)
  obtain ⟨c, hc0, hc1, hall⟩ := collapse_net hp (circuit_wf net_wf) hb _ hL'
  exact ⟨c, hc0, hc1, fun e he => hall _ (List.mem_map.mpr ⟨e, he, rfl⟩)⟩

/-- A constant gate (no pins) of the circuit drives its INIT bit 0 at every time, in every behaviour. -/
theorem const_hold {p : DelayPar} {x : Beh} (hb : Behaves p (circuit net boundary) x) {s : Nat}
    (hs : s < 186873) (hk : keepPS (gateAt s) = true) (h0 : (gateAt s).k = 0) (hout : (gateAt s).out = s) :
    ∀ t, x s t = (gateAt s).init.testBit 0 := by
  obtain ⟨c, -, -, hall⟩ := hb
  obtain ⟨F, -, hF⟩ := hall _ (gateAt_mem_circuit hs hk)
  have hst : (gateAt s).start p = 0 := by
    simp only [Gate.start]
    have : (gateAt s).arcs = [] := by
      have hwf := (circuit_wf net_wf).1 _ (gateAt_mem_circuit hs hk)
      have := hwf.2.1; rw [h0] at this; exact List.length_eq_zero_iff.mp this
    rw [this]; rfl
  intro t
  have := (hF t (by omega)).2
  rw [hout, h0] at this
  simpa [addr] using this

end Formal.Cells.ViewPS
