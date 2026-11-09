import Formal.Net.Compute.OnDecoded

/-!
# Shared glue for the per-unit decoded-netlist theorems `Net/Compute/PS/<Unit>.lean` (shard C, 2026-11-09)

**Problem.** `OnDecoded.corr_sound` gives, for a checked certificate, that every mapped yosys net's
value equals the decoded valuation at its node, for an input environment that reads each mapped
input bit at its node. The per-unit theorems want: the word at the unit's decoded output nodes
equals `unitVal cells outs xs`, with `xs` the words at the unit's decoded input nodes (any number of
ports, any widths). This file proves that step once (`unit_ps`).

* `inWords M v ws`: port `p` (width `ws[p]`) read as `word (v ∘ inNode M p) ws[p]`.
* `inEnvL_ok`: if every psi entry `(p, k, d)` has `p < ws.length` and `k < ws[p]`, then
  `inEnv (inWords M v ws)` reads each mapped input bit at its node.
* `outsMapped`: every output wire is a cell-output net with a phi entry, or an input bit with a psi
  entry (decidable); `outNode` is the phi resp. psi node.
* `unit_ps`: certificate checks + `Settled` ⇒ `word (v ∘ outNode M outs) outs.length = unitVal …`.

Not covered: timing; input bits that psi does not map (the cells do not read them, so their nodes
`inNode … = 0` play no role in `unitVal`; they still appear in the input words of the statements).
-/

namespace Formal.Net.Compute.PS
open Formal.Target Formal.Net.Compute Formal.Net.Compute.OnDecoded

/-- The unit's input ports read at their decoded nodes; port `p` has width `ws[p]`. -/
def inWords (M : Maps) (v : Nat → Bool) (ws : List Nat) : List Nat :=
  (List.range ws.length).map fun p => word (fun k => v (inNode M p k)) (ws.getD p 0)

theorem inEnvL_ok (M : Maps) (ws : List Nat)
    (hpsi : M.psi.all (fun e => decide (e.1 < ws.length) && decide (e.2.1 < ws.getD e.1 0)) = true)
    (v : Nat → Bool) :
    ∀ p k d, lk2 M.psi p k = some d → inEnv (inWords M v ws) (.inp p k) = v d := by
  intro p k d h
  have hm := List.all_eq_true.mp hpsi _ (lk2_mem _ _ _ _ h)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
  have hd : inNode M p k = d := by simp [inNode, h]
  simp only [inEnv, inWords]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm.1]
  simp only [Option.map_some, Option.getD_some]
  rw [testBit_word, hd]
  simp only [hm.2, decide_true, Bool.true_and]

/-- The decoded node carrying output bit `i`. -/
def outNode (M : Maps) (outs : List W) (i : Nat) : Nat :=
  match outs.getD i .c0 with
  | .net n => (lk M.phi n).getD 0
  | .inp p k => inNode M p k
  | _ => 0

/-- Every output wire is a mapped net driven by a cell, or a mapped input bit (a unit output wired
straight to an input, e.g. the sign bit of `>>>`). -/
def outsMapped (M : Maps) (cells : List Cell) (outs : List W) : Bool :=
  (List.range outs.length).all fun i => match outs.getD i .c0 with
    | .net n => mem n (cells.flatMap Cell.outs) && (lk M.phi n).isSome
    | .inp p k => (lk2 M.psi p k).isSome
    | _ => false

theorem out_wire {M : Maps} {cells : List Cell} {outs : List W} (ho : outsMapped M cells outs = true)
    (i : Nat) (hi : i < outs.length) :
    (∃ n, outs.getD i .c0 = .net n ∧ n ∈ cells.flatMap Cell.outs ∧ lk M.phi n = some (outNode M outs i)) ∨
    (∃ p k, outs.getD i .c0 = .inp p k ∧ lk2 M.psi p k = some (outNode M outs i)) := by
  have h := List.all_eq_true.mp ho i (List.mem_range.mpr hi)
  revert h
  unfold outNode
  split
  · rename_i n hn
    intro h
    simp only [Bool.and_eq_true, Option.isSome_iff_exists] at h
    obtain ⟨h1, d, hd⟩ := h
    refine Or.inl ⟨n, hn, (mem_iff _ _).mp h1, ?_⟩
    simp only [hd, Option.getD_some]
  · rename_i p k hn
    intro h
    simp only [Option.isSome_iff_exists] at h
    obtain ⟨d, hd⟩ := h
    refine Or.inr ⟨p, k, hn, ?_⟩
    simp only [inNode, hd, Option.getD_some]
  · intro h; simp at h

/-- **A checked unit on the decoded netlist**: the word at the decoded output nodes is the cell
netlist's `unitVal` at the words read at the decoded input nodes. -/
theorem unit_ps {M : Maps} {D : List GC} {N : Net} (hD : ∀ c ∈ D, ∃ g ∈ N.gates, GC.ofGate g = c)
    {cells : List Cell} {outs : List W} {certs : List CC} (htopo : topoOK cells [] = true)
    (hcells : ∀ i, i < cells.length → cellOK M D (cells.getD i dfltCell) (certs.getD i dfltCC) = true)
    (ws : List Nat)
    (hpsi : M.psi.all (fun e => decide (e.1 < ws.length) && decide (e.2.1 < ws.getD e.1 0)) = true)
    (ho : outsMapped M cells outs = true)
    {v : Nat → Bool} (hS : Settled N (D.map GC.out) v) :
    word (v ∘ outNode M outs) outs.length = unitVal cells outs (inWords M v ws) := by
  have hc := corr_sound (cert := fun i => certs.getD i dfltCC) hD htopo hcells hS (inEnvL_ok M ws hpsi v)
  unfold unitVal
  apply word_congr
  intro i hi
  show v (outNode M outs i) = eval _ [] cells (outs.getD i .c0)
  rcases out_wire ho i hi with ⟨n, hn, hmem, hz⟩ | ⟨p, k, hn, hz⟩
  · rw [hn]
    exact (hc n hmem (outNode M outs i) hz).symm
  · rw [hn]
    exact (inEnvL_ok M ws hpsi v p k _ hz).symm

end Formal.Net.Compute.PS
