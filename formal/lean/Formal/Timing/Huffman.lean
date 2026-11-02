import Formal.Timing.ChunkCM

/-!
# Storage nodes cut every loop: a rank certificate over chunked view data (shard C)

**Problem, plainly.** THE goal asks that the circuit's feedback loops be handled inside the
proof, not cut by hand. Which loops are there? Call a logic gate a **storage node** if one of its
pins reads (through its routing) the gate's own output (a C-element, latch or arbiter state LUT).
If the other logic gates (the **combinational** ones) admit a rank that strictly increases along
every pin-to-source link between combinational gates, then every cycle of the circuit passes
through a storage node: the circuit is storage nodes plus acyclic logic (a Huffman machine), and
timing obligations are needed only at storage nodes and along the acyclic paths between them.

This file: the generic check (`rankChunkOK`, a Boolean per chunk, with ranks read from any
lookup function `rk`, e.g. chunk trees) and its soundness `ranked_of_chunks`. Nothing here is
about a particular netlist.
-/

namespace Formal.Timing.Huffman
open Formal.Target Formal.Timing.SpecChainM Formal.Timing.ChunkCM

/-- Some pin's source is the gate's own output. -/
def isStor (g : Gate) (pv : PinData) : Bool := pv.any fun e => e.1 == g.out

/-- A combinational logic gate: kept, not a copy gate, not a storage node. -/
def isComb (keep : Gate → Bool) (g : Gate) (pv : PinData) : Bool :=
  keep g && (cpIn g).isNone && !isStor g pv

/-- The check for one chunk starting at node `base`: the rank lookup is defined exactly at the
combinational gates, and every pin source with a rank has a smaller one. -/
def rankChunkOK (rk : Nat → Option Nat) (keep : Gate → Bool) : Nat → List Gate → List PinData → Bool
  | _, [], _ => true
  | _, _ :: _, [] => false
  | base, g :: gs, pv :: vs =>
    ((rk base).isSome == isComb keep g pv) &&
    (!(isComb keep g pv) || (List.range g.k).all fun i =>
      match rk (pv.getD i (0, 0)).1 with
      | some r' => decide (r' < (rk base).getD 0)
      | none => true) &&
    rankChunkOK rk keep (base + 1) gs vs

theorem rankChunkOK_sound {rk : Nat → Option Nat} {keep : Gate → Bool} :
    ∀ (base : Nat) (gs : List Gate) (vs : List PinData), rankChunkOK rk keep base gs vs = true →
      ∀ o, o < gs.length →
        (rk (base + o)).isSome = isComb keep (gs.getD o default) (vs.getD o []) ∧
        (isComb keep (gs.getD o default) (vs.getD o []) = true →
          ∀ i, i < (gs.getD o default).k → ∀ r', rk ((vs.getD o []).getD i (0, 0)).1 = some r' →
            r' < (rk (base + o)).getD 0)
  | _, [], _, _, o, h => by simp at h
  | _, _ :: _, [], h, _, _ => by simp [rankChunkOK] at h
  | base, g :: gs, pv :: vs, h, o, ho => by
    simp only [rankChunkOK, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true, Bool.not_eq_true',
      List.all_eq_true, List.mem_range] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    cases o with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      refine ⟨h1, fun hc i hi r' hr => ?_⟩
      rcases h2 with h2 | h2
      · rw [hc] at h2; cases h2
      · have := h2 i hi; rw [hr] at this; simpa using this
    | succ o =>
      have := rankChunkOK_sound (base + 1) gs vs h3 o (by simp at ho; omega)
      simp only [List.getD_cons_succ]
      rw [show base + (o + 1) = base + 1 + o by omega]
      exact this

/-- Node-indexed view of chunked data. -/
def gAt (cs : List (List Gate)) (C w : Nat) : Gate := (cs.getD (w / C) []).getD (w % C) default
def pvAt (vss : List (List PinData)) (C w : Nat) : PinData := (vss.getD (w / C) []).getD (w % C) []

/-- **Soundness over chunks.** If every chunk passes, then with `ρ w := (rk w).getD 0`, for every
combinational gate at node `w` (inside the chunks) and every pin whose source `s` is itself a
combinational gate inside the chunks, `ρ s < ρ w`. -/
theorem ranked_of_chunks {rk : Nat → Option Nat} {keep : Gate → Bool} {cs : List (List Gate)}
    {vss : List (List PinData)} {C : Nat}
    (hok : ∀ c, c < cs.length → rankChunkOK rk keep (C * c) (cs.getD c []) (vss.getD c []) = true) :
    ∀ w, w / C < cs.length → w % C < (cs.getD (w / C) []).length →
      isComb keep (gAt cs C w) (pvAt vss C w) = true →
      ∀ i, i < (gAt cs C w).k →
        ∀ s, s = ((pvAt vss C w).getD i (0, 0)).1 →
          s / C < cs.length → s % C < (cs.getD (s / C) []).length →
          isComb keep (gAt cs C s) (pvAt vss C s) = true →
          (rk s).getD 0 < (rk w).getD 0 := by
  intro w hw ho hc i hi s hs hs1 hs2 hcs
  have hW := rankChunkOK_sound _ _ _ (hok _ hw) _ ho
  have hS := rankChunkOK_sound _ _ _ (hok _ hs1) _ hs2
  rw [Nat.div_add_mod] at hW hS
  have hsome : (rk s).isSome = true := by rw [hS.1]; exact hcs
  obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp hsome
  have := hW.2 hc i hi r' (by unfold pvAt at hs; rw [← hs]; exact hr')
  rw [hr']; exact this

end Formal.Timing.Huffman
