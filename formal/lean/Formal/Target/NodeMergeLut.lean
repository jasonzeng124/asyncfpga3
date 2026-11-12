import Formal.Target.NodeMerge

/-!
# Formal.Target.NodeMergeLut — every LUT input pin reads its slice's site-pin wire (H_DECODE, pin wiring)

Shard A, 2026-11-08. Companion of `NodeMerge` (pips). A LUT gate `SITE.<L>LUT.O6` / `.O5` of the decoded netlist
reads nodes `ins[0..k-1]`; Spec's `addr` and prjxray's `INIT[b]` indexing assume `ins[j]` is the LUT's physical pin
`<L><j+1>` (A1..A6). This file checks that, against prjxray's tables, for every LUT gate.

**Trusted data (H_DECODE):** `SP`: the slice sites of the part (`tilegrid.json`: site name, its tile, and its rank
among the tile's slices, i.e. prjxray's `X0`/`X1` site of the tile type), and for each tile type and rank the wire
of site pin `<L><j+1>` (`tile_type_*.json`, `site_pins`). The node's canonical wire `C` is the certificate shared
with `NodeMerge`.
* `LutOK D P C g`: `g` is named after a site of the table, and each input `j` reads a node whose canonical wire is
  that site's pin `<L><j+1>` wire in the site's tile.
* `lut_pin_driver`: with `PipOK` of the pip `h` that drives `ins[j]`, the fabric joins `h`'s destination wire to
  the site-pin wire of pin `<L><j+1>`: the netlist's pin order is the chip's.
-/

namespace Formal.Target.NM
open Formal.Target Formal.Target.RT

structure Site where
  name : String
  tile : Nat
  rank : Nat

/-- `sites`: slice sites by index; `pins`: key `ty * 2 + rank`, then key `L * 6 + j` -> wire of pin `<L><j+1>`. -/
structure SP where
  sites : NT Site
  pins : NT (NT Nat)

def letter (L : Nat) : String := ["A", "B", "C", "D"].getD L ""

def lutName (S : Site) (L : Nat) (o6 : Bool) : String :=
  S.name ++ "." ++ letter L ++ "LUT.O" ++ (if o6 then "6" else "5")

def pinWire (P : SP) (ty rank L j : Nat) : Option Nat :=
  match P.pins.get (ty * 2 + rank) with
  | some t => t.get (L * 6 + j)
  | none => none

def isLut (g : Gate) : Bool := g.name.endsWith "LUT.O6" || g.name.endsWith "LUT.O5"

/-- **What a checked LUT gate satisfies.** -/
def LutOK (D : DB) (P : SP) (C : NT (Nat × Nat)) (g : Gate) : Prop :=
  ∃ (s : Nat) (S : Site) (T : Tl) (L : Nat) (o6 : Bool),
    P.sites.get s = some S ∧ D.tiles.get S.tile = some T ∧ g.name = lutName S L o6 ∧
    ∀ j (n : Nat), g.ins[j]? = some n → ∃ w, pinWire P T.ty S.rank L j = some w ∧ C.get n = some (S.tile, w)

/-- Certificate: site index, letter, O6? -/
structure LC where
  s : Nat
  L : Nat
  o6 : Bool

def pinsOK (P : SP) (C : NT (Nat × Nat)) (tile ty rank L : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | j, n :: ns =>
    (match pinWire P ty rank L j, C.get n with
      | some w, some a => eqP a (tile, w)
      | _, _ => false) && pinsOK P C tile ty rank L (j + 1) ns

theorem pinsOK_sound (P : SP) (C : NT (Nat × Nat)) (tile ty rank L : Nat) :
    ∀ (j0 : Nat) (ns : List Nat), pinsOK P C tile ty rank L j0 ns = true →
      ∀ j n, ns[j]? = some n → ∃ w, pinWire P ty rank L (j0 + j) = some w ∧ C.get n = some (tile, w)
  | _, [], _, j, n, h => by simp at h
  | j0, m :: ns, h, j, n, hj => by
    simp only [pinsOK, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
      subst hj
      cases hw : pinWire P ty rank L j0 <;> cases hc : C.get m <;> simp only [hw, hc, reduceCtorEq] at h1
      exact ⟨_, rfl, by rw [eqP_eq h1]⟩
    | succ j =>
      simp only [List.getElem?_cons_succ] at hj
      obtain ⟨w, hw, hc⟩ := pinsOK_sound P C tile ty rank L (j0 + 1) ns h2 j n hj
      exact ⟨w, by rw [show j0 + (j + 1) = j0 + 1 + j by omega]; exact hw, hc⟩

def chkLut (D : DB) (P : SP) (C : NT (Nat × Nat)) (g : Gate) (c : LC) : Bool :=
  match P.sites.get c.s with
  | some S =>
    match D.tiles.get S.tile with
    | some T => eqB (bl (lutName S c.L c.o6)) (bl g.name) && pinsOK P C S.tile T.ty S.rank c.L 0 g.ins
    | none => false
  | none => false

theorem chkLut_sound {D : DB} {P : SP} {C : NT (Nat × Nat)} {g : Gate} {c : LC} (h : chkLut D P C g c = true) :
    LutOK D P C g := by
  unfold chkLut at h
  cases hS : P.sites.get c.s with
  | none => simp [hS] at h
  | some S =>
    cases hT : D.tiles.get S.tile with
    | none => simp [hS, hT] at h
    | some T =>
      simp only [hS, hT, Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      refine ⟨c.s, S, T, c.L, c.o6, hS, hT, (eq_of_eqB h1).symm, fun j n hj => ?_⟩
      have := pinsOK_sound P C S.tile T.ty S.rank c.L 0 g.ins h2 j n hj
      simpa using this

def chkLutList (D : DB) (P : SP) (C : NT (Nat × Nat)) : List Gate → List (Option LC) → Bool
  | [], [] => true
  | g :: gs, c :: cs =>
    (match c with
      | some c => chkLut D P C g c
      | none => !isLut g) && chkLutList D P C gs cs
  | _, _ => false

theorem chkLutList_sound (D : DB) (P : SP) (C : NT (Nat × Nat)) : ∀ (gs : List Gate) (cs : List (Option LC)),
    chkLutList D P C gs cs = true → ∀ g ∈ gs, isLut g = true → LutOK D P C g
  | [], [], _, g, hg, _ => by simp at hg
  | [], _ :: _, h, _, _, _ => by simp [chkLutList] at h
  | _ :: _, [], h, _, _, _ => by simp [chkLutList] at h
  | g' :: gs, c :: cs, h, g, hg, hp => by
    simp only [chkLutList, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hg with rfl | hg
    · split at h1
      · exact chkLut_sound h1
      · simp [hp] at h1
    · exact chkLutList_sound D P C gs cs h2 g hg hp

/-- **The pip driving LUT pin `<L><j+1>` reaches that pin's site wire.** If pip `h` drives the node that input `j`
of LUT gate `g` reads, the fabric joins `h`'s destination wire to the site-pin wire `<L><j+1>` of `g`'s site. -/
theorem lut_pin_driver {D : DB} {P : SP} {C : NT (Nat × Nat)} {g h : Gate} (hg : LutOK D P C g)
    (hh : PipOK D C h) {j : Nat} (hj : g.ins[j]? = some h.out) :
    ∃ (s : Nat) (S : Site) (T : Tl) (L : Nat) (o6 : Bool) (w th dh : Nat) (Ah : Tl) (dnh : String),
      P.sites.get s = some S ∧ D.tiles.get S.tile = some T ∧ g.name = lutName S L o6 ∧
      pinWire P T.ty S.rank L j = some w ∧
      D.tiles.get th = some Ah ∧ D.wires.get dh = some dnh ∧ (∃ pre sn, h.name = pre ++ Ah.name ++ "." ++ dnh ++ "." ++ sn) ∧
      Conn D (th, dh) (S.tile, w) := by
  obtain ⟨s, S, T, L, o6, hS, hT, hn, hp⟩ := hg
  obtain ⟨w, hw, hc⟩ := hp j h.out hj
  obtain ⟨tl, th, dh, sh, Ah, dnh, snh, i, a, b, hAh, hdh, hsh, hnh, _, _, _, hb, cb⟩ := hh
  rw [hc] at hb
  cases hb
  exact ⟨s, S, T, L, o6, w, th, dh, Ah, dnh, hS, hT, hn, hw, hAh, hdh, ⟨_, snh, hnh⟩, cb⟩

end Formal.Target.NM
