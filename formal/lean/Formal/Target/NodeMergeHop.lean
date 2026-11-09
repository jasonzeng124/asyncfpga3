import Formal.Target.NodeMergeLut
import Formal.Target.RoundTripSel

/-!
# Formal.Target.NodeMergeHop — site output hops reach their slice's output-pin wires (H_DECODE, site hops)

Shard A, 2026-11-09. Companion of `NodeMerge` (pips) and `NodeMergeLut` (LUT input pins). The decoder models a
slice output as a copy gate `hop TILE/WIRE` (`k = 1`, INIT `0b10`) from a slice-internal node named
`SITE.<src>` (a LUT's `A6`/`A5`, `F7A`, `F8`, a CARRY4's `XOR<i>`/`CO<i>`, a flop's `AQ`/`A5Q`) to a routing node.
Until now nothing checked that the destination is the right output pin of the right site: a decoder that sent
`SLICE_X0Y16.A6` to the L-slice's pin, or to another tile, passed every Lean check.

**Trusted data (H_DECODE):** `P.sites` (NodeMergeLut: slice sites, tile, rank), `SP3`: for each tile type and rank the
wire of each slice output pin (`tile_type_*.json` `site_pins`: `A..D`, `AMUX..DMUX`, `COUT`, `AQ..DQ`), and
`hopTab`, the slice's own output wiring (7-series CLB: pin `<L>` is O6; `<L>MUX` selects O6, O5, the F7/F8 mux of its
row, XOR<i>, CO<i> or `<L>5Q`; `COUT` is CO3; `<L>Q` the flop). `C` (canonical wire of a node) is the certificate shared
with `NodeMerge`; `nm` is the netlist's node-name function.
* `HopOK`: a hop gate reads one node named `S.name ++ "." ++ src`, for a site `S` of the table, and drives a node
  whose canonical wire is the output-pin wire `p` of `S`'s tile and rank, with `(src, p)` in `hopTab`.
* `OutOK`: a site-logic gate named `S.name ++ "." ++ gs` (`ALUT.O6`, `CARRY4.O2`, `F8`, …) drives the node named
  `S.name ++ "." ++ os` given by `outTab` (`A6`, `XOR2`, `F8`, …).
* `hop_from_gate`: if a gate with `OutOK` drives the node a hop with `HopOK` reads, and site names contain no `.`,
  the two sites have the same name and the gate's output (`gs`, renamed `os`) reaches output-pin wire `p` of that
  site with `(os, p)` in `hopTab`.
-/

namespace Formal.Target.NM
open Formal.Target Formal.Target.RT Formal.Target.RTS

/-- Slice output pins, by index (`tile_type_*.json` site-pin names). -/
def outPins : List String := ["A", "B", "C", "D", "AMUX", "BMUX", "CMUX", "DMUX", "COUT", "AQ", "BQ", "CQ", "DQ"]

/-- The slice's output wiring (trusted, 7-series CLB): which internal node may reach which output pin. -/
def hopTab : List (String × Nat) :=
  [("A6", 0), ("B6", 1), ("C6", 2), ("D6", 3),
   ("A6", 4), ("A5", 4), ("B6", 5), ("B5", 5), ("C6", 6), ("C5", 6), ("D6", 7), ("D5", 7),
   ("F7A", 4), ("F8", 5), ("F7B", 6),
   ("XOR0", 4), ("XOR1", 5), ("XOR2", 6), ("XOR3", 7),
   ("CO0", 4), ("CO1", 5), ("CO2", 6), ("CO3", 7), ("CO3", 8),
   ("A5Q", 4), ("B5Q", 5), ("C5Q", 6), ("D5Q", 7),
   ("AQ", 9), ("BQ", 10), ("CQ", 11), ("DQ", 12)]

/-- The decoder's naming of site-logic gate outputs: gate suffix -> output-node suffix. -/
def outTab : List (String × String) :=
  [("ALUT.O6", "A6"), ("ALUT.O5", "A5"), ("BLUT.O6", "B6"), ("BLUT.O5", "B5"),
   ("CLUT.O6", "C6"), ("CLUT.O5", "C5"), ("DLUT.O6", "D6"), ("DLUT.O5", "D5"),
   ("F7A", "F7A"), ("F7B", "F7B"), ("F8", "F8"),
   ("CARRY4.O0", "XOR0"), ("CARRY4.O1", "XOR1"), ("CARRY4.O2", "XOR2"), ("CARRY4.O3", "XOR3"),
   ("CARRY4.CO0", "CO0"), ("CARRY4.CO1", "CO1"), ("CARRY4.CO2", "CO2"), ("CARRY4.CO3", "CO3")]

/-- Output-pin wires: key `ty * 2 + rank`, then pin index -> wire. -/
structure SP3 where
  outs : NT (NT Nat)

def outWire (Q3 : SP3) (ty rank p : Nat) : Option Nat :=
  match Q3.outs.get (ty * 2 + rank) with
  | some t => t.get p
  | none => none

def isHop (g : Gate) : Bool := hopB (bl g.name)

/-- **What a checked hop satisfies.** -/
def HopOK (D : DB) (P : SP) (Q3 : SP3) (C : NT (Nat × Nat)) (nm : Nat → String) (g : Gate) : Prop :=
  ∃ (s : Nat) (S : Site) (T : Tl) (n : Nat) (src : String) (p w : Nat),
    g.k = 1 ∧ g.init = 2 ∧ g.ins = [n] ∧ P.sites.get s = some S ∧ D.tiles.get S.tile = some T ∧
    nm n = S.name ++ "." ++ src ∧ (src, p) ∈ hopTab ∧ outWire Q3 T.ty S.rank p = some w ∧
    C.get g.out = some (S.tile, w)

/-- **What a checked site-logic gate satisfies.** -/
def OutOK (P : SP) (nm : Nat → String) (g : Gate) : Prop :=
  ∃ (s : Nat) (S : Site) (gs os : String),
    P.sites.get s = some S ∧ (gs, os) ∈ outTab ∧ g.name = S.name ++ "." ++ gs ∧ nm g.out = S.name ++ "." ++ os

/-! ## The checks -/

/-- Hop certificate: site index, `hopTab` index. -/
structure HC where
  s : Nat
  t : Nat

def chkHop (D : DB) (P : SP) (Q3 : SP3) (C : NT (Nat × Nat)) (N : ITree) (g : Gate) (c : HC) : Bool :=
  match P.sites.get c.s, hopTab[c.t]?, g.ins with
  | some S, some (src, p), [n] =>
    match D.tiles.get S.tile with
    | some T =>
      match N.get n, outWire Q3 T.ty S.rank p, C.get g.out with
      | some x, some w, some a =>
        g.k == 1 && g.init == 2 && eqB (bl x) (bl (S.name ++ "." ++ src)) && eqP a (S.tile, w)
      | _, _, _ => false
    | none => false
  | _, _, _ => false

/-- A hop that needs no certificate reads a node whose (checked) name is not a slice node. -/
def hopExempt (N : ITree) (g : Gate) : Bool :=
  !isHop g || (match g.ins with
    | [n] => (match N.get n with
      | some x => !isSliceC x.toList
      | none => false)
    | _ => false)

theorem chkHop_sound {D : DB} {P : SP} {Q3 : SP3} {C : NT (Nat × Nat)} {N : ITree} {nm : Nat → String}
    (hN : ∀ i x, N.get i = some x → nm i = x) {g : Gate} {c : HC} (h : chkHop D P Q3 C N g c = true) :
    HopOK D P Q3 C nm g := by
  unfold chkHop at h
  split at h
  · rename_i S src p n hS ht hg
    split at h
    · rename_i T hT
      split at h
      · rename_i x w a hx hw ha
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨hk, hi⟩, hn⟩, he⟩ := h
        refine ⟨c.s, S, T, n, src, p, w, hk, hi, hg, hS, hT, ?_, List.mem_of_getElem? ht, hw, ?_⟩
        · rw [hN n x hx]; exact eq_of_eqB hn
        · rw [ha, eqP_eq he]
      · simp at h
    · simp at h
  · simp at h

def chkHopList (D : DB) (P : SP) (Q3 : SP3) (C : NT (Nat × Nat)) (N : ITree) : List Gate → List (Option HC) → Bool
  | [], [] => true
  | g :: gs, c :: cs =>
    (match c with
      | some c => chkHop D P Q3 C N g c
      | none => hopExempt N g) && chkHopList D P Q3 C N gs cs
  | _, _ => false

/-- The claim per gate: a hop reading a node whose name starts with `SLICE` is checked. -/
abbrev HopClaim (D : DB) (P : SP) (Q3 : SP3) (C : NT (Nat × Nat)) (nm : Nat → String) (g : Gate) : Prop :=
  isHop g = true → (∀ n, g.ins = [n] → isSliceC (nm n).toList = true) → HopOK D P Q3 C nm g

theorem chkHopList_sound (D : DB) (P : SP) (Q3 : SP3) (C : NT (Nat × Nat)) (N : ITree) (nm : Nat → String)
    (hN : ∀ i x, N.get i = some x → nm i = x) : ∀ (gs : List Gate) (cs : List (Option HC)),
    chkHopList D P Q3 C N gs cs = true → ∀ g ∈ gs, HopClaim D P Q3 C nm g
  | [], [], _, g, hg => by simp at hg
  | [], _ :: _, h, _, _ => by simp [chkHopList] at h
  | _ :: _, [], h, _, _ => by simp [chkHopList] at h
  | g' :: gs, c :: cs, h, g, hg => by
    simp only [chkHopList, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hg with rfl | hg
    · intro hh hs
      split at h1
      · exact chkHop_sound hN h1
      · exfalso
        simp only [hopExempt, hh, Bool.not_true, Bool.false_or] at h1
        split at h1
        · rename_i n hn
          split at h1
          · rename_i x hx
            have := hs n hn
            rw [hN n x hx] at this
            simp [this] at h1
          · simp at h1
        · simp at h1
    · exact chkHopList_sound D P Q3 C N nm hN gs cs h2 g hg

/-- Out-name certificate: site index, `outTab` index. -/
structure OC where
  s : Nat
  t : Nat

def chkOut (P : SP) (N : ITree) (g : Gate) (c : OC) : Bool :=
  match P.sites.get c.s, outTab[c.t]?, N.get g.out with
  | some S, some (gs, os), some x => eqB (bl g.name) (bl (S.name ++ "." ++ gs)) && eqB (bl x) (bl (S.name ++ "." ++ os))
  | _, _, _ => false

theorem chkOut_sound {P : SP} {N : ITree} {nm : Nat → String} (hN : ∀ i x, N.get i = some x → nm i = x) {g : Gate}
    {c : OC} (h : chkOut P N g c = true) : OutOK P nm g := by
  unfold chkOut at h
  split at h
  · rename_i S gs os x hS ht hx
    simp only [Bool.and_eq_true] at h
    exact ⟨c.s, S, gs, os, hS, List.mem_of_getElem? ht, eq_of_eqB h.1, by rw [hN _ x hx]; exact eq_of_eqB h.2⟩
  · simp at h

/-- A gate needs no out-name certificate when its output node is not in the name certificate `N`. -/
def chkOutList (P : SP) (N : ITree) : List Gate → List (Option OC) → Bool
  | [], [] => true
  | g :: gs, c :: cs =>
    (match c with
      | some c => chkOut P N g c
      | none => (N.get g.out).isNone) && chkOutList P N gs cs
  | _, _ => false

abbrev OutClaim (P : SP) (N : ITree) (nm : Nat → String) (g : Gate) : Prop := (N.get g.out).isSome = true → OutOK P nm g

theorem chkOutList_sound (P : SP) (N : ITree) (nm : Nat → String) (hN : ∀ i x, N.get i = some x → nm i = x) :
    ∀ (gs : List Gate) (cs : List (Option OC)), chkOutList P N gs cs = true → ∀ g ∈ gs, OutClaim P N nm g
  | [], [], _, g, hg => by simp at hg
  | [], _ :: _, h, _, _ => by simp [chkOutList] at h
  | _ :: _, [], h, _, _ => by simp [chkOutList] at h
  | g' :: gs, c :: cs, h, g, hg => by
    simp only [chkOutList, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hg with rfl | hg
    · intro hs
      split at h1
      · exact chkOut_sound hN h1
      · rw [Option.isNone_iff_eq_none] at h1; rw [h1] at hs; simp at hs
    · exact chkOutList_sound P N nm hN gs cs h2 g hg

/-! ## Gate output to pin wire -/

theorem split_dot : ∀ (a c : List Char) (b d : List Char), '.' ∉ a → '.' ∉ c → a ++ '.' :: b = c ++ '.' :: d →
    a = c ∧ b = d
  | [], [], b, d, _, _, h => by simp at h; exact ⟨rfl, h⟩
  | [], x :: c, b, d, _, hc, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) hc
  | x :: a, [], b, d, ha, _, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact absurd (h.1 ▸ List.mem_cons_self) ha
  | x :: a, y :: c, b, d, ha, hc, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    obtain ⟨hxy, h⟩ := h
    obtain ⟨e1, e2⟩ := split_dot a c b d (fun hm => ha (List.mem_cons_of_mem _ hm))
      (fun hm => hc (List.mem_cons_of_mem _ hm)) h
    exact ⟨by rw [hxy, e1], e2⟩

theorem str_split_dot {a b c d : String} (ha : '.' ∉ a.toList) (hc : '.' ∉ c.toList)
    (h : a ++ "." ++ b = c ++ "." ++ d) : a = c ∧ b = d := by
  have h' := congrArg String.toList h
  simp only [String.toList_append] at h'
  have : a.toList ++ '.' :: b.toList = c.toList ++ '.' :: d.toList := by simpa using h'
  obtain ⟨e1, e2⟩ := split_dot _ _ _ _ ha hc this
  exact ⟨String.ext e1, String.ext e2⟩

/-- **A site-logic gate's output reaches its site's output-pin wire through the hop that reads it.** -/
theorem hop_from_gate {D : DB} {P : SP} {Q3 : SP3} {C : NT (Nat × Nat)} {nm : Nat → String} {g h : Gate}
    (hdot : ∀ s S, P.sites.get s = some S → '.' ∉ S.name.toList)
    (hh : HopOK D P Q3 C nm h) (hg : OutOK P nm g) (hr : h.ins = [g.out]) :
    ∃ (S : Site) (T : Tl) (gs os : String) (p w : Nat),
      g.name = S.name ++ "." ++ gs ∧ (gs, os) ∈ outTab ∧ (os, p) ∈ hopTab ∧ D.tiles.get S.tile = some T ∧
      outWire Q3 T.ty S.rank p = some w ∧ C.get h.out = some (S.tile, w) := by
  obtain ⟨s, S, T, n, src, p, w, _, _, hin, hS, hT, hnm, hp, hw, hc⟩ := hh
  obtain ⟨s', S', gs, os, hS', hgo, hgn, hon⟩ := hg
  rw [hr] at hin
  have hn : n = g.out := by simpa using hin.symm
  subst hn
  rw [hon] at hnm
  obtain ⟨e1, e2⟩ := str_split_dot (hdot s' S' hS') (hdot s S hS) hnm
  subst e2
  refine ⟨S, T, gs, os, p, w, ?_, hgo, hp, hT, hw, hc⟩
  rw [hgn, e1]

end Formal.Target.NM
