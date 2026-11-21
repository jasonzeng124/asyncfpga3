import Formal.Target.NodeMergeLut

/-!
# Formal.Target.NodeMergePin — MUXF7/F8 select pins and CARRY4 carry-in read their site-pin wires (H_DECODE)

Shard A, 2026-11-08. Companion of `NodeMerge` (pips) and `NodeMergeLut` (LUT pins), for the other logic gates
that read a routing wire: a MUXF7/F8 gate `SITE.F7A` / `.F7B` / `.F8` reads its select on input 2 (site pin AX / CX
/ BX), and a CARRY4 output gate `SITE.CARRY4.CO<i>` / `.O<i>` reads the carry-in on input 0 (site pin CIN, joined by
tileconn to the slice below's COUT) unless that input is a constant (PRECYINIT; re-encoded by `RTPSSel`).
The pin layout (`expect`) is the decoder's (`build_net.py`), the one B's `PrimsPS` models.

**Trusted data (H_DECODE):** `SP2`: per tile type and slice rank, the wires of site pins AX, BX, CX, CIN
(`tile_type_*.json`); the sites table is `NodeMergeLut`'s.
* `XOK D P Q C g`: `g` is named `SITE.<suffix>` for a site of the table and a suffix of `expect`, and its expected
  input reads a node whose canonical wire is joined by tileconn (`Conn`) to that site pin's wire -- or, for a
  carry-in only, the node is one of the listed constant nodes `K`.
-/

namespace Formal.Target.NM
open Formal.Target Formal.Target.RT

/-- Site pin keys: 0 AX, 1 BX, 2 CX, 3 CIN. Key `ty * 2 + rank`, then pin key -> wire. -/
structure SP2 where
  pins : NT (NT Nat)

/-- **The decoder's pin layout**: gate-name suffix -> (input index, site pin key, may be a constant?). -/
def expect (suf : String) : Option (Nat × Nat × Bool) :=
  if suf = "F7A" then some (2, 0, false)
  else if suf = "F7B" then some (2, 2, false)
  else if suf = "F8" then some (2, 1, false)
  else if suf ∈ ["CARRY4.CO0", "CARRY4.CO1", "CARRY4.CO2", "CARRY4.CO3",
                 "CARRY4.O0", "CARRY4.O1", "CARRY4.O2", "CARRY4.O3"] then some (0, 3, true)
  else none

def isX (g : Gate) : Bool :=
  g.name.endsWith ".F7A" || g.name.endsWith ".F7B" || g.name.endsWith ".F8" || g.name.endsWith ".CARRY4.CO0" ||
  g.name.endsWith ".CARRY4.CO1" || g.name.endsWith ".CARRY4.CO2" || g.name.endsWith ".CARRY4.CO3" ||
  g.name.endsWith ".CARRY4.O0" || g.name.endsWith ".CARRY4.O1" || g.name.endsWith ".CARRY4.O2" ||
  g.name.endsWith ".CARRY4.O3"

def pinWire2 (Q : SP2) (ty rank key : Nat) : Option Nat :=
  match Q.pins.get (ty * 2 + rank) with
  | some t => t.get key
  | none => none

/-- **What a checked MUXF / CARRY4 gate satisfies.** -/
def XOK (D : DB) (P : SP) (Q : SP2) (C : NT (Nat × Nat)) (K : List Nat) (g : Gate) : Prop :=
  ∃ (s : Nat) (S : Site) (T : Tl) (suf : String) (j key : Nat) (cst : Bool) (n : Nat),
    P.sites.get s = some S ∧ D.tiles.get S.tile = some T ∧ g.name = S.name ++ "." ++ suf ∧
    expect suf = some (j, key, cst) ∧ g.ins[j]? = some n ∧
    ((∃ w a, pinWire2 Q T.ty S.rank key = some w ∧ C.get n = some a ∧ Conn D (S.tile, w) a) ∨
     (cst = true ∧ n ∈ K))

/-- Certificate: site, suffix, and a tileconn path from the pin wire to the node's canonical wire (`none`: the
node is a listed constant). -/
structure XC where
  s : Nat
  suf : String
  path : Option (List (Nat × Nat × Bool × Nat))

def chkX (D : DB) (P : SP) (Q : SP2) (C : NT (Nat × Nat)) (K : List Nat) (g : Gate) (c : XC) : Bool :=
  match P.sites.get c.s, expect c.suf with
  | some S, some (j, key, cst) =>
    match D.tiles.get S.tile, g.ins[j]? with
    | some T, some n =>
      eqB (bl (S.name ++ "." ++ c.suf)) (bl g.name) &&
      (match c.path with
        | some p =>
          (match pinWire2 Q T.ty S.rank key with
            | some w => endOK D C n (S.tile, w) p
            | none => false)
        | none => cst && K.contains n)
    | _, _ => false
  | _, _ => false

theorem chkX_sound {D : DB} {P : SP} {Q : SP2} {C : NT (Nat × Nat)} {K : List Nat} {g : Gate} {c : XC}
    (h : chkX D P Q C K g c = true) : XOK D P Q C K g := by
  unfold chkX at h
  cases hS : P.sites.get c.s with
  | none => simp [hS] at h
  | some S =>
    cases he : expect c.suf with
    | none => simp [hS, he] at h
    | some e =>
      obtain ⟨j, key, cst⟩ := e
      cases hT : D.tiles.get S.tile with
      | none => simp [hS, he, hT] at h
      | some T =>
        cases hn : g.ins[j]? with
        | none => simp [hS, he, hT, hn] at h
        | some n =>
          simp only [hS, he, hT, hn, Bool.and_eq_true] at h
          obtain ⟨h1, h2⟩ := h
          refine ⟨c.s, S, T, c.suf, j, key, cst, n, hS, hT, (eq_of_eqB h1).symm, he, hn, ?_⟩
          cases hp : c.path with
          | some p =>
            rw [hp] at h2
            cases hw : pinWire2 Q T.ty S.rank key with
            | none => simp [hw] at h2
            | some w =>
              simp only [hw] at h2
              obtain ⟨a, ha, ca⟩ := endOK_sound h2
              exact Or.inl ⟨w, a, rfl, ha, ca⟩
          | none =>
            rw [hp] at h2
            simp only [Bool.and_eq_true, List.contains_iff_mem] at h2
            exact Or.inr ⟨h2.1, h2.2⟩

def chkXList (D : DB) (P : SP) (Q : SP2) (C : NT (Nat × Nat)) (K : List Nat) : List Gate → List (Option XC) → Bool
  | [], [] => true
  | g :: gs, c :: cs =>
    (match c with
      | some c => chkX D P Q C K g c
      | none => !isX g) && chkXList D P Q C K gs cs
  | _, _ => false

theorem chkXList_sound (D : DB) (P : SP) (Q : SP2) (C : NT (Nat × Nat)) (K : List Nat) :
    ∀ (gs : List Gate) (cs : List (Option XC)),
    chkXList D P Q C K gs cs = true → ∀ g ∈ gs, isX g = true → XOK D P Q C K g
  | [], [], _, g, hg, _ => by simp at hg
  | [], _ :: _, h, _, _, _ => by simp [chkXList] at h
  | _ :: _, [], h, _, _, _ => by simp [chkXList] at h
  | g' :: gs, c :: cs, h, g, hg, hp => by
    simp only [chkXList, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hg with rfl | hg
    · split at h1
      · exact chkX_sound h1
      · simp [hp] at h1
    · exact chkXList_sound D P Q C K gs cs h2 g hg hp

end Formal.Target.NM
