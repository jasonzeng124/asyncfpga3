import Formal.Target.RoundTrip

/-!
# Formal.Target.NodeMerge — the netlist's nodes are prjxray's electrical nodes (H_DECODE, wire-to-node merge)

Shard A, 2026-11-08. The Lean round trip (`RoundTrip`, `FormalWit/RTPS`, `RTPSSel`) re-encodes every pip gate as
its FASM feature `TILE.DST.SRC` **from its name**: it never looks at which netlist nodes the gate reads and drives.
So a decoder that wired a pip gate to the wrong node would still pass it. This file closes that gap for pips.

**Trusted data (part of H_DECODE):** a `DB`, a transcription of prjxray-db's `tilegrid.json` (tile name, tile
type, grid x/y) and `tileconn.json` (rules: a grid offset, two tile types, wire pairs) for the part. Tile types
and wire names are interned (indices into the tables). The generator may leave out tiles, rules and wire pairs
nobody uses: `Conn` over a subset of the rules is contained in prjxray's relation, which is the direction proved.

* `DB.Edge p q`: tileconn joins wire `p.2` of tile `p.1` to wire `q.2` of tile `q.1` (tile `q.1` sits at the
  rule's grid offset from tile `p.1`, the tile types match the rule's, and the wire pair is one of the rule's).
* `Conn`: the equivalence closure of `Edge` -- "electrically one node" (as prjxray and the decoder's
  `Fabric.node` define it).
* `PipOK D C g`: pip gate `g` is named `[~]T.D.S` for a tile `T` and wires `D`, `S` of the tables, the node it
  reads has the canonical wire `C(in)` and `Conn (T, S) C(in)`, and the node it drives has `C(out)` with
  `Conn (T, D) C(out)`. `C` (node index -> one wire) is part of the certificate, not trusted.
* `chkList_sound`: a Boolean per-gate check with path certificates (`walk`) proves `PipOK` for every pip gate.
* `pip_link`: if pip `h` reads the node pip `g` drives, then the fabric joins `g`'s destination wire to `h`'s
  source wire (`Conn`). Plainly: every pip-to-pip connection of the netlist is a real connection of the chip.

Not covered here: LUT/MUX/CARRY input pins and site hops (their wire is a site pin of the tile type, from
`tile_type_*.json`), and the converse (two netlist nodes that are one fabric node).
-/

namespace Formal.Target.NM
open Formal.Target Formal.Target.RT

/-! ## Nat-keyed lookup trees (the generator balances them; nothing depends on that) -/

inductive NT (α : Type) where
  | nil
  | leaf (j : Nat) (v : α)
  | node (m : Nat) (l r : NT α)

def NT.get {α : Type} : NT α → Nat → Option α
  | .nil, _ => none
  | .leaf j v, i => if i = j then some v else none
  | .node m l r, i => if i < m then l.get i else r.get i

/-! ## The trusted tables -/

/-- A tile: name, type (index), grid position. -/
structure Tl where
  name : String
  ty : Nat
  x : Nat
  y : Nat

/-- A tileconn rule: tile of type `t2` at offset `(dxp - dxn, dyp - dyn)` from a tile of type `t1`; wire pairs
`(w1, w2)` (keyed by their index in prjxray's list). -/
structure Rl where
  dxp : Nat
  dxn : Nat
  dyp : Nat
  dyn : Nat
  t1 : Nat
  t2 : Nat
  pairs : NT (Nat × Nat)

structure DB where
  tiles : NT Tl
  wires : NT String
  rules : NT Rl

/-- Tiles `A`, `B` are placed as rule `R` says (end 1, end 2). -/
def Place (A B : Tl) (R : Rl) : Prop :=
  A.ty = R.t1 ∧ B.ty = R.t2 ∧ A.x + R.dxp = B.x + R.dxn ∧ A.y + R.dyp = B.y + R.dyn

/-- **One tileconn connection** from (tile, wire) `p` to (tile, wire) `q`. -/
def DB.Edge (D : DB) (p q : Nat × Nat) : Prop :=
  ∃ A B r R k, D.tiles.get p.1 = some A ∧ D.tiles.get q.1 = some B ∧ D.rules.get r = some R ∧
    R.pairs.get k = some (p.2, q.2) ∧ Place A B R

/-- **Electrically one node**: the equivalence closure of `Edge`. -/
inductive Conn (D : DB) : Nat × Nat → Nat × Nat → Prop
  | refl (p : Nat × Nat) : Conn D p p
  | fwd {p q r : Nat × Nat} : D.Edge p q → Conn D q r → Conn D p r
  | bwd {p q r : Nat × Nat} : D.Edge q p → Conn D q r → Conn D p r

theorem Conn.trans {D : DB} {p q r : Nat × Nat} (h1 : Conn D p q) (h2 : Conn D q r) : Conn D p r := by
  induction h1 with
  | refl => exact h2
  | fwd e _ ih => exact .fwd e (ih h2)
  | bwd e _ ih => exact .bwd e (ih h2)

theorem Conn.symm {D : DB} {p q : Nat × Nat} (h : Conn D p q) : Conn D q p := by
  induction h with
  | refl => exact .refl _
  | fwd e _ ih => exact ih.trans (.bwd e (.refl _))
  | bwd e _ ih => exact ih.trans (.fwd e (.refl _))

/-! ## Path certificates -/

def placeB (A B : Tl) (R : Rl) : Bool :=
  A.ty == R.t1 && B.ty == R.t2 && A.x + R.dxp == B.x + R.dxn && A.y + R.dyp == B.y + R.dyn

theorem place_of {A B : Tl} {R : Rl} (h : placeB A B R = true) : Place A B R := by
  simp only [placeB, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

/-- One step `(rule, pair index, backwards?, next tile)` from `p`. -/
def DB.step (D : DB) (p : Nat × Nat) (s : Nat × Nat × Bool × Nat) : Option (Nat × Nat) :=
  match D.tiles.get p.1, D.tiles.get s.2.2.2, D.rules.get s.1 with
  | some A, some B, some R =>
    match R.pairs.get s.2.1 with
    | some (w1, w2) =>
      if s.2.2.1 then (if placeB B A R && p.2 == w2 then some (s.2.2.2, w1) else none)
      else (if placeB A B R && p.2 == w1 then some (s.2.2.2, w2) else none)
    | none => none
  | _, _, _ => none

theorem step_sound (D : DB) (p : Nat × Nat) (s : Nat × Nat × Bool × Nat) (q : Nat × Nat)
    (h : D.step p s = some q) : Conn D p q := by
  obtain ⟨r, k, b, tj⟩ := s
  obtain ⟨ti, wi⟩ := p
  simp only [DB.step] at h
  split at h
  · rename_i A B R hA hB hR
    split at h
    · rename_i w1 w2 hk
      cases b
      · simp only [Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨hpl, hw⟩ := hc
          simp only [Option.some.injEq] at h
          subst h; subst hw
          exact .fwd ⟨A, B, r, R, k, hA, hB, hR, hk, place_of hpl⟩ (.refl _)
        · simp at h
      · simp only [↓reduceIte] at h
        split at h
        · rename_i hc
          simp only [Bool.and_eq_true, beq_iff_eq] at hc
          obtain ⟨hpl, hw⟩ := hc
          simp only [Option.some.injEq] at h
          subst h; subst hw
          exact .bwd ⟨B, A, r, R, k, hB, hA, hR, hk, place_of hpl⟩ (.refl _)
        · simp at h
    · simp at h
  · simp at h

def DB.walk (D : DB) : Nat × Nat → List (Nat × Nat × Bool × Nat) → Option (Nat × Nat)
  | p, [] => some p
  | p, s :: ss => match D.step p s with
    | some q => D.walk q ss
    | none => none

theorem walk_sound (D : DB) : ∀ (ss : List (Nat × Nat × Bool × Nat)) (p q : Nat × Nat),
    D.walk p ss = some q → Conn D p q
  | [], p, q, h => by simp only [DB.walk, Option.some.injEq] at h; subst h; exact .refl _
  | s :: ss, p, q, h => by
    simp only [DB.walk] at h
    split at h
    · rename_i q' hq
      exact (step_sound D p s q' hq).trans (walk_sound D ss q' q h)
    · simp at h

/-! ## Pip gates -/

/-- A pip gate: one input, not a site hop (the same split as `RoundTrip.feats`; implicit pips `~…` included). -/
def isPip (g : Gate) : Bool := g.k == 1 && g.name.startsWith "hop " == false

/-- Certificate for one pip gate: implicit (`~`)?, tile, destination and source wire, and paths from the
pip's source / destination wire to the canonical wire of the node it reads / drives. -/
structure PC where
  til : Bool
  t : Nat
  d : Nat
  s : Nat
  pin : List (Nat × Nat × Bool × Nat)
  pout : List (Nat × Nat × Bool × Nat)

def pipName (D : DB) (c : PC) : Option String :=
  match D.tiles.get c.t, D.wires.get c.d, D.wires.get c.s with
  | some A, some dn, some sn => some ((if c.til then "~" else "") ++ A.name ++ "." ++ dn ++ "." ++ sn)
  | _, _, _ => none

def eqP (a b : Nat × Nat) : Bool := a.1 == b.1 && a.2 == b.2

theorem eqP_eq {a b : Nat × Nat} (h : eqP a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [eqP, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl

def endOK (D : DB) (C : NT (Nat × Nat)) (n : Nat) (p : Nat × Nat) (path : List (Nat × Nat × Bool × Nat)) : Bool :=
  match C.get n, D.walk p path with
  | some a, some b => eqP a b
  | _, _ => false

theorem endOK_sound {D : DB} {C : NT (Nat × Nat)} {n : Nat} {p : Nat × Nat} {path : List (Nat × Nat × Bool × Nat)}
    (h : endOK D C n p path = true) : ∃ a, C.get n = some a ∧ Conn D p a := by
  simp only [endOK] at h
  split at h
  · rename_i a b ha hb
    exact ⟨a, ha, (eqP_eq h) ▸ walk_sound D path p b hb⟩
  · simp at h

def chkPip (D : DB) (C : NT (Nat × Nat)) (g : Gate) (c : PC) : Bool :=
  (match pipName D c with
    | some s => eqB (bl s) (bl g.name)
    | none => false) &&
  (match g.ins with
    | [i] => endOK D C i (c.t, c.s) c.pin
    | _ => false) &&
  endOK D C g.out (c.t, c.d) c.pout

/-- **What a checked pip gate satisfies.** -/
def PipOK (D : DB) (C : NT (Nat × Nat)) (g : Gate) : Prop :=
  ∃ (til : Bool) (t d s : Nat) (A : Tl) (dn sn : String) (i : Nat) (a b : Nat × Nat),
    D.tiles.get t = some A ∧ D.wires.get d = some dn ∧ D.wires.get s = some sn ∧
    g.name = (if til then "~" else "") ++ A.name ++ "." ++ dn ++ "." ++ sn ∧
    g.ins = [i] ∧ C.get i = some a ∧ Conn D (t, s) a ∧ C.get g.out = some b ∧ Conn D (t, d) b

theorem pipName_sound {D : DB} {c : PC} {s : String} (h : pipName D c = some s) :
    ∃ A dn sn, D.tiles.get c.t = some A ∧ D.wires.get c.d = some dn ∧ D.wires.get c.s = some sn ∧
      s = (if c.til then "~" else "") ++ A.name ++ "." ++ dn ++ "." ++ sn := by
  unfold pipName at h
  cases hA : D.tiles.get c.t <;> cases hd : D.wires.get c.d <;> cases hs : D.wires.get c.s <;>
    simp only [hA, hd, hs, reduceCtorEq, Option.some.injEq] at h
  exact ⟨_, _, _, rfl, rfl, rfl, h.symm⟩

theorem chkPip_sound {D : DB} {C : NT (Nat × Nat)} {g : Gate} {c : PC} (h : chkPip D C g c = true) :
    PipOK D C g := by
  simp only [chkPip, Bool.and_eq_true] at h
  obtain ⟨⟨hn, hi⟩, ho⟩ := h
  obtain ⟨b, hb, cb⟩ := endOK_sound ho
  cases hp : pipName D c with
  | none => rw [hp] at hn; simp at hn
  | some s =>
    rw [hp] at hn
    obtain ⟨A, dn, sn, hA, hd, hs, hse⟩ := pipName_sound hp
    have hname : s = g.name := eq_of_eqB hn
    cases hgi : g.ins with
    | nil => rw [hgi] at hi; simp at hi
    | cons i rest =>
      cases rest with
      | cons _ _ => rw [hgi] at hi; simp at hi
      | nil =>
        rw [hgi] at hi
        obtain ⟨a, ha, ca⟩ := endOK_sound hi
        exact ⟨c.til, c.t, c.d, c.s, A, dn, sn, i, a, b, hA, hd, hs, hname ▸ hse, hgi, ha, ca, hb, cb⟩

/-- Gates and their certificates (`none` for a gate that is not a pip). -/
def chkList (D : DB) (C : NT (Nat × Nat)) : List Gate → List (Option PC) → Bool
  | [], [] => true
  | g :: gs, c :: cs =>
    (match c with
      | some c => chkPip D C g c
      | none => !isPip g) && chkList D C gs cs
  | _, _ => false

theorem chkList_sound (D : DB) (C : NT (Nat × Nat)) : ∀ (gs : List Gate) (cs : List (Option PC)),
    chkList D C gs cs = true → ∀ g ∈ gs, isPip g = true → PipOK D C g
  | [], [], _, g, hg, _ => by simp at hg
  | [], _ :: _, h, _, _, _ => by simp [chkList] at h
  | _ :: _, [], h, _, _, _ => by simp [chkList] at h
  | g' :: gs, c :: cs, h, g, hg, hp => by
    simp only [chkList, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.1 hg with rfl | hg
    · split at h1
      · exact chkPip_sound h1
      · simp [hp] at h1
    · exact chkList_sound D C gs cs h2 g hg hp

/-- Chunked form: a check on `(l.drop a).take n` covers those gates. -/
theorem chk_slice (D : DB) (C : NT (Nat × Nat)) (l : List Gate) (a n : Nat) (cs : List (Option PC))
    (h : chkList D C ((l.drop a).take n) cs = true) :
    ∀ g ∈ (l.drop a).take n, isPip g = true → PipOK D C g :=
  chkList_sound D C _ cs h

theorem all_drop_take (P : Gate → Prop) (l : List Gate) (a n : Nat)
    (h1 : ∀ g ∈ (l.drop a).take n, P g) (h2 : ∀ g ∈ l.drop (a + n), P g) : ∀ g ∈ l.drop a, P g := by
  intro g hg
  rw [← List.take_append_drop n (l.drop a), List.drop_drop] at hg
  rcases List.mem_append.1 hg with h | h
  · exact h1 g h
  · exact h2 g h

theorem all_drop_len (P : Gate → Prop) (l : List Gate) (a : Nat) (h : l.length ≤ a) : ∀ g ∈ l.drop a, P g := by
  rw [List.drop_eq_nil_of_le h]; simp

/-! ## What it means: pip-to-pip connections are real -/

/-- **If pip `h` reads the node that pip `g` drives, the fabric joins `g`'s destination wire to `h`'s source
wire** (tile and wire as named in the gates' names `[~]T.D.S`). -/
theorem pip_link {D : DB} {C : NT (Nat × Nat)} {g h : Gate} (hg : PipOK D C g) (hh : PipOK D C h)
    (ih : h.ins = [g.out]) :
    ∃ (tg dg th sh : Nat) (Ag Ah : Tl) (dng shn : String),
      D.tiles.get tg = some Ag ∧ D.wires.get dg = some dng ∧ D.tiles.get th = some Ah ∧ D.wires.get sh = some shn ∧
      (∃ pre s, g.name = pre ++ Ag.name ++ "." ++ dng ++ "." ++ s) ∧
      (∃ pre d, h.name = pre ++ Ah.name ++ "." ++ d ++ "." ++ shn) ∧ Conn D (tg, dg) (th, sh) := by
  obtain ⟨tl, tg, dg, sg, Ag, dng, sng, ig, ag, bg, hAg, hdg, hsg, hng, hig, hag, cag, hbg, cbg⟩ := hg
  obtain ⟨tl', th, dh, sh, Ah, dnh, shn, i', ah, bh, hAh, hdh, hsh, hnh, hih, hah, cah, hbh, cbh⟩ := hh
  rw [ih] at hih
  cases hih
  rw [hbg] at hah
  cases hah
  exact ⟨tg, dg, th, sh, Ag, Ah, dng, shn, hAg, hdg, hAh, hsh, ⟨_, sng, hng⟩, ⟨_, dnh, hnh⟩, cbg.trans cah.symm⟩

end Formal.Target.NM
