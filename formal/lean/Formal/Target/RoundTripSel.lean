import Formal.Target.RoundTrip

/-!
# Formal.Target.RoundTripSel — re-encode the slice output-mux and carry selects (H_DECODE, S1, part 3)

Shard A, 2026-11-06. `RoundTrip.feats` re-encodes pips and LUT6 INIT bits. The decoder also models a slice's
output-mux select (`<L>OUTMUX.<O6|O5|F7|F8|XOR|CY|<L>5Q>`) as a site hop gate `hop TILE/…_<L>MUX` reading the
site-internal node it selects, and a CARRY4's `PRECYINIT` / `<L>CY0` selects through which nodes its CARRY4 gates
read. `selF pre nm g` re-encodes those selects from the gate's own fields and the names of the nodes it reads
(`nm i` = the name of node `i`; in the theorem `nm` is `fun i => net.names.getD i ""`), as roundtrip.py does:

* a hop gate (`k = 1`, name `hop …<L>MUX`) reading node `SLICE_….<pin>`: the feature
  `<pre SLICE_…>.<L>OUTMUX.<o>`, `o` = `O6` for pin `<L>6`, `O5` for `<L>5`, `<L>5Q` for `<L>5Q`, `F7` for
  `F7A`/`F7B`, `F8` for `F8`, `XOR` for `XOR…`, `CY` for `CO…` (any other pin: no feature);
* a CARRY4 `CO3` gate (`k = 10`, name `<site>.CARRY4.CO3`, pins `CI, CYINIT, S0..S3, DI0..DI3`):
  `<pre site>.PRECYINIT.<p>`, `p` = `CIN` if `CI` reads a non-constant node, else `AX` if `CYINIT` does,
  else `C1` / `C0` for `CONST1` / `CONST0`; and `<pre site>.CARRY4.<L>CY0` for each `DI<j>` (`L` = `ABCD[j]`)
  that reads a slice LUT's O5 node (`SLICE_….<x>5`).

A site missing from the prefix table (`pre` gives `""`) gets no feature (RTPS's table holds the LUT sites only).

`nmC NT f` looks node names up in a certificate tree `NT` first and falls back to `f`; `nmC_eq`: if every leaf of
`NT` is right for `f`, it IS `f`. `chkN`/`chkN_sound`/`getD_mid` check certificate leaves against a chunk of the
names list. So the kernel never walks the 187k-name list per lookup, and nothing it uses is unchecked.
-/

namespace Formal.Target.RTS
open Formal.Target Formal.Target.RT

/-! ## Name tests (structural; cheap in the kernel) -/

/-- The name's bytes start with `hop ` (104 111 112 32). -/
def hopB : List UInt8 → Bool
  | a :: b :: c :: d :: _ => a.toNat == 104 && b.toNat == 111 && c.toNat == 112 && d.toNat == 32
  | _ => false

/-- A name `…<L>MUX`: the letter `L`. -/
def muxL (cs : List Char) : Option Char :=
  match cs.reverse with
  | 'X' :: 'U' :: 'M' :: l :: _ => some l
  | _ => none

def isSliceC : List Char → Bool
  | 'S' :: 'L' :: 'I' :: 'C' :: 'E' :: _ => true
  | _ => false

/-- A name `….CARRY4.CO3`. -/
def isCO3 (cs : List Char) : Bool :=
  match cs.reverse with
  | '3' :: 'O' :: 'C' :: '.' :: '4' :: 'Y' :: 'R' :: 'R' :: 'A' :: 'C' :: '.' :: _ => true
  | _ => false

def isConstC (cs : List Char) : Bool :=
  cs == ['C', 'O', 'N', 'S', 'T', '0'] || cs == ['C', 'O', 'N', 'S', 'T', '1']

/-- A slice LUT's O5 node `SLICE_….<x>5`. -/
def isO5C (cs : List Char) : Bool := isSliceC cs && cs.getLast? == some '5'

/-- The output-mux select of a hop of letter `L` reading site pin `pin` (roundtrip.py's table). -/
def outSel (L : Char) (pin : List Char) : Option String :=
  if pin == [L, '6'] then some "O6"
  else if pin == [L, '5'] then some "O5"
  else if pin == [L, '5', 'Q'] then some (String.ofList [L, '5', 'Q'])
  else if pin == ['F', '7', 'A'] || pin == ['F', '7', 'B'] then some "F7"
  else if pin == ['F', '8'] then some "F8"
  else match pin with
    | 'X' :: 'O' :: 'R' :: _ => some "XOR"
    | 'C' :: 'O' :: _ => some "CY"
    | _ => none

/-! ## The select re-encoder -/

/-- The output-mux select feature of a hop gate. -/
def muxFeat (pre : String → String) (nm : Nat → String) (g : Gate) : List String :=
  match muxL g.name.toList, g.ins with
  | some L, [i] =>
    match splitC '.' (nm i).toList with
    | [site, pin] =>
      if isSliceC site then
        match outSel L pin with
        | some o =>
          let p := pre (String.ofList site)
          if p.isEmpty then [] else [p ++ "." ++ String.ofList [L] ++ "OUTMUX." ++ o]
        | none => []
      else []
    | _ => []
  | _, _ => []

/-- The `CY0` feature of carry stage `l` whose `DI` pin reads node `d`. -/
def cy0Feat (p : String) (nm : Nat → String) (d : Nat) (l : Char) : List String :=
  if isO5C (nm d).toList then [p ++ ".CARRY4." ++ String.ofList [l] ++ "CY0"] else []

/-- The `PRECYINIT` and `CY0` features of a CARRY4 `CO3` gate. -/
def carryFeat (pre : String → String) (nm : Nat → String) (g : Gate) : List String :=
  match g.ins with
  | [ci, cy, _, _, _, _, d0, d1, d2, d3] =>
    match splitC '.' g.name.toList with
    | [site, _, _] =>
      let p := pre (String.ofList site)
      if p.isEmpty then [] else
      let pc := if !isConstC (nm ci).toList then "CIN" else if !isConstC (nm cy).toList then "AX"
        else if (nm cy).toList == ['C', 'O', 'N', 'S', 'T', '1'] then "C1" else "C0"
      (p ++ ".PRECYINIT." ++ pc) ::
        (cy0Feat p nm d0 'A' ++ cy0Feat p nm d1 'B' ++ cy0Feat p nm d2 'C' ++ cy0Feat p nm d3 'D')
    | _ => []
  | _ => []

/-- **The select features gate `g` stands for** (output-mux hops and CARRY4 `CO3` gates; every other gate:
none). `nm i` is the name of node `i`. -/
def selF (pre : String → String) (nm : Nat → String) (g : Gate) : List String :=
  if g.k == 1 && hopB (bl g.name) then muxFeat pre nm g
  else if g.k == 10 && isCO3 g.name.toList then carryFeat pre nm g
  else []

/-- The extended re-encoder: `RoundTrip.feats` and the select features. -/
def featsX (pre : String → String) (nm : Nat → String) (g : Gate) : List String := feats pre g ++ selF pre nm g

/-! ## Checked node-name lookup -/

/-- Look node `i`'s name up in the certificate tree `NT`, else ask `f`. -/
def nmC (NT : ITree) (f : Nat → String) (i : Nat) : String :=
  match NT.get i with
  | some s => s
  | none => f i

theorem nmC_eq (NT : ITree) (f : Nat → String) (h : ∀ p ∈ NT.leaves, f p.2 = p.1) : nmC NT f = f := by
  funext i
  unfold nmC
  split
  · rename_i s hs
    exact (h _ (ITree.get_sound NT i s hs)).symm
  · rfl

theorem ITree.forall_node {P : String × Nat → Prop} (m : Nat) (l r : ITree) (hl : ∀ p ∈ l.leaves, P p)
    (hr : ∀ p ∈ r.leaves, P p) : ∀ p ∈ (ITree.node m l r).leaves, P p := by
  intro p hp
  rcases List.mem_append.1 hp with h | h
  · exact hl p h
  · exact hr p h

/-- The certificate pairs `(name, index)` (increasing indices) match the list `l` read from index `k`. -/
def chkN : List String → Nat → List (String × Nat) → Bool
  | _, _, [] => true
  | [], _, _ :: _ => false
  | x :: xs, k, (s, j) :: cs =>
    if j == k then eqB (bl x) (bl s) && chkN xs (k + 1) cs else chkN xs (k + 1) ((s, j) :: cs)

theorem chkN_sound : ∀ (l : List String) (k : Nat) (cs : List (String × Nat)), chkN l k cs = true →
    ∀ p ∈ cs, k ≤ p.2 ∧ p.2 < k + l.length ∧ l.getD (p.2 - k) "" = p.1
  | _, _, [], _ => by simp
  | [], _, _ :: _, h => by simp [chkN] at h
  | x :: xs, k, (s, j) :: cs, h => by
    intro p hp
    simp only [chkN] at h
    split at h
    · rename_i hjk
      have hjk : j = k := by simpa using hjk
      subst hjk
      simp only [Bool.and_eq_true] at h
      have hs := eq_of_eqB h.1
      subst hs
      rcases List.mem_cons.1 hp with hp | hp
      · subst hp; simp
      · obtain ⟨h1, h2, h3⟩ := chkN_sound xs (j + 1) cs h.2 p hp
        refine ⟨by omega, by simp; omega, ?_⟩
        rw [show p.2 - j = (p.2 - (j + 1)) + 1 by omega]
        simpa using h3
    · obtain ⟨h1, h2, h3⟩ := chkN_sound xs (k + 1) ((s, j) :: cs) h p hp
      refine ⟨by omega, by simp; omega, ?_⟩
      rw [show p.2 - k = (p.2 - (k + 1)) + 1 by omega]
      simpa using h3

theorem getD_mid (A l B : List String) (j : Nat) (h1 : A.length ≤ j) (h2 : j < A.length + l.length) :
    (A ++ l ++ B).getD j "" = l.getD (j - A.length) "" := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.append_assoc,
    List.getElem?_append_right h1, List.getElem?_append_left (by omega)]

/-- A name chunk `l` sitting at `A ++ l ++ B`, with `A.length = k`: certificate leaves checked against `l` are
right for the whole list. -/
theorem chkN_mid (A l B : List String) (k : Nat) (hk : A.length = k) (cs : List (String × Nat))
    (h : chkN l k cs = true) : ∀ p ∈ cs, (A ++ l ++ B).getD p.2 "" = p.1 := by
  intro p hp
  obtain ⟨h1, h2, h3⟩ := chkN_sound l k cs h p hp
  subst hk
  rw [getD_mid A l B p.2 h1 h2, h3]

/-! ## Combining with the pip/INIT round trip -/

/-- If the select features plus leftovers `L2` are a permutation of the old leftovers `L`, the extended
re-encoder plus `L2` is a permutation of the target. -/
theorem roundtrip_ext (gates : List Gate) (pre : String → String) (nm : Nat → String) (get : Nat → String)
    (L L2 : List Nat) (tf : List String)
    (hrt : ((gates.flatMap (feats pre)) ++ L.map get).Perm tf)
    (hsel : ((gates.flatMap (selF pre nm)) ++ L2.map get).Perm (L.map get)) :
    ((gates.flatMap (featsX pre nm)) ++ L2.map get).Perm tf := by
  have h1 := flatMap_append_perm gates (feats pre) (selF pre nm)
  refine ((h1.append_right _).trans ?_).trans hrt
  rw [List.append_assoc]
  exact hsel.append_left _

end Formal.Target.RTS
