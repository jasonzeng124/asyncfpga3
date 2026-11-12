import Formal.Net.Fasm.Basic
import Formal.Net.Import.Netlist

/-!
# Track 11c: the bitstream netlist of a whole small design = its yosys netlist

11b (`Formal.Net.Fasm`) reads the physical LUT netlist out of the bits
(`formal/tools/fasm2lean`). 11a (`Formal.Net.Import`) reads the logical
netlist of each library cell out of yosys (`Formal/Net/Import/Cells.lean`).
This file connects the two for a design built from several cells, where
internal nets (the arbiter's `q`, the link's controller node feeding its
latch enables) are NOT visible at any port, so 11b's "state = the value at
the output port" reading no longer works.

## The statement

The logical design is a list of cell instances (`Inst`): an imported
`Import.Netlist` from `Cells.lean`, unchanged, plus where each of its input
ports comes from (`Sig`: a top-level port, or a STATE net of another
instance) and which top-level output ports each of its output ports drives.

The physical side is 11b's `PNet` (physical INITs on physical pins A1..A6,
every pin's source as the bits route it), plus a **renaming** `rho`:
`rho[k][j]` is the physical LUT output that is claimed to be state net `j` of
instance `k`. The renaming is only a witness (the tool proposes it from
nextpnr's placement); nothing below trusts it.

`Design.Correct` says: for EVERY valuation `val` of the top-level inputs and of
every logical state net,
* (next) for each instance `k`, 11a's `Netlist.next` of the yosys netlist
  equals, state by state, the excitation of the physical LUT output `rho[k][j]`
  -- its physical INIT applied to its physical pins, where a pin reads a port,
  a tie, a renamed state, or (recursively) any other physical LUT, which is
  then combinational;
* (outs) for each instance, 11a's `Netlist.outs` equals, port by port, the
  value of the top-level output port the BITS drive;
* (structure) `rho` is injective, names only LUT outputs that exist, has one
  entry per logical state net; the physical output ports are exactly the
  logical ones; there are as many physical LUT sites as logical LUT cells;
  every physical input port is a logical one.

That is "the two netlists are equal up to net renaming" in the functional
sense: same state nets (under `rho`), same next-state function, same outputs.

## How it is decided

`Correct` quantifies over all `val : Sig → Bool`. `check` decides it per
instance over the finitely many signals that instance can read on EITHER side
(`supp`: its logical inputs and states, plus the physical support `psupp` of
every physical source it is compared with, computed through the physical
combinational LUTs). `check_sound` proves that this suffices (`peval_congr`:
physical evaluation reads only `psupp`). So a physical pin wired to the wrong
net -- even to one the logical instance never reads -- is in the support and
is caught. No unproved goals, no added axioms, no native code: `check D = true` is
closed by `decide` per seed.
-/

namespace Formal.Net.FasmLink
open Formal.Cells

abbrev PSrc := Formal.Net.Fasm.Src
abbrev PNet := Formal.Net.Fasm.PNet
abbrev Netlist := Formal.Net.Import.Netlist

/-- A signal of the logical design: a top-level port, or state net `j` of
instance `k`. -/
inductive Sig
  | port (name : String)
  | st (k j : Nat)
  deriving DecidableEq, Repr

/-- One cell instance: an imported yosys netlist (unchanged), where its input
ports come from (one `Sig` per `nl.inputs`, in order), and which top-level
output port each of its output ports drives (`(index into nl.outputs, port)`;
one output may drive several ports). -/
structure Inst where
  name : String
  nl : Netlist
  ins : List Sig
  outs : List (Nat × String)

structure Design where
  insts : List Inst
  net : PNet
  /-- the physical input ports, in `Src.port` index order -/
  ports : List String
  /-- the renaming: `rho[k][j]` = physical source of state `j` of instance `k` -/
  rho : List (List PSrc)
  fuel : Nat

/-- Index of the first occurrence. -/
def idx? {α} [DecidableEq α] (a : α) : List α → Option Nat
  | [] => none
  | b :: l => if a = b then some 0 else (idx? a l).map (· + 1)

def findSt (s : PSrc) : List (List PSrc) → Nat → Option Sig
  | [], _ => none
  | r :: rs, k => match idx? s r with
    | some j => some (.st k j)
    | none => findSt s rs (k + 1)

def dedup : List Sig → List Sig
  | [] => []
  | a :: l => if a ∈ dedup l then dedup l else a :: dedup l

theorem mem_dedup : ∀ (l : List Sig) x, x ∈ l → x ∈ dedup l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons a l ih =>
    intro x h
    simp only [dedup]
    rcases List.mem_cons.1 h with rfl | h
    · split
      · assumption
      · simp
    · split
      · exact ih x h
      · exact List.mem_cons_of_mem _ (ih x h)

namespace Design
variable (D : Design)

/-- The logical state a physical source is renamed to, if any. -/
def stOf (s : PSrc) : Option Sig := findSt s D.rho 0

/-- Physical value of a source, with the renamed state sources read from
`val` and every other LUT output evaluated combinationally (fuel = depth). -/
def peval (val : Sig → Bool) : Nat → PSrc → Option Bool
  | _, .const v => some v
  | _, .port i => (D.ports[i]?).map fun n => val (.port n)
  | 0, .lut i o => (D.stOf (.lut i o)).map val
  | f + 1, .lut i o =>
    match D.stOf (.lut i o) with
    | some s => some (val s)
    | none =>
      match D.net.luts[i]? with
      | some L => (L.pins.mapM (peval val f)).map (L.fn o)
      | none => none

/-- Signals `peval` reads. -/
def psupp : Nat → PSrc → List Sig
  | _, .const _ => []
  | _, .port i => match D.ports[i]? with
    | some n => [.port n]
    | none => []
  | 0, .lut i o => match D.stOf (.lut i o) with
    | some s => [s]
    | none => []
  | f + 1, .lut i o =>
    match D.stOf (.lut i o) with
    | some s => [s]
    | none =>
      match D.net.luts[i]? with
      | some L => L.pins.flatMap (psupp f)
      | none => []

/-- Physical excitation of a renamed state source: its LUT on its pins. -/
def pnext (val : Sig → Bool) : PSrc → Option Bool
  | .lut i o => match D.net.luts[i]? with
    | some L => (L.pins.mapM (D.peval val D.fuel)).map (L.fn o)
    | none => none
  | _ => none

def pnextSupp : PSrc → List Sig
  | .lut i _ => match D.net.luts[i]? with
    | some L => L.pins.flatMap (D.psupp D.fuel)
    | none => []
  | _ => []

/-- Physical value at a top-level output port. -/
def pport (val : Sig → Bool) (p : String) : Option Bool :=
  match D.net.outs.find? (·.1 == p) with
  | some (_, s) => D.peval val D.fuel s
  | none => none

def pportSupp (p : String) : List Sig :=
  match D.net.outs.find? (·.1 == p) with
  | some (_, s) => D.psupp D.fuel s
  | none => []

/-- Logical input and state vectors of instance `k`. -/
def lins (val : Sig → Bool) (I : Inst) : List Bool := I.ins.map val
def stSigs (k : Nat) (I : Inst) : List Sig := (List.range I.nl.state.length).map (Sig.st k)
def lst (val : Sig → Bool) (k : Nat) (I : Inst) : List Bool := (stSigs k I).map val

/-- **The per-instance claim.** -/
def InstOK (val : Sig → Bool) (k : Nat) (I : Inst) (r : List PSrc) : Prop :=
  I.nl.next Formal.Net.Import.boolSem (lins val I) (lst val k I) = r.mapM (D.pnext val) ∧
  ∀ o ∈ I.outs,
    (I.nl.outs Formal.Net.Import.boolSem (lins val I) (lst val k I)).bind (·[o.1]?) = D.pport val o.2

instance (val k I r) : Decidable (D.InstOK val k I r) := by
  unfold InstOK; exact inferInstance

/-- Everything instance `k` can read, on either side (with repetitions). -/
def suppRaw (k : Nat) (I : Inst) (r : List PSrc) : List Sig :=
  I.ins ++ stSigs k I ++ r.flatMap D.pnextSupp ++ I.outs.flatMap (fun o => D.pportSupp o.2)

/-- ... without repetitions: the check enumerates `2 ^ (supp k I r).length` cases. -/
def supp (k : Nat) (I : Inst) (r : List PSrc) : List Sig := dedup (D.suppRaw k I r)

/-- A LUT output of an existing physical LUT. -/
def isLut : PSrc → Bool
  | .lut i _ => decide (i < D.net.luts.length)
  | _ => false

/-- Structural part of the claim. -/
def Structure : Prop :=
  D.rho.length = D.insts.length ∧
  (∀ q ∈ D.insts.zip D.rho, q.2.length = q.1.nl.state.length) ∧
  D.rho.flatten.Nodup ∧
  (∀ s ∈ D.rho.flatten, D.isLut s = true) ∧
  (∀ p ∈ D.net.outs.map (·.1), ∃ I ∈ D.insts, ∃ o ∈ I.outs, o.2 = p) ∧
  (∀ I ∈ D.insts, ∀ o ∈ I.outs, o.2 ∈ D.net.outs.map (·.1)) ∧
  (D.net.outs.map (·.1)).Nodup ∧
  D.net.luts.length = (D.insts.flatMap fun I => I.nl.cells.filter fun c =>
      match c.kind with
      | .lut _ | .lut6_2 => true
      | _ => false).length ∧
  (∀ p ∈ D.ports, ∃ I ∈ D.insts, Sig.port p ∈ I.ins)

instance : Decidable D.Structure := by unfold Structure; exact inferInstance

/-- **The theorem form**: structure, and every instance's claim for every
valuation. -/
def Correct : Prop :=
  D.Structure ∧
  ∀ (val : Sig → Bool) k I r, D.insts[k]? = some I → D.rho[k]? = some r → D.InstOK val k I r

/-! ## The finite check -/

/-- All `n`-bit lists satisfy `f`. -/
def forallBits : Nat → (List Bool → Bool) → Bool
  | 0, f => f []
  | n + 1, f => forallBits n (fun l => f (true :: l)) && forallBits n (fun l => f (false :: l))

theorem forallBits_sound : ∀ n f, forallBits n f = true → ∀ l : List Bool, l.length = n → f l = true := by
  intro n
  induction n with
  | zero => intro f h l hl; cases l with
    | nil => exact h
    | cons _ _ => simp at hl
  | succ n ih =>
    intro f h l hl
    cases l with
    | nil => simp at hl
    | cons b l =>
      simp only [forallBits, Bool.and_eq_true] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      cases b
      · exact ih _ h.2 l hl
      · exact ih _ h.1 l hl

/-- The valuation given by bit list `l` on the signals `V` (false elsewhere). -/
def assoc : List Sig → List Bool → Sig → Bool
  | a :: as, b :: bs, x => if x = a then b else assoc as bs x
  | _, _, _ => false

theorem assoc_map (v : Sig → Bool) : ∀ (V : List Sig) x, x ∈ V → assoc V (V.map v) x = v x := by
  intro V
  induction V with
  | nil => intro x h; cases h
  | cons a V ih =>
    intro x h
    simp only [List.map_cons, assoc]
    by_cases hx : x = a
    · subst hx; simp
    · simp only [hx, ite_false]
      exact ih x (by simpa [hx] using h)

/-- The Boolean check, per seed closed by `decide`. -/
def checkInst (k : Nat) (I : Inst) (r : List PSrc) : Bool :=
  forallBits (D.supp k I r).length fun l => decide (D.InstOK (assoc (D.supp k I r) l) k I r)

def checkAll : List Inst → List (List PSrc) → Nat → Bool
  | I :: Is, r :: rs, k => D.checkInst k I r && checkAll Is rs (k + 1)
  | _, _, _ => true

def check : Bool := decide D.Structure && checkAll D D.insts D.rho 0

/-! ## Soundness: the physical side reads only its support -/

theorem mapM_congr {α β : Type} (f g : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    intro h
    simp only [List.mapM_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem peval_congr (v w : Sig → Bool) :
    ∀ f s, (∀ x ∈ D.psupp f s, v x = w x) → D.peval v f s = D.peval w f s := by
  intro f
  induction f with
  | zero =>
    intro s h
    cases s with
    | const b => rfl
    | port i =>
      simp only [peval, psupp] at h ⊢
      cases hp : D.ports[i]? with
      | none => rfl
      | some n => simp only [hp] at h; simp [h (.port n) (by simp)]
    | lut i o =>
      simp only [peval, psupp] at h ⊢
      cases hs : D.stOf (.lut i o) with
      | none => rfl
      | some s => simp only [hs] at h; simp [h s (by simp)]
  | succ f ih =>
    intro s h
    cases s with
    | const b => rfl
    | port i =>
      simp only [peval, psupp] at h ⊢
      cases hp : D.ports[i]? with
      | none => rfl
      | some n => simp only [hp] at h; simp [h (.port n) (by simp)]
    | lut i o =>
      simp only [peval, psupp] at h ⊢
      cases hs : D.stOf (.lut i o) with
      | some s => simp only [hs] at h; simp [h s (by simp)]
      | none =>
        simp only [hs] at h ⊢
        cases hL : D.net.luts[i]? with
        | none => rfl
        | some L =>
          simp only [hL] at h ⊢
          rw [mapM_congr (D.peval v f) (D.peval w f) L.pins
            (fun p hp => ih p (fun x hx => h x (List.mem_flatMap.2 ⟨p, hp, hx⟩)))]

theorem pnext_congr (v w : Sig → Bool) (s : PSrc) (h : ∀ x ∈ D.pnextSupp s, v x = w x) :
    D.pnext v s = D.pnext w s := by
  cases s with
  | const _ => rfl
  | port _ => rfl
  | lut i o =>
    simp only [pnext, pnextSupp] at h ⊢
    cases hL : D.net.luts[i]? with
    | none => rfl
    | some L =>
      simp only [hL] at h ⊢
      rw [mapM_congr (D.peval v D.fuel) (D.peval w D.fuel) L.pins
        (fun p hp => D.peval_congr v w D.fuel p (fun x hx => h x (List.mem_flatMap.2 ⟨p, hp, hx⟩)))]

theorem pport_congr (v w : Sig → Bool) (p : String) (h : ∀ x ∈ D.pportSupp p, v x = w x) :
    D.pport v p = D.pport w p := by
  simp only [pport, pportSupp] at h ⊢
  cases hf : D.net.outs.find? (·.1 == p) with
  | none => rfl
  | some q =>
    simp only [hf] at h ⊢
    exact D.peval_congr v w D.fuel q.2 h

theorem instOK_congr (v w : Sig → Bool) (k : Nat) (I : Inst) (r : List PSrc)
    (h' : ∀ x ∈ D.supp k I r, v x = w x) : D.InstOK v k I r ↔ D.InstOK w k I r := by
  have h : ∀ x ∈ D.suppRaw k I r, v x = w x := fun x hx => h' x (mem_dedup _ x hx)
  have hin : lins v I = lins w I :=
    List.map_congr_left (fun x hx => h x (by simp [suppRaw, hx]))
  have hst : lst v k I = lst w k I :=
    List.map_congr_left (fun x hx => h x (by simp [suppRaw, hx]))
  have hnx : r.mapM (D.pnext v) = r.mapM (D.pnext w) :=
    mapM_congr _ _ r (fun s hs => D.pnext_congr v w s
      (fun x hx => h x (by simp only [suppRaw, List.mem_append, List.mem_flatMap]; exact Or.inl (Or.inr ⟨s, hs, hx⟩))))
  have hpo : ∀ o ∈ I.outs, D.pport v o.2 = D.pport w o.2 := fun o ho =>
    D.pport_congr v w o.2
      (fun x hx => h x (by simp only [suppRaw, List.mem_append, List.mem_flatMap]; exact Or.inr ⟨o, ho, hx⟩))
  unfold InstOK
  rw [hin, hst, hnx]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun o ho => (h2 o ho).trans (hpo o ho)⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, fun o ho => (h2 o ho).trans (hpo o ho).symm⟩

theorem checkInst_sound (k : Nat) (I : Inst) (r : List PSrc) (hc : D.checkInst k I r = true)
    (val : Sig → Bool) : D.InstOK val k I r := by
  let V := D.supp k I r
  have h1 := forallBits_sound _ _ hc (V.map val) (by simp [V])
  have h2 : D.InstOK (assoc V (V.map val)) k I r := of_decide_eq_true h1
  exact (D.instOK_congr _ _ k I r (fun x hx => assoc_map val V x hx)).1 h2

theorem checkAll_sound : ∀ (Is : List Inst) (rs : List (List PSrc)) (k0 : Nat),
    checkAll D Is rs k0 = true → ∀ val k I r, Is[k]? = some I → rs[k]? = some r →
      D.InstOK val (k0 + k) I r := by
  intro Is
  induction Is with
  | nil => intro rs k0 _ val k I r hI; simp at hI
  | cons I0 Is ih =>
    intro rs k0 hc val k I r hI hr
    cases rs with
    | nil => simp at hr
    | cons r0 rs =>
      simp only [checkAll, Bool.and_eq_true] at hc
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hI hr
        subst hI; subst hr
        exact D.checkInst_sound k0 I0 r0 hc.1 val
      | succ k =>
        simp only [List.getElem?_cons_succ] at hI hr
        have := ih rs (k0 + 1) hc.2 val k I r hI hr
        rwa [Nat.add_assoc, Nat.add_comm 1 k] at this

theorem check_sound (h : D.check = true) : D.Correct := by
  simp only [check, Bool.and_eq_true] at h
  refine ⟨of_decide_eq_true h.1, fun val k I r hI hr => ?_⟩
  have := D.checkAll_sound D.insts D.rho 0 h.2 val k I r hI hr
  rwa [Nat.zero_add] at this

/-! ## Completeness: a design that is `Correct` passes `check`

So `check D = false` (decided) proves `¬ D.Correct`: the negative controls use
this direction. -/

theorem forallBits_complete : ∀ n f, (∀ l : List Bool, l.length = n → f l = true) → forallBits n f = true := by
  intro n
  induction n with
  | zero => intro f h; exact h [] rfl
  | succ n ih =>
    intro f h
    simp only [forallBits, Bool.and_eq_true]
    exact ⟨ih _ (fun l hl => h _ (by simp [hl])), ih _ (fun l hl => h _ (by simp [hl]))⟩

theorem checkAll_complete : ∀ (Is : List Inst) (rs : List (List PSrc)) (k0 : Nat),
    (∀ val k I r, Is[k]? = some I → rs[k]? = some r → D.InstOK val (k0 + k) I r) →
    checkAll D Is rs k0 = true := by
  intro Is
  induction Is with
  | nil => intro rs k0 _; cases rs <;> rfl
  | cons I0 Is ih =>
    intro rs k0 h
    cases rs with
    | nil => rfl
    | cons r0 rs =>
      simp only [checkAll, Bool.and_eq_true]
      refine ⟨forallBits_complete _ _ (fun l _ => decide_eq_true (by
          have := h (assoc (D.supp k0 I0 r0) l) 0 I0 r0 rfl rfl
          rwa [Nat.add_zero] at this)), ih rs (k0 + 1) (fun val k I r hI hr => ?_)⟩
      have := h val (k + 1) I r (by simpa using hI) (by simpa using hr)
      rwa [Nat.add_assoc, Nat.add_comm 1 k] 

theorem check_complete (h : D.Correct) : D.check = true := by
  simp only [check, Bool.and_eq_true]
  refine ⟨decide_eq_true h.1, D.checkAll_complete D.insts D.rho 0 (fun val k I r hI hr => ?_)⟩
  rw [Nat.zero_add]; exact h.2 val k I r hI hr

theorem not_correct (h : D.check = false) : ¬ D.Correct := fun hc => by
  rw [D.check_complete hc] at h; cases h

end Design
end Formal.Net.FasmLink
