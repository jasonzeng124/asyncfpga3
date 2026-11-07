import Formal.Gen.Netlist

/-!
# Probe C-11f: a whole routed design, read back from its bitstream, checked gate by gate

Hand-written half of `Formal.Net.FasmDesign`. The generated half
(`Formal/Net/FasmDesign/GcdD/*.lean`, by `formal/tools/fasm2lean3/gen3.py`) gives

* `rho : Trie` -- a renaming, physical net id -> logical source (a yosys net id or
  a constant). It is a *hint* produced by gen3 from nextpnr's placement; nothing is
  assumed about it: it is the object the theorems are about.
* `insts : List Inst` -- one entry per used physical primitive output group:
  the physical cell decoded from the bits (`phys`), the logical yosys cell it
  implements (`log`, or `none` for a route-through / constant LUT or buffer that
  nextpnr added), the corresponding output pins, and the support (`supp`): the
  logical nets the two cells read.

`Inst.check` is a Boolean test run by `decide +kernel`; `Inst.check_sound` turns
it into `Inst.Sound`, stated with the Core Boolean LUT semantics (`boolSem`,
shard A's `Lut.eval`). All primitive semantics are `Formal.Gen.Cell.out`
(probe 11d): no new primitive model is introduced here.

## What `Inst.Sound rho i` says (no hypotheses)

* **logical cell `l`, physical cell not opaque.** `kindOk`: a physical LUT may
  implement any logical cell (only its function is compared); a physical buffer
  implements a logical buffer; any other physical primitive (FF, CARRY4,
  MUXF7/F8) has exactly `l`'s kind, and a flip-flop also has `l`'s INIT.
  `outs` is non-empty, and for every pair `(pp, lp)` in it: the physical net on
  `pp` renames to the logical net on `lp`, and for EVERY `env : Nat → Bool`
  (a value for every logical net) the physical output -- its input pins read
  through `rho` -- is defined and equals the logical output.
* **route-through** (`log = none`). The physical output net renames to a source
  `s`, and the output equals `s` under every `env`.
* **opaque** (BSCAN). Every physical pin renames to the logical cell's pin net,
  and the logical cell is opaque too.

Read together over all instances: valuing every physical net by the logical net
`rho` maps it to, every physical gate computes what its logical gate computes.
This is a gate-level (connectivity and function) statement; it says nothing
about delays, glitches or X.

Kernel-cost choices: the renaming is a Braun-style binary trie keyed by `Nat`
(~log2 n steps per lookup), the check reads LUT tables with `Nat.testBit`
(`fastSem`, proved equal to `boolSem`), and the `∀ env` is decided by
enumerating the support nets (`forallEnv`, `forallEnv_sound`).
-/

namespace Formal.Net.FasmDesign
open Formal.Gen Formal.Net.CoreLut

/-! ## The renaming -/

/-- Binary trie keyed by `Nat`: key `0` at the root, key `2j+1` is key `j` of
the left subtree, key `2j+2` is key `j` of the right subtree. -/
inductive Trie where
  | leaf
  | node (v : Option Src) (l r : Trie)

def Trie.find : Trie → Nat → Option Src
  | .leaf, _ => none
  | .node v l r, n =>
    match n with
    | 0 => v
    | k + 1 => if k % 2 = 0 then l.find (k / 2) else r.find (k / 2)

/-- Rename a physical source: a net through the trie, a constant to itself. -/
def ren (rho : Trie) : Src → Option Src
  | .net n => rho.find n
  | .const b => some (.const b)

/-! ## Values -/

def srcVal (env : Nat → Bool) : Src → Bool
  | .net n => env n
  | .const b => b

/-- The physical cell's input pins (in `inPins` order), each renamed. -/
def pinsP (rho : Trie) (c : Cell) : Option (List Src) :=
  (inPins c.kind).mapM fun q => (c.conn.lookup q).bind (ren rho)

/-- The logical cell's input pins (in `inPins` order). -/
def pinsL (c : Cell) : Option (List Src) :=
  (inPins c.kind).mapM fun q => c.conn.lookup q

/-- Physical output `pp`, every input pin valued by `env` at its renamed net. -/
def physOut (rho : Trie) (env : Nat → Bool) (p : Cell) (pp : Pin) : Option Bool := do
  let ps ← pinsP rho p
  p.out boolSem pp (ps.map (srcVal env))

/-- Logical output `lp` under `env`. -/
def logOut (env : Nat → Bool) (l : Cell) (lp : Pin) : Option Bool := do
  let ls ← pinsL l
  l.out boolSem lp (ls.map (srcVal env))

/-! ## Fast table reading -/

/-- The LUT table read with `Nat.testBit` at the LSB-first address. -/
def fastSem : Sem Bool := ⟨fun init ins => init.testBit (lsbIdx ins), id⟩

/-- The fast reading IS the Core Boolean semantics (`evalL` = `Lut.eval`). -/
theorem fastSem_eq : fastSem = boolSem := by
  unfold fastSem boolSem
  congr 1
  funext init ins
  exact (evalL_eq_testBit init ins).symm

/-! ## Enumerating valuations -/

def upd (e : Nat → Bool) (n : Nat) (b : Bool) : Nat → Bool :=
  fun m => if m = n then b else e m

/-- `f` holds for every valuation of the nets `supp` (others `false`). -/
def forallEnv : List Nat → ((Nat → Bool) → Bool) → Bool
  | [], f => f (fun _ => false)
  | n :: ns, f => forallEnv ns (fun e => f (upd e n false)) && forallEnv ns (fun e => f (upd e n true))

/-- `env` on `supp`, `false` elsewhere. -/
def restrict (supp : List Nat) (env : Nat → Bool) : Nat → Bool :=
  fun m => if m ∈ supp then env m else false

theorem forallEnv_sound : ∀ (supp : List Nat) (f : (Nat → Bool) → Bool),
    forallEnv supp f = true → ∀ env, f (restrict supp env) = true := by
  intro supp
  induction supp with
  | nil =>
    intro f h env
    have : restrict [] env = fun _ => false := by
      funext m; simp [restrict]
    rw [this]; exact h
  | cons n ns ih =>
    intro f h env
    simp only [forallEnv, Bool.and_eq_true] at h
    have e : restrict (n :: ns) env = upd (restrict ns env) n (env n) := by
      funext m
      by_cases hm : m = n
      · subst hm; simp [restrict, upd]
      · simp [restrict, upd, hm]
    rw [e]
    cases hb : env n
    · exact ih _ h.1 env
    · exact ih _ h.2 env

/-- Every net of `ss` is in `supp`. -/
def suppOk (supp : List Nat) (ss : List Src) : Bool :=
  ss.all fun s => match s with
    | .net n => supp.contains n
    | .const _ => true

theorem srcVal_restrict (supp : List Nat) (env : Nat → Bool) (s : Src)
    (h : suppOk supp [s] = true) : srcVal (restrict supp env) s = srcVal env s := by
  cases s with
  | net n =>
    simp only [suppOk, List.all_cons, List.all_nil, Bool.and_true, List.contains_iff_mem] at h
    simp [srcVal, restrict, h]
  | const b => rfl

theorem map_restrict (supp : List Nat) (env : Nat → Bool) (ss : List Src)
    (h : suppOk supp ss = true) : ss.map (srcVal (restrict supp env)) = ss.map (srcVal env) := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [suppOk, List.all_cons, Bool.and_eq_true] at h
    simp only [List.map_cons]
    rw [ih h.2, srcVal_restrict supp env s
      (by simp only [suppOk, List.all_cons, List.all_nil, Bool.and_true]; exact h.1)]

/-! ## Instances and the check -/

structure Inst where
  phys : Cell
  log : Option Cell
  /-- (physical output pin, logical output pin) pairs that must agree. -/
  outs : List (Pin × Pin)
  /-- The logical nets either cell reads (enumerated by the check). -/
  supp : List Nat

def kindIsFF : Kind → Bool
  | .fdre | .fdse | .fdce | .fdpe => true
  | _ => false

def kindIsBuf : Kind → Bool
  | .buf _ => true
  | _ => false

/-- Which logical cells a physical primitive may implement (see the module doc). -/
def kindOk (p l : Cell) : Bool :=
  match p.kind with
  | .lut6_2 => true
  | .buf _ => kindIsBuf l.kind
  | k => k == l.kind && (!kindIsFF k || p.init == l.init)

/-- The physical net on `pp` renames to the logical net on `lp`. -/
def outRen (rho : Trie) (p l : Cell) (pp lp : Pin) : Bool :=
  match p.conn.lookup pp, l.conn.lookup lp with
  | some s, some t => ren rho s == some t
  | _, _ => false

def outEq (p l : Cell) (ps ls : List Src) (env : Nat → Bool) (pp lp : Pin) : Bool :=
  match p.out fastSem pp (ps.map (srcVal env)), l.out fastSem lp (ls.map (srcVal env)) with
  | some a, some b => a == b
  | _, _ => false

def rtEq (p : Cell) (ps : List Src) (s : Src) (env : Nat → Bool) (pp : Pin) : Bool :=
  p.out fastSem pp (ps.map (srcVal env)) == some (srcVal env s)

def Inst.check (rho : Trie) (i : Inst) : Bool :=
  match i.log with
  | some l =>
    if i.phys.kind.isOpaque then
      l.kind.isOpaque && i.phys.conn.all (fun x => ren rho x.2 == l.conn.lookup x.1)
    else
      match pinsP rho i.phys, pinsL l with
      | some ps, some ls =>
        kindOk i.phys l && !i.outs.isEmpty && suppOk i.supp ps && suppOk i.supp ls &&
        i.outs.all (fun o => outRen rho i.phys l o.1 o.2) &&
        forallEnv i.supp (fun env => i.outs.all fun o => outEq i.phys l ps ls env o.1 o.2)
      | _, _ => false
  | none =>
    match pinsP rho i.phys with
    | some ps =>
      !i.phys.kind.isOpaque && !i.outs.isEmpty && suppOk i.supp ps &&
      i.outs.all fun o =>
        match (i.phys.conn.lookup o.1).bind (ren rho) with
        | some s => suppOk i.supp [s] && forallEnv i.supp (fun env => rtEq i.phys ps s env o.1)
        | none => false
    | none => false

def checkAll (rho : Trie) (insts : List Inst) : Bool := insts.all (·.check rho)

/-! ## Soundness -/

def Inst.Sound (rho : Trie) (i : Inst) : Prop :=
  match i.log with
  | some l =>
    if i.phys.kind.isOpaque then
      l.kind.isOpaque = true ∧ ∀ q s, (q, s) ∈ i.phys.conn → ren rho s = l.conn.lookup q
    else
      kindOk i.phys l = true ∧ i.outs ≠ [] ∧
      ∀ pp lp, (pp, lp) ∈ i.outs →
        (∃ s t, i.phys.conn.lookup pp = some s ∧ l.conn.lookup lp = some t ∧ ren rho s = some t) ∧
        ∀ env : Nat → Bool, ∃ v, physOut rho env i.phys pp = some v ∧ logOut env l lp = some v
  | none =>
    i.phys.kind.isOpaque = false ∧ i.outs ≠ [] ∧
    ∀ pp lp, (pp, lp) ∈ i.outs → ∃ s, (i.phys.conn.lookup pp).bind (ren rho) = some s ∧
      ∀ env : Nat → Bool, physOut rho env i.phys pp = some (srcVal env s)

theorem outRen_sound {rho : Trie} {p l : Cell} {pp lp : Pin} (h : outRen rho p l pp lp = true) :
    ∃ s t, p.conn.lookup pp = some s ∧ l.conn.lookup lp = some t ∧ ren rho s = some t := by
  unfold outRen at h
  split at h
  · rename_i s t hs ht
    exact ⟨s, t, hs, ht, by simpa using h⟩
  · simp at h

theorem outEq_sound {p l : Cell} {ps ls : List Src} {env : Nat → Bool} {pp lp : Pin}
    (h : outEq p l ps ls env pp lp = true) :
    ∃ v, p.out boolSem pp (ps.map (srcVal env)) = some v ∧
      l.out boolSem lp (ls.map (srcVal env)) = some v := by
  unfold outEq at h
  rw [fastSem_eq] at h
  split at h
  · rename_i a b ha hb
    have : a = b := by simpa using h
    subst this
    exact ⟨a, ha, hb⟩
  · simp at h

theorem Inst.check_sound (rho : Trie) (i : Inst) (h : i.check rho = true) : i.Sound rho := by
  obtain ⟨p, log, outs, supp⟩ := i
  cases log with
  | some l =>
    simp only [Inst.check] at h
    simp only [Inst.Sound]
    by_cases hop : p.kind.isOpaque = true
    · simp only [hop, ite_true, Bool.and_eq_true, List.all_eq_true] at h ⊢
      refine ⟨h.1, fun q s hm => ?_⟩
      have := h.2 (q, s) hm
      simpa using this
    · simp only [hop, ite_false, Bool.false_eq_true] at h ⊢
      cases hp : pinsP rho p with
      | none => simp [hp] at h
      | some ps =>
        cases hl : pinsL l with
        | none => simp [hp, hl] at h
        | some ls =>
          simp only [hp, hl, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
            List.all_eq_true] at h
          obtain ⟨⟨⟨⟨⟨hk, hne⟩, hsp⟩, hsl⟩, hren⟩, hall⟩ := h
          refine ⟨hk, hne, fun pp lp hm => ⟨outRen_sound (hren (pp, lp) hm), fun env => ?_⟩⟩
          have h1 := forallEnv_sound supp _ hall env
          simp only [List.all_eq_true] at h1
          obtain ⟨v, hv1, hv2⟩ := outEq_sound (h1 (pp, lp) hm)
          rw [map_restrict supp env ps hsp] at hv1
          rw [map_restrict supp env ls hsl] at hv2
          exact ⟨v, by simp [physOut, hp, hv1], by simp [logOut, hl, hv2]⟩
  | none =>
    simp only [Inst.check] at h
    simp only [Inst.Sound]
    cases hp : pinsP rho p with
    | none => simp [hp] at h
    | some ps =>
      simp only [hp, Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
        List.all_eq_true] at h
      obtain ⟨⟨⟨hop, hne⟩, hsp⟩, hall⟩ := h
      refine ⟨hop, hne, fun pp lp hm => ?_⟩
      have h1 := hall (pp, lp) hm
      simp only at h1
      split at h1
      · rename_i s hs
        simp only [Bool.and_eq_true] at h1
        refine ⟨s, hs, fun env => ?_⟩
        have h2 := forallEnv_sound supp _ h1.2 env
        simp only [rtEq, fastSem_eq, beq_iff_eq] at h2
        rw [map_restrict supp env ps hsp, srcVal_restrict supp env s h1.1] at h2
        simp [physOut, hp, h2]
      · simp at h1

theorem checkAll_sound (rho : Trie) (insts : List Inst) (h : checkAll rho insts = true) :
    ∀ i ∈ insts, i.Sound rho := by
  intro i hi
  simp only [checkAll, List.all_eq_true] at h
  exact Inst.check_sound rho i (h i hi)

/-! ## H_CELLS, INIT half -/

/-- Each `(k, nl, name)`: instance `k` carries a logical cell, and the cell `name`
of the generated library netlist `nl` (`Formal.Gen.Cells`) has its kind and INIT. -/
def bindsOk (insts : List Inst) (binds : List (Nat × Netlist × String)) : Bool :=
  binds.all fun b =>
    match insts[b.1]?, b.2.1.cell? b.2.2 with
    | some i, some g =>
      match i.log with
      | some l => g.kind == l.kind && g.init == l.init
      | none => false
    | _, _ => false

theorem bindsOk_sound (insts : List Inst) (binds : List (Nat × Netlist × String))
    (h : bindsOk insts binds = true) :
    ∀ k nl nm, (k, nl, nm) ∈ binds → ∃ i l g, insts[k]? = some i ∧ i.log = some l ∧
      nl.cell? nm = some g ∧ g.kind = l.kind ∧ g.init = l.init := by
  intro k nl nm hm
  simp only [bindsOk, List.all_eq_true] at h
  have h1 := h _ hm
  simp only at h1
  split at h1
  · rename_i i g hi hg
    split at h1
    · rename_i l hl
      simp only [Bool.and_eq_true, beq_iff_eq] at h1
      exact ⟨i, l, g, hi, hl, hg, h1.1, h1.2⟩
    · simp at h1
  · simp at h1

end Formal.Net.FasmDesign
