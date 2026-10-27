import Formal.Cells.Prelim

/-!
# bd_ctree: a tree of C-elements vs a flat N-input C-element (probe 5c)

`cells/rtl/bd_ce.v`, module `bd_ctree`, builds an N-input rendezvous for
N > 4 as a tree of the one-LUT C-elements `bd_c2`/`bd_c3`/`bd_c4`: the inputs
are cut into chunks of four, each chunk is a `bd_ctree` of width <= 4 (a chunk
of one input is a plain wire, `assign q = a[0]`), and the chunk outputs feed a
`bd_ctree` of width `NCHUNK`. Its header claims:

1. the tree is NOT a flat N-input C-element (header example
   `C(C(a0,a1), C(a2,a3,a4))` with vector `0 1 1 1 1`);
2. under the four-phase discipline it equals one.

Scope of "equals" here (claude/audit REPORT row 21): EQUALITY OF REACHABLE
(phase, inputs, output) STATE SETS in an atomic-cell (H_ATOMIC_CELL),
speed-independent model, plus step matching (`live`). It is not trace
equality, and not a timed result (for timed tree cells see `CTreeTimed`).

## Model (what is proved about)

* **Speed-independent interleaving model.** A state is the input vector plus
  the output bit of every cell. A move is either one environment input change
  or one cell *firing*: the cell's output becomes its real LUT6 INIT evaluated
  (with `lutB`, rst = 0) on its current pin values, its own output on the
  feedback pin. Any cell may fire at any time (unbounded, unknown cell delay),
  moves interleave, nothing else happens. This is hypothesis
  **H_ATOMIC_CELL** (see `Fire`).
* **Interconnect wires may have their own unbounded delay**: the constructor
  `T.wire` is a routed wire modelled as a one-bit buffer that copies its
  source at an arbitrary later time. Every theorem below is for every tree,
  so it holds with or without wire delays on any edge (see `withWires`).
* **Environment disciplines** (`Disc`): `fourPhase` (**H_FOUR_PHASE**: in a
  phase `v` each input moves only toward `v`, so it changes at most once; the
  phase turns only when every leaf input is `v` AND the tree output is `v`),
  `noAck` (the turn waits for the inputs but not for the output), `free`
  (inputs change arbitrarily: "samples N unrelated levels").
* **H_RESET**: the run starts with every input 0 and every cell output 0
  (an explicit hypothesis `H_RESET : AllQ false t0`). The INIT lemmas
  `c2r_rst` etc. show why: with rst = 1 every cell's next value is 0.

## What is proved

* `c2_eq`, `c3_eq`, `c4_eq`: the INITs are the C-element (majority-with-hold).
* Counterexamples (part 1), all with the real INITs:
  `cex_code5` (the generate block's own N = 5 shape `C2(C4(a0..a3), a4)`),
  `cex_header5` (the header's `C(C(a0,a1),C(a2,a3,a4))`): a reachable state
  with inputs `0 1 1 1 1` from which the tree output rises 0 -> 1, a move no
  flat 5-input C-element can make (`flat_rise_needs_all`).
  `cex_noAck5`: without the wait for the acknowledge the code shape also
  fails (output rises while the inputs read `0 0 0 0 1`), so the ack wait in
  H_FOUR_PHASE is needed, not decorative.
* Under H_FOUR_PHASE, for EVERY tree shape (induction on the tree):
  - `reach_inv`: the phase invariant (a cell holding `v` sees `v` on all its
    children);
  - `tree_move_is_flat_move`: each tree move leaves the output unchanged or
    changes it to `v` while every leaf input is `v` (a flat C-element move);
  - `fire_mono`: in phase `v` no cell output ever moves away from `v`: every
    cell switches at most once per phase, no excitation is ever withdrawn
    (speed-independent persistence, no runt/glitch at any node);
  - `settled_at_turn`: when the ack arrives, every internal cell is settled;
  - `refines_flat` / `flat_refines`: the reachable (phase, inputs, output)
    states of the tree are exactly those of the flat C-element over the same
    inputs (`reachable_eq_flat`). Every tree step is a flat step or a
    stutter, and every flat step is matched by a finite sequence of tree
    steps (`live`).
* Instances: `gen 5`, `gen 8` (the generate block's shapes, checked equal to
  the hand-written trees by `rfl`), `withWires (gen 5)`, and `ctree_eq_flat`
  for every width 2..64 of the generate block (`gen_ok` by evaluation).
-/

namespace Formal.Cells.CTree
open Formal.Cells

/-! ## The cells, with the real INITs and pin maps from `bd_ce.v` -/

/-- `bd_c2`: `I0=a I1=b I2=q I3=rst I4=0 I5=0`. -/
def INIT_C2 : Nat := 0x00E800E800E800E8
/-- `bd_c3`: `I0=a I1=b I2=c I3=q I4=rst I5=0`. -/
def INIT_C3 : Nat := 0x0000FE800000FE80
/-- `bd_c4`: `I0=a I1=b I2=c I3=d I4=q I5=rst`. -/
def INIT_C4 : Nat := 0x00000000FFFE8000

def c2r (rst a b q : Bool) : Bool := lutB INIT_C2 [a, b, q, rst, false, false]
def c3r (rst a b c q : Bool) : Bool := lutB INIT_C3 [a, b, c, q, rst, false]
def c4r (rst a b c d q : Bool) : Bool := lutB INIT_C4 [a, b, c, d, q, rst]

/-- The cells in operation (rst = 0). -/
def c2 (a b q : Bool) : Bool := c2r false a b q
def c3 (a b c q : Bool) : Bool := c3r false a b c q
def c4 (a b c d q : Bool) : Bool := c4r false a b c d q

/-- Flat C-element on a list of input values: all 1 -> 1, all 0 -> 0, else hold. -/
def celem (l : List Bool) (q : Bool) : Bool :=
  if l.all id then true else if l.all (! ·) then false else q

theorem c2_eq : ∀ a b q, c2 a b q = celem [a, b] q := by decide
theorem c3_eq : ∀ a b c q, c3 a b c q = celem [a, b, c] q := by decide
theorem c4_eq : ∀ a b c d q, c4 a b c d q = celem [a, b, c, d] q := by decide

/-- Reset: with rst = 1 every cell's next output is 0, whatever its inputs. -/
theorem c2r_rst : ∀ a b q, c2r true a b q = false := by decide
theorem c3r_rst : ∀ a b c q, c3r true a b c q = false := by decide
theorem c4r_rst : ∀ a b c d q, c4r true a b c d q = false := by decide

/-! Per-cell facts used by the tree induction, all by `decide` over the INIT. -/

theorem c2_inv : ∀ v a b q : Bool, (q = v → a = v ∧ b = v) → c2 a b q = v → a = v ∧ b = v := by
  decide
theorem c3_inv : ∀ v a b c q : Bool, (q = v → a = v ∧ b = v ∧ c = v) →
    c3 a b c q = v → a = v ∧ b = v ∧ c = v := by decide
theorem c4_inv : ∀ v a b c d q : Bool, (q = v → a = v ∧ b = v ∧ c = v ∧ d = v) →
    c4 a b c d q = v → a = v ∧ b = v ∧ c = v ∧ d = v := by decide
theorem c2_out : ∀ v a b q : Bool, (q = v → a = v ∧ b = v) →
    c2 a b q = q ∨ (c2 a b q = v ∧ a = v ∧ b = v) := by decide
theorem c3_out : ∀ v a b c q : Bool, (q = v → a = v ∧ b = v ∧ c = v) →
    c3 a b c q = q ∨ (c3 a b c q = v ∧ a = v ∧ b = v ∧ c = v) := by decide
theorem c4_out : ∀ v a b c d q : Bool, (q = v → a = v ∧ b = v ∧ c = v ∧ d = v) →
    c4 a b c d q = q ∨ (c4 a b c d q = v ∧ a = v ∧ b = v ∧ c = v ∧ d = v) := by decide
theorem c2_all : ∀ v q : Bool, c2 v v q = v := by decide
theorem c3_all : ∀ v q : Bool, c3 v v v q = v := by decide
theorem c4_all : ∀ v q : Bool, c4 v v v v q = v := by decide
theorem buf_out : ∀ v x q : Bool, (q = v → x = v) → x = q ∨ x = v := by decide

/-! ## Trees and their state -/

/-- A C-element tree whose cells carry their current output bit. -/
inductive T where
  /-- input `a[i]` (a chunk of one input is a plain wire in the RTL) -/
  | leaf (i : Nat)
  /-- a routed wire with its own unbounded delay, holding the value it last copied -/
  | wire (q : Bool) (c : T)
  | n2 (q : Bool) (a b : T)
  | n3 (q : Bool) (a b c : T)
  | n4 (q : Bool) (a b c d : T)
  deriving DecidableEq, Repr

abbrev Inp := Nat → Bool

def upd (inp : Inp) (i : Nat) (b : Bool) : Inp := fun j => if j = i then b else inp j

/-- The value a node drives. -/
def out (inp : Inp) : T → Bool
  | .leaf i => inp i
  | .wire q _ => q
  | .n2 q _ _ => q
  | .n3 q _ _ _ => q
  | .n4 q _ _ _ _ => q

def leaves : T → List Nat
  | .leaf i => [i]
  | .wire _ c => leaves c
  | .n2 _ a b => leaves a ++ leaves b
  | .n3 _ a b c => leaves a ++ leaves b ++ leaves c
  | .n4 _ a b c d => leaves a ++ leaves b ++ leaves c ++ leaves d

def IsCell : T → Prop
  | .leaf _ => False
  | _ => True

/-- Every leaf input equals `v`. -/
def AllV (inp : Inp) (v : Bool) : T → Prop
  | .leaf i => inp i = v
  | .wire _ c => AllV inp v c
  | .n2 _ a b => AllV inp v a ∧ AllV inp v b
  | .n3 _ a b c => AllV inp v a ∧ AllV inp v b ∧ AllV inp v c
  | .n4 _ a b c d => AllV inp v a ∧ AllV inp v b ∧ AllV inp v c ∧ AllV inp v d

/-- Every cell (and wire) holds `v`. -/
def AllQ (v : Bool) : T → Prop
  | .leaf _ => True
  | .wire q c => q = v ∧ AllQ v c
  | .n2 q a b => q = v ∧ AllQ v a ∧ AllQ v b
  | .n3 q a b c => q = v ∧ AllQ v a ∧ AllQ v b ∧ AllQ v c
  | .n4 q a b c d => q = v ∧ AllQ v a ∧ AllQ v b ∧ AllQ v c ∧ AllQ v d

instance decAllV (inp : Inp) (v : Bool) : (t : T) → Decidable (AllV inp v t)
  | .leaf i => inferInstanceAs (Decidable (inp i = v))
  | .wire _ c => decAllV inp v c
  | .n2 _ a b => @instDecidableAnd _ _ (decAllV inp v a) (decAllV inp v b)
  | .n3 _ a b c => @instDecidableAnd _ _ (decAllV inp v a)
      (@instDecidableAnd _ _ (decAllV inp v b) (decAllV inp v c))
  | .n4 _ a b c d => @instDecidableAnd _ _ (decAllV inp v a)
      (@instDecidableAnd _ _ (decAllV inp v b)
        (@instDecidableAnd _ _ (decAllV inp v c) (decAllV inp v d)))

instance decAllQ (v : Bool) : (t : T) → Decidable (AllQ v t)
  | .leaf _ => inferInstanceAs (Decidable True)
  | .wire q c => @instDecidableAnd _ _ (inferInstanceAs (Decidable (q = v))) (decAllQ v c)
  | .n2 q a b => @instDecidableAnd _ _ (inferInstanceAs (Decidable (q = v)))
      (@instDecidableAnd _ _ (decAllQ v a) (decAllQ v b))
  | .n3 q a b c => @instDecidableAnd _ _ (inferInstanceAs (Decidable (q = v)))
      (@instDecidableAnd _ _ (decAllQ v a)
        (@instDecidableAnd _ _ (decAllQ v b) (decAllQ v c)))
  | .n4 q a b c d => @instDecidableAnd _ _ (inferInstanceAs (Decidable (q = v)))
      (@instDecidableAnd _ _ (decAllQ v a)
        (@instDecidableAnd _ _ (decAllQ v b)
          (@instDecidableAnd _ _ (decAllQ v c) (decAllQ v d))))

instance decIsCell : (t : T) → Decidable (IsCell t)
  | .leaf _ => inferInstanceAs (Decidable False)
  | .wire _ _ => inferInstanceAs (Decidable True)
  | .n2 _ _ _ => inferInstanceAs (Decidable True)
  | .n3 _ _ _ _ => inferInstanceAs (Decidable True)
  | .n4 _ _ _ _ _ => inferInstanceAs (Decidable True)

/-- **H_ATOMIC_CELL** (the speed-independent model). One atomic move: one cell
(or wire) replaces its output by its LUT INIT evaluated on its current pins,
its own current output on the feedback pin. Physically this stands for: (i) a
LUT's output makes one clean transition when its addressed INIT bit changes
(no glitch/runt: see `fire_mono` for why no excitation is ever withdrawn, and
probe 4/5a for the single-input-change glitch freedom under H_KLEENE_LUT);
(ii) the feedback branch of the cell's output fork reaches its own I-pin
before any other pin of that LUT changes again (isochronic feedback fork).
Test: GLS of a routed tree with the feedback pip delay maximised against
the shortest round trip through the environment. -/
inductive Fire (inp : Inp) : T → T → Prop
  | wire (q : Bool) (c : T) : Fire inp (.wire q c) (.wire (out inp c) c)
  | wireC {q : Bool} {c c' : T} : Fire inp c c' → Fire inp (.wire q c) (.wire q c')
  | n2 (q : Bool) (a b : T) : Fire inp (.n2 q a b) (.n2 (c2 (out inp a) (out inp b) q) a b)
  | n2a {q : Bool} {a a' b : T} : Fire inp a a' → Fire inp (.n2 q a b) (.n2 q a' b)
  | n2b {q : Bool} {a b b' : T} : Fire inp b b' → Fire inp (.n2 q a b) (.n2 q a b')
  | n3 (q : Bool) (a b c : T) :
      Fire inp (.n3 q a b c) (.n3 (c3 (out inp a) (out inp b) (out inp c) q) a b c)
  | n3a {q : Bool} {a a' b c : T} : Fire inp a a' → Fire inp (.n3 q a b c) (.n3 q a' b c)
  | n3b {q : Bool} {a b b' c : T} : Fire inp b b' → Fire inp (.n3 q a b c) (.n3 q a b' c)
  | n3c {q : Bool} {a b c c' : T} : Fire inp c c' → Fire inp (.n3 q a b c) (.n3 q a b c')
  | n4 (q : Bool) (a b c d : T) :
      Fire inp (.n4 q a b c d)
        (.n4 (c4 (out inp a) (out inp b) (out inp c) (out inp d) q) a b c d)
  | n4a {q : Bool} {a a' b c d : T} : Fire inp a a' → Fire inp (.n4 q a b c d) (.n4 q a' b c d)
  | n4b {q : Bool} {a b b' c d : T} : Fire inp b b' → Fire inp (.n4 q a b c d) (.n4 q a b' c d)
  | n4c {q : Bool} {a b c c' d : T} : Fire inp c c' → Fire inp (.n4 q a b c d) (.n4 q a b c' d)
  | n4d {q : Bool} {a b c d d' : T} : Fire inp d d' → Fire inp (.n4 q a b c d) (.n4 q a b c d')

/-! ## The phase invariant -/

/-- In phase `v`: every cell (and wire) that holds `v` sees `v` on all its inputs. -/
def Inv (v : Bool) (inp : Inp) : T → Prop
  | .leaf _ => True
  | .wire q c => (q = v → out inp c = v) ∧ Inv v inp c
  | .n2 q a b => (q = v → out inp a = v ∧ out inp b = v) ∧ Inv v inp a ∧ Inv v inp b
  | .n3 q a b c => (q = v → out inp a = v ∧ out inp b = v ∧ out inp c = v) ∧
      Inv v inp a ∧ Inv v inp b ∧ Inv v inp c
  | .n4 q a b c d => (q = v → out inp a = v ∧ out inp b = v ∧ out inp c = v ∧ out inp d = v) ∧
      Inv v inp a ∧ Inv v inp b ∧ Inv v inp c ∧ Inv v inp d

theorem all_of_inv {v : Bool} {inp : Inp} : ∀ {t : T}, Inv v inp t → out inp t = v → AllV inp v t
  | .leaf _, _, h => h
  | .wire _ c, ⟨h1, h2⟩, h => all_of_inv (t := c) h2 (h1 h)
  | .n2 _ a b, ⟨h1, ha, hb⟩, h =>
      have e := h1 h
      ⟨all_of_inv (t := a) ha e.1, all_of_inv (t := b) hb e.2⟩
  | .n3 _ a b c, ⟨h1, ha, hb, hc⟩, h =>
      have e := h1 h
      ⟨all_of_inv (t := a) ha e.1, all_of_inv (t := b) hb e.2.1, all_of_inv (t := c) hc e.2.2⟩
  | .n4 _ a b c d, ⟨h1, ha, hb, hc, hd⟩, h =>
      have e := h1 h
      ⟨all_of_inv (t := a) ha e.1, all_of_inv (t := b) hb e.2.1,
       all_of_inv (t := c) hc e.2.2.1, all_of_inv (t := d) hd e.2.2.2⟩

/-- When the output holds `v`, every internal cell holds `v` (all settled). -/
theorem allQ_of_inv {v : Bool} {inp : Inp} : ∀ {t : T}, Inv v inp t → out inp t = v → AllQ v t
  | .leaf _, _, _ => trivial
  | .wire _ c, ⟨h1, h2⟩, h => ⟨h, allQ_of_inv (t := c) h2 (h1 h)⟩
  | .n2 _ a b, ⟨h1, ha, hb⟩, h =>
      have e := h1 h
      ⟨h, allQ_of_inv (t := a) ha e.1, allQ_of_inv (t := b) hb e.2⟩
  | .n3 _ a b c, ⟨h1, ha, hb, hc⟩, h =>
      have e := h1 h
      ⟨h, allQ_of_inv (t := a) ha e.1, allQ_of_inv (t := b) hb e.2.1,
        allQ_of_inv (t := c) hc e.2.2⟩
  | .n4 _ a b c d, ⟨h1, ha, hb, hc, hd⟩, h =>
      have e := h1 h
      ⟨h, allQ_of_inv (t := a) ha e.1, allQ_of_inv (t := b) hb e.2.1,
       allQ_of_inv (t := c) hc e.2.2.1, allQ_of_inv (t := d) hd e.2.2.2⟩

theorem keep_v {v x y : Bool} {P : Prop} (h : y = x ∨ (y = v ∧ P)) (hx : x = v) : y = v := by
  rcases h with e | ⟨e, _⟩
  · exact e.trans hx
  · exact e

/-- One firing preserves the invariant, and changes the node's output only to
`v`, and only when every leaf below is `v`. -/
theorem fire_inv {v : Bool} {inp : Inp} {t t' : T} (hf : Fire inp t t') :
    Inv v inp t → Inv v inp t' ∧ (out inp t' = out inp t ∨ (out inp t' = v ∧ AllV inp v t)) := by
  induction hf with
  | wire q c =>
    intro ⟨h1, h2⟩
    refine ⟨⟨fun h => h, h2⟩, ?_⟩
    rcases buf_out v _ q h1 with e | e
    · exact Or.inl e
    · exact Or.inr ⟨e, all_of_inv (t := c) h2 e⟩
  | wireC _ ih =>
    intro ⟨h1, h2⟩
    obtain ⟨i', o'⟩ := ih h2
    exact ⟨⟨fun hq => keep_v o' (h1 hq), i'⟩, Or.inl rfl⟩
  | n2 q a b =>
    intro ⟨h1, ha, hb⟩
    refine ⟨⟨c2_inv v _ _ q h1, ha, hb⟩, ?_⟩
    rcases c2_out v _ _ q h1 with e | ⟨e, ea, eb⟩
    · exact Or.inl e
    · exact Or.inr ⟨e, all_of_inv ha ea, all_of_inv hb eb⟩
  | n2a _ ih =>
    intro ⟨h1, ha, hb⟩
    obtain ⟨i', o'⟩ := ih ha
    exact ⟨⟨fun hq => ⟨keep_v o' (h1 hq).1, (h1 hq).2⟩, i', hb⟩, Or.inl rfl⟩
  | n2b _ ih =>
    intro ⟨h1, ha, hb⟩
    obtain ⟨i', o'⟩ := ih hb
    exact ⟨⟨fun hq => ⟨(h1 hq).1, keep_v o' (h1 hq).2⟩, ha, i'⟩, Or.inl rfl⟩
  | n3 q a b c =>
    intro ⟨h1, ha, hb, hc⟩
    refine ⟨⟨c3_inv v _ _ _ q h1, ha, hb, hc⟩, ?_⟩
    rcases c3_out v _ _ _ q h1 with e | ⟨e, ea, eb, ec⟩
    · exact Or.inl e
    · exact Or.inr ⟨e, all_of_inv ha ea, all_of_inv hb eb, all_of_inv hc ec⟩
  | n3a _ ih =>
    intro ⟨h1, ha, hb, hc⟩
    obtain ⟨i', o'⟩ := ih ha
    exact ⟨⟨fun hq => ⟨keep_v o' (h1 hq).1, (h1 hq).2⟩, i', hb, hc⟩, Or.inl rfl⟩
  | n3b _ ih =>
    intro ⟨h1, ha, hb, hc⟩
    obtain ⟨i', o'⟩ := ih hb
    exact ⟨⟨fun hq => ⟨(h1 hq).1, keep_v o' (h1 hq).2.1, (h1 hq).2.2⟩, ha, i', hc⟩, Or.inl rfl⟩
  | n3c _ ih =>
    intro ⟨h1, ha, hb, hc⟩
    obtain ⟨i', o'⟩ := ih hc
    exact ⟨⟨fun hq => ⟨(h1 hq).1, (h1 hq).2.1, keep_v o' (h1 hq).2.2⟩, ha, hb, i'⟩, Or.inl rfl⟩
  | n4 q a b c d =>
    intro ⟨h1, ha, hb, hc, hd⟩
    refine ⟨⟨c4_inv v _ _ _ _ q h1, ha, hb, hc, hd⟩, ?_⟩
    rcases c4_out v _ _ _ _ q h1 with e | ⟨e, ea, eb, ec, ed⟩
    · exact Or.inl e
    · exact Or.inr ⟨e, all_of_inv ha ea, all_of_inv hb eb, all_of_inv hc ec, all_of_inv hd ed⟩
  | n4a _ ih =>
    intro ⟨h1, ha, hb, hc, hd⟩
    obtain ⟨i', o'⟩ := ih ha
    exact ⟨⟨fun hq => ⟨keep_v o' (h1 hq).1, (h1 hq).2⟩, i', hb, hc, hd⟩, Or.inl rfl⟩
  | n4b _ ih =>
    intro ⟨h1, ha, hb, hc, hd⟩
    obtain ⟨i', o'⟩ := ih hb
    exact ⟨⟨fun hq => ⟨(h1 hq).1, keep_v o' (h1 hq).2.1, (h1 hq).2.2⟩, ha, i', hc, hd⟩,
      Or.inl rfl⟩
  | n4c _ ih =>
    intro ⟨h1, ha, hb, hc, hd⟩
    obtain ⟨i', o'⟩ := ih hc
    exact ⟨⟨fun hq => ⟨(h1 hq).1, (h1 hq).2.1, keep_v o' (h1 hq).2.2.1, (h1 hq).2.2.2⟩,
      ha, hb, i', hd⟩, Or.inl rfl⟩
  | n4d _ ih =>
    intro ⟨h1, ha, hb, hc, hd⟩
    obtain ⟨i', o'⟩ := ih hd
    exact ⟨⟨fun hq => ⟨(h1 hq).1, (h1 hq).2.1, (h1 hq).2.2.1, keep_v o' (h1 hq).2.2.2⟩,
      ha, hb, hc, i'⟩, Or.inl rfl⟩

/-- Inputs only move toward `v`. -/
def Mon (v : Bool) (inp inp' : Inp) : Prop := ∀ j, inp j = v → inp' j = v

theorem mon_upd (v : Bool) (inp : Inp) (i : Nat) : Mon v inp (upd inp i v) := by
  intro j h; unfold upd; split
  · rfl
  · exact h

theorem out_mon {v : Bool} {inp inp' : Inp} (hm : Mon v inp inp') :
    ∀ {t : T}, out inp t = v → out inp' t = v
  | .leaf i, h => hm i h
  | .wire _ _, h => h
  | .n2 _ _ _, h => h
  | .n3 _ _ _ _, h => h
  | .n4 _ _ _ _ _, h => h

theorem inv_env {v : Bool} {inp inp' : Inp} (hm : Mon v inp inp') :
    ∀ {t : T}, Inv v inp t → Inv v inp' t
  | .leaf _, _ => trivial
  | .wire _ c, ⟨h1, h2⟩ => ⟨fun hq => out_mon hm (h1 hq), inv_env hm (t := c) h2⟩
  | .n2 _ a b, ⟨h1, ha, hb⟩ =>
      ⟨fun hq => ⟨out_mon hm (h1 hq).1, out_mon hm (h1 hq).2⟩,
       inv_env hm (t := a) ha, inv_env hm (t := b) hb⟩
  | .n3 _ a b c, ⟨h1, ha, hb, hc⟩ =>
      ⟨fun hq => ⟨out_mon hm (h1 hq).1, out_mon hm (h1 hq).2.1, out_mon hm (h1 hq).2.2⟩,
       inv_env hm (t := a) ha, inv_env hm (t := b) hb, inv_env hm (t := c) hc⟩
  | .n4 _ a b c d, ⟨h1, ha, hb, hc, hd⟩ =>
      ⟨fun hq => ⟨out_mon hm (h1 hq).1, out_mon hm (h1 hq).2.1, out_mon hm (h1 hq).2.2.1,
        out_mon hm (h1 hq).2.2.2⟩,
       inv_env hm (t := a) ha, inv_env hm (t := b) hb, inv_env hm (t := c) hc,
       inv_env hm (t := d) hd⟩

theorem not_both {q v : Bool} (h1 : q = v) (h2 : q = !v) : False := by
  subst h1; cases q <;> simp at h2

/-- At the phase turn (output = `v`) the invariant of the next phase holds. -/
theorem inv_flip {v : Bool} {inp : Inp} : ∀ {t : T}, Inv v inp t → out inp t = v → Inv (!v) inp t
  | .leaf _, _, _ => trivial
  | .wire _ c, ⟨h1, h2⟩, h => ⟨fun hq => (not_both h hq).elim, inv_flip (t := c) h2 (h1 h)⟩
  | .n2 _ a b, ⟨h1, ha, hb⟩, h =>
      have e := h1 h
      ⟨fun hq => (not_both h hq).elim, inv_flip (t := a) ha e.1, inv_flip (t := b) hb e.2⟩
  | .n3 _ a b c, ⟨h1, ha, hb, hc⟩, h =>
      have e := h1 h
      ⟨fun hq => (not_both h hq).elim, inv_flip (t := a) ha e.1, inv_flip (t := b) hb e.2.1,
        inv_flip (t := c) hc e.2.2⟩
  | .n4 _ a b c d, ⟨h1, ha, hb, hc, hd⟩, h =>
      have e := h1 h
      ⟨fun hq => (not_both h hq).elim, inv_flip (t := a) ha e.1, inv_flip (t := b) hb e.2.1,
        inv_flip (t := c) hc e.2.2.1, inv_flip (t := d) hd e.2.2.2⟩

theorem inv_of_allQ {w : Bool} {inp : Inp} : ∀ {t : T}, AllQ w t → Inv (!w) inp t
  | .leaf _, _ => trivial
  | .wire _ c, ⟨h, hc⟩ => ⟨fun hq => (not_both h hq).elim, inv_of_allQ (t := c) hc⟩
  | .n2 _ a b, ⟨h, ha, hb⟩ =>
      ⟨fun hq => (not_both h hq).elim, inv_of_allQ (t := a) ha, inv_of_allQ (t := b) hb⟩
  | .n3 _ a b c, ⟨h, ha, hb, hc⟩ =>
      ⟨fun hq => (not_both h hq).elim, inv_of_allQ (t := a) ha, inv_of_allQ (t := b) hb,
        inv_of_allQ (t := c) hc⟩
  | .n4 _ a b c d, ⟨h, ha, hb, hc, hd⟩ =>
      ⟨fun hq => (not_both h hq).elim, inv_of_allQ (t := a) ha, inv_of_allQ (t := b) hb,
        inv_of_allQ (t := c) hc, inv_of_allQ (t := d) hd⟩

/-! ## Shape facts -/

theorem fire_leaves {inp : Inp} {t t' : T} (hf : Fire inp t t') : leaves t' = leaves t := by
  induction hf <;> simp_all [leaves]

theorem fire_cell {inp : Inp} {t t' : T} (hf : Fire inp t t') : IsCell t' := by
  cases hf <;> trivial

theorem out_cell {inp inp' : Inp} : ∀ {t : T}, IsCell t → out inp t = out inp' t
  | .leaf _, h => h.elim
  | .wire _ _, _ => rfl
  | .n2 _ _ _, _ => rfl
  | .n3 _ _ _ _, _ => rfl
  | .n4 _ _ _ _ _, _ => rfl

theorem out_allQ {v : Bool} {inp : Inp} : ∀ {t : T}, IsCell t → AllQ v t → out inp t = v
  | .leaf _, h, _ => h.elim
  | .wire _ _, _, h => h.1
  | .n2 _ _ _, _, h => h.1
  | .n3 _ _ _ _, _, h => h.1
  | .n4 _ _ _ _ _, _, h => h.1

theorem out_allQV {v : Bool} {inp : Inp} : ∀ {t : T}, AllQ v t → AllV inp v t → out inp t = v
  | .leaf _, _, h => h
  | .wire _ _, h, _ => h.1
  | .n2 _ _ _, h, _ => h.1
  | .n3 _ _ _ _, h, _ => h.1
  | .n4 _ _ _ _ _, h, _ => h.1

theorem allV_iff {inp : Inp} {v : Bool} : ∀ {t : T}, AllV inp v t ↔ ∀ i ∈ leaves t, inp i = v
  | .leaf i => by simp [AllV, leaves]
  | .wire _ c => by simpa [AllV, leaves] using allV_iff (t := c)
  | .n2 _ a b => by
      simp only [AllV, leaves, List.mem_append, allV_iff (t := a), allV_iff (t := b)]
      constructor
      · intro ⟨ha, hb⟩ i hi; rcases hi with h | h; exact ha i h; exact hb i h
      · intro h; exact ⟨fun i hi => h i (Or.inl hi), fun i hi => h i (Or.inr hi)⟩
  | .n3 _ a b c => by
      simp only [AllV, leaves, List.mem_append, allV_iff (t := a), allV_iff (t := b),
        allV_iff (t := c)]
      constructor
      · intro ⟨ha, hb, hc⟩ i hi
        rcases hi with (h | h) | h
        · exact ha i h
        · exact hb i h
        · exact hc i h
      · intro h
        exact ⟨fun i hi => h i (Or.inl (Or.inl hi)), fun i hi => h i (Or.inl (Or.inr hi)),
          fun i hi => h i (Or.inr hi)⟩
  | .n4 _ a b c d => by
      simp only [AllV, leaves, List.mem_append, allV_iff (t := a), allV_iff (t := b),
        allV_iff (t := c), allV_iff (t := d)]
      constructor
      · intro ⟨ha, hb, hc, hd⟩ i hi
        rcases hi with ((h | h) | h) | h
        · exact ha i h
        · exact hb i h
        · exact hc i h
        · exact hd i h
      · intro h
        exact ⟨fun i hi => h i (Or.inl (Or.inl (Or.inl hi))),
          fun i hi => h i (Or.inl (Or.inl (Or.inr hi))),
          fun i hi => h i (Or.inl (Or.inr hi)), fun i hi => h i (Or.inr hi)⟩

theorem leaves_ne : ∀ (t : T), leaves t ≠ []
  | .leaf _ => by simp [leaves]
  | .wire _ c => by simpa [leaves] using leaves_ne c
  | .n2 _ a _ => by simp [leaves, leaves_ne a]
  | .n3 _ a _ _ => by simp [leaves, leaves_ne a]
  | .n4 _ a _ _ _ => by simp [leaves, leaves_ne a]

/-! ## Monotonicity: no cell ever moves away from `v` during phase `v` -/

/-- `t'` is `t` with some cells moved to `v` (none moved away from `v`). -/
def Mono (v : Bool) : T → T → Prop
  | .leaf i, .leaf j => i = j
  | .wire q c, .wire q' c' => (q = v → q' = v) ∧ Mono v c c'
  | .n2 q a b, .n2 q' a' b' => (q = v → q' = v) ∧ Mono v a a' ∧ Mono v b b'
  | .n3 q a b c, .n3 q' a' b' c' => (q = v → q' = v) ∧ Mono v a a' ∧ Mono v b b' ∧ Mono v c c'
  | .n4 q a b c d, .n4 q' a' b' c' d' =>
      (q = v → q' = v) ∧ Mono v a a' ∧ Mono v b b' ∧ Mono v c c' ∧ Mono v d d'
  | _, _ => False

theorem mono_refl (v : Bool) : ∀ (t : T), Mono v t t
  | .leaf _ => rfl
  | .wire _ c => ⟨id, mono_refl v c⟩
  | .n2 _ a b => ⟨id, mono_refl v a, mono_refl v b⟩
  | .n3 _ a b c => ⟨id, mono_refl v a, mono_refl v b, mono_refl v c⟩
  | .n4 _ a b c d => ⟨id, mono_refl v a, mono_refl v b, mono_refl v c, mono_refl v d⟩

theorem toward_v {v x q : Bool} {P : Prop} (h : x = q ∨ (x = v ∧ P)) : q = v → x = v := by
  intro hq; rcases h with e | ⟨e, _⟩
  · exact e.trans hq
  · exact e

/-- **Persistence / monotonicity.** Under the invariant, one firing moves
cells only toward `v`. With `Mon` for the inputs this says: during a phase
every node (input, wire or cell) changes at most once, and no node that
became `v` ever reverts, so an excited cell stays excited until it fires. -/
theorem fire_mono {v : Bool} {inp : Inp} {t t' : T} (hf : Fire inp t t') :
    Inv v inp t → Mono v t t' := by
  induction hf with
  | wire q c =>
    intro ⟨h1, _⟩; exact ⟨toward_v (buf_out v _ q h1 |>.imp id (fun e => ⟨e, trivial⟩)),
      mono_refl v c⟩
  | wireC _ ih => intro ⟨_, h2⟩; exact ⟨id, ih h2⟩
  | n2 q a b =>
    intro ⟨h1, _, _⟩; exact ⟨toward_v (c2_out v _ _ q h1), mono_refl v a, mono_refl v b⟩
  | n2a _ ih => intro ⟨_, ha, _⟩; exact ⟨id, ih ha, mono_refl _ _⟩
  | n2b _ ih => intro ⟨_, _, hb⟩; exact ⟨id, mono_refl _ _, ih hb⟩
  | n3 q a b c =>
    intro ⟨h1, _, _, _⟩
    exact ⟨toward_v (c3_out v _ _ _ q h1), mono_refl v a, mono_refl v b, mono_refl v c⟩
  | n3a _ ih => intro ⟨_, ha, _, _⟩; exact ⟨id, ih ha, mono_refl _ _, mono_refl _ _⟩
  | n3b _ ih => intro ⟨_, _, hb, _⟩; exact ⟨id, mono_refl _ _, ih hb, mono_refl _ _⟩
  | n3c _ ih => intro ⟨_, _, _, hc⟩; exact ⟨id, mono_refl _ _, mono_refl _ _, ih hc⟩
  | n4 q a b c d =>
    intro ⟨h1, _, _, _, _⟩
    exact ⟨toward_v (c4_out v _ _ _ _ q h1), mono_refl v a, mono_refl v b, mono_refl v c,
      mono_refl v d⟩
  | n4a _ ih => intro ⟨_, ha, _, _, _⟩; exact ⟨id, ih ha, mono_refl _ _, mono_refl _ _, mono_refl _ _⟩
  | n4b _ ih => intro ⟨_, _, hb, _, _⟩; exact ⟨id, mono_refl _ _, ih hb, mono_refl _ _, mono_refl _ _⟩
  | n4c _ ih => intro ⟨_, _, _, hc, _⟩; exact ⟨id, mono_refl _ _, mono_refl _ _, ih hc, mono_refl _ _⟩
  | n4d _ ih => intro ⟨_, _, _, _, hd⟩; exact ⟨id, mono_refl _ _, mono_refl _ _, mono_refl _ _, ih hd⟩

/-! ## The closed system: tree + environment -/

/-- Environment disciplines. -/
inductive Disc where
  /-- **H_FOUR_PHASE**: in phase `v` an input may only move to `v` (so each
  input rises once, then falls once, per transaction); the phase turns only
  when every leaf input is `v` (all rise before any falls) and the tree output
  is `v` (nothing moves again until the acknowledge has completed). Test: a
  protocol monitor on the bd_ctree inputs/output in GLS of the real users
  (join/fork). -/
  | fourPhase
  /-- As `fourPhase` but the turn does not wait for the tree output. -/
  | noAck
  /-- Any input may change to any value at any time. -/
  | free
  deriving DecidableEq

structure St where
  ph : Bool
  inp : Inp
  t : T

inductive Step (d : Disc) : St → St → Prop
  | fire {ph : Bool} {inp : Inp} {t t' : T} : Fire inp t t' → Step d ⟨ph, inp, t⟩ ⟨ph, inp, t'⟩
  | envPhase {ph : Bool} {inp : Inp} {t : T} (i : Nat) :
      d ≠ .free → inp i = !ph → Step d ⟨ph, inp, t⟩ ⟨ph, upd inp i ph, t⟩
  | envFree {ph : Bool} {inp : Inp} {t : T} (i : Nat) (b : Bool) :
      d = .free → Step d ⟨ph, inp, t⟩ ⟨ph, upd inp i b, t⟩
  | turn {ph : Bool} {inp : Inp} {t : T} :
      d ≠ .free → AllV inp ph t → (d = .fourPhase → out inp t = ph) →
      Step d ⟨ph, inp, t⟩ ⟨!ph, inp, t⟩

/-- Reachable states from the reset state: phase "rising", inputs all 0, tree `t0`. -/
inductive Reach (d : Disc) (t0 : T) : St → Prop
  | init : Reach d t0 ⟨true, fun _ => false, t0⟩
  | step {s s' : St} : Reach d t0 s → Step d s s' → Reach d t0 s'

theorem reach_shape {d : Disc} {t0 : T} {s : St} (h : Reach d t0 s) :
    leaves s.t = leaves t0 ∧ (IsCell t0 → IsCell s.t) := by
  induction h with
  | init => exact ⟨rfl, id⟩
  | step _ hs ih =>
    cases hs with
    | fire hf => exact ⟨(fire_leaves hf).trans ih.1, fun _ => fire_cell hf⟩
    | envPhase => exact ih
    | envFree => exact ih
    | turn => exact ih

/-- The phase invariant holds in every reachable state (H_RESET, H_FOUR_PHASE). -/
theorem reach_inv {t0 : T} (H_RESET : AllQ false t0) {s : St} (h : Reach .fourPhase t0 s) :
    Inv s.ph s.inp s.t := by
  induction h with
  | init => exact inv_of_allQ (w := false) H_RESET
  | step _ hs ih =>
    cases hs with
    | fire hf => exact (fire_inv hf ih).1
    | envPhase i _ _ => exact inv_env (mon_upd _ _ i) ih
    | envFree _ _ hd => exact absurd hd (by decide)
    | turn _ _ hO => exact inv_flip ih (hO rfl)

/-- **Each tree move is a flat C-element move (or a stutter).** In every
reachable state, a firing anywhere in the tree either leaves the tree output
unchanged or sets it to the phase value `v` while every leaf input is `v`. -/
theorem tree_move_is_flat_move {t0 : T} (H_RESET : AllQ false t0) {s : St}
    (h : Reach .fourPhase t0 s) {t' : T} (hf : Fire s.inp s.t t') :
    out s.inp t' = out s.inp s.t ∨
      (out s.inp t' = s.ph ∧ ∀ i ∈ leaves t0, s.inp i = s.ph) := by
  rcases (fire_inv hf (reach_inv H_RESET h)).2 with e | ⟨e, hA⟩
  · exact Or.inl e
  · exact Or.inr ⟨e, (reach_shape h).1 ▸ allV_iff.mp hA⟩

/-- Monotonicity in every reachable state. -/
theorem reach_mono {t0 : T} (H_RESET : AllQ false t0) {s : St}
    (h : Reach .fourPhase t0 s) {t' : T} (hf : Fire s.inp s.t t') : Mono s.ph s.t t' :=
  fire_mono hf (reach_inv H_RESET h)

/-- When the acknowledge arrives (output = phase), every internal cell and
wire holds the phase value: fundamental mode at the turn is a consequence of
waiting for the ack, not an extra assumption. -/
theorem settled_at_turn {t0 : T} (H_RESET : AllQ false t0) {s : St}
    (h : Reach .fourPhase t0 s) (hout : out s.inp s.t = s.ph) : AllQ s.ph s.t :=
  allQ_of_inv (reach_inv H_RESET h) hout

/-! ## The flat C-element and the equivalence -/

structure FSt where
  ph : Bool
  inp : Inp
  z : Bool

/-- A flat C-element over the inputs `L`, under the same environment. -/
inductive FStep (L : List Nat) : FSt → FSt → Prop
  | fire {ph : Bool} {inp : Inp} {z : Bool} (b : Bool) :
      (∀ i ∈ L, inp i = b) → FStep L ⟨ph, inp, z⟩ ⟨ph, inp, b⟩
  | env {ph : Bool} {inp : Inp} {z : Bool} (i : Nat) :
      inp i = !ph → FStep L ⟨ph, inp, z⟩ ⟨ph, upd inp i ph, z⟩
  | turn {ph : Bool} {inp : Inp} {z : Bool} :
      (∀ i ∈ L, inp i = ph) → z = ph → FStep L ⟨ph, inp, z⟩ ⟨!ph, inp, z⟩

inductive FReach (L : List Nat) : FSt → Prop
  | init : FReach L ⟨true, fun _ => false, false⟩
  | step {f f' : FSt} : FReach L f → FStep L f f' → FReach L f'

/-- A flat C-element's output can rise only when every input is 1. -/
theorem flat_rise_needs_all {L : List Nat} {ph ph' : Bool} {inp inp' : Inp}
    (h : FStep L ⟨ph, inp, false⟩ ⟨ph', inp', true⟩) : ∀ i ∈ L, inp' i = true := by
  cases h with
  | fire _ hb => exact hb

/-- **Refinement**: the observable part of every reachable tree state is a
reachable state of the flat C-element (H_RESET, H_FOUR_PHASE, root is a cell). -/
theorem refines_flat {t0 : T} (H_RESET : AllQ false t0) (hcell : IsCell t0) {s : St}
    (h : Reach .fourPhase t0 s) : FReach (leaves t0) ⟨s.ph, s.inp, out s.inp s.t⟩ := by
  induction h with
  | init =>
    rw [out_allQ hcell H_RESET]; exact FReach.init
  | @step s s' hr hs ih =>
    have hsh := reach_shape hr
    have hinv := reach_inv H_RESET hr
    cases hs with
    | @fire ph inp t t' hf =>
      rcases (fire_inv hf hinv).2 with e | ⟨e, hA⟩
      · simp only at e ⊢; rw [e]; exact ih
      · simp only at e ⊢; rw [e]
        exact FReach.step ih (FStep.fire _ (hsh.1 ▸ allV_iff.mp hA))
    | envPhase i _ hi =>
      simp only
      rw [out_cell (inp' := _) (hsh.2 hcell)]
      exact FReach.step ih (FStep.env i hi)
    | envFree _ _ hd => exact absurd hd (by decide)
    | turn _ hA hO =>
      exact FReach.step ih (FStep.turn (hsh.1 ▸ allV_iff.mp hA) (hO rfl))

/-! ### Completeness: the tree can always catch up -/

inductive Star (r : T → T → Prop) : T → T → Prop
  | refl (a : T) : Star r a a
  | tail {a b c : T} : Star r a b → r b c → Star r a c

theorem Star.trans' {r : T → T → Prop} {a b c : T} (h1 : Star r a b) (h2 : Star r b c) :
    Star r a c := by
  induction h2 with
  | refl => exact h1
  | tail _ h ih => exact Star.tail ih h

theorem Star.lift {r : T → T → Prop} (f : T → T) (hf : ∀ x y, r x y → r (f x) (f y))
    {a b : T} (h : Star r a b) : Star r (f a) (f b) := by
  induction h with
  | refl => exact Star.refl _
  | tail _ h ih => exact Star.tail ih (hf _ _ h)

theorem fire_allV {inp : Inp} {v : Bool} {t t' : T} (hf : Fire inp t t') (h : AllV inp v t) :
    AllV inp v t' := allV_iff.mpr (fire_leaves hf ▸ allV_iff.mp h)

theorem star_allV {inp : Inp} {v : Bool} {t t' : T} (hs : Star (Fire inp) t t')
    (h : AllV inp v t) : AllV inp v t' := by
  induction hs with
  | refl => exact h
  | tail _ hf ih => exact fire_allV hf ih

/-- **Liveness (no deadlock).** When every leaf input is `v`, cell firings alone
take the tree to a state where every cell holds `v` (so the output is `v`). -/
theorem live {inp : Inp} {v : Bool} :
    ∀ {t : T}, AllV inp v t → ∃ t', Star (Fire inp) t t' ∧ AllQ v t' ∧ AllV inp v t'
  | .leaf i, h => ⟨.leaf i, Star.refl _, trivial, h⟩
  | .wire q c, h => by
    obtain ⟨c', hs, hq, ha⟩ := live (t := c) h
    exact ⟨.wire (out inp c') c',
      Star.tail (Star.lift (r := Fire inp) (fun x => .wire q x) (fun _ _ h => Fire.wireC h) hs) (Fire.wire q c'),
      ⟨out_allQV hq ha, hq⟩, ha⟩
  | .n2 q a b, ⟨ha0, hb0⟩ => by
    obtain ⟨a', sa, qa, va⟩ := live (t := a) ha0
    obtain ⟨b', sb, qb, vb⟩ := live (t := b) hb0
    refine ⟨.n2 (c2 (out inp a') (out inp b') q) a' b', ?_, ?_, ⟨va, vb⟩⟩
    · exact Star.tail
        ((Star.lift (r := Fire inp) (fun x => .n2 q x b) (fun _ _ h => Fire.n2a h) sa).trans'
          (Star.lift (r := Fire inp) (fun x => .n2 q a' x) (fun _ _ h => Fire.n2b h) sb))
        (Fire.n2 q a' b')
    · refine ⟨?_, qa, qb⟩
      rw [out_allQV qa va, out_allQV qb vb]; exact c2_all v q
  | .n3 q a b c, ⟨ha0, hb0, hc0⟩ => by
    obtain ⟨a', sa, qa, va⟩ := live (t := a) ha0
    obtain ⟨b', sb, qb, vb⟩ := live (t := b) hb0
    obtain ⟨c', sc, qc, vc⟩ := live (t := c) hc0
    refine ⟨.n3 (c3 (out inp a') (out inp b') (out inp c') q) a' b' c', ?_, ?_, ⟨va, vb, vc⟩⟩
    · exact Star.tail
        (((Star.lift (r := Fire inp) (fun x => .n3 q x b c) (fun _ _ h => Fire.n3a h) sa).trans'
          (Star.lift (r := Fire inp) (fun x => .n3 q a' x c) (fun _ _ h => Fire.n3b h) sb)).trans'
          (Star.lift (r := Fire inp) (fun x => .n3 q a' b' x) (fun _ _ h => Fire.n3c h) sc))
        (Fire.n3 q a' b' c')
    · refine ⟨?_, qa, qb, qc⟩
      rw [out_allQV qa va, out_allQV qb vb, out_allQV qc vc]; exact c3_all v q
  | .n4 q a b c d, ⟨ha0, hb0, hc0, hd0⟩ => by
    obtain ⟨a', sa, qa, va⟩ := live (t := a) ha0
    obtain ⟨b', sb, qb, vb⟩ := live (t := b) hb0
    obtain ⟨c', sc, qc, vc⟩ := live (t := c) hc0
    obtain ⟨d', sd, qd, vd⟩ := live (t := d) hd0
    refine ⟨.n4 (c4 (out inp a') (out inp b') (out inp c') (out inp d') q) a' b' c' d', ?_, ?_,
      ⟨va, vb, vc, vd⟩⟩
    · exact Star.tail
        ((((Star.lift (r := Fire inp) (fun x => .n4 q x b c d) (fun _ _ h => Fire.n4a h) sa).trans'
          (Star.lift (r := Fire inp) (fun x => .n4 q a' x c d) (fun _ _ h => Fire.n4b h) sb)).trans'
          (Star.lift (r := Fire inp) (fun x => .n4 q a' b' x d) (fun _ _ h => Fire.n4c h) sc)).trans'
          (Star.lift (r := Fire inp) (fun x => .n4 q a' b' c' x) (fun _ _ h => Fire.n4d h) sd))
        (Fire.n4 q a' b' c' d')
    · refine ⟨?_, qa, qb, qc, qd⟩
      rw [out_allQV qa va, out_allQV qb vb, out_allQV qc vc, out_allQV qd vd]; exact c4_all v q

theorem reach_star {d : Disc} {t0 : T} {ph : Bool} {inp : Inp} {t t' : T}
    (h : Reach d t0 ⟨ph, inp, t⟩) (hs : Star (Fire inp) t t') : Reach d t0 ⟨ph, inp, t'⟩ := by
  induction hs with
  | refl => exact h
  | tail _ hf ih => exact Reach.step ih (Step.fire hf)

/-- **Completeness**: every reachable state of the flat C-element is the
observable part of a reachable tree state. -/
theorem flat_refines {t0 : T} (H_RESET : AllQ false t0) (hcell : IsCell t0) {f : FSt}
    (h : FReach (leaves t0) f) :
    ∃ t, Reach .fourPhase t0 ⟨f.ph, f.inp, t⟩ ∧ out f.inp t = f.z := by
  induction h with
  | init => exact ⟨t0, Reach.init, out_allQ hcell H_RESET⟩
  | step _ hs ih =>
    obtain ⟨t, hR, hout⟩ := ih
    have hsh := reach_shape hR
    have hinv := reach_inv H_RESET hR
    cases hs with
    | @fire ph inp z b hb =>
      simp only at hR hout hsh hinv ⊢
      by_cases hbz : b = z
      · subst hbz; exact ⟨t, hR, hout⟩
      · by_cases hbp : b = ph
        · subst hbp
          have hA : AllV inp b t := allV_iff.mpr (hsh.1 ▸ hb)
          obtain ⟨t', hs', hq, hv⟩ := live hA
          exact ⟨t', reach_star hR hs', out_allQV hq hv⟩
        · -- b = !ph and z = ph: the leaves would be both `ph` and `!ph`.
          exfalso
          have hz : z = ph := by
            cases b <;> cases z <;> cases ph <;> simp_all
          have hA := allV_iff.mp (all_of_inv hinv (hout.trans hz))
          rw [hsh.1] at hA
          obtain ⟨i, hi⟩ := List.exists_mem_of_ne_nil _ (leaves_ne t0)
          have e1 := hA i hi
          have e2 := hb i hi
          rw [e1] at e2
          exact hbp e2.symm
    | env i hi =>
      refine ⟨t, Reach.step hR (Step.envPhase i (by decide) hi), ?_⟩
      exact (out_cell (hsh.2 hcell)).symm.trans hout
    | turn hL hz =>
      exact ⟨t, Reach.step hR (Step.turn (by decide) (allV_iff.mpr (hsh.1 ▸ hL))
        (fun _ => hout.trans hz)), hout⟩

/-- **Main theorem (part 2), any tree shape.** Under H_RESET and H_FOUR_PHASE,
the reachable (phase, inputs, output) states of the tree are exactly those of
a flat C-element over the tree's inputs. Scope: equality of reachable-state
sets in the atomic-cell model (H_ATOMIC_CELL), not equality of traces. -/
theorem reachable_eq_flat {t0 : T} (H_RESET : AllQ false t0) (hcell : IsCell t0)
    (ph : Bool) (inp : Inp) (z : Bool) :
    FReach (leaves t0) ⟨ph, inp, z⟩ ↔ ∃ t, Reach .fourPhase t0 ⟨ph, inp, t⟩ ∧ out inp t = z := by
  constructor
  · exact flat_refines H_RESET hcell
  · intro ⟨t, hR, hz⟩
    have := refines_flat H_RESET hcell hR
    simp only at this; rw [hz] at this; exact this

/-! ## The generate block of `bd_ctree` -/

/-- Chunks of four, the last one shorter. -/
def chunks4 : List T → List (List T)
  | [] => []
  | a :: b :: c :: d :: rest => [a, b, c, d] :: chunks4 rest
  | xs => [xs]

/-- `bd_ctree` of width 1..4: a wire, `bd_c2`, `bd_c3`, `bd_c4` (reset state 0). -/
def node : List T → T
  | [a] => a
  | [a, b] => .n2 false a b
  | [a, b, c] => .n3 false a b c
  | [a, b, c, d] => .n4 false a b c d
  | _ => .leaf 0

/-- The recursion of the generate block (with fuel). -/
def genL : Nat → List T → T
  | 0, _ => .leaf 0
  | f + 1, xs => if xs.length ≤ 4 then node xs else genL f ((chunks4 xs).map node)

/-- `bd_ctree #(.N(n))` as a tree over `a[0..n-1]`. -/
def gen (n : Nat) : T := genL n ((List.range n).map .leaf)

/-- N = 5 per the generate block: `C2(C4(a0..a3), a4)`. -/
def t5 : T := .n2 false (.n4 false (.leaf 0) (.leaf 1) (.leaf 2) (.leaf 3)) (.leaf 4)
/-- N = 8 per the generate block: `C2(C4(a0..a3), C4(a4..a7))`. -/
def t8 : T := .n2 false (.n4 false (.leaf 0) (.leaf 1) (.leaf 2) (.leaf 3))
  (.n4 false (.leaf 4) (.leaf 5) (.leaf 6) (.leaf 7))
/-- N = 5 as in the header's example: `C(C(a0,a1), C(a2,a3,a4))` (not what the code builds). -/
def h5 : T := .n2 false (.n2 false (.leaf 0) (.leaf 1)) (.n3 false (.leaf 2) (.leaf 3) (.leaf 4))

theorem gen5 : gen 5 = t5 := rfl
theorem gen8 : gen 8 = t8 := rfl
theorem gen9 : gen 9 = .n3 false (.n4 false (.leaf 0) (.leaf 1) (.leaf 2) (.leaf 3))
    (.n4 false (.leaf 4) (.leaf 5) (.leaf 6) (.leaf 7)) (.leaf 8) := rfl

/-- Put a delayed wire on every edge (child -> parent) of a tree. -/
def withWires : T → T
  | .leaf i => .wire false (.leaf i)
  | .wire q c => .wire q (withWires c)
  | .n2 q a b => .n2 q (withWires a) (withWires b)
  | .n3 q a b c => .n3 q (withWires a) (withWires b) (withWires c)
  | .n4 q a b c d => .n4 q (withWires a) (withWires b) (withWires c) (withWires d)

/-! ### Part 2 instances -/

theorem ctree5_eq_flat (ph : Bool) (inp : Inp) (z : Bool) :
    FReach [0, 1, 2, 3, 4] ⟨ph, inp, z⟩ ↔
      ∃ t, Reach .fourPhase (gen 5) ⟨ph, inp, t⟩ ∧ out inp t = z :=
  reachable_eq_flat (t0 := gen 5) (by decide) (by decide) ph inp z

theorem ctree8_eq_flat (ph : Bool) (inp : Inp) (z : Bool) :
    FReach [0, 1, 2, 3, 4, 5, 6, 7] ⟨ph, inp, z⟩ ↔
      ∃ t, Reach .fourPhase (gen 8) ⟨ph, inp, t⟩ ∧ out inp t = z :=
  reachable_eq_flat (t0 := gen 8) (by decide) (by decide) ph inp z

theorem header5_eq_flat (ph : Bool) (inp : Inp) (z : Bool) :
    FReach [0, 1, 2, 3, 4] ⟨ph, inp, z⟩ ↔
      ∃ t, Reach .fourPhase h5 ⟨ph, inp, t⟩ ∧ out inp t = z :=
  reachable_eq_flat (t0 := h5) (by decide) (by decide) ph inp z

theorem ctree5_wires_eq_flat (ph : Bool) (inp : Inp) (z : Bool) :
    FReach [0, 1, 2, 3, 4] ⟨ph, inp, z⟩ ↔
      ∃ t, Reach .fourPhase (withWires (gen 5)) ⟨ph, inp, t⟩ ∧ out inp t = z :=
  reachable_eq_flat (t0 := withWires (gen 5)) (by decide) (by decide) ph inp z

/-- The generate block yields, for every width 2..64, a tree whose root is a
cell, whose cells all come out of reset at 0, and whose leaves are exactly
`a[0..n-1]` in order. (Checked by evaluation; the bound is only what `decide`
was asked to enumerate.) -/
theorem gen_ok : ∀ n, n < 65 → 2 ≤ n →
    IsCell (gen n) ∧ AllQ false (gen n) ∧ leaves (gen n) = List.range n := by decide

/-- **Part 2 for every width the RTL is used at (2..64).** -/
theorem ctree_eq_flat (n : Nat) (hn : n < 65) (h2 : 2 ≤ n) (ph : Bool) (inp : Inp) (z : Bool) :
    FReach (List.range n) ⟨ph, inp, z⟩ ↔
      ∃ t, Reach .fourPhase (gen n) ⟨ph, inp, t⟩ ∧ out inp t = z := by
  obtain ⟨hc, hq, hl⟩ := gen_ok n hn h2
  rw [← hl]; exact reachable_eq_flat hq hc ph inp z

/-! ## Part 1: the counterexamples -/

theorem Fire.n2' {inp : Inp} {q nq : Bool} {a b : T} (h : nq = c2 (out inp a) (out inp b) q) :
    Fire inp (.n2 q a b) (.n2 nq a b) := h ▸ Fire.n2 q a b
theorem Fire.n3' {inp : Inp} {q nq : Bool} {a b c : T}
    (h : nq = c3 (out inp a) (out inp b) (out inp c) q) :
    Fire inp (.n3 q a b c) (.n3 nq a b c) := h ▸ Fire.n3 q a b c
theorem Fire.n4' {inp : Inp} {q nq : Bool} {a b c d : T}
    (h : nq = c4 (out inp a) (out inp b) (out inp c) (out inp d) q) :
    Fire inp (.n4 q a b c d) (.n4 nq a b c d) := h ▸ Fire.n4 q a b c d

def z0 : Inp := fun _ => false

/-- The generate block's N = 5 tree under a free environment: inputs
`1 1 1 1 0` (the C4 chunk fires to 1), then `0 1 1 1 0`, then `0 1 1 1 1`.
From that reachable state the tree output rises 0 -> 1 although input 0 is 0;
`flat_rise_needs_all` says no flat 5-input C-element can make that move (and
it held 0 throughout, since its inputs were never all 1). -/
theorem cex_code5 :
    let inp := upd (upd (upd (upd (upd (upd z0 0 true) 1 true) 2 true) 3 true) 0 false) 4 true
    let s : St := ⟨true, inp,
      .n2 false (.n4 true (.leaf 0) (.leaf 1) (.leaf 2) (.leaf 3)) (.leaf 4)⟩
    let t' := T.n2 true (.n4 true (.leaf 0) (.leaf 1) (.leaf 2) (.leaf 3)) (.leaf 4)
    Reach .free (gen 5) s ∧ Fire s.inp s.t t' ∧ out s.inp s.t = false ∧ out s.inp t' = true ∧
      [inp 0, inp 1, inp 2, inp 3, inp 4] = [false, true, true, true, true] ∧
      ¬ (∀ i ∈ leaves (gen 5), inp i = true) := by
  refine ⟨?_, Fire.n2' (by decide), rfl, rfl, by decide, by decide⟩
  have r0 : Reach .free (gen 5) ⟨true, z0, t5⟩ := Reach.init
  have r1 := Reach.step r0 (Step.envFree 0 true rfl)
  have r2 := Reach.step r1 (Step.envFree 1 true rfl)
  have r3 := Reach.step r2 (Step.envFree 2 true rfl)
  have r4 := Reach.step r3 (Step.envFree 3 true rfl)
  have r5 := Reach.step r4 (Step.fire (Fire.n2a (q := false) (b := .leaf 4)
    (Fire.n4' (nq := true) (q := false) (a := .leaf 0) (b := .leaf 1) (c := .leaf 2)
      (d := .leaf 3) (by decide))))
  have r6 := Reach.step r5 (Step.envFree 0 false rfl)
  exact Reach.step r6 (Step.envFree 4 true rfl)

/-- The header's own example `C(C(a0,a1), C(a2,a3,a4))` with the vector
`0 1 1 1 1`: inputs `0 0 1 1 1` (right cell fires to 1), `0 0 0 1 1`,
`1 1 0 1 1` (left cell fires to 1), `0 1 0 1 1`, `0 1 1 1 1`; then the top
cell sees two ones and rises. The inputs were never all 1. -/
theorem cex_header5 :
    let inp := upd (upd (upd (upd (upd (upd (upd (upd z0 2 true) 3 true) 4 true)
      2 false) 0 true) 1 true) 0 false) 2 true
    let s : St := ⟨true, inp,
      .n2 false (.n2 true (.leaf 0) (.leaf 1)) (.n3 true (.leaf 2) (.leaf 3) (.leaf 4))⟩
    let t' := T.n2 true (.n2 true (.leaf 0) (.leaf 1)) (.n3 true (.leaf 2) (.leaf 3) (.leaf 4))
    Reach .free h5 s ∧ Fire s.inp s.t t' ∧ out s.inp s.t = false ∧ out s.inp t' = true ∧
      [inp 0, inp 1, inp 2, inp 3, inp 4] = [false, true, true, true, true] ∧
      ¬ (∀ i ∈ leaves h5, inp i = true) := by
  refine ⟨?_, Fire.n2' (by decide), rfl, rfl, by decide, by decide⟩
  have r0 : Reach .free h5 ⟨true, z0, h5⟩ := Reach.init
  have r1 := Reach.step r0 (Step.envFree 2 true rfl)
  have r2 := Reach.step r1 (Step.envFree 3 true rfl)
  have r3 := Reach.step r2 (Step.envFree 4 true rfl)
  have r4 := Reach.step r3 (Step.fire (Fire.n2b (q := false)
    (a := .n2 false (.leaf 0) (.leaf 1))
    (Fire.n3' (nq := true) (q := false) (a := .leaf 2) (b := .leaf 3) (c := .leaf 4)
      (by decide))))
  have r5 := Reach.step r4 (Step.envFree 2 false rfl)
  have r6 := Reach.step r5 (Step.envFree 0 true rfl)
  have r7 := Reach.step r6 (Step.envFree 1 true rfl)
  have r8 := Reach.step r7 (Step.fire (Fire.n2a (q := false)
    (b := .n3 true (.leaf 2) (.leaf 3) (.leaf 4))
    (Fire.n2' (nq := true) (q := false) (a := .leaf 0) (b := .leaf 1) (by decide))))
  have r9 := Reach.step r8 (Step.envFree 0 false rfl)
  exact Reach.step r9 (Step.envFree 2 true rfl)

/-- Without the wait for the acknowledge (`noAck`), the generate block's N = 5
tree fails even with every input rising once and falling once: all five
rise, the C4 chunk fires, the environment turns before the top cell has
fired and lowers a0..a3; the top cell then sees (1, a4 = 1) and rises while
the inputs read `0 0 0 0 1` in the falling phase. -/
theorem cex_noAck5 :
    let inp := upd (upd (upd (upd (upd (upd (upd (upd (upd z0 0 true) 1 true) 2 true) 3 true)
      4 true) 0 false) 1 false) 2 false) 3 false
    let s : St := ⟨false, inp,
      .n2 false (.n4 true (.leaf 0) (.leaf 1) (.leaf 2) (.leaf 3)) (.leaf 4)⟩
    let t' := T.n2 true (.n4 true (.leaf 0) (.leaf 1) (.leaf 2) (.leaf 3)) (.leaf 4)
    Reach .noAck (gen 5) s ∧ Fire s.inp s.t t' ∧ out s.inp s.t = false ∧ out s.inp t' = true ∧
      [inp 0, inp 1, inp 2, inp 3, inp 4] = [false, false, false, false, true] ∧
      ¬ (∀ i ∈ leaves (gen 5), inp i = true) := by
  refine ⟨?_, Fire.n2' (by decide), rfl, rfl, by decide, by decide⟩
  have hd : Disc.noAck ≠ .free := by decide
  have r0 : Reach .noAck (gen 5) ⟨true, z0, t5⟩ := Reach.init
  have r1 := Reach.step r0 (Step.envPhase 0 hd rfl)
  have r2 := Reach.step r1 (Step.envPhase 1 hd rfl)
  have r3 := Reach.step r2 (Step.envPhase 2 hd rfl)
  have r4 := Reach.step r3 (Step.envPhase 3 hd rfl)
  have r5 := Reach.step r4 (Step.envPhase 4 hd rfl)
  have r6 := Reach.step r5 (Step.fire (Fire.n2a (q := false) (b := .leaf 4)
    (Fire.n4' (nq := true) (q := false) (a := .leaf 0) (b := .leaf 1) (c := .leaf 2)
      (d := .leaf 3) (by decide))))
  have r7 := Reach.step r6 (Step.turn hd (by decide) (fun h => absurd h (by decide)))
  have r8 := Reach.step r7 (Step.envPhase 0 hd rfl)
  have r9 := Reach.step r8 (Step.envPhase 1 hd rfl)
  have r10 := Reach.step r9 (Step.envPhase 2 hd rfl)
  exact Reach.step r10 (Step.envPhase 3 hd rfl)

end Formal.Cells.CTree
