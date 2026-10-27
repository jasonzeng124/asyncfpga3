import Formal.Core.Kleene

/-!
# Formal.Core.Lut — LUT INIT tables, Boolean and Kleene evaluation

Shared Core definitions (track 4, shard A).

## Model

* `Lut k` is a k-input LUT given by its `2^k`-bit INIT, exactly as in a Xilinx
  `LUTk #(.INIT(...))` instance: input `I0` is the **least significant** address
  bit, so the output for Boolean inputs `x` is `INIT[Σ x_i 2^i]`
  (`Lut.addr`, `Lut.eval`). A 7-series `LUT6_2` is `Lut62`: `O6` is the full
  LUT6, `O5` is the LUT5 on `I0..I4` reading `INIT[31:0]` (`I5` must be tied 1
  in a fractured use, as in every library cell).
* Kleene evaluation `Lut.keval` is defined **structurally, as the LUT's mux
  tree**: each input drives the select of one rank of 2:1 muxes; a mux whose
  select is `X` outputs `K3.merge` of its two data inputs (equal data pass
  through, unequal data give `X`). This is the pass-transistor mux-tree reading
  of the silicon (formal/PROGRAM.md, "LUT"), and it is exactly what Verilog's
  `?:` does with an X select, i.e. the research GLS `SLICE_LUTX` model. The
  timed tree (per-level skew, runts) is `Formal.Core.LutTree` (sibling probe).
* `Lut.kevalSpec` is the **specification** "1 if every INIT entry consistent
  with the inputs is 1, 0 if every one is 0, else X", written literally.
  `Lut.keval_eq_kevalSpec` proves the two coincide, so the mux-tree reading and
  the set-based reading cannot disagree (and the rank order of the tree is
  irrelevant).

## Main results

* `Lut.keval_ofBoolVec` : on Boolean inputs Kleene eval = Boolean eval.
* `Lut.keval_mono` : monotone in the information order.
* `Lut.keval_eq_ofBool_iff`, `Lut.keval_eq_X_iff` : characterization.
* `Lut.keval_hull_eq_ofBool_iff` : a transition `x → x'` (any set of inputs
  changing) is hazard-free in the Kleene abstraction iff every Boolean vector
  in the subcube spanned by `x, x'` gives the same output.
* `Lut.keval_setAt_X_iff`, `Lut.no_static_hazard_single` : one input changing,
  output unchanged ⇒ Kleene output with that input `X` is the defined value.
* `Lut.two_change_hazard`, `Init.bd_c2_two_change_hazard` : this fails for two
  simultaneous changes (XOR2; and the C-element itself, on opposite-sense
  changes of its two inputs).
* `Init.bd_c2_*` : X containment of the C-element's feedback.
* `Init.*` : INIT constants for every LUT in cells/rtl/bd_ce.v, bd_arb.v,
  bd_latch.v, each with its Boolean function proved by `decide`.

Fidelity: whether real 7-series LUTs obey this Kleene semantics (in particular
that a mux with an intermediate select voltage and equal data outputs that
data level cleanly) is a **hypothesis**, not a theorem; see
formal/notes/A-kleene-lut.md.
-/

namespace Formal.Core

open K3

/-- Address of a Boolean input vector; input `I0` = `x 0` is the LSB. -/
def addr : {k : Nat} → (Fin k → Bool) → Nat
  | 0, _ => 0
  | _ + 1, x => (x 0).toNat + 2 * addr (vtail x)

theorem addr_vcons {k : Nat} (b : Bool) (y : Fin k → Bool) :
    addr (vcons b y) = b.toNat + 2 * addr y := rfl

theorem addr_lt : ∀ {k : Nat} (x : Fin k → Bool), addr x < 2 ^ k
  | 0, _ => by simp [addr]
  | k + 1, x => by
      have h := addr_lt (vtail x)
      have hb : (x 0).toNat ≤ 1 := Bool.toNat_le _
      simp only [addr, Nat.pow_succ]
      omega

/-- Kleene evaluation of the mux tree over a truth table `t` (entry `t a` at
address `a`). Input `I0` (`v 0`) drives the ROOT mux, choosing between the
sub-tree over even addresses and the one over odd addresses; `I(k-1)` drives
the rank next to the INIT cells. This is the order of the research GLS model
(`cells/gls/prims.v` `SLICE_LUTX`, A1 at the root); the silicon probably has
A6 at the root (formal/notes/A-lut-tree.md). The order is irrelevant to the
static semantics: `Lut.keval_eq_kevalSpec` shows the result equals the
order-free set specification. -/
def kevalT : (k : Nat) → (Nat → Bool) → (Fin k → K3) → K3
  | 0, t, _ => ofBool (t 0)
  | k + 1, t, v =>
      match v 0 with
      | .zero => kevalT k (fun a => t (2 * a)) (vtail v)
      | .one => kevalT k (fun a => t (2 * a + 1)) (vtail v)
      | .X => merge (kevalT k (fun a => t (2 * a)) (vtail v))
                    (kevalT k (fun a => t (2 * a + 1)) (vtail v))

section kevalT
variable {k : Nat} (t : Nat → Bool) (w : Fin k → K3)

theorem kevalT_vcons_zero :
    kevalT (k + 1) t (vcons zero w) = kevalT k (fun a => t (2 * a)) w := rfl
theorem kevalT_vcons_one :
    kevalT (k + 1) t (vcons one w) = kevalT k (fun a => t (2 * a + 1)) w := rfl
theorem kevalT_vcons_X :
    kevalT (k + 1) t (vcons X w) =
      merge (kevalT k (fun a => t (2 * a)) w) (kevalT k (fun a => t (2 * a + 1)) w) := rfl
end kevalT

theorem ofBoolVec_vcons {k : Nat} (b : Bool) (y : Fin k → Bool) :
    ofBoolVec (vcons b y) = vcons (ofBool b) (ofBoolVec y) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem vle_vcons {k : Nat} {c d : K3} {u v : Fin k → K3} :
    VLe (vcons c u) (vcons d v) ↔ c ⊑ d ∧ VLe u v := by
  constructor
  · intro h; exact ⟨h 0, fun i => h i.succ⟩
  · intro ⟨h0, h⟩ i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact h0
    · exact h j

theorem kevalT_ofBoolVec : ∀ {k : Nat} (t : Nat → Bool) (x : Fin k → Bool),
    kevalT k t (ofBoolVec x) = ofBool (t (addr x))
  | 0, _, _ => rfl
  | k + 1, t, x => by
      rw [← vcons_vtail x, ofBoolVec_vcons, addr_vcons]
      cases x 0
      · rw [ofBool_false, kevalT_vcons_zero, kevalT_ofBoolVec]; simp
      · rw [ofBool_true, kevalT_vcons_one, kevalT_ofBoolVec]; simp [Nat.add_comm]

theorem kevalT_mono : ∀ {k : Nat} (t : Nat → Bool) {u v : Fin k → K3},
    VLe u v → kevalT k t u ⊑ kevalT k t v
  | 0, _, _, _, _ => le_refl _
  | k + 1, t, u, v, h => by
      rw [← vcons_vtail u, ← vcons_vtail v] at h ⊢
      rw [vle_vcons] at h
      obtain ⟨h0, h⟩ := h
      have IHe := kevalT_mono (fun a => t (2 * a)) h
      have IHo := kevalT_mono (fun a => t (2 * a + 1)) h
      revert h0
      cases u 0 <;> cases v 0 <;> intro h0
      all_goals first
        | exact absurd h0 (by decide)
        | rw [kevalT_vcons_zero, kevalT_vcons_zero]; exact IHe
        | rw [kevalT_vcons_one, kevalT_vcons_one]; exact IHo
        | rw [kevalT_vcons_X, kevalT_vcons_X]; exact merge_mono IHe IHo
        | rw [kevalT_vcons_X, kevalT_vcons_zero]; exact le_trans (merge_le_left _ _) IHe
        | rw [kevalT_vcons_X, kevalT_vcons_one]; exact le_trans (merge_le_right _ _) IHo

/-- Characterization: the mux tree outputs the defined value `b` iff every
table entry addressed by a Boolean resolution of the inputs is `b`. -/
theorem kevalT_eq_ofBool_iff : ∀ {k : Nat} (t : Nat → Bool) (v : Fin k → K3) (b : Bool),
    kevalT k t v = ofBool b ↔ ∀ x, Consistent v x → t (addr x) = b
  | 0, t, v, b => by
      constructor
      · intro h x _; exact ofBool_inj.mp h
      · intro h; exact congrArg ofBool (h (fun i => i.elim0) (fun i => i.elim0))
  | k + 1, t, v, b => by
      rw [← vcons_vtail v]
      generalize v 0 = c
      generalize vtail v = w
      rw [forall_vcons (P := fun x => Consistent (vcons c w) x → t (addr x) = b)]
      simp only [consistent_vcons, addr_vcons]
      have IHe := kevalT_eq_ofBool_iff (fun a => t (2 * a)) w b
      have IHo := kevalT_eq_ofBool_iff (fun a => t (2 * a + 1)) w b
      cases c
      · rw [kevalT_vcons_zero, IHe]
        constructor
        · intro h d y ⟨hd, hy⟩
          have : d = false := by cases d <;> first | rfl | exact absurd hd (by decide)
          subst this; simpa using h y hy
        · intro h y hy; simpa using h false y ⟨Or.inr rfl, hy⟩
      · rw [kevalT_vcons_one, IHo]
        constructor
        · intro h d y ⟨hd, hy⟩
          have : d = true := by cases d <;> first | rfl | exact absurd hd (by decide)
          subst this; simpa [Nat.add_comm] using h y hy
        · intro h y hy; simpa [Nat.add_comm] using h true y ⟨Or.inr rfl, hy⟩
      · rw [kevalT_vcons_X, merge_eq_ofBool_iff, IHe, IHo]
        constructor
        · intro ⟨he, ho⟩ d y ⟨_, hy⟩
          cases d
          · simpa using he y hy
          · simpa [Nat.add_comm] using ho y hy
        · intro h
          exact ⟨fun y hy => by simpa using h false y ⟨X_le _, hy⟩,
                 fun y hy => by simpa [Nat.add_comm] using h true y ⟨X_le _, hy⟩⟩

/-! ## LUTs -/

/-- A k-input LUT: its INIT, `2^k` bits, entry `a` = output at address `a`. -/
structure Lut (k : Nat) where
  init : BitVec (2 ^ k)
  deriving DecidableEq

namespace Lut

variable {k : Nat} (L : Lut k)

/-- INIT entry at address `a`. -/
def entry (a : Nat) : Bool := L.init.getLsbD a

/-- Boolean evaluation: `INIT[addr x]`. -/
def eval (x : Fin k → Bool) : Bool := L.entry (addr x)

/-- Kleene evaluation, as the LUT's mux tree (see module doc). -/
def keval (v : Fin k → K3) : K3 := kevalT k L.entry v

/-- Kleene evaluation, as specified: 1 if every INIT entry consistent with the
inputs is 1, 0 if every one is 0, else X. (Computable, but enumerates all
`2^k` Boolean vectors; use `keval` for computation.) -/
def kevalSpec (v : Fin k → K3) : K3 :=
  if ∀ x, Consistent v x → L.eval x = true then one
  else if ∀ x, Consistent v x → L.eval x = false then zero
  else X

/-- Kleene eval agrees with Boolean eval on Boolean inputs. -/
theorem keval_ofBoolVec (x : Fin k → Bool) : L.keval (ofBoolVec x) = ofBool (L.eval x) :=
  kevalT_ofBoolVec _ x

/-- Kleene eval is monotone in the information order. -/
theorem keval_mono {u v : Fin k → K3} (h : VLe u v) : L.keval u ⊑ L.keval v :=
  kevalT_mono _ h

theorem keval_eq_ofBool_iff (v : Fin k → K3) (b : Bool) :
    L.keval v = ofBool b ↔ ∀ x, Consistent v x → L.eval x = b :=
  kevalT_eq_ofBool_iff _ v b

/-- The mux-tree evaluation equals the set-based specification. -/
theorem keval_eq_kevalSpec (v : Fin k → K3) : L.keval v = L.kevalSpec v := by
  unfold kevalSpec
  split
  · next h => exact (L.keval_eq_ofBool_iff v true).mpr h
  · next h1 =>
    split
    · next h => exact (L.keval_eq_ofBool_iff v false).mpr h
    · next h2 =>
      rw [← L.keval_eq_ofBool_iff] at h1 h2
      revert h1 h2
      cases L.keval v <;> simp

/-- `X` exactly when two Boolean resolutions of the inputs disagree. -/
theorem keval_eq_X_iff (v : Fin k → K3) :
    L.keval v = X ↔ ∃ x y, Consistent v x ∧ Consistent v y ∧ L.eval x ≠ L.eval y := by
  constructor
  · intro hX
    let x0 := fun i => pick (v i)
    have h0 : Consistent v x0 := consistent_pick v
    -- if all resolutions agreed with x0 the output would be defined
    apply Classical.byContradiction
    intro hne
    have hall : ∀ y, Consistent v y → L.eval y = L.eval x0 := by
      intro y hy
      apply Classical.byContradiction
      intro hd
      exact hne ⟨y, x0, hy, h0, hd⟩
    have := (L.keval_eq_ofBool_iff v (L.eval x0)).mpr hall
    rw [hX] at this
    exact ofBool_ne_X _ this.symm
  · intro ⟨x, y, hx, hy, hd⟩
    cases h : L.keval v with
    | X => rfl
    | zero =>
      have hz := (L.keval_eq_ofBool_iff v false).mp h
      exact absurd ((hz x hx).trans (hz y hy).symm) hd
    | one =>
      have hz := (L.keval_eq_ofBool_iff v true).mp h
      exact absurd ((hz x hx).trans (hz y hy).symm) hd

/-! ## Transitions and static hazards -/

/-- Kleene picture of a transition `x → x'`: inputs that change are `X`. -/
def hull {k : Nat} (x x' : Fin k → Bool) : Fin k → K3 :=
  fun i => if x i = x' i then ofBool (x i) else X

theorem consistent_hull {x x' y : Fin k → Bool} :
    Consistent (hull x x') y ↔ ∀ i, x i = x' i → y i = x i := by
  constructor
  · intro h i he
    have := h i
    simp only [hull, he, ite_true, ofBool_le_iff] at this
    rw [he]; exact ofBool_inj.mp this
  · intro h i
    by_cases he : x i = x' i
    · simp only [hull, he, ite_true]; rw [h i he, he]; exact le_refl _
    · simp only [hull, he, ite_false]; exact X_le _

/-- A transition `x → x'` (any set of inputs changing, in any order and with
any intermediate values) has a defined Kleene output `b` iff every Boolean
vector in the subcube between `x` and `x'` evaluates to `b`. -/
theorem keval_hull_eq_ofBool_iff (x x' : Fin k → Bool) (b : Bool) :
    L.keval (hull x x') = ofBool b ↔
      ∀ y, (∀ i, x i = x' i → y i = x i) → L.eval y = b := by
  rw [keval_eq_ofBool_iff]
  exact ⟨fun h y hy => h y (consistent_hull.mpr hy),
         fun h y hy => h y (consistent_hull.mp hy)⟩

theorem consistent_setAt_X {x y : Fin k → Bool} {j : Fin k} :
    Consistent (setAt (ofBoolVec x) j X) y ↔ y = setAt x j (y j) := by
  constructor
  · intro h; funext i
    by_cases hij : i = j
    · subst hij; simp [setAt]
    · have := h i
      simp only [setAt, hij, ite_false, ofBoolVec, ofBool_le_iff] at this ⊢
      exact (ofBool_inj.mp this)
  · intro h i
    by_cases hij : i = j
    · simp [setAt, hij, X_le]
    · rw [h]; simp only [setAt, hij, ite_false, ofBoolVec]; exact le_refl _

/-- One input `j` at `X`, the others Boolean: the output is the defined value
`b` iff both Boolean values of input `j` give `b`. -/
theorem keval_setAt_X_iff (x : Fin k → Bool) (j : Fin k) (b : Bool) :
    L.keval (setAt (ofBoolVec x) j X) = ofBool b ↔
      L.eval (setAt x j false) = b ∧ L.eval (setAt x j true) = b := by
  rw [keval_eq_ofBool_iff]
  constructor
  · intro h
    refine ⟨h _ (consistent_setAt_X.mpr ?_), h _ (consistent_setAt_X.mpr ?_)⟩ <;>
      simp [setAt]
  · intro ⟨hf, ht⟩ y hy
    rw [consistent_setAt_X.mp hy]
    cases y j
    · exact hf
    · exact ht

theorem setAt_self {α : Type} (x : Fin k → α) (j : Fin k) : setAt x j (x j) = x := by
  funext i; by_cases h : i = j <;> simp [setAt, h]

/-- **No static hazard on a single-input change.** If input `j` alone moves
(`x → setAt x j (!x j)`, passing through `X`) and the Boolean output is the
same before and after, the Kleene output while `j` is `X` is that same value. -/
theorem no_static_hazard_single (x : Fin k → Bool) (j : Fin k)
    (h : L.eval (setAt x j (!x j)) = L.eval x) :
    L.keval (setAt (ofBoolVec x) j X) = ofBool (L.eval x) := by
  rw [keval_setAt_X_iff]
  have hs := congrArg L.eval (setAt_self x j)
  revert h hs
  cases x j <;> simp_all

/-- Conversely, a single-input change that changes the Boolean output makes
the Kleene output `X` (the transition is visible, never masked). -/
theorem single_change_visible (x : Fin k → Bool) (j : Fin k)
    (h : L.eval (setAt x j (!x j)) ≠ L.eval x) :
    L.keval (setAt (ofBoolVec x) j X) = X := by
  rw [keval_eq_X_iff]
  refine ⟨setAt x j (!x j), x, consistent_setAt_X.mpr ?_, consistent_setAt_X.mpr ?_, h⟩
  · funext i; by_cases hij : i = j <;> simp [setAt, hij]
  · exact (setAt_self x j).symm

end Lut

/-- The same with `hull`: a transition flipping one input. -/
theorem Lut.hull_single {k : Nat} (x : Fin k → Bool) (j : Fin k) :
    hull x (setAt x j (!x j)) = setAt (ofBoolVec x) j X := by
  funext i
  by_cases hij : i = j
  · subst hij; cases h : x i <;> simp [Lut.hull, setAt, h]
  · simp [Lut.hull, setAt, hij, ofBoolVec]

/-- 2-input XOR (`LUT2 #(.INIT(4'h6))`). -/
def xor2 : Lut 2 := ⟨0x6#4⟩

/-- **Two simultaneous changes can glitch.** XOR2, `00 → 11`: output 0 before
and after, but the Kleene output with both inputs `X` is `X` (physically, the
order of arrival passes through `01` or `10`, where the output is 1). -/
theorem Lut.two_change_hazard :
    ∃ (L : Lut 2) (x x' : Fin 2 → Bool),
      L.eval x = L.eval x' ∧ L.keval (Lut.hull x x') = X :=
  ⟨xor2, fun _ => false, fun _ => true, by decide, by decide⟩

/-- Hence the single-input theorem does not generalize to two inputs. -/
theorem Lut.not_no_static_hazard_two :
    ¬ ∀ (L : Lut 2) (x x' : Fin 2 → Bool),
        L.eval x = L.eval x' → L.keval (Lut.hull x x') = ofBool (L.eval x) := by
  intro h
  have := h xor2 (fun _ => false) (fun _ => true) (by decide)
  revert this; decide

/-! ## LUT6_2 (fractured) -/

/-- A 7-series `LUT6_2`: `O6` = LUT6 on `I0..I5`, `O5` = LUT5 on `I0..I4`
reading `INIT[31:0]`. Library cells tie `I5 = 1`, so `O6` reads `INIT[63:32]`. -/
structure Lut62 where
  init : BitVec 64
  deriving DecidableEq

namespace Lut62
def o6 (L : Lut62) : Lut 6 := ⟨L.init⟩
def o5 (L : Lut62) : Lut 5 := ⟨L.init.setWidth 32⟩
end Lut62

/-! ## Vector literals -/

/-- Boolean pin vector from a list `[I0, I1, ...]` (missing pins are 0). -/
abbrev bvec (l : List Bool) (k : Nat) : Fin k → Bool := ofList false l k

/-- Kleene pin vector from a list `[I0, I1, ...]` (missing pins are `X`). -/
abbrev kvec (l : List K3) (k : Nat) : Fin k → K3 := ofList X l k

/-- Majority of three. -/
def maj (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

/-! ## INIT constants of the cell library

Every LUT instance in cells/rtl/bd_ce.v, bd_arb.v, bd_latch.v. Pin order is
`[I0, I1, I2, I3, I4, I5]` as wired in the RTL; tied pins are noted. Each
constant carries its Boolean function, proved by `decide` from the INIT. -/

namespace Init

/-- bd_ce.v:34 `bd_c2`: I0=a, I1=b, I2=q (feedback), I3=rst, I4=I5=0. -/
def bd_c2 : Lut 6 := ⟨0x00E9_00E8_00E8_00E8#64⟩
/-- bd_ce.v:40 `bd_c2_set`: same pins as `bd_c2`. -/
def bd_c2_set : Lut 6 := ⟨0xFFE8_FFE8_FFE8_FFE8#64⟩
/-- bd_ce.v:49 `bd_c2n` = C(a,~b): I0=a, I1=b, I2=q, I3=rst, I4=I5=0. -/
def bd_c2n : Lut 6 := ⟨0x00B2_00B2_00B2_00B2#64⟩
/-- bd_ce.v:55 `bd_c2n_set`; also `bd_arbcell`'s state node (bd_arb.v:89). -/
def bd_c2n_set : Lut 6 := ⟨0xFFB2_FFB2_FFB2_FFB2#64⟩
/-- bd_ce.v:62 `bd_c3`: I0=a, I1=b, I2=c, I3=q, I4=rst, I5=0. -/
def bd_c3 : Lut 6 := ⟨0x0000_FE80_0000_FE80#64⟩
/-- bd_ce.v:70 `bd_c4`: I0..I3=a,b,c,d, I4=q, I5=rst. -/
def bd_c4 : Lut 6 := ⟨0x0000_0000_FFFE_8000#64⟩
/-- bd_ce.v:81 `bd_c2_norst`: I0=a, I1=b, I2=q, I3..I5=0. -/
def bd_c2_norst : Lut 6 := ⟨0xE8E8_E8E8_E8E8_E8E8#64⟩
/-- bd_ce.v:86 `bd_c3_norst`: I0=a, I1=b, I2=c, I3=q, I4=I5=0. -/
def bd_c3_norst : Lut 6 := ⟨0xFE80_FE80_FE80_FE80#64⟩
/-- bd_arb.v:91 (`bd_arbcell`) and bd_arb.v:249 (`bd_arbiter`) `ugrant`,
LUT6_2: I0=r1, I1=r2, I2=q, I3=I4=0, I5=1; O5=g1, O6=g2. -/
def arb_grant : Lut62 := ⟨0x0C0C_0C0C_A0A0_A0A0#64⟩
/-- bd_arb.v:245 `bd_arbiter` `ustate`, LUT6_2: I0=r1, I1=r2, I2=q, I3=rst,
I4=A0, I5=1; O6=q (feedback), O5=R0. -/
def arb_state : Lut62 := ⟨0xFFF0_FFB2_ACAC_ACAC#64⟩
/-- bd_latch.v:38 `bd_latch` pair, LUT6_2: I0=d_i, I1=en, I2=q_i, I3=d_j,
I4=q_j, I5=1; O5=q_i, O6=q_j. -/
def latch_pair : Lut62 := ⟨0xFF33_CC00_B8B8_B8B8#64⟩
/-- bd_latch.v:44 `bd_latch` odd bit: I0=d, I1=en, I2=q, I3..I5=0. -/
def latch_odd : Lut 6 := ⟨0xB8B8_B8B8_B8B8_B8B8#64⟩
/-- bd_latch.v:64 `bd_latch_rst`, RESET_VALUE bit 0: I0=d, I1=en, I2=q, I3=rst. -/
def latch_rst0 : Lut 6 := ⟨0x00B8_00B8_00B8_00B8#64⟩
/-- bd_latch.v:64 `bd_latch_rst`, RESET_VALUE bit 1. -/
def latch_rst1 : Lut 6 := ⟨0xFFB8_FFB8_FFB8_FFB8#64⟩
/-- bd_latch.v:126,135,180 `bd_delay`/`bd_delay_gated` buffer, LUT1 2'h2. -/
def delay_buf : Lut 1 := ⟨0x2#2⟩
/-- bd_latch.v:116,138 `bd_delay` FASTFALL side LUT2 (SIDE_INIT 4'h8), and
bd_latch.v:183 `bd_delay_gated` LUT2 4'h8: I0=s[i], I1=a (or gate). AND. -/
def delay_and : Lut 2 := ⟨0x8#4⟩
/-- bd_latch.v:116,138 `bd_delay` FASTRISE side LUT2 (SIDE_INIT 4'hE). OR. -/
def delay_or : Lut 2 := ⟨0xE#4⟩
/-- bd_latch.v:209 `bd_datamux` pair, LUT6_2: I0=s, I1=a_i, I2=b_i, I3=a_j,
I4=b_j, I5=1; O5=z_i, O6=z_j. -/
def datamux_pair : Lut62 := ⟨0xFFAA_5500_E4E4_E4E4#64⟩
/-- bd_latch.v:215 `bd_datamux` odd bit, LUT3 8'hE4: I0=s, I1=a, I2=b. -/
def datamux_odd : Lut 3 := ⟨0xE4#8⟩

/-! ### Boolean functions of the constants (checks the transcription and the
headers' claims) -/

theorem bd_c2_eval (a b q r : Bool) :
    bd_c2.eval (bvec [a, b, q, r, false, false] 6) = (!r && maj a b q) := by
  revert a b q r; decide
theorem bd_c2_set_eval (a b q r : Bool) :
    bd_c2_set.eval (bvec [a, b, q, r, false, false] 6) = (r || maj a b q) := by
  revert a b q r; decide
theorem bd_c2n_eval (a b q r : Bool) :
    bd_c2n.eval (bvec [a, b, q, r, false, false] 6) = (!r && maj a (!b) q) := by
  revert a b q r; decide
theorem bd_c2n_set_eval (a b q r : Bool) :
    bd_c2n_set.eval (bvec [a, b, q, r, false, false] 6) = (r || maj a (!b) q) := by
  revert a b q r; decide
theorem bd_c3_eval (a b c q r : Bool) :
    bd_c3.eval (bvec [a, b, c, q, r, false] 6) =
      (!r && ((a && b && c) || (q && (a || b || c)))) := by
  revert a b c q r; decide
theorem bd_c4_eval (a b c d q r : Bool) :
    bd_c4.eval (bvec [a, b, c, d, q, r] 6) =
      (!r && ((a && b && c && d) || (q && (a || b || c || d)))) := by
  revert a b c d q r; decide
theorem bd_c2_norst_eval (a b q : Bool) :
    bd_c2_norst.eval (bvec [a, b, q, false, false, false] 6) = maj a b q := by
  revert a b q; decide
theorem bd_c3_norst_eval (a b c q : Bool) :
    bd_c3_norst.eval (bvec [a, b, c, q, false, false] 6) =
      ((a && b && c) || (q && (a || b || c))) := by
  revert a b c q; decide
theorem arb_grant_g1 (r1 r2 q : Bool) :
    arb_grant.o5.eval (bvec [r1, r2, q, false, false] 5) = (r1 && q) := by
  revert r1 r2 q; decide
theorem arb_grant_g2 (r1 r2 q : Bool) :
    arb_grant.o6.eval (bvec [r1, r2, q, false, false, true] 6) = (r2 && !q) := by
  revert r1 r2 q; decide
/-- `q = rst + (A0 ? q : C(r1,~r2))`: q frozen while A0 is high. -/
theorem arb_state_q (r1 r2 q rst a0 : Bool) :
    arb_state.o6.eval (bvec [r1, r2, q, rst, a0, true] 6) =
      (rst || (if a0 then q else maj r1 (!r2) q)) := by
  revert r1 r2 q rst a0; decide
/-- `R0 = r1.q + r2.~q`. -/
theorem arb_state_R0 (r1 r2 q rst a0 : Bool) :
    arb_state.o5.eval (bvec [r1, r2, q, rst, a0] 5) = ((r1 && q) || (r2 && !q)) := by
  revert r1 r2 q rst a0; decide
theorem latch_pair_qi (di en qi dj qj : Bool) :
    latch_pair.o5.eval (bvec [di, en, qi, dj, qj] 5) = (if en then di else qi) := by
  revert di en qi dj qj; decide
theorem latch_pair_qj (di en qi dj qj : Bool) :
    latch_pair.o6.eval (bvec [di, en, qi, dj, qj, true] 6) = (if en then dj else qj) := by
  revert di en qi dj qj; decide
theorem latch_odd_eval (d en q : Bool) :
    latch_odd.eval (bvec [d, en, q, false, false, false] 6) = (if en then d else q) := by
  revert d en q; decide
theorem latch_rst0_eval (d en q r : Bool) :
    latch_rst0.eval (bvec [d, en, q, r, false, false] 6) = (!r && if en then d else q) := by
  revert d en q r; decide
theorem latch_rst1_eval (d en q r : Bool) :
    latch_rst1.eval (bvec [d, en, q, r, false, false] 6) = (r || if en then d else q) := by
  revert d en q r; decide
theorem delay_buf_eval (a : Bool) : delay_buf.eval (bvec [a] 1) = a := by
  revert a; decide
theorem delay_and_eval (s a : Bool) : delay_and.eval (bvec [s, a] 2) = (s && a) := by
  revert s a; decide
theorem delay_or_eval (s a : Bool) : delay_or.eval (bvec [s, a] 2) = (s || a) := by
  revert s a; decide
theorem datamux_pair_zi (s ai bi aj bj : Bool) :
    datamux_pair.o5.eval (bvec [s, ai, bi, aj, bj] 5) = (if s then bi else ai) := by
  revert s ai bi aj bj; decide
theorem datamux_pair_zj (s ai bi aj bj : Bool) :
    datamux_pair.o6.eval (bvec [s, ai, bi, aj, bj, true] 6) = (if s then bj else aj) := by
  revert s ai bi aj bj; decide
theorem datamux_odd_eval (s a b : Bool) :
    datamux_odd.eval (bvec [s, a, b] 3) = (if s then b else a) := by
  revert s a b; decide

/-! ### Kleene facts about the C-element `bd_c2` -/

/-- **X containment**: feedback `q = X`, reset low, inputs agree ⇒ output is
the inputs' value. The agreement of `a` and `b` masks the unknown state. -/
theorem bd_c2_contain (a : Bool) :
    bd_c2.keval (kvec [ofBool a, ofBool a, X, zero, zero, zero] 6) = ofBool a := by
  revert a; decide

/-- With `a ≠ b` the C-element holds, so `q = X` propagates to the output. -/
theorem bd_c2_hold_X (a : Bool) :
    bd_c2.keval (kvec [ofBool a, ofBool (!a), X, zero, zero, zero] 6) = X := by
  revert a; decide

/-- Reset high forces 0 whatever `a`, `b`, `q` are, `X` included. -/
theorem bd_c2_reset (a b q : K3) :
    bd_c2.keval (kvec [a, b, q, one, zero, zero] 6) = zero := by
  cases a <;> cases b <;> cases q <;> decide

/-- The C-element itself has a static hazard on opposite-sense input changes:
`a b = 0 1 → 1 0` with `q = 0` holds 0 at both ends, but its Kleene output
during the transition is `X` (it passes through `11` or `00`; through `11`
it would fire). This is the arbiter's runt condition in Kleene form. -/
theorem bd_c2_two_change_hazard :
    bd_c2.eval (bvec [false, true, false, false, false, false] 6) = false ∧
    bd_c2.eval (bvec [true, false, false, false, false, false] 6) = false ∧
    bd_c2.keval (Lut.hull (bvec [false, true, false, false, false, false] 6)
                          (bvec [true, false, false, false, false, false] 6)) = X := by
  decide

end Init

end Formal.Core
