import Formal.Net.Compute.Struct
import Formal.Net.GcdHwLib

/-!
# H_COMPUTE_FN, part 7: signed less-than as a CARRY4 lexicographic chain

yosys maps a 32-bit signed `<` into bit groups (lowest first): for each group `k` a LUT `E_k`
("the groups are equal") and a LUT `D_k` ("the group of `a` is greater", sign bit toggled: the
signed order), a CARRY4 chain `c_k = E_k ? c_(k-1) : D_k` (`c_(-1) = 0`; `c_k` is the carry-out
of group `k`'s position), and a final LUT `lt = ¬c_last ∧ ¬(every E_k)`.

`SltOK` (decidable): each `E_k`, `D_k` is checked exhaustively over its group's bits; the chain
is checked STRUCTURALLY (the CARRY4 cell at the given index has `S = E_k`, `DI = D_k`, carry-in
the previous group's carry-out; `run_cell` gives the equation); `lt` is checked over the `E_k`
and the last carry as cut points. `slt_sound`: the net `lt` is `slt a b`, for every `a, b`.
-/

namespace Formal.Net.Compute
open Formal.Net.GcdHw

/-! ## Groups and their values -/

/-- Signed order as unsigned order with bit 31 toggled. -/
def tog (i : Nat) (b : Bool) : Bool := if i = 31 then !b else b

def gval (lo len : Nat) (l : List Bool) (off : Nat) : Nat :=
  ((List.range len).map fun t => 2 ^ t * (tog (lo + t) (l.getD (off + t) false)).toNat).sum

def grpS (lo len : Nat) : List Leaf :=
  (List.range len).map (fun t => .inp 0 (lo + t)) ++ (List.range len).map (fun t => .inp 1 (lo + t))

/-- One group: its bits, its `E` and `D` nets, and the CARRY4 position carrying it. -/
structure SGrp where
  lo : Nat
  len : Nat
  e : Nat
  d : Nat
  cell : Nat   -- index of the CARRY4 in the cell list
  pos : Nat    -- position 0..3 in it
  deriving Repr, DecidableEq

def chOf (pos : Nat) : Cell → Nat
  | .carry4 _ _ _ _ _ _ _ _ co0 co1 co2 co3 => [co0, co1, co2, co3].getD pos 0
  | _ => 0

def SGrp.ch (g : SGrp) (cells : List Cell) : Nat := chOf g.pos (cells.getD g.cell (.inv .c0 0))

/-- The structural chain fact for group `g` in cell `c` (previous carry-out `prev`, `none` for
the first group). -/
def chainOKc (cells : List Cell) (g : SGrp) (prev : Option Nat) : Cell → Bool
  | .carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3 =>
    decide (g.pos < 4) && di.length == 4 && s.length == 4 &&
    s.getD g.pos .c0 == .net g.e && di.getD g.pos .c0 == .net g.d &&
    (if g.pos = 0 then
      (match prev with
       | none => ci == .c0 && cy == .c0
       | some p => ci == .net p && cy == .c0)
     else (match prev with
       | none => false
       | some p => [co0, co1, co2].getD (g.pos - 1) 0 == p)) &&
    (insNets (.carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3)).all
      (fun n => !(((cells.drop g.cell).flatMap Cell.outs).contains n))
  | _ => false

def chainOK (cells : List Cell) (g : SGrp) (prev : Option Nat) : Bool :=
  chainOKc cells g prev (cells.getD g.cell (.inv .c0 0))

def eqSpecG (lo len : Nat) (l : List Bool) : Bool := gval lo len l 0 == gval lo len l len
def gtSpecG (lo len : Nat) (l : List Bool) : Bool := decide (gval lo len l len < gval lo len l 0)

def GrpsOK : List SGrp → Nat → Prop
  | [], lo => lo = 32
  | g :: gs, lo => g.lo = lo ∧ 0 < g.len ∧ GrpsOK gs (lo + g.len)

instance : (gs : List SGrp) → (lo : Nat) → Decidable (GrpsOK gs lo)
  | [], lo => inferInstanceAs (Decidable (lo = 32))
  | g :: gs, lo => by
    unfold GrpsOK; exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
      (instDecidableGrpsOK gs (lo + g.len)))

def chainAll (cells : List Cell) : List SGrp → Option Nat → Bool
  | [], _ => true
  | g :: gs, prev => chainOK cells g prev && chainAll cells gs (some (g.ch cells))

def lastCh (cells : List Cell) : List SGrp → Option Nat → Option Nat
  | [], p => p
  | g :: gs, _ => lastCh cells gs (some (g.ch cells))

def SltOK (cells : List Cell) (gs : List SGrp) (lt : Nat) : Prop :=
  (cells.flatMap Cell.outs).Nodup ∧ GrpsOK gs 0 ∧ chainAll cells gs none = true ∧
  (∀ g ∈ gs, NetOK cells [] g.e (grpS g.lo g.len) (eqSpecG g.lo g.len) ∧
    NetOK cells [] g.d (grpS g.lo g.len) (gtSpecG g.lo g.len)) ∧
  (∃ cl, lastCh cells gs none = some cl ∧
    NetOK cells (gs.map SGrp.e ++ [cl]) lt (gs.map (fun g => .cut g.e) ++ [.cut cl])
      (fun l => !(l.getD gs.length false) && !((l.take gs.length).all id)))

end Formal.Net.Compute

/-! ## Arithmetic -/

namespace Formal.Net.Compute
open Formal.Net.GcdHw

theorem mod_two_eq_testBit (x : Nat) : x % 2 = if x.testBit 0 then 1 else 0 := by
  rw [Nat.testBit_zero]; rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h]

theorem mod_mul_eq (x P Q : Nat) : x % (P * Q) = x % P + P * (x / P % Q) := Nat.mod_mul

/-- Lexicographic order of a high digit and a low part. -/
theorem lex_lt (x y P Q : Nat) (hP : 0 < P) :
    decide (y % (P * Q) < x % (P * Q)) =
      if x / P % Q = y / P % Q then decide (y % P < x % P) else decide (y / P % Q < x / P % Q) := by
  rw [mod_mul_eq, mod_mul_eq]
  have hx := Nat.mod_lt x hP
  have hy := Nat.mod_lt y hP
  by_cases he : x / P % Q = y / P % Q
  · rw [if_pos he, he]; simp only [decide_eq_decide]; omega
  · rw [if_neg he]
    simp only [decide_eq_decide]
    rcases Nat.lt_or_gt_of_ne he with h | h
    · have : P * (x / P % Q) + P ≤ P * (y / P % Q) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
      constructor
      · intro; omega
      · intro; omega
    · have : P * (y / P % Q) + P ≤ P * (x / P % Q) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h
      constructor
      · intro; omega
      · intro; omega

theorem lex_eq (x y P Q : Nat) (hP : 0 < P) :
    (x % (P * Q) = y % (P * Q)) ↔ (x % P = y % P ∧ x / P % Q = y / P % Q) := by
  rw [mod_mul_eq, mod_mul_eq]
  have hx := Nat.mod_lt x hP
  have hy := Nat.mod_lt y hP
  constructor
  · intro h
    by_cases he : x / P % Q = y / P % Q
    · rw [he] at h; exact ⟨by omega, he⟩
    · exfalso
      rcases Nat.lt_or_gt_of_ne he with h' | h'
      · have : P * (x / P % Q) + P ≤ P * (y / P % Q) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h'
        omega
      · have : P * (y / P % Q) + P ≤ P * (x / P % Q) := by
          rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ h'
        omega
  · rintro ⟨h1, h2⟩; rw [h1, h2]

/-- The value of `len` bits of `x` from `lo`. -/
theorem sum_bits (x lo : Nat) : ∀ len : Nat,
    ((List.range len).map fun t => 2 ^ t * (x.testBit (lo + t)).toNat).sum = x / 2 ^ lo % 2 ^ len
  | 0 => by simp [Nat.mod_one]
  | len + 1 => by
    rw [List.range_succ, List.map_append, List.sum_append, sum_bits x lo len]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
    rw [Nat.pow_succ, mod_mul_eq, Nat.testBit_eq_decide_div_mod_eq, Nat.pow_add,
      ← Nat.div_div_eq_div_mul]
    rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ lo / 2 ^ len) with h | h <;> simp [h]

/-- Toggling bit 31 is the signed order's flip. -/
theorem flip_bit (a i : Nat) (hi : i < 32) : (Ops.flip 32 a).testBit i = tog i (a.testBit i) := by
  unfold Ops.flip tog
  have hb : (a % 2 ^ 32).testBit i = a.testBit i := by
    rw [Nat.testBit_mod_two_pow]; simp [hi]
  rw [Nat.testBit_mod_two_pow]
  simp only [hi, decide_true, Bool.true_and, show 32 - 1 = 31 from rfl]
  rw [← hb, Nat.add_comm]
  by_cases h31 : i = 31
  · subst h31; rw [if_pos rfl, Nat.testBit_two_pow_add_eq]
  · rw [if_neg h31, Nat.testBit_two_pow_add_gt (by omega)]

end Formal.Net.Compute

/-! ## The CARRY4 chain, structurally -/

namespace Formal.Net.Compute
open Formal.Net.GcdHw
open Formal.Core.Prims (bmux bout bc1 bc2 bc3 bc4)

theorem c4_co (env : Leaf → Bool) (cells : List Cell) (hnd : (cells.flatMap Cell.outs).Nodup)
    (i : Nat) {ci cy : W} {di s : List W} {o0 o1 o2 o3 co0 co1 co2 co3 : Nat}
    (hc : cells[i]? = some (.carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3))
    (htopo : ∀ n ∈ insNets (.carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3),
      n ∉ (cells.drop i).flatMap Cell.outs) :
    let R := run env [] cells (fun _ => false)
    let r := wv env R
    R co0 = bmux (r (s.getD 0 .c0)) (r (di.getD 0 .c0)) (r ci || r cy) ∧
    R co1 = bmux (r (s.getD 1 .c0)) (r (di.getD 1 .c0)) (R co0) ∧
    R co2 = bmux (r (s.getD 2 .c0)) (r (di.getD 2 .c0)) (R co1) ∧
    R co3 = bmux (r (s.getD 3 .c0)) (r (di.getD 3 .c0)) (R co2) := by
  intro R r
  have e := fun j hj => run_cell env cells hnd i _ hc htopo j hj
  have e4 := e 4 (by simp [Cell.outs])
  have e5 := e 5 (by simp [Cell.outs])
  have e6 := e 6 (by simp [Cell.outs])
  have e7 := e 7 (by simp [Cell.outs])
  simp only [Cell.outs, Cell.vals, List.getElem_cons_succ, List.getElem_cons_zero,
    List.getD_cons_succ, List.getD_cons_zero, bout] at e4 e5 e6 e7
  refine ⟨e4, ?_, ?_, ?_⟩
  · show R co1 = _
    rw [show R co0 = _ from e4]; exact e5
  · show R co2 = _
    rw [show R co1 = _ from e5]; exact e6
  · show R co3 = _
    rw [show R co2 = _ from e6]; exact e7

end Formal.Net.Compute

namespace Formal.Net.Compute
open Formal.Net.GcdHw
open Formal.Core.Prims (bmux)

theorem getD_carry4 {cells : List Cell} {i : Nat} {ci cy : W} {di s : List W}
    {o0 o1 o2 o3 co0 co1 co2 co3 : Nat}
    (h : cells.getD i (.inv .c0 0) = .carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3) :
    cells[i]? = some (.carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3) := by
  rw [List.getD_eq_getElem?_getD] at h
  cases hc : cells[i]? with
  | none => rw [hc] at h; cases h
  | some c => rw [hc] at h; simp at h; rw [h]

/-- The previous carry's value (`false` before the first group). -/
def pv (R : Nat → Bool) : Option Nat → Bool
  | none => false
  | some p => R p

/-- **One step of the chain**, from the structural certificate. -/
theorem chain_step (env : Leaf → Bool) (cells : List Cell) (hnd : (cells.flatMap Cell.outs).Nodup)
    (g : SGrp) (prev : Option Nat) (hok : chainOK cells g prev = true) :
    run env [] cells (fun _ => false) (g.ch cells) =
      if run env [] cells (fun _ => false) g.e then pv (run env [] cells (fun _ => false)) prev
      else run env [] cells (fun _ => false) g.d := by
  unfold chainOK at hok
  unfold SGrp.ch
  generalize hcg : cells.getD g.cell (.inv .c0 0) = c at hok
  cases c with
  | lut _ _ _ => simp [chainOKc] at hok
  | muxf _ _ _ _ => simp [chainOKc] at hok
  | inv _ _ => simp [chainOKc] at hok
  | carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3 =>
    simp only [chainOKc, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hok
    obtain ⟨⟨⟨⟨⟨⟨hpos, hdl⟩, hsl⟩, hse⟩, hde⟩, hprev⟩, htop⟩ := hok
    have htopo : ∀ n ∈ insNets (.carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3),
        n ∉ (cells.drop g.cell).flatMap Cell.outs := by
      intro n hn hm
      have := List.all_eq_true.mp htop n hn
      simp only [Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at this
      exact this n hm rfl
    obtain ⟨h0, h1, h2, h3⟩ := c4_co env cells hnd g.cell (getD_carry4 hcg) htopo
    simp only [chOf]
    have hr : ∀ n, wv env (run env [] cells (fun _ => false)) (.net n) =
        run env [] cells (fun _ => false) n := fun _ => rfl
    rcases (show g.pos = 0 ∨ g.pos = 1 ∨ g.pos = 2 ∨ g.pos = 3 by omega) with hp | hp | hp | hp <;>
      rw [hp] at hse hde hprev ⊢ <;> simp only [List.getD_cons_zero, List.getD_cons_succ] at hprev ⊢
    · rw [h0, hse, hde, hr, hr]
      cases prev with
      | none =>
        simp only [Bool.and_eq_true, beq_iff_eq, if_true] at hprev
        obtain ⟨rfl, rfl⟩ := hprev; simp [bmux, wv, pv]
      | some p =>
        simp only [Bool.and_eq_true, beq_iff_eq, if_true] at hprev
        obtain ⟨rfl, rfl⟩ := hprev; simp [bmux, wv, pv]
    · rw [h1, hse, hde, hr, hr]
      cases prev with
      | none => simp at hprev
      | some p => simp at hprev; subst hprev; simp [bmux, pv]
    · rw [h2, hse, hde, hr, hr]
      cases prev with
      | none => simp at hprev
      | some p => simp at hprev; subst hprev; simp [bmux, pv]
    · rw [h3, hse, hde, hr, hr]
      cases prev with
      | none => simp at hprev
      | some p => simp at hprev; subst hprev; simp [bmux, pv]

end Formal.Net.Compute

/-! ## Soundness -/

namespace Formal.Net.Compute
open Formal.Net.GcdHw

theorem grps_mem : ∀ (gs : List SGrp) (lo : Nat), GrpsOK gs lo → ∀ g ∈ gs, g.lo + g.len ≤ 32
  | [], _, _, _, hg => by simp at hg
  | g :: gs, lo, ⟨h1, h2, h3⟩, g', hg' => by
    rcases List.mem_cons.mp hg' with rfl | hm
    · have := grps_le' gs _ h3; omega
    · exact grps_mem gs _ h3 g' hm
where grps_le' : ∀ (gs : List SGrp) (lo : Nat), GrpsOK gs lo → lo ≤ 32
  | [], _, h => by simp [GrpsOK] at h; omega
  | g :: gs, lo, ⟨_, hl, h⟩ => by have := grps_le' gs _ h; omega

theorem grps_le : ∀ (gs : List SGrp) (lo : Nat), GrpsOK gs lo → lo ≤ 32
  | [], _, h => by simp [GrpsOK] at h; omega
  | g :: gs, lo, ⟨_, hl, h⟩ => by have := grps_le gs _ h; omega

theorem gval_grp (xs : List Nat) (a b lo len : Nat) (ha : xs.getD 0 0 = a) (hb : xs.getD 1 0 = b)
    (cells : List Cell) (hl : lo + len ≤ 32) :
    gval lo len ((grpS lo len).map (cutEnv (inEnv xs) cells)) 0 =
      Ops.flip 32 a / 2 ^ lo % 2 ^ len ∧
    gval lo len ((grpS lo len).map (cutEnv (inEnv xs) cells)) len =
      Ops.flip 32 b / 2 ^ lo % 2 ^ len := by
  constructor
  · rw [← sum_bits]
    unfold gval
    congr 1
    apply List.map_congr_left
    intro t ht
    have ht' := List.mem_range.mp ht
    rw [flip_bit _ _ (by omega)]
    congr 2
    simp only [grpS, List.map_append, List.map_map, Nat.zero_add]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using ht'),
      List.getElem?_map, List.getElem?_range ht']
    rw [List.getD_eq_getElem?_getD] at ha hb
    simp [cutEnv, inEnv, ha, hb]
  · rw [← sum_bits]
    unfold gval
    congr 1
    apply List.map_congr_left
    intro t ht
    have ht' := List.mem_range.mp ht
    rw [flip_bit _ _ (by omega)]
    congr 2
    simp only [grpS, List.map_append, List.map_map]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp only [List.length_map, List.length_range, Nat.add_sub_cancel_left]
    rw [List.getElem?_map, List.getElem?_range ht']
    rw [List.getD_eq_getElem?_getD] at ha hb
    simp [cutEnv, inEnv, ha, hb]

end Formal.Net.Compute

namespace Formal.Net.Compute
open Formal.Net.GcdHw

theorem chain_ind (env : Leaf → Bool) (cells : List Cell) (hnd : (cells.flatMap Cell.outs).Nodup)
    (x y : Nat) :
    ∀ (gs : List SGrp) (lo : Nat) (prev : Option Nat),
      GrpsOK gs lo → chainAll cells gs prev = true →
      (∀ g ∈ gs, run env [] cells (fun _ => false) g.e =
          (x / 2 ^ g.lo % 2 ^ g.len == y / 2 ^ g.lo % 2 ^ g.len) ∧
        run env [] cells (fun _ => false) g.d =
          decide (y / 2 ^ g.lo % 2 ^ g.len < x / 2 ^ g.lo % 2 ^ g.len)) →
      (prev = none → lo = 0) →
      pv (run env [] cells (fun _ => false)) prev = decide (y % 2 ^ lo < x % 2 ^ lo) →
      (∃ cl, lastCh cells gs prev = some cl ∧
        run env [] cells (fun _ => false) cl = decide (y % 2 ^ 32 < x % 2 ^ 32)) ∧
      ((gs.map fun g => run env [] cells (fun _ => false) g.e).all id = true ↔
        x / 2 ^ lo % 2 ^ (32 - lo) = y / 2 ^ lo % 2 ^ (32 - lo))
  | [], lo, prev, hg, _, _, hnone, hpv => by
    simp only [GrpsOK] at hg
    subst hg
    cases prev with
    | none => exact absurd (hnone rfl) (by decide)
    | some p =>
      refine ⟨⟨p, rfl, hpv⟩, ?_⟩
      simp [Nat.mod_one]
  | g :: gs, lo, prev, ⟨hlo, hlen, hg⟩, hch, hv, hnone, hpv => by
    simp only [chainAll, Bool.and_eq_true] at hch
    have hle := grps_le gs _ hg
    obtain ⟨he, hd⟩ := hv g (List.mem_cons_self ..)
    have hstep := chain_step env cells hnd g prev hch.1
    have hP : 0 < 2 ^ lo := Nat.two_pow_pos _
    have hnew : run env [] cells (fun _ => false) (g.ch cells) =
        decide (y % 2 ^ (lo + g.len) < x % 2 ^ (lo + g.len)) := by
      rw [hstep, he, hd, hpv, Nat.pow_add, lex_lt x y _ _ hP, hlo]
      by_cases hq : x / 2 ^ lo % 2 ^ g.len = y / 2 ^ lo % 2 ^ g.len
      · simp [hq]
      · simp [hq]
    obtain ⟨hcl, hall⟩ := chain_ind env cells hnd x y gs (lo + g.len) (some (g.ch cells)) hg hch.2
      (fun g' hg' => hv g' (List.mem_cons_of_mem _ hg')) (fun h => by cases h) hnew
    refine ⟨hcl, ?_⟩
    simp only [List.map_cons, List.all_cons, Bool.and_eq_true, id, hall, he, hlo, beq_iff_eq]
    have e1 : 2 ^ (32 - lo) = 2 ^ g.len * 2 ^ (32 - (lo + g.len)) := by
      rw [← Nat.pow_add]; congr 1; omega
    have e2 : ∀ z, z / 2 ^ (lo + g.len) = z / 2 ^ lo / 2 ^ g.len := by
      intro z; rw [Nat.pow_add, Nat.div_div_eq_div_mul]
    rw [e1, lex_eq _ _ _ _ (Nat.two_pow_pos _), e2, e2]

/-- **A certified signed comparator computes `slt`**: the net `lt` is `slt a b` (bdc's signed
order: flip the sign bit, compare unsigned) for every `a, b`. -/
theorem slt_sound {cells : List Cell} {gs : List SGrp} {lt : Nat} (h : SltOK cells gs lt)
    (xs : List Nat) :
    run (inEnv xs) [] cells (fun _ => false) lt =
      decide (Ops.flip 32 (xs.getD 0 0) < Ops.flip 32 (xs.getD 1 0)) := by
  obtain ⟨hnd, hg, hch, hgrp, cl, hcl, hlt⟩ := h
  let a := xs.getD 0 0
  let b := xs.getD 1 0
  let env := inEnv xs
  let R := run env [] cells (fun _ => false)
  let x := Ops.flip 32 a
  let y := Ops.flip 32 b
  have hx : x < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hy : y < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hv : ∀ g ∈ gs, R g.e = (x / 2 ^ g.lo % 2 ^ g.len == y / 2 ^ g.lo % 2 ^ g.len) ∧
      R g.d = decide (y / 2 ^ g.lo % 2 ^ g.len < x / 2 ^ g.lo % 2 ^ g.len) := by
    intro g hgm
    obtain ⟨⟨he1, he2, he3⟩, ⟨hd1, hd2, hd3⟩⟩ := hgrp g hgm
    obtain ⟨gv0, gv1⟩ := gval_grp xs a b g.lo g.len rfl rfl cells (grps_mem gs 0 hg g hgm)
    constructor
    · show run env [] cells (fun _ => false) g.e = _
      rw [cert_val hnd he1 he2 he3 env]
      simp only [eqSpecG]
      rw [gv0, gv1]
    · show run env [] cells (fun _ => false) g.d = _
      rw [cert_val hnd hd1 hd2 hd3 env]
      simp only [gtSpecG]
      rw [gv0, gv1]
  obtain ⟨⟨cl', hcl', hR⟩, hall⟩ := chain_ind env cells hnd x y gs 0 none hg hch hv (fun _ => rfl)
    (by simp [pv, Nat.mod_one])
  rw [hcl] at hcl'
  injection hcl' with hcl'
  subst hcl'
  obtain ⟨hl1, hl2, hl3⟩ := hlt
  show R lt = _
  rw [show R lt = _ from cert_val hnd hl1 hl2 hl3 env]
  have hmap : (gs.map (fun g => Leaf.cut g.e) ++ [Leaf.cut cl]).map (cutEnv env cells) =
      gs.map (fun g => R g.e) ++ [R cl] := by
    simp [List.map_append, List.map_map, Function.comp_def, cutEnv, R]
  rw [hmap]
  have hlen : (gs.map fun g => R g.e).length = gs.length := by simp
  have g1 : (gs.map (fun g => R g.e) ++ [R cl]).getD gs.length false = R cl := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
    simp
  have g2 : (gs.map (fun g => R g.e) ++ [R cl]).take gs.length = gs.map (fun g => R g.e) := by
    rw [List.take_append_of_le_length (by simp)]
    exact List.take_of_length_le (by simp)
  have hR' : R cl = decide (y < x) := by
    show run env [] cells (fun _ => false) cl = _
    rw [hR, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]
  have hall' : (gs.map fun g => R g.e).all id = true ↔ x = y := by
    have := hall
    simp only [Nat.pow_zero, Nat.div_one, Nat.sub_zero, Nat.mod_eq_of_lt hx,
      Nat.mod_eq_of_lt hy] at this
    exact this
  rw [g1, g2, hR']
  show _ = decide (x < y)
  by_cases hxy : x = y
  · have : (gs.map fun g => R g.e).all id = true := hall'.mpr hxy
    rw [this]; simp [hxy]
  · have : (gs.map fun g => R g.e).all id = false := by
      cases h : (gs.map fun g => R g.e).all id
      · rfl
      · exact absurd (hall'.mp h) hxy
    rw [this]
    rcases Nat.lt_or_gt_of_ne hxy with h | h
    · simp [h, show ¬ y < x by omega]
    · simp [h, show ¬ x < y by omega]

end Formal.Net.Compute
