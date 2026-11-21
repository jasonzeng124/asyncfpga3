import Formal.Net.Compute.Basic

/-!
# H_COMPUTE_FN, part 6: supports under constant inputs (constant folding)

When some leaves are fixed (`fix l = some b`; e.g. a shifter whose shift-amount port carries the
constant 1), the structural support of a wire still contains every leaf any path reaches. This
file computes a FOLDED abstract value per net: `known b` (the net is the constant `b` whenever
the environment agrees with `fix`), or `sup L` (it depends only on the leaves `L`). A cell whose
inputs are all known is known; a MUXF whose select is known is its selected input; anything else
is the union of its inputs' supports.

`fold_sound`: for any two environments that agree with `fix`, a `known b` net has value `b` in
both, and a `sup L` net has the same value in both when they agree on `L`.
-/

namespace Formal.Net.Compute
open Formal.Core.LutList (lutB)

inductive AV where
  | known (b : Bool)
  | sup (L : List Leaf)
  deriving Repr

def AV.supp : AV → List Leaf
  | .known _ => []
  | .sup L => L

def AV.isKnown : AV → Bool
  | .known _ => true
  | .sup _ => false

def AV.kv : AV → Bool
  | .known b => b
  | .sup _ => false

def aw (fix : Leaf → Option Bool) (a : Nat → AV) : W → AV
  | .inp p k => match fix (.inp p k) with
    | some b => .known b
    | none => .sup [.inp p k]
  | .net n => a n
  | .c0 => .known false
  | .c1 => .known true

/-! ## LUT cofactors: which unknown inputs matter, given the known ones -/

/-- Known inputs of a LUT, by position. -/
def knOf (r : W → AV) (is : List W) : List (Option Bool) :=
  is.map fun w => match r w with
    | .known b => some b
    | .sup _ => none

/-- The input vector for mask `m`: known positions take their value, the others bit `p` of `m`. -/
def asg : List (Option Bool) → Nat → List Bool
  | [], _ => []
  | o :: k, m => (match o with | some b => b | none => m % 2 = 1) :: asg k (m / 2)

/-- Position `p` is irrelevant: flipping mask bit `p` never changes the LUT output. -/
def irrel (init : Nat) (k : List (Option Bool)) (p : Nat) : Bool :=
  (List.range (2 ^ k.length)).all fun m => lutB init (asg k m) == lutB init (asg k (m ^^^ 2 ^ p))

/-- The unknown positions that matter. -/
def relOf (init : Nat) (k : List (Option Bool)) : List Nat :=
  (List.range k.length).filter fun p => (k.getD p none).isNone && !irrel init k p

def alut (r : W → AV) (init : Nat) (is : List W) : AV :=
  let k := knOf r is
  let R := relOf init k
  if R = [] then .known (lutB init (asg k 0))
  else .sup (R.flatMap fun p => (r (is.getD p .c0)).supp)

def acell (r : W → AV) (c : Cell) (j : Nat) : AV :=
  if c.ins.all (fun w => (r w).isKnown) then .known ((c.vals (fun w => (r w).kv)).getD j false)
  else match c with
    | .muxf i0 i1 s _ => match r s with
      | .known b => if j = 0 then (if b then r i1 else r i0) else .known false
      | .sup _ => .sup (c.ins.flatMap fun w => (r w).supp)
    | .lut init is _ => if j = 0 then alut r init is else .known false
    | _ => .sup (c.ins.flatMap fun w => (r w).supp)

def astep (fix : Leaf → Option Bool) (C : List Nat) (a : Nat → AV) (c : Cell) : Nat → AV :=
  fun m => if m ∈ c.outs then (if m ∈ C then .sup [.cut m] else acell (aw fix a) c (c.outs.idxOf m))
    else a m

def arun (fix : Leaf → Option Bool) (C : List Nat) : List Cell → (Nat → AV) → (Nat → AV)
  | [], a => a
  | c :: cs, a => arun fix C cs (astep fix C a c)

/-- The folded abstract value of wire `w`. -/
def afOf (fix : Leaf → Option Bool) (C : List Nat) (cells : List Cell) (w : W) : AV :=
  aw fix (arun fix C cells (fun _ => .known false)) w

/-- The relation between an abstract value and two concrete ones. -/
def Rel (env1 env2 : Leaf → Bool) : AV → Bool → Bool → Prop
  | .known b, b1, b2 => b1 = b ∧ b2 = b
  | .sup L, b1, b2 => (∀ l ∈ L, env1 l = env2 l) → b1 = b2

def Agrees (fix : Leaf → Option Bool) (env : Leaf → Bool) : Prop := ∀ l b, fix l = some b → env l = b

theorem rel_wire {fix : Leaf → Option Bool} {env1 env2 : Leaf → Bool} {a : Nat → AV}
    {v1 v2 : Nat → Bool} (h1 : Agrees fix env1) (h2 : Agrees fix env2)
    (hI : ∀ m, Rel env1 env2 (a m) (v1 m) (v2 m)) (w : W) :
    Rel env1 env2 (aw fix a w) (wv env1 v1 w) (wv env2 v2 w) := by
  cases w with
  | inp p k =>
    simp only [aw, wv]
    cases hf : fix (.inp p k) with
    | some b => exact ⟨h1 _ _ hf, h2 _ _ hf⟩
    | none => exact fun h => h _ (List.mem_singleton_self _)
  | net n => exact hI n
  | c0 => exact ⟨rfl, rfl⟩
  | c1 => exact ⟨rfl, rfl⟩

theorem rel_union {env1 env2 : Leaf → Bool} {r : W → AV} {r1 r2 : W → Bool} (ws : List W)
    (hR : ∀ w ∈ ws, Rel env1 env2 (r w) (r1 w) (r2 w))
    (h : ∀ l ∈ ws.flatMap (fun w => (r w).supp), env1 l = env2 l) : ∀ w ∈ ws, r1 w = r2 w := by
  intro w hw
  have hRw := hR w hw
  cases hrw : r w with
  | known b => rw [hrw] at hRw; exact hRw.1.trans hRw.2.symm
  | sup L =>
    rw [hrw] at hRw
    apply hRw
    intro l hl
    apply h l
    exact List.mem_flatMap.mpr ⟨w, hw, by simp [hrw, AV.supp, hl]⟩


/-! ### Soundness of the cofactor analysis -/

theorem asg_congr : ∀ (k : List (Option Bool)) (m1 m2 : Nat),
    (∀ p, p < k.length → (k.getD p none).isNone = true → m1.testBit p = m2.testBit p) →
    asg k m1 = asg k m2
  | [], _, _, _ => rfl
  | o :: k, m1, m2, h => by
    simp only [asg]
    have ht := asg_congr k (m1 / 2) (m2 / 2) (fun p hp hn => by
      have := h (p + 1) (by simp; omega) (by simpa using hn)
      simpa [Nat.testBit_succ] using this)
    rw [ht]
    cases o with
    | some b => rfl
    | none =>
      have := h 0 (by simp) rfl
      simp only [Nat.testBit_zero, decide_eq_decide] at this
      simp [this]

/-- A value vector consistent with the known positions. -/
def ConsL : List (Option Bool) → List Bool → Prop
  | [], [] => True
  | o :: k, b :: x => (∀ b', o = some b' → b = b') ∧ ConsL k x
  | _, _ => False

def encL : List Bool → Nat
  | [] => 0
  | b :: x => b.toNat + 2 * encL x

theorem asg_encL : ∀ (k : List (Option Bool)) (x : List Bool), ConsL k x → asg k (encL x) = x
  | [], [], _ => rfl
  | o :: k, b :: x, ⟨h1, h2⟩ => by
    simp only [asg, encL]
    have e1 : (b.toNat + 2 * encL x) / 2 = encL x := by cases b <;> simp <;> omega
    rw [e1, asg_encL k x h2]
    cases o with
    | some b' => rw [h1 b' rfl]
    | none => cases b <;> simp
  | [], _ :: _, h => absurd h (by simp [ConsL])
  | _ :: _, [], h => absurd h (by simp [ConsL])

theorem testBit_encL : ∀ (x : List Bool) (p : Nat), p < x.length → (encL x).testBit p = x.getD p false
  | [], _, h => absurd h (by simp)
  | b :: x, 0, _ => by simp [encL, Nat.testBit_zero]; cases b <;> simp <;> omega
  | b :: x, p + 1, h => by
    simp only [encL, Nat.testBit_succ]
    have e1 : (b.toNat + 2 * encL x) / 2 = encL x := by cases b <;> simp <;> omega
    rw [e1, testBit_encL x p (by simp at h; omega)]
    simp

/-- The mask with bits `< q` from `m2` and the others from `m1`. -/
def mix (q m1 m2 : Nat) : Nat := m2 % 2 ^ q ||| (m1 >>> q) <<< q

theorem testBit_mix (q m1 m2 p : Nat) :
    (mix q m1 m2).testBit p = if p < q then m2.testBit p else m1.testBit p := by
  simp only [mix, Nat.testBit_or, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight]
  by_cases h : p < q
  · simp [h, show ¬ (q ≤ p) by omega]
  · simp [h, show q ≤ p by omega, show q + (p - q) = p by omega]

/-- **Irrelevant positions do not matter**: masks agreeing on the relevant positions give the
same LUT output. -/
theorem chain (init : Nat) (k : List (Option Bool)) (m1 m2 : Nat)
    (h : ∀ p ∈ relOf init k, m1.testBit p = m2.testBit p) :
    lutB init (asg k m1) = lutB init (asg k m2) := by
  have step : ∀ q, q ≤ k.length → lutB init (asg k m1) = lutB init (asg k (mix q m1 m2)) := by
    intro q
    induction q with
    | zero =>
      intro _
      rw [asg_congr k m1 (mix 0 m1 m2) (fun p _ _ => by rw [testBit_mix]; simp)]
    | succ q ih =>
      intro hq
      rw [ih (by omega)]
      by_cases hb : m1.testBit q = m2.testBit q
      · rw [asg_congr k (mix q m1 m2) (mix (q + 1) m1 m2) (fun p _ _ => by
          rw [testBit_mix, testBit_mix]
          by_cases h1 : p < q
          · simp [h1, show p < q + 1 by omega]
          · by_cases h2 : p = q
            · subst h2; simp [hb]
            · simp [h1, show ¬ p < q + 1 by omega])]
      · by_cases hk : (k.getD q none).isNone = true
        · have hq' : q ∉ relOf init k := fun hm => hb (h q hm)
          have hirr : irrel init k q = true := by
            simp only [relOf, List.mem_filter, List.mem_range, Bool.and_eq_true, hk,
              Bool.not_eq_true', true_and, not_and] at hq'
            cases hi : irrel init k q
            · exact absurd hi (hq' (by omega))
            · rfl
          let m := mix q m1 m2 % 2 ^ k.length
          have hm : m < 2 ^ k.length := Nat.mod_lt _ (Nat.two_pow_pos _)
          have he := List.all_eq_true.mp hirr m (List.mem_range.mpr hm)
          simp only [beq_iff_eq] at he
          have c1 : asg k (mix q m1 m2) = asg k m := asg_congr k _ _ (fun p hp _ => by
            simp [m, Nat.testBit_mod_two_pow, hp])
          have c2 : asg k (m ^^^ 2 ^ q) = asg k (mix (q + 1) m1 m2) := asg_congr k _ _ (fun p hp _ => by
            simp only [m, Nat.testBit_xor, Nat.testBit_mod_two_pow, Nat.testBit_two_pow, hp,
              decide_true, Bool.true_and, testBit_mix]
            by_cases h1 : p < q
            · simp [h1, show p < q + 1 by omega, show q ≠ p by omega]
            · by_cases h2 : p = q
              · subst h2
                simp only [Nat.lt_irrefl, if_false, decide_true, Nat.lt_succ_self, if_true]
                cases h3 : m1.testBit p <;> cases h4 : m2.testBit p <;> simp_all
              · simp [h1, show ¬ p < q + 1 by omega, show q ≠ p by omega])
          rw [c1, he, c2]
        · rw [asg_congr k (mix q m1 m2) (mix (q + 1) m1 m2) (fun p hp hn => by
            rw [testBit_mix, testBit_mix]
            by_cases h1 : p < q
            · simp [h1, show p < q + 1 by omega]
            · by_cases h2 : p = q
              · subst h2; exact absurd hn hk
              · simp [h1, show ¬ p < q + 1 by omega])]
  rw [step k.length (Nat.le_refl _), asg_congr k _ m2 (fun p hp _ => by rw [testBit_mix]; simp [hp])]

theorem consL_map {env1 env2 : Leaf → Bool} {r : W → AV} {r1 r2 : W → Bool}
    (hR : ∀ w, Rel env1 env2 (r w) (r1 w) (r2 w)) :
    ∀ is : List W, ConsL (knOf r is) (is.map r1) ∧ ConsL (knOf r is) (is.map r2)
  | [] => ⟨trivial, trivial⟩
  | w :: is => by
    have ih := consL_map hR is
    have hw := hR w
    simp only [knOf, List.map_cons] at ih ⊢
    refine ⟨⟨?_, ih.1⟩, ⟨?_, ih.2⟩⟩ <;>
    · intro b' hb'
      cases hrw : r w with
      | known b => rw [hrw] at hw hb'; simp at hb'; subst hb'; first | exact hw.1 | exact hw.2
      | sup L => rw [hrw] at hb'; simp at hb'

theorem rel_lut {env1 env2 : Leaf → Bool} {r : W → AV} {r1 r2 : W → Bool} (init : Nat)
    (is : List W) (hR : ∀ w, Rel env1 env2 (r w) (r1 w) (r2 w)) :
    Rel env1 env2 (alut r init is) (lutB init (is.map r1)) (lutB init (is.map r2)) := by
  obtain ⟨c1, c2⟩ := consL_map hR is
  rw [← asg_encL _ _ c1, ← asg_encL _ _ c2]
  unfold alut
  simp only
  by_cases hR0 : relOf init (knOf r is) = []
  · rw [if_pos hR0]
    exact ⟨chain init _ _ 0 (by simp [hR0]), chain init _ _ 0 (by simp [hR0])⟩
  · rw [if_neg hR0]
    intro hag
    apply chain
    intro p hp
    have hlen : p < is.length := by
      simp only [relOf, List.mem_filter, List.mem_range, knOf, List.length_map] at hp; exact hp.1
    rw [testBit_encL _ _ (by simpa using hlen), testBit_encL _ _ (by simpa using hlen)]
    have hw := hR (is.getD p .c0)
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen,
      List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hlen]
    simp only [Option.map_some, Option.getD_some]
    have hge : is.getD p .c0 = is[p] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]; rfl
    rw [hge] at hw
    cases hrw : r is[p] with
    | known b => rw [hrw] at hw; exact hw.1.trans hw.2.symm
    | sup L =>
      rw [hrw] at hw
      apply hw
      intro l hl
      apply hag
      exact List.mem_flatMap.mpr ⟨p, hp, by rw [hge, hrw]; exact hl⟩

theorem rel_cell {env1 env2 : Leaf → Bool} {r : W → AV} {r1 r2 : W → Bool} (c : Cell) (j : Nat)
    (hR : ∀ w, Rel env1 env2 (r w) (r1 w) (r2 w)) (hc0 : r .c0 = .known false) :
    Rel env1 env2 (acell r c j) ((c.vals r1).getD j false) ((c.vals r2).getD j false) := by
  have h01 : r1 .c0 = false := by have := hR .c0; rw [hc0] at this; exact this.1
  have h02 : r2 .c0 = false := by have := hR .c0; rw [hc0] at this; exact this.2
  have hU : ∀ (r' : W → Bool), (∀ w ∈ c.ins, r' w = (r w).kv) → r' .c0 = false →
      c.vals r' = c.vals (fun w => (r w).kv) := by
    intro r' h h0
    apply vals_congr c h
    rw [h0, hc0]; rfl
  have hgen : (∀ l ∈ c.ins.flatMap (fun w => (r w).supp), env1 l = env2 l) →
      (c.vals r1).getD j false = (c.vals r2).getD j false := by
    intro h
    rw [vals_congr c (rel_union c.ins (fun w _ => hR w) h) (h01.trans h02.symm)]
  unfold acell
  by_cases hk : c.ins.all (fun w => (r w).isKnown) = true
  · rw [if_pos hk]
    have hin : ∀ (r' : W → Bool), (∀ w, (∀ b, r w = .known b → r' w = b)) →
        ∀ w ∈ c.ins, r' w = (r w).kv := by
      intro r' h w hw
      have := List.all_eq_true.mp hk w hw
      cases hrw : r w with
      | known b => exact h w b hrw
      | sup L => rw [hrw] at this; exact absurd this (by simp [AV.isKnown])
    have k1 : ∀ w, ∀ b, r w = .known b → r1 w = b := by
      intro w b hb; have := hR w; rw [hb] at this; exact this.1
    have k2 : ∀ w, ∀ b, r w = .known b → r2 w = b := by
      intro w b hb; have := hR w; rw [hb] at this; exact this.2
    rw [hU r1 (hin r1 k1) h01, hU r2 (hin r2 k2) h02]
    exact ⟨rfl, rfl⟩
  · rw [if_neg hk]
    cases c with
    | muxf i0 i1 s o =>
      cases hs : r s with
      | known b =>
        simp only [hs]
        have e1 : r1 s = b := by have := hR s; rw [hs] at this; exact this.1
        have e2 : r2 s = b := by have := hR s; rw [hs] at this; exact this.2
        by_cases hj : j = 0
        · subst hj
          simp only [if_true, Cell.vals, List.getD_cons_zero, e1, e2]
          cases b
          · exact hR i0
          · exact hR i1
        · simp only [hj, if_false]
          obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
          simp [Cell.vals, Rel]
      | sup L => simp only [hs]; exact hgen
    | lut init is o =>
      simp only
      by_cases hj : j = 0
      · subst hj
        simp only [if_true, Cell.vals, List.getD_cons_zero]
        exact rel_lut init is hR
      · simp only [hj, if_false]
        obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
        simp [Cell.vals, Rel]
    | inv i o => exact hgen
    | carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3 => exact hgen

theorem rel_step {fix : Leaf → Option Bool} {env1 env2 : Leaf → Bool} {C : List Nat}
    {a : Nat → AV} {v1 v2 : Nat → Bool} (h1 : Agrees fix env1) (h2 : Agrees fix env2)
    (hI : ∀ m, Rel env1 env2 (a m) (v1 m) (v2 m)) (c : Cell) :
    ∀ m, Rel env1 env2 (astep fix C a c m) (step env1 C v1 c m) (step env2 C v2 c m) := by
  intro m
  simp only [astep, step]
  by_cases ho : m ∈ c.outs
  · simp only [ho, if_true]
    by_cases hc : m ∈ C
    · simp only [hc, if_true, cutv]
      exact fun h => h _ (List.mem_singleton_self _)
    · simp only [hc, if_false, cutv]
      exact rel_cell c _ (rel_wire h1 h2 hI) rfl
  · simp only [ho, if_false]
    exact hI m

theorem rel_run {fix : Leaf → Option Bool} {env1 env2 : Leaf → Bool} {C : List Nat}
    (h1 : Agrees fix env1) (h2 : Agrees fix env2) :
    ∀ (cells : List Cell) {a : Nat → AV} {v1 v2 : Nat → Bool},
      (∀ m, Rel env1 env2 (a m) (v1 m) (v2 m)) →
      ∀ m, Rel env1 env2 (arun fix C cells a m) (run env1 C cells v1 m) (run env2 C cells v2 m)
  | [], _, _, _, h => h
  | c :: cs, _, _, _, h => rel_run h1 h2 cs (rel_step h1 h2 h c)

/-- **Folding soundness.** For two environments agreeing with `fix`: a wire folded to
`known b` evaluates to `b` in both; a wire folded to `sup L` evaluates equally in both when
they agree on `L`. -/
theorem fold_sound {fix : Leaf → Option Bool} {env1 env2 : Leaf → Bool} (C : List Nat)
    (cells : List Cell) (w : W) (h1 : Agrees fix env1) (h2 : Agrees fix env2) :
    Rel env1 env2 (afOf fix C cells w) (eval env1 C cells w) (eval env2 C cells w) :=
  rel_wire h1 h2 (rel_run h1 h2 cells (a := fun _ => .known false) (v1 := fun _ => false)
    (v2 := fun _ => false) (fun _ => ⟨rfl, rfl⟩)) w

end Formal.Net.Compute
