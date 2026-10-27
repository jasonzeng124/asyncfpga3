import Wip.C9c.Local

namespace Formal.Net.MullerAll
open Formal.Net Formal.Net.Muller Formal.Net.CoreLut

theorem ifN {p : Prop} [Decidable p] (h : ¬p) {α : Sort _} (a b : α) :
    (if p then a else b) = b := by simp [h]
theorem ifP {p : Prop} [Decidable p] (h : p) {α : Sort _} (a b : α) :
    (if p then a else b) = a := by simp [h]

/-! ## Node arithmetic -/
section Nodes
variable {k j : Nat}
@[simp] theorem ne_src_snk : (src = snk) ↔ False := by simp only [iff_false]; unfold snk src; omega
@[simp] theorem ne_src_c : (src = c j) ↔ False := by simp only [iff_false]; unfold c src; omega
@[simp] theorem ne_src_b : (src = b j) ↔ False := by simp only [iff_false]; unfold b src; omega
@[simp] theorem ne_src_w : (src = w j) ↔ False := by simp only [iff_false]; unfold src w; omega
@[simp] theorem ne_src_f : (src = f j) ↔ False := by simp only [iff_false]; unfold f src; omega
@[simp] theorem ne_snk_src : (snk = src) ↔ False := by simp only [iff_false]; unfold snk src; omega
@[simp] theorem ne_snk_c : (snk = c j) ↔ False := by simp only [iff_false]; unfold c snk; omega
@[simp] theorem ne_snk_b : (snk = b j) ↔ False := by simp only [iff_false]; unfold b snk; omega
@[simp] theorem ne_snk_w : (snk = w j) ↔ False := by simp only [iff_false]; unfold snk w; omega
@[simp] theorem ne_snk_f : (snk = f j) ↔ False := by simp only [iff_false]; unfold f snk; omega
@[simp] theorem ne_c_src : (c k = src) ↔ False := by simp only [iff_false]; unfold c src; omega
@[simp] theorem ne_c_snk : (c k = snk) ↔ False := by simp only [iff_false]; unfold c snk; omega
@[simp] theorem ne_c_b : (c k = b j) ↔ False := by simp only [iff_false]; unfold b c; omega
@[simp] theorem ne_c_w : (c k = w j) ↔ False := by simp only [iff_false]; unfold c w; omega
@[simp] theorem ne_c_f : (c k = f j) ↔ False := by simp only [iff_false]; unfold c f; omega
@[simp] theorem ne_b_src : (b k = src) ↔ False := by simp only [iff_false]; unfold b src; omega
@[simp] theorem ne_b_snk : (b k = snk) ↔ False := by simp only [iff_false]; unfold b snk; omega
@[simp] theorem ne_b_c : (b k = c j) ↔ False := by simp only [iff_false]; unfold b c; omega
@[simp] theorem ne_b_w : (b k = w j) ↔ False := by simp only [iff_false]; unfold b w; omega
@[simp] theorem ne_b_f : (b k = f j) ↔ False := by simp only [iff_false]; unfold b f; omega
@[simp] theorem ne_w_src : (w k = src) ↔ False := by simp only [iff_false]; unfold src w; omega
@[simp] theorem ne_w_snk : (w k = snk) ↔ False := by simp only [iff_false]; unfold snk w; omega
@[simp] theorem ne_w_c : (w k = c j) ↔ False := by simp only [iff_false]; unfold c w; omega
@[simp] theorem ne_w_b : (w k = b j) ↔ False := by simp only [iff_false]; unfold b w; omega
@[simp] theorem ne_w_f : (w k = f j) ↔ False := by simp only [iff_false]; unfold f w; omega
@[simp] theorem ne_f_src : (f k = src) ↔ False := by simp only [iff_false]; unfold f src; omega
@[simp] theorem ne_f_snk : (f k = snk) ↔ False := by simp only [iff_false]; unfold f snk; omega
@[simp] theorem ne_f_c : (f k = c j) ↔ False := by simp only [iff_false]; unfold c f; omega
@[simp] theorem ne_f_b : (f k = b j) ↔ False := by simp only [iff_false]; unfold b f; omega
@[simp] theorem ne_f_w : (f k = w j) ↔ False := by simp only [iff_false]; unfold f w; omega
@[simp] theorem inj_c : (c k = c j) ↔ k = j := by unfold c; omega
@[simp] theorem inj_b : (b k = b j) ↔ k = j := by unfold b; omega
@[simp] theorem inj_w : (w k = w j) ↔ k = j := by unfold w; omega
@[simp] theorem inj_f : (f k = f j) ↔ k = j := by unfold f; omega
end Nodes

theorem node_cases {n i : Nat} (hi : i < numNodes n) :
    i = src ∨ i = snk ∨ ∃ k, k < n ∧ (i = c k ∨ i = b k ∨ i = w k ∨ i = f k) := by
  unfold numNodes at hi
  by_cases h0 : i = 0
  · exact Or.inl h0
  by_cases h1 : i = 1
  · exact Or.inr (Or.inl h1)
  refine Or.inr (Or.inr ⟨(i - 2) / 4, by omega, ?_⟩)
  unfold c b w f
  omega

/-! ## Encoding of a position -/

def enc4 (a b c d : Bool) : Nat := a.toNat + 2 * b.toNat + 4 * c.toNat + 8 * d.toNat

section Enc
variable (a b c d x : Bool)
theorem enc4_lt : enc4 a b c d < 16 := by cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem bt_enc4_0 : bt (enc4 a b c d) 0 = a := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem bt_enc4_1 : bt (enc4 a b c d) 1 = b := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem bt_enc4_2 : bt (enc4 a b c d) 2 = c := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem bt_enc4_3 : bt (enc4 a b c d) 3 = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem isSt_enc4 : isSt (enc4 a b c d) = true := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem isSrc_enc4 : isSrc (enc4 a b c d) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem isSnk_enc4 : isSnk (enc4 a b c d) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem flip_enc4_0 : flip (enc4 a b c d) 0 = enc4 (!a) b c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem flip_enc4_1 : flip (enc4 a b c d) 1 = enc4 a (!b) c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem flip_enc4_2 : flip (enc4 a b c d) 2 = enc4 a b (!c) d := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem flip_enc4_3 : flip (enc4 a b c d) 3 = enc4 a b c (!d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
@[simp] theorem bt_src0 : bt (16 + x.toNat) 0 = x := by cases x <;> decide
@[simp] theorem isSrc_src : isSrc (16 + x.toNat) = true := by cases x <;> decide
@[simp] theorem isSnk_src : isSnk (16 + x.toNat) = false := by cases x <;> decide
@[simp] theorem isSt_src : isSt (16 + x.toNat) = false := by cases x <;> decide
theorem flip_src : flip (16 + x.toNat) 0 = 16 + (!x).toNat := by cases x <;> decide
@[simp] theorem bt_snk0 : bt (32 + x.toNat) 0 = x := by cases x <;> decide
@[simp] theorem isSrc_snk : isSrc (32 + x.toNat) = false := by cases x <;> decide
@[simp] theorem isSnk_snk : isSnk (32 + x.toNat) = true := by cases x <;> decide
@[simp] theorem isSt_snk : isSt (32 + x.toNat) = false := by cases x <;> decide
theorem flip_snk : flip (32 + x.toNat) 0 = 32 + (!x).toNat := by cases x <;> decide
end Enc

/-- The value of position `q` of an `n`-stage chain in state `s`: position 0 is
a sentinel (48), position 1 the source (`16 + src`), position `k + 2` stage
`k` (4 bits `c, b, w, f`), position `n + 2` the sink (`32 + snk`), beyond: 48. -/
def V (n s q : Nat) : Nat :=
  if q = 1 then 16 + (get s src).toNat
  else if q = n + 2 then 32 + (get s snk).toNat
  else if 2 ≤ q ∧ q ≤ n + 1 then
    enc4 (get s (c (q - 2))) (get s (b (q - 2))) (get s (w (q - 2))) (get s (f (q - 2)))
  else 48

def posOf (n i : Nat) : Nat := if i = 0 then 1 else if i = 1 then n + 2 else (i - 2) / 4 + 2
def typOf (i : Nat) : Nat := if i < 2 then 0 else (i - 2) % 4

section V
variable {n s q k : Nat}

theorem V_zero : V n s 0 = 48 := by simp [V]
theorem V_one : V n s 1 = 16 + (get s src).toNat := by simp [V]
theorem V_snk (hn : 1 ≤ n) : V n s (n + 2) = 32 + (get s snk).toNat := by
  unfold V; rw [ifN (by omega)]; simp
theorem V_st (hk : k < n) :
    V n s (k + 2) = enc4 (get s (c k)) (get s (b k)) (get s (w k)) (get s (f k)) := by
  unfold V; rw [ifN (by omega), ifN (by omega), ifP (by omega)]; simp
theorem V_out (h : n + 3 ≤ q) : V n s q = 48 := by
  unfold V; rw [ifN (by omega), ifN (by omega), ifN (by omega)]

theorem V_dom (hn : 1 ≤ n) : V n s q ∈ dom := by
  unfold V
  split
  · cases get s src <;> decide
  split
  · cases get s snk <;> decide
  split
  · simp only [dom, List.mem_append, List.mem_range]; exact Or.inl (enc4_lt ..)
  · decide

@[simp] theorem pos_src : posOf n src = 1 := by simp [posOf, src]
@[simp] theorem pos_snk : posOf n snk = n + 2 := by simp [posOf, snk]
@[simp] theorem pos_c : posOf n (c k) = k + 2 := by unfold posOf c; rw [ifN (by omega), ifN (by omega)]; omega
@[simp] theorem pos_b : posOf n (b k) = k + 2 := by unfold posOf b; rw [ifN (by omega), ifN (by omega)]; omega
@[simp] theorem pos_w : posOf n (w k) = k + 2 := by unfold posOf w; rw [ifN (by omega), ifN (by omega)]; omega
@[simp] theorem pos_f : posOf n (f k) = k + 2 := by unfold posOf f; rw [ifN (by omega), ifN (by omega)]; omega
@[simp] theorem typ_src : typOf src = 0 := by simp [typOf, src]
@[simp] theorem typ_snk : typOf snk = 0 := by simp [typOf, snk]
@[simp] theorem typ_c : typOf (c k) = 0 := by unfold typOf c; rw [ifN (by omega)]; omega
@[simp] theorem typ_b : typOf (b k) = 1 := by unfold typOf b; rw [ifN (by omega)]; omega
@[simp] theorem typ_w : typOf (w k) = 2 := by unfold typOf w; rw [ifN (by omega)]; omega
@[simp] theorem typ_f : typOf (f k) = 3 := by unfold typOf f; rw [ifN (by omega)]; omega

end V

/-! ## Node functions, unfolded -/

section NV
variable {m : Mode} {n s k : Nat}

theorem nv_src : nextVal m n s src = !get s (w 0) := by simp [nextVal]
theorem nv_snk : nextVal m n s snk = get s (b (n - 1)) := by simp [nextVal, src, snk]

theorem nv_c : nextVal m n s (c k) =
    evalL INIT_bd_c2n [pinA s k, pinB n s k, pinQ m s k, false, false, false] := by
  have h1 : (c k - 2) / 4 = k := by unfold c; omega
  have h2 : (c k - 2) % 4 = 0 := by unfold c; omega
  simp only [nextVal, ne_c_src, ne_c_snk, ite_false, h1, h2]
theorem nv_b : nextVal m n s (b k) = evalL INIT_buf [get s (c k)] := by
  have h1 : (b k - 2) / 4 = k := by unfold b; omega
  have h2 : (b k - 2) % 4 = 1 := by unfold b; omega
  simp only [nextVal, ne_b_src, ne_b_snk, ite_false, h1, h2]
theorem nv_w : nextVal m n s (w k) = get s (c k) := by
  have h1 : (w k - 2) / 4 = k := by unfold w; omega
  have h2 : (w k - 2) % 4 = 2 := by unfold w; omega
  simp only [nextVal, ne_w_src, ne_w_snk, ite_false, h1, h2]
theorem nv_f : nextVal m n s (f k) = if m = .iso then get s (f k) else get s (c k) := by
  have h1 : (f k - 2) / 4 = k := by unfold f; omega
  have h2 : (f k - 2) % 4 = 3 := by unfold f; omega
  simp only [nextVal, ne_f_src, ne_f_snk, ite_false, h1, h2]

theorem rs_src : readerStage n src = some 0 := by simp [readerStage]
theorem rs_snk : readerStage n snk = some (n - 1) := by simp [readerStage, src, snk]
theorem rs_c : readerStage n (c k) = none := by
  have h1 : (c k - 2) / 4 = k := by unfold c; omega
  have h2 : (c k - 2) % 4 = 0 := by unfold c; omega
  have h3 : ¬ c k < 2 := by unfold c; omega
  simp only [readerStage, ne_c_src, ne_c_snk, ite_false, h1, h2, h3]
theorem rs_b : readerStage n (b k) = if k + 1 < n then some (k + 1) else none := by
  have h1 : (b k - 2) / 4 = k := by unfold b; omega
  have h2 : (b k - 2) % 4 = 1 := by unfold b; omega
  have h3 : ¬ b k < 2 := by unfold b; omega
  simp only [readerStage, ne_b_src, ne_b_snk, ite_false, h1, h2, h3]
theorem rs_w : readerStage n (w k) = if 1 ≤ k then some (k - 1) else none := by
  have h1 : (w k - 2) / 4 = k := by unfold w; omega
  have h2 : (w k - 2) % 4 = 2 := by unfold w; omega
  have h3 : ¬ w k < 2 := by unfold w; omega
  simp only [readerStage, ne_w_src, ne_w_snk, ite_false, h1, h2, h3]
theorem rs_f : readerStage n (f k) = none := by
  have h1 : (f k - 2) / 4 = k := by unfold f; omega
  have h2 : (f k - 2) % 4 = 3 := by unfold f; omega
  have h3 : ¬ f k < 2 := by unfold f; omega
  simp only [readerStage, ne_f_src, ne_f_snk, ite_false, h1, h2, h3]

end NV


/-! ## The local view of every node -/

section Loc
variable {m : Mode} {n s k : Nat}

theorem VL (hk : k < n) :
    (if isSrc (V n s (k + 1)) then bt (V n s (k + 1)) 0 else bt (V n s (k + 1)) 1) = pinA s k := by
  cases k with
  | zero => simp [V_one, pinA]
  | succ j =>
    rw [show j + 1 + 1 = j + 2 from rfl, V_st (by omega)]
    simp [pinA]

theorem VR (hn : 1 ≤ n) (hk : k < n) :
    (if isSnk (V n s (k + 3)) then bt (V n s (k + 3)) 0 else bt (V n s (k + 3)) 2) = pinB n s k := by
  by_cases h : k + 1 = n
  · rw [show k + 3 = n + 2 by omega, V_snk hn]; simp [pinB, h]
  · rw [show k + 3 = (k + 1) + 2 by omega, V_st (by omega)]; simp [pinB, h]

theorem VLst (hk : k < n) : isSt (V n s (k + 1)) = decide (1 ≤ k) := by
  cases k with
  | zero => simp [V_one]
  | succ j =>
    rw [show j + 1 + 1 = j + 2 from rfl, V_st (by omega)]; simp

theorem VRst (hn : 1 ≤ n) (hk : k < n) : isSt (V n s (k + 3)) = decide (k + 1 < n) := by
  by_cases h : k + 1 = n
  · rw [show k + 3 = n + 2 by omega, V_snk hn]; simp; omega
  · rw [show k + 3 = (k + 1) + 2 by omega, V_st (by omega)]; simp; omega

theorem VLbits (hk : k < n) (h1 : 1 ≤ k) :
    bt (V n s (k + 1)) 3 = get s (f (k - 1)) ∧ bt (V n s (k + 1)) 0 = get s (c (k - 1)) := by
  rw [show k + 1 = (k - 1) + 2 by omega, V_st (by omega)]; simp

theorem VRbits (hk : k + 1 < n) :
    bt (V n s (k + 3)) 3 = get s (f (k + 1)) ∧ bt (V n s (k + 3)) 0 = get s (c (k + 1)) := by
  rw [show k + 3 = (k + 1) + 2 by omega, V_st hk]; simp

/-- Every node, read through its position: value, gate function, the rt
restriction, well-formedness. -/
theorem loc (hn : 1 ≤ n) {i : Nat} (hi : i < numNodes n) :
    get s i = bt (V n s (posOf n i)) (typOf i) ∧
    nextVal m n s i = lnext m (V n s (posOf n i - 1)) (V n s (posOf n i)) (V n s (posOf n i + 1)) (typOf i) ∧
    allowed m n s i = lallowed m (V n s (posOf n i - 1)) (V n s (posOf n i)) (V n s (posOf n i + 1)) (typOf i) ∧
    valid (V n s (posOf n i)) (typOf i) = true ∧
    1 ≤ posOf n i ∧ posOf n i ≤ n + 2 := by
  rcases node_cases hi with rfl | rfl | ⟨k, hk, rfl | rfl | rfl | rfl⟩
  · -- source
    have h2 : V n s (1 + 1) = enc4 (get s (c 0)) (get s (b 0)) (get s (w 0)) (get s (f 0)) :=
      V_st (k := 0) (by omega)
    simp only [pos_src, typ_src, V_one, h2, Nat.sub_self]
    refine ⟨by simp, ?_, ?_, by simp [valid], by omega, by omega⟩
    · simp [nv_src, lnext]
    · cases m <;> simp [allowed, lallowed, rs_src]
  · -- sink
    have h2 : V n s (n + 2 - 1) = enc4 (get s (c (n - 1))) (get s (b (n - 1))) (get s (w (n - 1)))
        (get s (f (n - 1))) := by
      rw [show n + 2 - 1 = (n - 1) + 2 by omega, V_st (by omega)]
    simp only [pos_snk, typ_snk, V_snk hn, h2]
    refine ⟨by simp, ?_, ?_, by simp [valid], by omega, by omega⟩
    · simp [nv_snk, lnext]
    · cases m <;> simp [allowed, lallowed, rs_snk]
  · -- C-element
    simp only [pos_c, typ_c, V_st hk, show k + 2 - 1 = k + 1 by omega, show k + 2 + 1 = k + 3 by omega]
    refine ⟨by simp, ?_, ?_, by simp [valid], by omega, by omega⟩
    · rw [nv_c, evalL_c2n]
      simp only [lnext, isSrc_enc4, isSnk_enc4, Bool.false_eq_true, ite_false, VL hk, VR hn hk]
      cases m <;> simp [pinQ]
    · cases m <;> simp [allowed, lallowed, rs_c]
  · -- req LUT1
    simp only [pos_b, typ_b, V_st hk, show k + 2 - 1 = k + 1 by omega, show k + 2 + 1 = k + 3 by omega]
    refine ⟨by simp, ?_, ?_, by simp [valid], by omega, by omega⟩
    · rw [nv_b, evalL_buf]; simp [lnext]
    · cases m
      · simp [allowed, lallowed]
      · simp [allowed, lallowed]
      · simp only [allowed, lallowed, rs_b, isSrc_enc4, isSnk_enc4, Bool.false_eq_true, ite_false,
          VRst hn hk]
        by_cases h : k + 1 < n
        · simp [h, VRbits h]
        · simp [h]
  · -- ack wire
    simp only [pos_w, typ_w, V_st hk, show k + 2 - 1 = k + 1 by omega, show k + 2 + 1 = k + 3 by omega]
    refine ⟨by simp, ?_, ?_, by simp [valid], by omega, by omega⟩
    · simp [nv_w, lnext]
    · cases m
      · simp [allowed, lallowed]
      · simp [allowed, lallowed]
      · simp only [allowed, lallowed, rs_w, isSrc_enc4, isSnk_enc4, Bool.false_eq_true, ite_false,
          VLst hk]
        by_cases h : 1 ≤ k
        · simp [h, VLbits hk h]
        · simp [h]
  · -- feedback wire
    simp only [pos_f, typ_f, V_st hk, show k + 2 - 1 = k + 1 by omega, show k + 2 + 1 = k + 3 by omega]
    refine ⟨by simp, ?_, ?_, by simp [valid], by omega, by omega⟩
    · rw [nv_f]; cases m <;> simp [lnext]
    · cases m <;> simp [allowed, lallowed, rs_f]

end Loc


/-! ## Firing a node changes exactly its position -/

section Fire
variable {n s y q : Nat}

theorem V_fire_other (hq : q ≠ posOf n y) : V n (fire s y) q = V n s q := by
  unfold V
  split
  · have e0 : y ≠ src := by rintro rfl; simp at hq; omega
    simp [get_fire, e0]
  split
  · have e1 : y ≠ snk := by rintro rfl; simp at hq; omega
    simp [get_fire, e1]
  split
  · have e2 : ∀ j, j + 2 = q → y ≠ c j ∧ y ≠ b j ∧ y ≠ w j ∧ y ≠ f j := by
      intro j hj
      refine ⟨?_, ?_, ?_, ?_⟩ <;> (rintro rfl; simp at hq; omega)
    obtain ⟨a1, a2, a3, a4⟩ := e2 (q - 2) (by omega)
    simp [get_fire, a1, a2, a3, a4]
  · rfl

theorem V_fire_self (hn : 1 ≤ n) (hy : y < numNodes n) :
    V n (fire s y) (posOf n y) = flip (V n s (posOf n y)) (typOf y) := by
  rcases node_cases hy with rfl | rfl | ⟨k, hk, rfl | rfl | rfl | rfl⟩
  · simp [V_one, get_fire, flip_src]
  · simp [V_snk hn, get_fire, flip_snk]
  · simp [V_st hk, get_fire, flip_enc4_0]
  · simp [V_st hk, get_fire, flip_enc4_1]
  · simp [V_st hk, get_fire, flip_enc4_2]
  · simp [V_st hk, get_fire, flip_enc4_3]

theorem V_fire (hn : 1 ≤ n) (hy : y < numNodes n) (q : Nat) :
    V n (fire s y) q = if q = posOf n y then flip (V n s q) (typOf y) else V n s q := by
  split
  · subst q; exact V_fire_self hn hy
  · exact V_fire_other (by assumption)

end Fire

theorem typ_lt (i : Nat) : typOf i < 4 := by unfold typOf; split <;> omega

theorem pos_typ_inj {n x y : Nat} (hx : x < numNodes n) (hy : y < numNodes n)
    (hp : posOf n x = posOf n y) (ht : typOf x = typOf y) : x = y := by
  rcases node_cases hx with rfl | rfl | ⟨k, hk, rfl | rfl | rfl | rfl⟩ <;>
  rcases node_cases hy with rfl | rfl | ⟨j, hj, rfl | rfl | rfl | rfl⟩ <;>
  simp at hp ht ⊢ <;> omega

/-! ## Soundness of the window checks -/

theorem mem_types {t : Nat} (h : t < 4) : t ∈ types := by
  simp only [types, List.mem_cons, List.not_mem_nil, or_false]; omega

theorem adm_mem {m : Mode} {a b : Nat} : adm m a b = true ↔ b ∈ adj m a := by
  simp [adm, List.contains_iff_mem]

section Spec
variable {m : Mode} {a b c d z t : Nat}

theorem chkMid_spec (h : chkMid m = true) (ha : a ∈ dom) (hab : adm m a b = true)
    (hbc : adm m b c = true) (ht : t < 4) (he : lenabled m a b c t = true) :
    adm m a (flip b t) = true ∧ adm m (flip b t) c = true ∧ followL a b c t = true ∧
    ∀ u, u < 4 → u ≠ t → valid b u = true → persist m a b (flip b t) c u = true := by
  unfold chkMid at h
  simp only [List.all_eq_true] at h
  have := h a ha b (adm_mem.1 hab) c (adm_mem.1 hbc) t (mem_types ht)
  simp only [he, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨h1, h2, h3, fun u hu hne hv => ?_⟩
  have := h4 u (mem_types hu)
  simpa [hne, hv] using this

theorem chkLeft_spec (h : chkLeft m = true) (hz : z ∈ dom) (hza : adm m z a = true)
    (hab : adm m a b = true) (hbc : adm m b c = true) (ht : t < 4)
    (he : lenabled m a b c t = true) {u : Nat} (hu : u < 4) (hv : valid a u = true) :
    (lexc m z a b u = true → lexc m z a (flip b t) u = true) ∧
    (lenabled m z a b u = true → lenabled m z a (flip b t) u = true) := by
  unfold chkLeft at h
  simp only [List.all_eq_true] at h
  have := h z hz a (adm_mem.1 hza) b (adm_mem.1 hab) c (adm_mem.1 hbc) t (mem_types ht)
  simp only [he, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this u (mem_types hu)
  simp only [hv, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rcases h1 with h1 | h1
    · rw [e] at h1; cases h1
    · exact h1
  · rcases h2 with h2 | h2
    · rw [e] at h2; cases h2
    · exact h2

theorem chkRight_spec (h : chkRight m = true) (ha : a ∈ dom)
    (hab : adm m a b = true) (hbc : adm m b c = true) (hcd : adm m c d = true) (ht : t < 4)
    (he : lenabled m a b c t = true) {u : Nat} (hu : u < 4) (hv : valid c u = true) :
    (lexc m b c d u = true → lexc m (flip b t) c d u = true) ∧
    (lenabled m b c d u = true → lenabled m (flip b t) c d u = true) := by
  unfold chkRight at h
  simp only [List.all_eq_true] at h
  have := h a ha b (adm_mem.1 hab) c (adm_mem.1 hbc) d (adm_mem.1 hcd) t (mem_types ht)
  simp only [he, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this u (mem_types hu)
  simp only [hv, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.or_eq_true,
    Bool.not_eq_true'] at this
  obtain ⟨h1, h2⟩ := this
  refine ⟨fun e => ?_, fun e => ?_⟩
  · rcases h1 with h1 | h1
    · rw [e] at h1; cases h1
    · exact h1
  · rcases h2 with h2 | h2
    · rw [e] at h2; cases h2
    · exact h2

end Spec


/-! ## The stage-local invariant -/

/-- **The hand invariant**: every two adjacent positions of the chain
(sentinel, source, stage 0, ..., stage n-1, sink, sentinel) form an admissible
pair (`adj`, one table per mode, 13 resp. 21 entries; the same table for every
`n` and every stage). -/
def Inv (m : Mode) (n s : Nat) : Prop := ∀ q, q ≤ n + 2 → adm m (V n s q) (V n s (q + 1)) = true

def chkAll (m : Mode) : Bool := chkMid m && chkLeft m && chkRight m && chkInit m

section Main
variable {m : Mode} {n s : Nat}

theorem excited_loc (hn : 1 ≤ n) {i : Nat} (hi : i < numNodes n) :
    excited m n s i = lexc m (V n s (posOf n i - 1)) (V n s (posOf n i)) (V n s (posOf n i + 1)) (typOf i) := by
  obtain ⟨h1, h2, -, -, -⟩ := loc (m := m) (s := s) hn hi
  simp [excited, lexc, h1, h2]

theorem enabled_loc (hn : 1 ≤ n) {i : Nat} (hi : i < numNodes n) :
    enabled m n s i = lenabled m (V n s (posOf n i - 1)) (V n s (posOf n i)) (V n s (posOf n i + 1)) (typOf i) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := loc (m := m) (s := s) hn hi
  simp [enabled, excited, lenabled, lexc, hi, h1, h2, h3, h4]

theorem chkAll_parts (hc : chkAll m = true) :
    chkMid m = true ∧ chkLeft m = true ∧ chkRight m = true ∧ chkInit m = true := by
  simp only [chkAll, Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1, hc.1.1.2, hc.1.2, hc.2⟩

theorem inv_adm (hI : Inv m n s) {q : Nat} (h1 : 1 ≤ q) (h2 : q ≤ n + 3) :
    adm m (V n s (q - 1)) (V n s q) = true := by
  have := hI (q - 1) (by omega); rwa [show q - 1 + 1 = q by omega] at this

/-- **Closure**: the invariant is inductive, for every `n`. -/
theorem inv_step (hn : 1 ≤ n) (hc : chkAll m = true) (hI : Inv m n s) {y : Nat}
    (hy : enabled m n s y = true) : Inv m n (fire s y) := by
  have hyN := enabled_lt hy
  obtain ⟨-, -, -, -, hp1, hp2⟩ := loc (m := m) (s := s) hn hyN
  rw [enabled_loc hn hyN] at hy
  obtain ⟨m1, m2, -, -⟩ := chkMid_spec (chkAll_parts hc).1 (V_dom hn)
    (inv_adm hI hp1 (by omega)) (hI _ hp2) (typ_lt y) hy
  intro q hq
  rw [V_fire hn hyN q, V_fire hn hyN (q + 1)]
  by_cases e1 : q = posOf n y
  · rw [ifP e1, ifN (by omega)]; subst e1; exact m2
  · by_cases e2 : q + 1 = posOf n y
    · rw [ifN e1, ifP e2, e2]
      have : q = posOf n y - 1 := by omega
      rw [this]; exact m1
    · rw [ifN e1, ifN e2]; exact hI q hq

/-- **Persistence**: firing an enabled node never withdraws the excitation, nor
the rt-enabledness, of any other node. -/
theorem persist_glob (hn : 1 ≤ n) (hc : chkAll m = true) (hI : Inv m n s) {x y : Nat}
    (hy : enabled m n s y = true) (hx : x < numNodes n) (hxy : x ≠ y) :
    (excited m n s x = true → excited m n (fire s y) x = true) ∧
    (enabled m n s x = true → enabled m n (fire s y) x = true) := by
  have hyN := enabled_lt hy
  obtain ⟨-, -, -, -, hp1, hp2⟩ := loc (m := m) (s := s) hn hyN
  obtain ⟨-, -, -, hvx, hx1, hx2⟩ := loc (m := m) (s := s) hn hx
  rw [enabled_loc hn hyN] at hy
  have hcs := chkAll_parts hc
  rw [excited_loc hn hx, excited_loc hn hx, enabled_loc hn hx, enabled_loc hn hx,
    V_fire hn hyN (posOf n x - 1), V_fire hn hyN (posOf n x), V_fire hn hyN (posOf n x + 1)]
  generalize hp : posOf n y = p at *
  generalize hq : posOf n x = q at *
  by_cases e0 : q = p
  · subst e0
    have ht : typOf x ≠ typOf y := fun e => hxy (pos_typ_inj hx hyN (hq.trans hp.symm) e)
    rw [ifN (by omega), ifP rfl, ifN (by omega)]
    obtain ⟨-, -, -, h4⟩ := chkMid_spec hcs.1 (V_dom hn) (inv_adm hI hp1 (by omega)) (hI _ hp2)
      (typ_lt y) hy
    have := h4 _ (typ_lt x) ht hvx
    simp only [persist, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at this
    obtain ⟨h1, h2⟩ := this
    refine ⟨fun e => ?_, fun e => ?_⟩
    · rcases h1 with h1 | h1
      · rw [e] at h1; cases h1
      · exact h1
    · rcases h2 with h2 | h2
      · rw [e] at h2; cases h2
      · exact h2
  by_cases e1 : q + 1 = p
  · rw [ifN (by omega), ifN (by omega), ifP e1, e1]
    subst e1
    exact chkLeft_spec hcs.2.1 (V_dom hn) (inv_adm hI hx1 (by omega)) (hI _ (by omega))
      (hI _ hp2) (typ_lt y) hy (typ_lt x) hvx
  by_cases e2 : q = p + 1
  · rw [ifP (by omega), ifN (by omega), ifN (by omega)]
    subst e2
    rw [show p + 1 - 1 = p by omega]
    exact chkRight_spec hcs.2.2.1 (V_dom hn) (inv_adm hI hp1 (by omega)) (hI _ hp2)
      (hI _ hx2) (typ_lt y) hy (typ_lt x) hvx
  · rw [ifN (by omega), ifN (by omega), ifN (by omega)]
    exact ⟨id, id⟩

end Main


/-! ## The pair (follow) rules, locally -/

section Pairs
variable {m : Mode} {n s : Nat}

theorem V_two (hn : 1 ≤ n) :
    V n s 2 = enc4 (get s (c 0)) (get s (b 0)) (get s (w 0)) (get s (f 0)) := V_st (k := 0) hn

theorem pairs_loc (hn : 1 ≤ n) {X Y : Nat} (hp : (X, Y) ∈ pairs n) :
    X < numNodes n ∧ Y < numNodes n ∧
    ((posOf n Y = posOf n X ∧ lpair (V n s (posOf n X)) (V n s (posOf n X)) true (typOf X) (typOf Y) = true) ∨
     (posOf n Y = posOf n X + 1 ∧
       lpair (V n s (posOf n X)) (V n s (posOf n Y)) false (typOf X) (typOf Y) = true)) := by
  simp only [pairs, List.mem_append, List.mem_flatMap, List.mem_filter, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq, decide_eq_true_eq] at hp
  have hN : ∀ k, k < n → c k < numNodes n ∧ b k < numNodes n ∧ w k < numNodes n ∧ f k < numNodes n := by
    intro k hk; unfold c b w f numNodes; omega
  have hs : src < numNodes n := by unfold src numNodes; omega
  have hk : snk < numNodes n := by unfold snk numNodes; omega
  rcases hp with ((⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) |
      ⟨k, hk', (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩) | ⟨k, ⟨hk', hk1⟩, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩
  · refine ⟨hs, (hN 0 hn).1, Or.inr ⟨by simp, ?_⟩⟩
    simp [V_one, V_two hn, lpair]
  · refine ⟨hs, (hN 0 hn).2.2.1, Or.inr ⟨by simp, ?_⟩⟩
    simp [V_one, V_two hn, lpair]
  · refine ⟨(hN (n - 1) (by omega)).1, hk, Or.inr ⟨by simp; omega, ?_⟩⟩
    simp [V_st (show n - 1 < n by omega), V_snk hn, lpair]
  · refine ⟨(hN (n - 1) (by omega)).2.1, hk, Or.inr ⟨by simp; omega, ?_⟩⟩
    simp [V_st (show n - 1 < n by omega), V_snk hn, lpair]
  · refine ⟨(hN k hk').1, (hN k hk').2.1, Or.inl ⟨by simp, ?_⟩⟩
    simp [V_st hk', lpair]
  · refine ⟨(hN k hk').1, (hN k hk').2.2.1, Or.inl ⟨by simp, ?_⟩⟩
    simp [V_st hk', lpair]
  · refine ⟨(hN (k - 1) (by omega)).1, (hN k hk').1, Or.inr ⟨by simp; omega, ?_⟩⟩
    simp [V_st hk', V_st (show k - 1 < n by omega), lpair]
  · refine ⟨(hN (k - 1) (by omega)).2.1, (hN k hk').1, Or.inr ⟨by simp; omega, ?_⟩⟩
    simp [V_st hk', V_st (show k - 1 < n by omega), lpair]
  · refine ⟨(hN (k - 1) (by omega)).2.1, (hN k hk').2.2.1, Or.inr ⟨by simp; omega, ?_⟩⟩
    simp [V_st hk', V_st (show k - 1 < n by omega), lpair]

end Pairs


section Good
variable {m : Mode} {n s : Nat}

theorem followL_spec {a b c t : Nat} (h : followL a b c t = true) {u : Nat} (hu : u < 4) :
    (lpair b b true t u = true → bt b t = bt b u) ∧
    (lpair b c false t u = true → bt b t = bt c u) ∧
    (lpair b b true u t = true → bt b t ≠ bt b u) ∧
    (lpair a b false u t = true → bt b t ≠ bt a u) := by
  unfold followL at h
  simp only [List.all_eq_true] at h
  have := h u (mem_types hu)
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq, bne_iff_ne,
    ne_eq] at this
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rcases h1 with h1 | h1
    · rw [e] at h1; cases h1
    · exact h1
  · rcases h2 with h2 | h2
    · rw [e] at h2; cases h2
    · exact h2
  · rcases h3 with h3 | h3
    · rw [e] at h3; cases h3
    · exact h3
  · rcases h4 with h4 | h4
    · rw [e] at h4; cases h4
    · exact h4

theorem follow_glob (hn : 1 ≤ n) (hc : chkAll m = true) (hI : Inv m n s) {y : Nat}
    (hy : enabled m n s y = true) : ∀ p ∈ pairs n, pairOk s y p = true := by
  intro ⟨X, Y⟩ hp
  obtain ⟨hX, hY, hpos⟩ := pairs_loc (s := s) hn hp
  have hyN := enabled_lt hy
  obtain ⟨-, -, -, -, hp1, hp2⟩ := loc (m := m) (s := s) hn hyN
  rw [enabled_loc hn hyN] at hy
  obtain ⟨-, -, hfl, -⟩ := chkMid_spec (chkAll_parts hc).1 (V_dom hn)
    (inv_adm hI hp1 (by omega)) (hI _ hp2) (typ_lt y) hy
  have gX := (loc (m := m) (s := s) hn hX).1
  have gY := (loc (m := m) (s := s) hn hY).1
  have hXY : X ≠ Y := by
    rintro rfl
    rcases hpos with ⟨-, hl⟩ | ⟨e, -⟩
    · simp [lpair] at hl; omega
    · omega
  unfold pairOk
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, beq_iff_eq, ne_eq]
  constructor
  · by_cases hyX : y = X
    · right; subst hyX
      rw [gX, gY]
      rcases hpos with ⟨e, hl⟩ | ⟨e, hl⟩
      · rw [e]; rw [e] at gY
        exact (followL_spec hfl (typ_lt Y)).1 hl
      · rw [e]; exact (followL_spec hfl (typ_lt Y)).2.1 (e ▸ hl)
    · left; exact hyX
  · by_cases hyY : y = Y
    · right; subst hyY
      rw [gX, gY]
      rcases hpos with ⟨e, hl⟩ | ⟨e, hl⟩
      · rw [← e]; rw [← e] at hl
        exact (followL_spec hfl (typ_lt X)).2.2.1 hl
      · have e' : posOf n y - 1 = posOf n X := by omega
        rw [e'] at hfl
        exact (followL_spec hfl (typ_lt X)).2.2.2 hl
    · left; exact hyY

theorem good_of_inv (hn : 1 ≤ n) (hc : chkAll m = true) (hI : Inv m n s) : Good m n s :=
  ⟨fun x _ hx hxy hy he => (persist_glob hn hc hI hy hx hxy).1 he,
   fun _ hy => follow_glob hn hc hI hy⟩

theorem V_init (q : Nat) :
    V n 0 q = if q = 0 then 48 else if q = 1 then 16 else if q ≤ n + 1 then 0
      else if q = n + 2 then 32 else 48 := by
  unfold V
  simp only [Muller.get, Nat.zero_testBit, Bool.toNat_false, Nat.add_zero]
  by_cases h0 : q = 0
  · subst h0; simp
  by_cases h1 : q = 1
  · subst h1; simp
  by_cases h2 : q ≤ n + 1
  · rw [ifN h1, ifN (by omega), ifP ⟨by omega, h2⟩, ifN h0, ifN h1, ifP h2]; rfl
  by_cases h3 : q = n + 2
  · rw [ifN h1, ifP h3, ifN h0, ifN h1, ifN h2, ifP h3]
  · rw [ifN h1, ifN h3, ifN (by omega), ifN h0, ifN h1, ifN h2, ifN h3]

theorem inv_init (hn : 1 ≤ n) (hc : chkAll m = true) : Inv m n 0 := by
  have h := (chkAll_parts hc).2.2.2
  simp only [chkInit, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  intro q hq
  rw [V_init, V_init]
  by_cases e0 : q = 0
  · subst e0; simpa using h1
  by_cases e1 : q = 1
  · subst e1; simp; rw [ifP (by omega)]; exact h2
  by_cases e2 : q + 1 ≤ n + 1
  · rw [ifN e0, ifN e1, ifP (by omega), ifN (by omega), ifN (by omega), ifP e2]; exact h3
  by_cases e3 : q = n + 1
  · rw [ifN e0, ifN e1, ifP (by omega), ifN (by omega), ifN (by omega), ifN e2, ifP (by omega)]
    exact h4
  · rw [ifN e0, ifN e1, ifN (by omega), ifP (by omega), ifN (by omega), ifN (by omega),
      ifN (by omega), ifN (by omega)]
    exact h5

theorem reach_inv (hn : 1 ≤ n) (hc : chkAll m = true) {s : Nat} (hs : Reach m n s) : Inv m n s := by
  induction hs with
  | init => exact inv_init hn hc
  | step _ hst ih =>
    obtain ⟨y, hy, rfl⟩ := hst
    exact inv_step hn hc ih hy

/-- Generic: for every `n ≥ 1`, every reachable state is `Good`. -/
theorem good_all (hn : 1 ≤ n) (hc : chkAll m = true) : ∀ s, Reach m n s → Good m n s :=
  fun _ hs => good_of_inv hn hc (reach_inv hn hc hs)

end Good

theorem chkAll_iso : chkAll .iso = true := by decide +kernel
theorem chkAll_rt : chkAll .rt = true := by decide +kernel


/-! ## Results for every `n` -/

section Results
variable {n : Nat}

/-- **Isochronic feedback, every `n ≥ 1`**: every reachable state of the real
`bd_link` chain is hazard-free (no excitation of any LUT, wire or environment
node is ever withdrawn) and obeys every pair rule. -/
theorem iso_good (hn : 1 ≤ n) : ∀ s, Reach .iso n s → Good .iso n s := good_all hn chkAll_iso

/-- **Free feedback wire + H_FB_BEFORE_INPUT, every `n ≥ 1`.** -/
theorem rt_good (hn : 1 ≤ n) : ∀ s, Reach .rt n s → Good .rt n s := good_all hn chkAll_rt

theorem iso_hazard_free (hn : 1 ≤ n) {s : Nat} (hs : Reach .iso n s) : HazardFree .iso n s :=
  (iso_good hn s hs).1
theorem rt_hazard_free (hn : 1 ≤ n) {s : Nat} (hs : Reach .rt n s) : HazardFree .rt n s :=
  (rt_good hn s hs).1

/-- Four-phase protocol on every link of the `n`-stage chain, every execution. -/
theorem iso_protocol (hn : 1 ≤ n) {σ} (hr : Run .iso n σ) {X Y : Nat} (hp : (X, Y) ∈ pairs n) :
    Handshake.Protocol (chanOf σ X Y) := run_protocol (iso_good hn) hr hp
theorem rt_protocol (hn : 1 ≤ n) {σ} (hr : Run .rt n σ) {X Y : Nat} (hp : (X, Y) ∈ pairs n) :
    Handshake.Protocol (chanOf σ X Y) := run_protocol (rt_good hn) hr hp

/-- Token order between consecutive stages, every execution, every `n`. -/
theorem iso_token_order {σ} (hr : Run .iso n σ) {k : Nat} (hk1 : 1 ≤ k) (hkn : k < n) (t : Nat) :
    tog (nodeTrace σ (c k)) t ≤ tog (nodeTrace σ (c (k - 1))) t ∧
    tog (nodeTrace σ (c (k - 1))) t ≤ tog (nodeTrace σ (c k)) t + 1 :=
  run_token_order (iso_good (by omega)) hr hk1 hkn t
theorem rt_token_order {σ} (hr : Run .rt n σ) {k : Nat} (hk1 : 1 ≤ k) (hkn : k < n) (t : Nat) :
    tog (nodeTrace σ (c k)) t ≤ tog (nodeTrace σ (c (k - 1))) t ∧
    tog (nodeTrace σ (c (k - 1))) t ≤ tog (nodeTrace σ (c k)) t + 1 :=
  run_token_order (rt_good (by omega)) hr hk1 hkn t

/-- Enabledness persistence in the rt semantics, every `n` (8g's (EP)). -/
theorem rt_ep (hn : 1 ≤ n) {s : Nat} (hs : Reach .rt n s) : MullerTimed.EP n s :=
  fun i j hij hi hj => (persist_glob hn chkAll_rt (reach_inv hn chkAll_rt hs) hj (enabled_lt hi) hij).2 hi

end Results

end Formal.Net.MullerAll
