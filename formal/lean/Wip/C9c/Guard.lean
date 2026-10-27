import Wip.C9c.Main
import Wip.C9c.GuardL

namespace Formal.Net.MullerAll
open Formal.Net Formal.Net.Muller Formal.Net.MullerTimed

/-! ## Local guard check, read as propositions -/

theorem lguard_spec {ws : List Nat} {zs : List (Nat × Nat × Bool)} {offs : List Nat}
    (h : lguardOk ws zs offs = true) :
    (wen ws 2 0 = true → (∀ z ∈ zs, wexc ws z.1 z.2.1 = false) ∧ llevel (wfire ws 2 0) zs = 0) ∧
    (linfl ws = true → ∀ off ∈ offs, ∀ t, t < 4 → valid (wv ws off) t = true → wen ws off t = true →
      linfl (wfire ws off t) = true →
      llevel (wfire ws off t) zs = llevel ws zs ∨
      (llevel (wfire ws off t) zs = llevel ws zs + 1 ∧
        (zs[llevel ws zs]?).map (fun z => (z.1, z.2.1)) = some (off, t))) ∧
    (linfl ws = true → ∀ j z, zs[j]? = some z → wexc ws z.1 z.2.1 = true → j ≤ llevel ws zs) := by
  unfold lguardOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hA, hB⟩ := h
  refine ⟨fun he => ?_, fun hi off hoff t ht hv he hi' => ?_, fun hi j z hz he => ?_⟩
  · simp only [he, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at hA
    exact hA
  · simp only [hi, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hB
    have := hB.1 off hoff t (mem_types ht)
    simp only [hv, he, hi', Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
      beq_iff_eq] at this
    exact this
  · simp only [hi, Bool.not_true, Bool.false_or, Bool.and_eq_true, List.all_eq_true] at hB
    have hj : j < zs.length := by
      apply Classical.byContradiction; intro hj
      rw [List.getElem?_eq_none (by omega)] at hz; cases hz
    have := hB.2 j (List.mem_range.2 hj)
    simp only [hz, he, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact this


/-! ## Windows and the loop lists, related to the global ones -/

def RelP (n Q : Nat) (offs : List Nat) (z : Nat × Bool) (l : Nat × Nat × Bool) : Prop :=
  z.1 < numNodes n ∧ posOf n z.1 = Q - 2 + l.1 ∧ typOf z.1 = l.2.1 ∧ z.2 = l.2.2 ∧ l.1 ∈ offs

def Rel (n Q : Nat) (offs : List Nat) : List (Nat × Bool) → List (Nat × Nat × Bool) → Prop
  | [], [] => True
  | z :: zs, l :: ls => RelP n Q offs z l ∧ Rel n Q offs zs ls
  | _, _ => False

theorem rel_get {n Q : Nat} {offs : List Nat} : ∀ {zs : List (Nat × Bool)} {ls : List (Nat × Nat × Bool)},
    Rel n Q offs zs ls → ∀ j : Nat,
    (∀ z, zs[j]? = some z → ∃ l, ls[j]? = some l ∧ RelP n Q offs z l) ∧
    (∀ l, ls[j]? = some l → ∃ z, zs[j]? = some z ∧ RelP n Q offs z l)
  | [], [], _, j => by simp
  | z :: zs, l :: ls, h, j => by
    obtain ⟨h1, h2⟩ := h
    cases j with
    | zero => exact ⟨fun z' hz => ⟨l, rfl, by simp at hz; exact hz ▸ h1⟩,
                     fun l' hl => ⟨z, rfl, by simp at hl; exact hl ▸ h1⟩⟩
    | succ j => simpa using rel_get h2 j
  | [], _ :: _, h, _ => h.elim
  | _ :: _, [], h, _ => h.elim

theorem rel_mem {n Q : Nat} {offs : List Nat} {zs : List (Nat × Bool)} {ls : List (Nat × Nat × Bool)}
    (hR : Rel n Q offs zs ls) {z : Nat × Bool} (hz : z ∈ zs) : ∃ l ∈ ls, RelP n Q offs z l := by
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.1 hz
  obtain ⟨l, hl1, hl⟩ := (rel_get hR j).1 z hj
  exact ⟨l, List.mem_of_getElem? hl1, hl⟩

/-- A window of positions around stage `k` (`Q = k + 2`): its real entries are
the positions' values, and firing a node at a moving offset is a local flip. -/
structure WinOK (n Q : Nat) (ws : Nat → List Nat) (offs : List Nat) : Prop where
  real : ∀ s i, (i ∈ offs ∨ i + 1 ∈ offs ∨ (1 ≤ i ∧ i - 1 ∈ offs)) → wv (ws s) i = V n s (Q - 2 + i)
  fire : ∀ s y, y < numNodes n → Q - 2 ≤ posOf n y → posOf n y - (Q - 2) ∈ offs →
    ws (fire s y) = wfire (ws s) (posOf n y - (Q - 2)) (typOf y)
  two : 2 ∈ offs
  pos : ∀ o ∈ offs, 1 ≤ o
  Q2 : 2 ≤ Q

section Win
variable {n Q : Nat} {ws : Nat → List Nat} {offs : List Nat}

theorem win_get (hn : 1 ≤ n) (hW : WinOK n Q ws offs) (s : Nat) {z : Nat × Bool} {l : Nat × Nat × Bool}
    (h : RelP n Q offs z l) : get s z.1 = bt (wv (ws s) l.1) l.2.1 := by
  obtain ⟨h1, h2, h3, -, h5⟩ := h
  rw [(loc (m := .rt) (s := s) hn h1).1, h2, h3, hW.real s _ (Or.inl h5)]

theorem win_ck (hn : 1 ≤ n) (hW : WinOK n Q ws offs) {k : Nat} (hk : k < n) (hQ : Q = k + 2)
    (s : Nat) : get s (c k) = bt (wv (ws s) 2) 0 ∧ get s (f k) = bt (wv (ws s) 2) 3 := by
  rw [hW.real s 2 (Or.inl hW.two), show Q - 2 + 2 = k + 2 by omega, V_st hk]; simp

theorem win_level (hn : 1 ≤ n) (hW : WinOK n Q ws offs) {k : Nat} (hk : k < n) (hQ : Q = k + 2)
    (s : Nat) : ∀ {zs : List (Nat × Bool)} {ls : List (Nat × Nat × Bool)}, Rel n Q offs zs ls →
    level s k zs = llevel (ws s) ls
  | [], [], _ => rfl
  | z :: zs, l :: ls, h => by
    obtain ⟨h1, h2⟩ := h
    simp only [level, llevel, isDone, ldone, win_get hn hW s h1, (win_ck hn hW hk hQ s).1, h1.2.2.2.1,
      win_level hn hW hk hQ s h2]
    rfl
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem win_infl (hn : 1 ≤ n) (hW : WinOK n Q ws offs) {k : Nat} (hk : k < n) (hQ : Q = k + 2)
    (s : Nat) : inflight s k = linfl (ws s) := by
  simp [inflight, linfl, (win_ck hn hW hk hQ s).1, (win_ck hn hW hk hQ s).2]

theorem win_nbr (hW : WinOK n Q ws offs) (s : Nat) {o : Nat} (ho : o ∈ offs) :
    wv (ws s) (o - 1) = V n s (Q - 2 + o - 1) ∧ wv (ws s) o = V n s (Q - 2 + o) ∧
    wv (ws s) (o + 1) = V n s (Q - 2 + o + 1) := by
  have h1 := hW.pos o ho
  refine ⟨?_, hW.real s o (Or.inl ho), ?_⟩
  · rw [hW.real s (o - 1) (Or.inr (Or.inl (by rw [show o - 1 + 1 = o by omega]; exact ho)))]
    congr 1; omega
  · rw [hW.real s (o + 1) (Or.inr (Or.inr ⟨by omega, by simpa using ho⟩))]
    rfl

theorem win_exc (hn : 1 ≤ n) (hW : WinOK n Q ws offs) (s : Nat) {z : Nat × Bool} {l : Nat × Nat × Bool}
    (h : RelP n Q offs z l) : excited .rt n s z.1 = wexc (ws s) l.1 l.2.1 := by
  obtain ⟨h1, h2, h3, -, h5⟩ := h
  obtain ⟨e1, e2, e3⟩ := win_nbr hW s h5
  rw [excited_loc hn h1, h2, h3, wexc, e1, e2, e3]

theorem win_en (hn : 1 ≤ n) (hW : WinOK n Q ws offs) (s : Nat) {y o : Nat} (hy : y < numNodes n)
    (hp : posOf n y = Q - 2 + o) (ho : o ∈ offs) : enabled .rt n s y = wen (ws s) o (typOf y) := by
  obtain ⟨e1, e2, e3⟩ := win_nbr hW s ho
  rw [enabled_loc hn hy, hp, wen, e1, e2, e3]

end Win


section GG
variable {n Q : Nat} {ws : Nat → List Nat} {offs : List Nat}

/-- **Gluing lemma for the loop certificate**: the local window check implies
8g's per-state guard check `guardOkB`, for every `n`. -/
theorem guard_glob (hn : 1 ≤ n) (hW : WinOK n Q ws offs) {k : Nat} (hk : k < n) (hQ : Q = k + 2)
    {zs : List (Nat × Bool)} {ls : List (Nat × Nat × Bool)} (hR : Rel n Q offs zs ls) {s : Nat}
    (hloc : lguardOk (ws s) ls offs = true) : guardOkB n s (k, zs) = true := by
  obtain ⟨hE, hM, hX⟩ := lguard_spec hloc
  have hcN : c k < numNodes n := by unfold c numNodes; omega
  have hcp : posOf n (c k) = Q - 2 + 2 := by simp; omega
  have hcp1 : Q - 2 ≤ posOf n (c k) := by simp; omega
  have hcp2 : posOf n (c k) - (Q - 2) = 2 := by simp; omega
  unfold guardOkB
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true, beq_iff_eq]
  refine ⟨?_, ?_⟩
  · by_cases hen : enabled .rt n s (c k) = true
    · right
      rw [win_en hn hW s hcN hcp hW.two, typ_c] at hen
      obtain ⟨h1, h2⟩ := hE hen
      refine ⟨fun z hz => ?_, ?_⟩
      · obtain ⟨l, hlm, hl⟩ := rel_mem hR hz
        rw [win_exc hn hW s hl]
        exact h1 l hlm
      · rw [win_level hn hW hk hQ _ hR, hW.fire s _ hcN hcp1 (by rw [hcp2]; exact hW.two), hcp2, typ_c]; exact h2
    · left; simpa using hen
  · by_cases hinf : inflight s k = true
    · right
      have hinfL : linfl (ws s) = true := by rw [← win_infl hn hW hk hQ]; exact hinf
      refine ⟨fun y hy => ?_, fun j hj => ?_⟩
      · have hyN : y < numNodes n := List.mem_range.1 hy
        by_cases hen : enabled .rt n s y = true
        · by_cases hpos : Q - 2 ≤ posOf n y ∧ posOf n y - (Q - 2) ∈ offs
          · obtain ⟨hp1, hp2⟩ := hpos
            have hpo : posOf n y = Q - 2 + (posOf n y - (Q - 2)) := by omega
            have hen' := hen
            rw [win_en hn hW s hyN hpo hp2] at hen'
            have hvalid : valid (wv (ws s) (posOf n y - (Q - 2))) (typOf y) = true := by
              rw [hW.real s _ (Or.inl hp2), ← hpo]; exact (loc (m := .rt) (s := s) hn hyN).2.2.2.1
            rw [win_infl hn hW hk hQ, win_level hn hW hk hQ _ hR, win_level hn hW hk hQ _ hR,
              hW.fire s y hyN hp1 hp2]
            by_cases hinf' : linfl (wfire (ws s) (posOf n y - (Q - 2)) (typOf y)) = true
            · rcases hM hinfL _ hp2 (typOf y) (typ_lt y) hvalid hen' hinf' with h | ⟨h1, h2⟩
              · exact Or.inl (Or.inr h)
              · refine Or.inr ⟨h1, ?_⟩
                cases hl : ls[llevel (ws s) ls]? with
                | none => rw [hl] at h2; cases h2
                | some l =>
                  rw [hl] at h2
                  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h2
                  obtain ⟨z, hz, hzl⟩ := (rel_get hR _).2 l hl
                  rw [hz]
                  simp only [Option.map_some, Option.some.injEq]
                  exact pos_typ_inj hzl.1 hyN (by rw [hzl.2.1, h2.1]; omega) (by rw [hzl.2.2.1, h2.2])
            · exact Or.inl (Or.inl (Or.inr (by simpa using hinf')))
          · -- a node outside the moving window: the loop does not move
            have hne : ∀ z ∈ zs, get s z.1 = get (fire s y) z.1 := by
              intro z hz
              obtain ⟨l, -, hl⟩ := rel_mem hR hz
              have hzy : y ≠ z.1 := by
                rintro rfl
                apply hpos; rw [hl.2.1]
                refine ⟨by omega, ?_⟩
                rw [show Q - 2 + l.1 - (Q - 2) = l.1 by omega]; exact hl.2.2.2.2
              simp [get_fire, hzy]
            have hcy : y ≠ c k := by
              rintro rfl; apply hpos; exact ⟨hcp1, by rw [hcp2]; exact hW.two⟩
            have := level_congr (k := k) hne (by simp [get_fire, hcy])
            exact Or.inl (Or.inr this.symm)
        · exact Or.inl (Or.inl (Or.inl (by simpa using hen)))
      · have hjl : j < zs.length := List.mem_range.1 hj
        cases hz : zs[j]? with
        | none => rfl
        | some z =>
          simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq]
          obtain ⟨l, hl, hzl⟩ := (rel_get hR j).1 z hz
          by_cases he : excited .rt n s z.1 = true
          · right
            rw [win_level hn hW hk hQ s hR]
            rw [win_exc hn hW s hzl] at he
            exact hX hinfL j l hl he
          · left; simpa using he
    · left; simpa using hinf

end GG


/-! ## The two windows, the two loops -/

def wsP (n s Q : Nat) : List Nat := [V n s (Q - 2), V n s (Q - 1), V n s Q, V n s (Q + 1), 48]
def wsS (n s Q : Nat) : List Nat := [48, V n s (Q - 1), V n s Q, V n s (Q + 1), V n s (Q + 2)]

section Inst
variable {n Q k : Nat}

theorem winP (hn : 1 ≤ n) (hQ : 2 ≤ Q) : WinOK n Q (fun s => wsP n s Q) [1, 2] where
  real s i hi := by
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by simp at hi; omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [wsP, wv] <;> congr 1 <;> omega
  fire s y hy h1 h2 := by
    have : posOf n y = Q - 1 ∨ posOf n y = Q := by simp at h2; omega
    simp only [wsP, wfire, wv, V_fire hn hy]
    rcases this with h | h <;> rw [h] <;>
      simp [show Q - 1 - (Q - 2) = 1 by omega, show Q - (Q - 2) = 2 by omega, List.set] <;> omega
  two := by simp
  pos o ho := by simp at ho; omega
  Q2 := hQ

theorem winS (hn : 1 ≤ n) (hQ : 2 ≤ Q) : WinOK n Q (fun s => wsS n s Q) [2, 3] where
  real s i hi := by
    have : i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by simp at hi; omega
    rcases this with rfl | rfl | rfl | rfl <;> simp [wsS, wv] <;> congr 1 <;> omega
  fire s y hy h1 h2 := by
    have : posOf n y = Q ∨ posOf n y = Q + 1 := by simp at h2; omega
    simp only [wsS, wfire, wv, V_fire hn hy]
    rcases this with h | h <;> rw [h] <;>
      simp [show Q - (Q - 2) = 2 by omega, show Q + 1 - (Q - 2) = 3 by omega, List.set] <;> omega
  two := by simp
  pos o ho := by simp at ho; omega
  Q2 := hQ

theorem predG_eq (k : Nat) : predG k = (k, (predG k).2) := by
  unfold predG; split <;> simp_all

theorem succG_eq (n k : Nat) : succG n k = (k, (succG n k).2) := by
  unfold succG; split <;> simp_all

theorem isSrc_V (hk : k < n) (s : Nat) : isSrc (V n s (k + 1)) = decide (k = 0) := by
  cases k with
  | zero => simp [V_one]
  | succ j => rw [show j + 1 + 1 = j + 2 from rfl, V_st (by omega)]; simp

theorem isSnk_V (hn : 1 ≤ n) (hk : k < n) (s : Nat) : isSnk (V n s (k + 3)) = decide (k + 1 = n) := by
  by_cases h : k + 1 = n
  · rw [show k + 3 = n + 2 by omega, V_snk hn]; simp [h]
  · rw [show k + 3 = (k + 1) + 2 by omega, V_st (by omega)]; simp [h]

theorem rel_pred (hn : 1 ≤ n) {k : Nat} (hk : k < n) (s : Nat) :
    Rel n (k + 2) [1, 2] (predG k).2 (predL (wsP n s (k + 2))) := by
  have hN : ∀ j, j < n → c j < numNodes n ∧ b j < numNodes n ∧ w j < numNodes n ∧ f j < numNodes n := by
    intro j hj; unfold c b w f numNodes; omega
  have hs : src < numNodes n := by unfold src numNodes; omega
  have hw : wv (wsP n s (k + 2)) 1 = V n s (k + 1) := by simp [wsP, wv]
  unfold predL predG
  rw [hw, isSrc_V hk]
  by_cases h0 : k = 0
  · subst h0
    simp [Rel, RelP, (hN 0 hn).2.2.1, hs]
  · have h1 := hN (k - 1) (by omega)
    simp [h0, Rel, RelP, (hN k hk).2.2.1, h1.1, h1.2.1]
    omega

theorem rel_succ (hn : 1 ≤ n) {k : Nat} (hk : k < n) (s : Nat) :
    Rel n (k + 2) [2, 3] (succG n k).2 (succL (wsS n s (k + 2))) := by
  have hN : ∀ j, j < n → c j < numNodes n ∧ b j < numNodes n ∧ w j < numNodes n ∧ f j < numNodes n := by
    intro j hj; unfold c b w f numNodes; omega
  have hs : snk < numNodes n := by unfold snk numNodes; omega
  have hw : wv (wsS n s (k + 2)) 3 = V n s (k + 3) := by simp [wsS, wv]
  unfold succL succG
  rw [hw, isSnk_V hn hk]
  by_cases h0 : k + 1 = n
  · simp [h0, Rel, RelP, (hN k hk).2.1, hs]
  · have h1 := hN (k + 1) (by omega)
    simp [h0, Rel, RelP, (hN k hk).2.1, h1.1, h1.2.2.1]

end Inst

theorem chkPredW_0 : chkPredW 0 = true := by decide +kernel
theorem chkPredW_1 : chkPredW 1 = true := by decide +kernel
theorem chkPredW_2 : chkPredW 2 = true := by decide +kernel
theorem chkPredW_3 : chkPredW 3 = true := by decide +kernel
theorem chkPredW_4 : chkPredW 4 = true := by decide +kernel
theorem chkPredW_5 : chkPredW 5 = true := by decide +kernel
theorem chkPredW_6 : chkPredW 6 = true := by decide +kernel
theorem chkPredW_7 : chkPredW 7 = true := by decide +kernel
theorem chkPredW_8 : chkPredW 8 = true := by decide +kernel
theorem chkPredW_9 : chkPredW 9 = true := by decide +kernel
theorem chkPredW_10 : chkPredW 10 = true := by decide +kernel
theorem chkPredW_11 : chkPredW 11 = true := by decide +kernel
theorem chkPredW_12 : chkPredW 12 = true := by decide +kernel
theorem chkPredW_13 : chkPredW 13 = true := by decide +kernel
theorem chkPredW_14 : chkPredW 14 = true := by decide +kernel
theorem chkPredW_15 : chkPredW 15 = true := by decide +kernel
theorem chkPredW_all : ∀ v, v < 16 → chkPredW v = true
  | 0, _ => chkPredW_0
  | 1, _ => chkPredW_1
  | 2, _ => chkPredW_2
  | 3, _ => chkPredW_3
  | 4, _ => chkPredW_4
  | 5, _ => chkPredW_5
  | 6, _ => chkPredW_6
  | 7, _ => chkPredW_7
  | 8, _ => chkPredW_8
  | 9, _ => chkPredW_9
  | 10, _ => chkPredW_10
  | 11, _ => chkPredW_11
  | 12, _ => chkPredW_12
  | 13, _ => chkPredW_13
  | 14, _ => chkPredW_14
  | 15, _ => chkPredW_15
  | _ + 16, h => absurd h (by omega)
theorem chkSuccW_0 : chkSuccW 0 = true := by decide +kernel
theorem chkSuccW_1 : chkSuccW 1 = true := by decide +kernel
theorem chkSuccW_2 : chkSuccW 2 = true := by decide +kernel
theorem chkSuccW_3 : chkSuccW 3 = true := by decide +kernel
theorem chkSuccW_4 : chkSuccW 4 = true := by decide +kernel
theorem chkSuccW_5 : chkSuccW 5 = true := by decide +kernel
theorem chkSuccW_6 : chkSuccW 6 = true := by decide +kernel
theorem chkSuccW_7 : chkSuccW 7 = true := by decide +kernel
theorem chkSuccW_8 : chkSuccW 8 = true := by decide +kernel
theorem chkSuccW_9 : chkSuccW 9 = true := by decide +kernel
theorem chkSuccW_10 : chkSuccW 10 = true := by decide +kernel
theorem chkSuccW_11 : chkSuccW 11 = true := by decide +kernel
theorem chkSuccW_12 : chkSuccW 12 = true := by decide +kernel
theorem chkSuccW_13 : chkSuccW 13 = true := by decide +kernel
theorem chkSuccW_14 : chkSuccW 14 = true := by decide +kernel
theorem chkSuccW_15 : chkSuccW 15 = true := by decide +kernel
theorem chkSuccW_all : ∀ v, v < 16 → chkSuccW v = true
  | 0, _ => chkSuccW_0
  | 1, _ => chkSuccW_1
  | 2, _ => chkSuccW_2
  | 3, _ => chkSuccW_3
  | 4, _ => chkSuccW_4
  | 5, _ => chkSuccW_5
  | 6, _ => chkSuccW_6
  | 7, _ => chkSuccW_7
  | 8, _ => chkSuccW_8
  | 9, _ => chkSuccW_9
  | 10, _ => chkSuccW_10
  | 11, _ => chkSuccW_11
  | 12, _ => chkSuccW_12
  | 13, _ => chkSuccW_13
  | 14, _ => chkSuccW_14
  | 15, _ => chkSuccW_15
  | _ + 16, h => absurd h (by omega)

end Formal.Net.MullerAll
