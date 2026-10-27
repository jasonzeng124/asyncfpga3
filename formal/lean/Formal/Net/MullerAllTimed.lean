import Formal.Net.MullerAll
import Formal.Net.MullerTimed

/-!
# Probe 9c: the timed Muller chain for EVERY number of stages

## Problem statement (plain language)

Probe 8g (`MullerTimed.lean`) proved, generically in n, that if a certificate
`Cert n` holds (enabledness persistence in the rt semantics plus a per-state
"loop level" check `guardOkB` for the two feedback loops of every stage),
then every timed trace of the real chain whose delays satisfy `FbBound`
(H_FB_DELAY: the feedback route's max delay is below the min delay of each
neighbour loop) is a run of 8c's rt semantics; with 8c's `Good .rt n` this
gives the four-phase protocol, token order and no glitch in time. 8g closed
`Cert n` by kernel BFS for n <= 3 only.

**Here `Cert n` is proved for every n >= 1 (`cert_all`)**, and with
`MullerAll.rt_good` the timed corollaries hold for every n:
`timedAll_reach`, `timedAll_step_run`, `timedAll_protocol`,
`timedAll_token_order`, `timedAll_hazard_free`.

Assumptions: exactly 8g's (`Timed n lo hi x`: H_INERTIAL per node,
H_LUMP for the req path, H_ATOMIC_LUT, H_RESET_CLEAN, H_ENV; and `FbBound`),
plus `1 ≤ n`. Not covered: the equality case of `FbBound`, corner
correlation, the data path (see `formal/notes/C-8g-mullertimed.md`).

## Method

`guardOkB n s (k, loop)` only looks at nodes of positions `k+1 .. k+3` and their
neighbours. For each loop a 5-slot window of positions is used (`wsP`:
positions `Q-2 .. Q+1` for the pred loop, `wsS`: `Q-1 .. Q+2` for the succ loop,
`Q = k + 2`, the unused slot a constant sentinel), the loop is translated to
window offsets (`predL`, `succL`, related by `Rel`), and the window check
`lguardOk` is done once for every window allowed by `MullerAll.Inv`
(`chkPredW_v`, `chkSuccW_v`, one `decide +kernel` per value of the middle
stage, to keep each kernel run small). `guard_glob` is the gluing lemma.
-/

namespace Formal.Net.MullerAll
open Formal.Net Formal.Net.Muller Formal.Net.MullerTimed

/-! ## Five-position windows for the loop (guard) certificate of probe 8g -/

def wv (ws : List Nat) (i : Nat) : Nat := ws.getD i 48
def wexc (ws : List Nat) (off t : Nat) : Bool := lexc .rt (wv ws (off - 1)) (wv ws off) (wv ws (off + 1)) t
def wen (ws : List Nat) (off t : Nat) : Bool := lenabled .rt (wv ws (off - 1)) (wv ws off) (wv ws (off + 1)) t
def wfire (ws : List Nat) (off t : Nat) : List Nat := ws.set off (flip (wv ws off) t)

def ldone (ws : List Nat) (z : Nat × Nat × Bool) : Bool := (bt (wv ws z.1) z.2.1 == bt (wv ws 2) 0) == z.2.2

def llevel (ws : List Nat) : List (Nat × Nat × Bool) → Nat
  | [] => 0
  | z :: zs => if ldone ws z then llevel ws zs + 1 else 0

def linfl (ws : List Nat) : Bool := bt (wv ws 2) 3 != bt (wv ws 2) 0

def lguardOk (ws : List Nat) (zs : List (Nat × Nat × Bool)) (offs : List Nat) : Bool :=
  (!wen ws 2 0 || (zs.all (fun z => !wexc ws z.1 z.2.1) && llevel (wfire ws 2 0) zs == 0)) &&
  (!linfl ws ||
    ((offs.all fun off => types.all fun t => !valid (wv ws off) t || !wen ws off t ||
        !linfl (wfire ws off t) || llevel (wfire ws off t) zs == llevel ws zs ||
        (llevel (wfire ws off t) zs == llevel ws zs + 1 &&
          (zs[llevel ws zs]?).map (fun z => (z.1, z.2.1)) == some (off, t))) &&
     (List.range zs.length).all fun j => match zs[j]? with
        | some z => !wexc ws z.1 z.2.1 || decide (j ≤ llevel ws zs)
        | none => true))

def predL (ws : List Nat) : List (Nat × Nat × Bool) :=
  if isSrc (wv ws 1) then [(2, 2, true), (1, 0, false)] else [(2, 2, true), (1, 0, false), (1, 1, false)]
def succL (ws : List Nat) : List (Nat × Nat × Bool) :=
  if isSnk (wv ws 3) then [(2, 1, true), (3, 0, true)] else [(2, 1, true), (3, 0, true), (3, 2, true)]

/-- Pred-side loops: window `[Q-2, Q-1, Q, Q+1, -]`, the moving nodes at `Q-1, Q`. -/
def chkPredW (v2 : Nat) : Bool :=
  dom.all fun v0 => (adj .rt v0).all fun v1 => !(adj .rt v1).contains v2 ||
    (adj .rt v2).all fun v3 =>
      lguardOk [v0, v1, v2, v3, 48] (predL [v0, v1, v2, v3, 48]) [1, 2]

/-- Succ-side loops: window `[-, Q-1, Q, Q+1, Q+2]`, the moving nodes at `Q, Q+1`. -/
def chkSuccW (v2 : Nat) : Bool :=
  dom.all fun v1 => !(adj .rt v1).contains v2 ||
    (adj .rt v2).all fun v3 => (adj .rt v3).all fun v4 =>
      lguardOk [48, v1, v2, v3, v4] (succL [48, v1, v2, v3, v4]) [2, 3]

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

section Cert
variable {n : Nat}

theorem mem_guards {g : Nat × List (Nat × Bool)} :
    g ∈ guards n ↔ ∃ k, k < n ∧ (g = predG k ∨ g = succG n k) := by
  simp [guards, List.mem_flatMap, List.mem_range]

theorem wsP_eq (s k : Nat) : wsP n s (k + 2) = [V n s k, V n s (k + 1), V n s (k + 2), V n s (k + 3), 48] := by
  simp [wsP]
theorem wsS_eq (s k : Nat) :
    wsS n s (k + 2) = [48, V n s (k + 1), V n s (k + 2), V n s (k + 3), V n s (k + 4)] := by
  simp [wsS]

theorem guard_all (hn : 1 ≤ n) {s : Nat} (hs : Reach .rt n s) :
    ∀ g ∈ guards n, guardOkB n s g = true := by
  have hI := reach_inv hn chkAll_rt hs
  intro g hg
  obtain ⟨k, hk, rfl | rfl⟩ := mem_guards.1 hg
  · have hv : V n s (k + 2) < 16 := by rw [V_st hk]; exact enc4_lt ..
    have hc := chkPredW_all _ hv
    unfold chkPredW at hc
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
    have hl : lguardOk (wsP n s (k + 2)) (predL (wsP n s (k + 2))) [1, 2] = true := by
      rw [wsP_eq]
      have h1 := hc (V n s k) (V_dom hn) (V n s (k + 1)) (adm_mem.1 (hI k (by omega)))
      rcases h1 with h1 | h1
      · have := hI (k + 1) (by omega); simp only [adm] at this; rw [this] at h1; cases h1
      · exact h1 _ (adm_mem.1 (hI (k + 2) (by omega)))
    rw [predG_eq]
    exact guard_glob hn (winP hn (by omega)) hk rfl (rel_pred hn hk s) hl
  · have hv : V n s (k + 2) < 16 := by rw [V_st hk]; exact enc4_lt ..
    have hc := chkSuccW_all _ hv
    unfold chkSuccW at hc
    simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
    have hl : lguardOk (wsS n s (k + 2)) (succL (wsS n s (k + 2))) [2, 3] = true := by
      rw [wsS_eq]
      rcases hc (V n s (k + 1)) (V_dom hn) with h1 | h1
      · have := hI (k + 1) (by omega); simp only [adm] at this; rw [this] at h1; cases h1
      · exact h1 _ (adm_mem.1 (hI (k + 2) (by omega))) _ (adm_mem.1 (hI (k + 3) (by omega)))
    rw [succG_eq]
    exact guard_glob hn (winS hn (by omega)) hk rfl (rel_succ hn hk s) hl

theorem wf_all (hn : 1 ≤ n) : ∀ g ∈ guards n,
    g.1 < n ∧ g.2 ≠ [] ∧ ∀ z ∈ g.2, z.1 < numNodes n ∧ z.1 ≠ c g.1 := by
  intro g hg
  obtain ⟨k, hk, rfl | rfl⟩ := mem_guards.1 hg
  · unfold predG
    split
    · subst k; simp [numNodes, w, src, c]; omega
    · simp [numNodes, w, c, b]; omega
  · unfold succG
    split
    · simp [numNodes, b, snk, c]; omega
    · simp [numNodes, w, c, b]; omega

theorem cover_all (hn : 1 ≤ n) : ∀ i, i < numNodes n → ∀ k, readerStage n i = some k →
    ∃ g ∈ guards n, g.1 = k ∧ g.2.getLast?.map Prod.fst = some i := by
  intro i hi k hk
  rcases node_cases hi with rfl | rfl | ⟨j, hj, rfl | rfl | rfl | rfl⟩
  · rw [rs_src] at hk; cases hk
    exact ⟨predG 0, mem_guards.2 ⟨0, hn, Or.inl rfl⟩, by simp [predG], by simp [predG]⟩
  · rw [rs_snk] at hk; cases hk
    refine ⟨succG n (n - 1), mem_guards.2 ⟨n - 1, by omega, Or.inr rfl⟩, ?_, ?_⟩ <;>
      simp [succG, show n - 1 + 1 = n by omega]
  · rw [rs_c] at hk; cases hk
  · rw [rs_b] at hk
    split at hk
    · cases hk
      refine ⟨predG (j + 1), mem_guards.2 ⟨j + 1, by omega, Or.inl rfl⟩, ?_, ?_⟩ <;> simp [predG]
    · cases hk
  · rw [rs_w] at hk
    split at hk
    · cases hk
      refine ⟨succG n (j - 1), mem_guards.2 ⟨j - 1, by omega, Or.inr rfl⟩, ?_, ?_⟩ <;>
        simp [succG, show j - 1 + 1 = j by omega, show j ≠ n by omega]
    · cases hk
  · rw [rs_f] at hk; cases hk

/-- **8g's certificate, for every `n ≥ 1`** (replaces `checkT n = true`). -/
theorem cert_all (hn : 1 ≤ n) : Cert n where
  ep := fun _ hs => rt_ep hn hs
  guard := fun _ hs => guard_all hn hs
  wf := wf_all hn
  cover := cover_all hn

end Cert

/-! ## Timed corollaries for every `n` -/

section TimedAll
variable {n : Nat} {lo hi : Nat → Nat} {x : Nat → Nat}

/-- **H_FB_BEFORE_INPUT from delay bounds, every `n ≥ 1`.** Every state of a
timed trace (every LUT, route, feedback route, environment node an inertial
channel `[lo, hi]` after its real gate function; the feedback a free wire)
that satisfies `FbBound` is reachable in 8c's rt semantics. -/
theorem timedAll_reach (hn : 1 ≤ n) (hT : Timed n lo hi x) (hB : FbBound n lo hi) (t : Nat) :
    Reach .rt n (x t) := timed_reach hT (cert_all hn) hB.guards t

theorem timedAll_step_run (hn : 1 ≤ n) (hT : Timed n lo hi x) (hB : FbBound n lo hi) (t : Nat) :
    RunL n (x t) (chg n x t) ∧ finalL (x t) (chg n x t) = x (t + 1) :=
  timed_step_run hT (cert_all hn) hB.guards t

/-- Four-phase protocol on every link, every timed trace, every `n`. -/
theorem timedAll_protocol (hn : 1 ≤ n) (hT : Timed n lo hi x) (hB : FbBound n lo hi) {X Y : Nat}
    (hp : (X, Y) ∈ pairs n) :
    Handshake.Protocol ⟨fun t => get (x t) X, fun t => get (x t) Y, fun _ => 0⟩ :=
  timed_protocol hT (cert_all hn) hB.guards (rt_good hn) hp

/-- Token order between consecutive stages, every timed trace, every `n`. -/
theorem timedAll_token_order (hT : Timed n lo hi x) (hB : FbBound n lo hi) {k : Nat}
    (hk1 : 1 ≤ k) (hkn : k < n) (t : Nat) :
    tog (fun t => get (x t) (c k)) t ≤ tog (fun t => get (x t) (c (k - 1))) t ∧
    tog (fun t => get (x t) (c (k - 1))) t ≤ tog (fun t => get (x t) (c k)) t + 1 :=
  timed_token_order hT (cert_all (by omega)) hB.guards (rt_good (by omega)) hk1 hkn t

/-- No glitch on any LUT, wire or environment node, every timed trace, every `n`. -/
theorem timedAll_hazard_free (hn : 1 ≤ n) (hT : Timed n lo hi x) (hB : FbBound n lo hi) {t i : Nat}
    (hiN : i < numNodes n) (he : nextVal .free n (x t) i ≠ get (x t) i)
    (hs : get (x (t + 1)) i = get (x t) i) :
    nextVal .free n (x (t + 1)) i ≠ get (x (t + 1)) i :=
  timed_hazard_free hT (cert_all hn) hB.guards (rt_good hn) hiN he hs

end TimedAll

end Formal.Net.MullerAll
