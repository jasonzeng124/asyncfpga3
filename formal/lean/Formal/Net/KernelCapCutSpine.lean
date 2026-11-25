import Formal.Net.KernelCapSafe
import Formal.Net.CapstoneCutCells

/-!
# Kernel-parametric: the control spine and the token's walk (from C-8r's CapstoneCutSpine)
-/


namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open KD KP

set_option linter.unusedSectionVars false

set_option maxRecDepth 100000

variable [KD] [KP]

theorem noloop' (c : Fin NC) : prodOf c ≠ consOf c := noloop c

/-! ## The walk -/


theorem cnt_succ' (f : Nat → Bool) (t : Nat) : cnt f (t + 1) = cnt f t + bn (f t) := rfl

/-- The next spine channel after the `k`-th visit of `c`. -/
def nxt (σ : Fin NC → Nat → Nat) (c : Fin NC) (k : Nat) : Option (Fin NC) :=
  match opAt (consOf c) with
  | .link _ o => if sp o then some o else none
  | .forkG _ os => os.find? sp
  | .bjoin _ o _ _ => if sp o then some o else none
  | .steerC _ t f => if sp t then some (bif sel2 (σ c k) then t else f) else none
  | .amerge _ _ z _ => some z
  | _ => none

structure WS where
  cur : Option (Fin NC)
  W : Fin NC → Nat

def wstep (σ : Fin NC → Nat → Nat) (s : WS) : WS :=
  match s.cur with
  | none => s
  | some c => ⟨nxt σ c (s.W c), fun d => s.W d + if d = c then 1 else 0⟩

def walk (σ : Fin NC → Nat → Nat) : Nat → WS
  | 0 => ⟨some start, fun _ => 0⟩
  | p + 1 => wstep σ (walk σ p)

/-- **H_WALK**: arriving at an arbiter stage, the walk finds the oracle's next label naming
the input it arrives on (`true` = input `y`). -/
def WalkOK (σ : Fin NC → Nat → Nat) (om : Nat → Nat → Bool) : Prop :=
  ∀ p d x y z w, (walk σ p).cur = some d → opAt (consOf d) = .amerge x y z w →
    om w ((walk σ p).W z) = decide (d = y)

variable (σ : Fin NC → Nat → Nat)

def visB (c : Fin NC) (q : Nat) : Bool := (walk σ q).cur == some c

theorem W_succ (p : Nat) (c : Fin NC) : (walk σ (p + 1)).W c = (walk σ p).W c + bn (visB σ c p) := by
  show (wstep σ (walk σ p)).W c = _
  unfold wstep visB
  cases h : (walk σ p).cur with
  | none => simp [bn]
  | some d =>
    simp only [bn]
    by_cases hcd : c = d
    · subst hcd; simp
    · have : (some d == some c) = false := by simp [Ne.symm hcd]
      simp [hcd, this]

theorem cur_succ (p : Nat) : (walk σ (p + 1)).cur =
    ((walk σ p).cur).bind (fun d => nxt σ d ((walk σ p).W d)) := by
  show (wstep σ (walk σ p)).cur = _
  unfold wstep
  cases h : (walk σ p).cur <;> simp [h]

theorem W_eq : ∀ p c, (walk σ p).W c = cnt (visB σ c) p := by
  intro p
  induction p with
  | zero => intro c; rfl
  | succ p ih => intro c; rw [W_succ, ih, cnt_succ']

theorem nxt_sp {c c' : Fin NC} {k : Nat} (h : nxt σ c k = some c') : sp c' = true := by
  unfold nxt at h
  split at h
  · split at h <;> simp_all
  · have := List.find?_some h; simpa using this
  · split at h <;> simp_all
  · split at h
    · rename_i hc
      have hs := spok (consOf c)
      rename_i heq
      rw [heq] at hs
      simp only [SpOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hs
      cases hsel : sel2 (σ c k) <;> simp [hsel] at h <;> subst h
      · rw [hs.1.2, ← hs.1.1]; assumption
      · assumption
    · simp at h
  · have hs := spok (consOf c)
    rename_i heq
    rw [heq] at hs
    simp only [SpOK, Bool.and_eq_true, bne_iff_ne] at hs
    simp at h; subst h; exact hs.1.2
  · simp at h

theorem nxt_out {c c' : Fin NC} {k : Nat} (h : nxt σ c k = some c') : c' ∈ (opAt (consOf c)).outsC := by
  unfold nxt at h
  split at h
  · rename_i heq; split at h
    · simp at h; subst h; rw [heq]; simp [K.outsC]
    · simp at h
  · rename_i heq; rw [heq]; simp only [K.outsC]; exact List.mem_of_find?_eq_some h
  · rename_i heq; split at h
    · simp at h; subst h; rw [heq]; simp [K.outsC]
    · simp at h
  · rename_i heq; split at h
    · simp at h; subst h; rw [heq]; cases sel2 (σ c k) <;> simp [K.outsC]
    · simp at h
  · rename_i heq; simp at h; subst h; rw [heq]; simp [K.outsC]
  · simp at h

theorem nxt_prod {c c' : Fin NC} {k : Nat} (h : nxt σ c k = some c') : prodOf c' = consOf c :=
  prod_out _ _ (nxt_out σ h)

theorem nxt_ne {c c' : Fin NC} {k : Nat} (h : nxt σ c k = some c') : c' ≠ c := by
  intro e; subst e; exact noloop _ (nxt_prod σ h)

/-- A walk transition into `c'` comes from an input of `c'`'s producer. -/
theorem nxt_in {c c' : Fin NC} {k : Nat} (h : nxt σ c k = some c') : c ∈ (opAt (prodOf c')).insC := by
  rw [nxt_prod σ h]; exact cons_mem c

theorem cur_sp : ∀ p c, (walk σ p).cur = some c → sp c = true := by
  intro p
  induction p with
  | zero => intro c h; simp [walk] at h; subst h; exact sp_start
  | succ p ih =>
    intro c h
    rw [cur_succ] at h
    cases hc : (walk σ p).cur with
    | none => rw [hc] at h; simp at h
    | some d => rw [hc] at h; exact nxt_sp σ h

/-- Transitions of the walk into `c`. -/
def tr (c : Fin NC) (q : Nat) : Bool :=
  match (walk σ q).cur with
  | some d => nxt σ d ((walk σ q).W d) == some c
  | none => false

theorem tr_some {c d : Fin NC} {q : Nat} (h : (walk σ q).cur = some d) :
    tr σ c q = (nxt σ d ((walk σ q).W d) == some c) := by
  unfold tr; rw [h]

theorem tr_none {c : Fin NC} {q : Nat} (h : (walk σ q).cur = none) : tr σ c q = false := by
  unfold tr; rw [h]

theorem visB_some {c d : Fin NC} {q : Nat} (h : (walk σ q).cur = some d) :
    visB σ c q = (some d == some c) := by
  unfold visB; rw [h]

theorem visB_none {c : Fin NC} {q : Nat} (h : (walk σ q).cur = none) : visB σ c q = false := by
  unfold visB; rw [h]; rfl

theorem flow : ∀ p c, (walk σ p).W c + bn ((walk σ p).cur == some c) =
    cnt (tr σ c) p + bn (c == start) := by
  intro p
  induction p with
  | zero =>
    intro c
    show 0 + bn (some start == some c) = 0 + bn (c == start)
    by_cases h : c = start
    · subst h; simp
    · have h1 : (some start == some c) = false := by simp [Ne.symm h]
      have h2 : (c == start) = false := by simp [h]
      rw [h1, h2]
  | succ p ih =>
    intro c
    rw [W_succ, cur_succ, cnt_succ']
    have hc := ih c
    cases h : (walk σ p).cur with
    | none =>
      rw [h] at hc
      rw [visB_none σ h, tr_none σ h]
      simp only [Option.bind_none]
      simp only [bn] at hc ⊢; simp at hc ⊢; omega
    | some d =>
      rw [h] at hc
      rw [visB_some σ h, tr_some σ h]
      simp only [Option.bind_some]
      omega

/-- Reindexing: counting walk times that visit `j` with a property of the visit index. -/
theorem cnt_visit (j : Fin NC) (f : Nat → Bool) : ∀ p,
    cnt (fun q => visB σ j q && f ((walk σ q).W j)) p = cnt f ((walk σ p).W j) := by
  intro p
  induction p with
  | zero => rfl
  | succ p ih =>
    rw [cnt_succ', ih, W_succ]
    cases hv : visB σ j p
    · simp [bn]
    · simp only [Bool.true_and, bn, ite_true]; rw [cnt_succ']; rfl

theorem in_cp {c i : Fin NC} (hin : ∀ d k, sp d = true → (nxt σ d k = some c ↔ d = i)) :
    ∀ p, cnt (tr σ c) p = (walk σ p).W i := by
  intro p
  rw [W_eq]
  apply CM.cnt_congr_lt
  intro q _
  cases h : (walk σ q).cur with
  | none => rw [tr_none σ h, visB_none σ h]
  | some d =>
    rw [tr_some σ h, visB_some σ h]
    have hs := cur_sp σ q d h
    have := hin d ((walk σ q).W d) hs
    by_cases hdi : d = i
    · subst hdi; simp [this.2 rfl]
    · have h1 : (nxt σ d ((walk σ q).W d) == some c) = false := by
        cases hn : nxt σ d ((walk σ q).W d) == some c
        · rfl
        · exact absurd (this.1 (by simpa using hn)) hdi
      have h2 : (some d == some i) = false := by simp [hdi]
      rw [h1, h2]

theorem in_st {c j : Fin NC} {b : Bool}
    (hin : ∀ d k, sp d = true → (nxt σ d k = some c ↔ d = j ∧ sel2 (σ j k) = b)) :
    ∀ p, cnt (tr σ c) p = cnt (fun k => sel2 (σ j k) == b) ((walk σ p).W j) := by
  intro p
  rw [← cnt_visit]
  apply CM.cnt_congr_lt
  intro q _
  cases h : (walk σ q).cur with
  | none => rw [tr_none σ h, visB_none σ h]; rfl
  | some d =>
    rw [tr_some σ h, visB_some σ h]
    have hs := cur_sp σ q d h
    have := hin d ((walk σ q).W d) hs
    by_cases hdj : d = j
    · subst hdj
      cases hb : (sel2 (σ d ((walk σ q).W d)) == b)
      · have h1 : (nxt σ d ((walk σ q).W d) == some c) = false := by
          cases hn : nxt σ d ((walk σ q).W d) == some c
          · rfl
          · have := (this.1 (by simpa using hn)).2; simp [this] at hb
        rw [h1]; simp
      · have := this.2 ⟨rfl, by simpa using hb⟩
        simp [this]
    · have h1 : (nxt σ d ((walk σ q).W d) == some c) = false := by
        cases hn : nxt σ d ((walk σ q).W d) == some c
        · rfl
        · exact absurd (this.1 (by simpa using hn)).1 hdj
      have h2 : (some d == some j) = false := by simp [hdj]
      rw [h1, h2]; simp

/-- The arbiter's input counts along the walk, under H_WALK. -/
theorem am_side (ω : Nat → Bool) {x y z : Fin NC} (hxy : x ≠ y) (hzx : z ≠ x) (hzy : z ≠ y)
    (hzs : z ≠ start)
    (hin : ∀ d k, sp d = true → (nxt σ d k = some z ↔ d = x ∨ d = y))
    (hw : ∀ p d, (walk σ p).cur = some d → (d = x ∨ d = y) → ω ((walk σ p).W z) = decide (d = y)) :
    ∀ p, (walk σ p).W y = cnt ω ((walk σ p).W z) +
        bn (((walk σ p).cur == some z) && ω ((walk σ p).W z)) ∧
      (walk σ p).W x = cnt (fun i => !ω i) ((walk σ p).W z) +
        bn (((walk σ p).cur == some z) && !ω ((walk σ p).W z)) := by
  intro p
  induction p with
  | zero =>
    have : (some start == some z) = false := by simp [Ne.symm hzs]
    show 0 = 0 + bn ((some start == some z) && _) ∧ 0 = 0 + bn ((some start == some z) && _)
    rw [this]; simp [bn]
  | succ p ih =>
    obtain ⟨iy, ix⟩ := ih
    rw [W_succ, W_succ, W_succ, cur_succ]
    cases h : (walk σ p).cur with
    | none =>
      rw [h] at iy ix
      rw [visB_none σ h, visB_none σ h, visB_none σ h]
      simp only [Option.bind_none]
      simp [bn] at iy ix ⊢; exact ⟨iy, ix⟩
    | some d =>
      rw [h] at iy ix
      rw [visB_some σ h, visB_some σ h, visB_some σ h]
      simp only [Option.bind_some]
      have hs := cur_sp σ p d h
      by_cases hdz : d = z
      · subst hdz
        have hn : (nxt σ d ((walk σ p).W d) == some d) = false := by
          cases hq : nxt σ d ((walk σ p).W d) with
          | none => rfl
          | some e => have := nxt_ne σ hq; simp [this]
        have h1 : (some d == some y) = false := by simp [hzy]
        have h2 : (some d == some x) = false := by simp [hzx]
        have h3 : (some d == some d) = true := by simp
        rw [hn, h1, h2, h3]
        simp only [h3, Bool.true_and] at iy ix
        simp only [Bool.false_and, bn, ite_true, Bool.false_eq_true, ite_false, Nat.add_zero]
        rw [cnt_succ', cnt_succ']
        cases hω : ω ((walk σ p).W d) <;> simp [hω, bn] at iy ix ⊢ <;> omega
      · have hzd : (some d == some z) = false := by simp [hdz]
        rw [hzd] at iy ix
        simp only [Bool.false_and, bn, Bool.false_eq_true, ite_false, Nat.add_zero] at iy ix
        rw [hzd]
        simp only [bn, Bool.false_eq_true, ite_false, Nat.add_zero]
        by_cases hdy : d = y
        · subst hdy
          have hn := (hin d ((walk σ p).W d) hs).2 (Or.inr rfl)
          have hω := hw p d h (Or.inr rfl)
          simp only [decide_true] at hω
          have h2 : (some d == some x) = false := by simp [Ne.symm hxy]
          rw [hn, h2]
          simp [hω, iy, ix]
        · by_cases hdx : d = x
          · subst hdx
            have hn := (hin d ((walk σ p).W d) hs).2 (Or.inl rfl)
            have hω := hw p d h (Or.inl rfl)
            simp only [hdy, decide_false] at hω
            have h1 : (some d == some y) = false := by simp [hdy]
            rw [hn, h1]
            simp [hω, iy, ix]
          · have hn : (nxt σ d ((walk σ p).W d) == some z) = false := by
              cases hq : nxt σ d ((walk σ p).W d) == some z
              · rfl
              · have := (hin d _ hs).1 (by simpa using hq)
                rcases this with e | e <;> contradiction
            have h1 : (some d == some y) = false := by simp [hdy]
            have h2 : (some d == some x) = false := by simp [hdx]
            rw [h1, h2, hn]
            simp only [Bool.false_and, Bool.false_eq_true, ite_false, Nat.add_zero]
            exact ⟨iy, ix⟩

end Formal.Net.KCap
