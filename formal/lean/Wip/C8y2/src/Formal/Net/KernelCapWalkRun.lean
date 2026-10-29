import Formal.Net.KernelCapCut

/-!
# Kernel-parametric: invariants of the token run for the walk (from C-8s's CapstoneWalkRun)
-/


namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open KD KP

set_option linter.unusedSectionVars false

variable [KD] [KP]

/-- Invariants of every reachable traced state. -/
structure RI (a b : Nat) (x : TS) : Prop where
  inv : GcdHw.Inv spine x.s
  fifo : Fifo (init a b) x
  br : ∀ (l c d t f : Nat), rules[l]? = some (Rule.branch c d t f) → BrI c d t f x
  cml : ∀ (l i res idx kk : Nat), rules[l]? = some (Rule.cm i res idx kk) →
    (x.pr idx).length = (x.pr res).length
  lab : ((x.pr cidx).filter (fun v => v % 4 != 2)).length = (x.cn cq1).length + (x.cn cq2).length

theorem fire_rule {l : Nat} {s : Store Nat Nat} {f : Fire Nat Nat} (hf : (G l).fire s = some f) :
    ∃ r, rules[l]? = some r := by
  unfold G graph graphV at hf
  split at hf
  · rename_i r hr; exact ⟨r, hr⟩
  · simp [inert] at hf

theorem tstep_step {x x' : TS} {l : Nat} (h : tstep x l = some x') : step G x.s l = some x'.s := by
  obtain ⟨r, hf, hs, -, -⟩ := tstep_some h
  simp [step, hf, hs]

theorem pres_inv : Pres (fun x => GcdHw.Inv spine x.s) :=
  fun x _ _ h hx => closedG _ _ _ hx (tstep_step h)

theorem heads_one {s : Store Nat Nat} {i : Nat} {vs : List Nat} (h : heads s [i] = some vs) :
    vs = [(s i).headD 0] ∧ (s i).take 1 = [(s i).headD 0] := by
  obtain ⟨e1, e2⟩ := heads_spec h
  exact ⟨by simpa using e1, e2 i (by simp)⟩

theorem out_none {l : Nat} {r : Rule} (hr : rules[l]? = some r) {s : Store Nat Nat}
    {f : Fire Nat Nat} (hf : (G l).fire s = some f) {c : Nat} (hc : c ∉ r.outsL) : f.2 c = [] := by
  apply (G l).push_outs s f c hf
  intro ho
  obtain ⟨r', hr', hc'⟩ := graph_outs ho
  rw [hr] at hr'; cases hr'; exact hc hc'

theorem pop_none {l : Nat} {r : Rule} (hr : rules[l]? = some r) {s : Store Nat Nat}
    {f : Fire Nat Nat} (hf : (G l).fire s = some f) {c : Nat} (hc : c ∉ r.insL) : f.1 c = 0 := by
  apply (G l).pop_ins s f c hf
  intro ho
  obtain ⟨r', hr', hc'⟩ := graph_ins ho
  rw [hr] at hr'; cases hr'; exact hc hc'

/-- The firing of a control_merge rule. -/
theorem fire_cm {l i res idx kk : Nat} (hr : rules[l]? = some (Rule.cm i res idx kk))
    {s : Store Nat Nat} {f : Fire Nat Nat} (hf : (G l).fire s = some f) :
    s i ≠ [] ∧ f.1 = popOf [i] ∧
    f.2 = fun c => (if c = res then [(s i).headD 0] else []) ++ (if c = idx then [kk] else []) := by
  obtain ⟨vs, out, hh, hout, rfl⟩ := fire_strict hr (by intros; simp) hf
  simp only [Rule.insL] at hh
  obtain ⟨e1, e2⟩ := heads_one hh
  simp only [Rule.out, natVI, Option.some.injEq] at hout
  subst hout; subst e1
  refine ⟨?_, rfl, ?_⟩
  · intro he; rw [he] at e2; simp at e2
  · funext c; simp

theorem pres_cml {l0 i0 res idx kk0 : Nat} (h0 : rules[l0]? = some (Rule.cm i0 res idx kk0)) :
    Pres (fun x => (x.pr idx).length = (x.pr res).length) := by
  have hc := List.all_eq_true.mp cmPair_chk _ (List.mem_of_getElem? h0)
  simp only [cmPairOK, Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.all_eq_true] at hc
  obtain ⟨⟨⟨hne, -⟩, -⟩, hall⟩ := hc
  intro x l x' h hx
  obtain ⟨f, hf, -, -, hp⟩ := tstep_some h
  show (x'.pr idx).length = (x'.pr res).length
  rw [hp, hp, List.length_append, List.length_append, hx]
  obtain ⟨r, hr⟩ := fire_rule hf
  by_cases ho : res ∈ r.outsL ∨ idx ∈ r.outsL
  · have hm := hall r (List.mem_of_getElem? hr)
    have hc1 : (r.outsL.contains res || r.outsL.contains idx) = true := by
      rcases ho with ho | ho <;> simp [ho]
    rw [hc1] at hm
    simp only [Bool.not_true, Bool.false_or] at hm
    cases r with
    | cm i2 res2 idx2 kk2 =>
      simp only [Bool.and_eq_true, beq_iff_eq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      obtain ⟨-, -, e⟩ := fire_cm hr hf
      rw [e]; simp [hne, Ne.symm hne]
    | _ => simp at hm
  · simp only [not_or] at ho
    rw [out_none hr hf ho.1, out_none hr hf ho.2]

theorem pres_lab : Pres (fun x => ((x.pr cidx).filter (fun v => v % 4 != 2)).length =
    (x.cn cq1).length + (x.cn cq2).length) := by
  intro x l x' h hx
  obtain ⟨f, hf, -, hc, hp⟩ := tstep_some h
  show ((x'.pr cidx).filter _).length = (x'.cn cq1).length + (x'.cn cq2).length
  rw [hp, hc, hc, List.filter_append, List.length_append, List.length_append, List.length_append, hx]
  obtain ⟨r, hr⟩ := fire_rule hf
  have hl := List.all_eq_true.mp lab_chk r (List.mem_of_getElem? hr)
  have hcp := List.all_eq_true.mp cmPair_chk r (List.mem_of_getElem? hr)
  by_cases ho : cidx ∈ r.outsL
  · -- r is a control_merge with index 249 (the producers of 249, by cmPair on rule 154)
    have h154 := List.all_eq_true.mp cmPair_chk _ (List.mem_of_getElem? r154)
    simp only [cmPairOK, Bool.and_eq_true, List.all_eq_true] at h154
    have := h154.2 r (List.mem_of_getElem? hr)
    simp only [Bool.not_eq_true', Bool.or_eq_false_iff, List.contains_eq_mem,
      decide_eq_false_iff_not, Bool.or_eq_true] at this
    rcases this with ⟨-, h2⟩ | this
    · exact absurd ho h2
    · cases r with
      | cm i res idx kk =>
        simp only [Bool.and_eq_true, beq_iff_eq] at this
        obtain ⟨rfl, rfl⟩ := this
        obtain ⟨hne, e1, e2⟩ := fire_cm hr hf
        simp only [labOK, bne_self_eq_false, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
          Prod.mk.injEq] at hl
        rw [e1, e2]
        have ht : ((x.s i).take 1).length = 1 := by
          cases hs : x.s i with
          | nil => exact absurd hs hne
          | cons _ _ => simp
        rcases hl with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | ⟨rfl, rfl⟩
        · simp [popOf, ht] <;> omega
        · simp [popOf, ht] <;> omega
        · simp [popOf] <;> omega
      | _ => simp at this
  · rw [out_none hr hf ho]
    have n13 : cq1 ∉ r.insL := by
      intro hm
      by_cases hl' : l = cl1
      · subst hl'; rw [r154] at hr; cases hr; exact ho (by simp [Rule.outsL])
      · exact ins_disj r154 hr (Ne.symm hl') (by simp [Rule.insL]) hm
    have n27 : cq2 ∉ r.insL := by
      intro hm
      by_cases hl' : l = cl2
      · subst hl'; rw [r155] at hr; cases hr; exact ho (by simp [Rule.outsL])
      · exact ins_disj r155 hr (Ne.symm hl') (by simp [Rule.insL]) hm
    rw [pop_none hr hf n13, pop_none hr hf n27]
    simp

theorem ri_pres (a b : Nat) : Pres (RI a b) := by
  intro x l x' h hx
  refine ⟨pres_inv x l x' h hx.inv, fifo_pres _ x l x' h hx.fifo, ?_, ?_, ?_⟩
  · intro l0 c d t f hr
    have := side_of hr; simp [sideOK] at this
    exact br_pres hr this x l x' h (hx.br l0 c d t f hr)
  · intro l0 i res idx kk hr
    exact pres_cml hr x l x' h (hx.cml l0 i res idx kk hr)
  · exact pres_lab x l x' h hx.lab

def x0 (a b : Nat) : TS := ⟨init a b, fun _ => [], fun _ => []⟩

theorem ri_x0 (a b : Nat) : RI a b (x0 a b) := by
  refine ⟨init_inv a b, fun c => by simp [x0], ?_, ?_, ?_⟩
  · intro l c d t f _; exact ⟨rfl, rfl, rfl⟩
  · intro l i res idx kk _; rfl
  · rfl

/-! ## Prefixes -/

theorem texec_pre : ∀ (ls : List Nat) (x y : TS), texec x ls = some y →
    ∀ c, (∃ t, y.pr c = x.pr c ++ t) ∧ (∃ t, y.cn c = x.cn c ++ t) := by
  intro ls
  induction ls with
  | nil => intro x y h c; simp [texec] at h; subst h; exact ⟨⟨[], by simp⟩, ⟨[], by simp⟩⟩
  | cons l ls ih =>
    intro x y h c
    simp only [texec] at h
    cases ht : tstep x l with
    | none => rw [ht] at h; simp at h
    | some z =>
      rw [ht] at h
      obtain ⟨f, -, -, hc, hp⟩ := tstep_some ht
      obtain ⟨⟨t1, e1⟩, ⟨t2, e2⟩⟩ := ih z y h c
      exact ⟨⟨f.2 c ++ t1, by rw [e1, hp, List.append_assoc]⟩,
        ⟨(x.s c).take (f.1 c) ++ t2, by rw [e2, hc, List.append_assoc]⟩⟩

theorem cn_pre {a b : Nat} {x y : TS} (hx : Fifo (init a b) x) (hy : Fifo (init a b) y) {c : Nat}
    (hyc : y.s c = []) (hp : ∃ t, y.pr c = x.pr c ++ t) : ∃ t, y.cn c = x.cn c ++ x.s c ++ t := by
  obtain ⟨t, ht⟩ := hp
  refine ⟨t, ?_⟩
  have e1 := hx c
  have e2 := hy c
  rw [hyc, List.append_nil, ht, ← List.append_assoc, e1] at e2
  exact e2.symm

/-! ## The spine token -/

theorem only_tok {s : Store Nat Nat} (hI : GcdHw.Inv spine s) {g h : Nat} (hg : g ∈ spine)
    (hh : h ∈ spine) (hne : s g ≠ []) (hgh : h ≠ g) : s h = [] := by
  cases hs : s h with
  | nil => rfl
  | cons v vs =>
    exfalso
    have := two_le_sum (f := fun c => (s c).length) spine_nodup hg hh (Ne.symm hgh)
      (by cases e : s g with | nil => exact absurd e hne | cons _ _ => simp)
      (by simp [hs])
    unfold GcdHw.Inv GcdHw.cnt at hI; omega

theorem tok_one {s : Store Nat Nat} (hI : GcdHw.Inv spine s) {g : Nat} (hg : g ∈ spine)
    (hne : s g ≠ []) : ∃ v, s g = [v] := by
  cases hs : s g with
  | nil => exact absurd hs hne
  | cons v vs =>
    cases vs with
    | nil => exact ⟨v, rfl⟩
    | cons w ws =>
      exfalso
      have := le_sum_of_mem (f := fun c => (s c).length) hg
      unfold GcdHw.Inv GcdHw.cnt at hI; simp [hs] at this; omega

/-- A firing that does not consume the spine token touches no spine channel. -/
theorem quiet {a b : Nat} {x x1 : TS} {l g : Nat} (hR : RI a b x) (hg : g ∈ spine)
    (hne : x.s g ≠ []) (h : tstep x l = some x1) (hl : ∀ r, rules[l]? = some r → g ∉ r.insL) :
    ∀ h ∈ spine, x1.s h = x.s h ∧ x1.cn h = x.cn h := by
  obtain ⟨f, hf, hs, hc, -⟩ := tstep_some h
  obtain ⟨r, hr⟩ := fire_rule hf
  have hpop : ∀ h ∈ spine, f.1 h = 0 := by
    intro h hh
    by_cases e : h = g
    · subst e; exact pop_none hr hf (hl r hr)
    · have := (G l).pop_le x.s f h hf
      rw [only_tok hR.inv hg hh hne e] at this; simpa using this
  have hI1 : GcdHw.Inv spine x1.s := pres_inv x l x1 h hR.inv
  have key := cnt_apply spine x.s f (fun c => (G l).pop_le x.s f c hf)
  rw [← hs, sum_zero hpop] at key
  have h1 : 1 ≤ GcdHw.cnt spine x.s := by
    have := le_sum_of_mem (f := fun c => (x.s c).length) hg
    unfold GcdHw.cnt
    exact Nat.le_trans (by cases e : x.s g with | nil => exact absurd e hne | cons _ _ => simp) this
  unfold GcdHw.Inv at hI1
  have hpush : (spine.map fun c => (f.2 c).length).sum = 0 := by omega
  intro h hh
  have hz : (f.2 h).length = 0 := by
    have := le_sum_of_mem (f := fun c => (f.2 c).length) hh; omega
  refine ⟨?_, ?_⟩
  · rw [hs]; simp [applyF, hpop h hh, List.length_eq_zero_iff.mp hz]
  · rw [hc, hpop h hh]; simp

/-- From a state holding the spine token on `g`, a run to a store without it reaches a state
(with the same spine) whose next firing consumes `g`. -/
theorem next_fire {a b : Nat} {y : TS} {g : Nat} (hg : g ∈ spine) (hyg : y.s g = []) :
    ∀ (ls : List Nat) (x : TS), RI a b x → x.s g ≠ [] → texec x ls = some y →
    ∃ x2 l x3 ls4, RI a b x2 ∧ (∀ h ∈ spine, x2.s h = x.s h ∧ x2.cn h = x.cn h) ∧
      tstep x2 l = some x3 ∧ texec x3 ls4 = some y ∧ ∃ r, rules[l]? = some r ∧ g ∈ r.insL := by
  intro ls
  induction ls with
  | nil => intro x _ hne h; simp [texec] at h; subst h; exact absurd hyg hne
  | cons l ls ih =>
    intro x hR hne h
    simp only [texec] at h
    cases ht : tstep x l with
    | none => rw [ht] at h; simp at h
    | some x1 =>
      rw [ht] at h
      by_cases hl : ∃ r, rules[l]? = some r ∧ g ∈ r.insL
      · exact ⟨x, l, x1, ls, hR, fun _ _ => ⟨rfl, rfl⟩, ht, h, hl⟩
      · have hq := quiet hR hg hne ht (fun r hr hm => hl ⟨r, hr, hm⟩)
        have hR1 := ri_pres a b x l x1 ht hR
        have hne1 : x1.s g ≠ [] := by rw [(hq g hg).1]; exact hne
        obtain ⟨x2, l2, x3, ls4, h1, h2, h3, h4, h5⟩ := ih x1 hR1 hne1 h
        exact ⟨x2, l2, x3, ls4, h1, fun h hh => ⟨(h2 h hh).1.trans (hq h hh).1,
          (h2 h hh).2.trans (hq h hh).2⟩, h3, h4, h5⟩

/-- The consuming firing changes the consumed count of `g` only, among spine channels. -/
theorem fire_cn {a b : Nat} {x x' : TS} {l g : Nat} {r : Rule} (hR : RI a b x) (hg : g ∈ spine)
    (hne : x.s g ≠ []) (h : tstep x l = some x') (hr : rules[l]? = some r) (hgr : g ∈ r.insL)
    (hm : ∀ s ds o iw, r ≠ .mux s ds o iw) :
    ∀ h ∈ spine, (x'.cn h).length = (x.cn h).length + bn (h == g) := by
  obtain ⟨f, hf, -, hc, -⟩ := tstep_some h
  obtain ⟨vs, out, -, -, rfl⟩ := fire_strict hr hm hf
  intro h hh
  rw [hc]
  by_cases e : h = g
  · subst e
    simp only [popOf, hgr, ite_true, List.length_append, beq_self_eq_true, bn]
    cases hs : x.s h with
    | nil => exact absurd hs hne
    | cons _ _ => simp
  · rw [only_tok hR.inv hg hh hne e]
    simp [bn, e]

end Formal.Net.KCap
