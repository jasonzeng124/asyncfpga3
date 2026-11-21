import Formal.Net.KernelCapDefs

/-!
# Kernel-parametric: per-channel histories of a token run (from C-8m's CapstoneSafeHist)
-/


namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open KD KP

set_option linter.unusedSectionVars false

variable [KD] [KP]

/-- A store with its consumed and produced histories. -/
structure TS where
  s : Store Nat Nat
  cn : Nat → List Nat
  pr : Nat → List Nat

def tstep (x : TS) (l : Nat) : Option TS :=
  ((G l).fire x.s).map fun r =>
    ⟨applyF x.s r, fun c => x.cn c ++ (x.s c).take (r.1 c), fun c => x.pr c ++ r.2 c⟩

def texec (x : TS) : List Nat → Option TS
  | [] => some x
  | l :: ls => (tstep x l).bind (texec · ls)

theorem run_exec {s : Store Nat Nat} {n : Nat} {t : Store Nat Nat} (h : Run (step G) s n t) :
    ∃ ls : List Nat, exec G s ls = some t := by
  induction h with
  | refl s => exact ⟨[], rfl⟩
  | cons l hs _ ih =>
    obtain ⟨ls, hl⟩ := ih
    exact ⟨l :: ls, by simp [exec, hs, hl]⟩

theorem texec_of_exec : ∀ (ls : List Nat) (x : TS) (t : Store Nat Nat), exec G x.s ls = some t →
    ∃ y, texec x ls = some y ∧ y.s = t := by
  intro ls
  induction ls with
  | nil => intro x t h; simp [exec] at h; exact ⟨x, rfl, h⟩
  | cons l ls ih =>
    intro x t h
    simp only [exec, step] at h
    cases hf : (G l).fire x.s with
    | none => rw [hf] at h; simp at h
    | some r =>
      rw [hf] at h
      simp only [Option.map_some, Option.bind_some] at h
      obtain ⟨y, hy, hs⟩ := ih ⟨applyF x.s r, fun c => x.cn c ++ (x.s c).take (r.1 c),
        fun c => x.pr c ++ r.2 c⟩ t h
      exact ⟨y, by simp [texec, tstep, hf, hy], hs⟩

def Pres (P : TS → Prop) : Prop := ∀ x l y, tstep x l = some y → P x → P y

theorem texec_pres {P : TS → Prop} (hP : Pres P) : ∀ (ls : List Nat) x y, texec x ls = some y →
    P x → P y := by
  intro ls
  induction ls with
  | nil => intro x y h hx; simp [texec] at h; exact h ▸ hx
  | cons l ls ih =>
    intro x y h hx
    simp only [texec] at h
    cases ht : tstep x l with
    | none => rw [ht] at h; simp at h
    | some z => rw [ht] at h; exact ih z y h (hP x l z ht hx)

theorem tstep_some {x y : TS} {l : Nat} (h : tstep x l = some y) :
    ∃ r, (G l).fire x.s = some r ∧ y.s = applyF x.s r ∧
      (∀ c, y.cn c = x.cn c ++ (x.s c).take (r.1 c)) ∧ (∀ c, y.pr c = x.pr c ++ r.2 c) := by
  unfold tstep at h
  cases hf : (G l).fire x.s with
  | none => rw [hf] at h; simp at h
  | some r =>
    rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h
    subst h; exact ⟨r, rfl, rfl, fun _ => rfl, fun _ => rfl⟩

/-! ## FIFO invariant -/

def Fifo (s0 : Store Nat Nat) (x : TS) : Prop := ∀ c, s0 c ++ x.pr c = x.cn c ++ x.s c

theorem fifo_pres (s0 : Store Nat Nat) : Pres (Fifo s0) := by
  intro x l y h hx c
  obtain ⟨r, _, hs, hc, hp⟩ := tstep_some h
  rw [hs, hc, hp, ← List.append_assoc, hx c, applyF]
  simp only [List.append_assoc]
  rw [← List.append_assoc (List.take _ _), List.take_append_drop]

/-! ## Quietness: other rules do not touch a rule's inputs / outputs -/

theorem ins_disj_g {rs : List Rule} (hI : checkIns rs = true) {l l' : Nat} {r r' : Rule}
    (hr : rs[l]? = some r) (hr' : rs[l']? = some r')
    (hne : l ≠ l') {c : Nat} (hc : c ∈ r.insL) (hc' : c ∈ r'.insL) : False :=
  flatten_disj (a := r.insL) (b := r'.insL) (of_decide_eq_true hI) (by simp [hr])
    (by simp [hr']) hne hc hc'

theorem ins_disj {l l' : Nat} {r r' : Rule} (hr : rules[l]? = some r) (hr' : rules[l']? = some r')
    (hne : l ≠ l') {c : Nat} (hc : c ∈ r.insL) (hc' : c ∈ r'.insL) : False :=
  ins_disj_g ins_ok hr hr' hne hc hc'

theorem outs_disj_g {P : List Nat} {rs : List Rule} (hO : checkOuts P rs = true) {l l' : Nat} {r r' : Rule}
    (hr : rs[l]? = some r) (hr' : rs[l']? = some r')
    (hne : l ≠ l') (hcm : r.isCmP P = false) {c : Nat} (hc : c ∈ r.outsL)
    (hc' : c ∈ r'.outsL) : False := by
  simp only [checkOuts, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hO
  obtain ⟨hO1, hO2⟩ := hO
  cases h2 : r'.isCmP P
  · exact flatten_disj (a := r.outsO P) (b := r'.outsO P) (c := c) hO1 (by simp [hr])
      (by simp [hr']) hne (by simp [Rule.outsO, hcm, hc]) (by simp [Rule.outsO, h2, hc'])
  · have := hO2 r' (List.mem_of_getElem? hr')
    simp only [h2, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    have := this c hc'
    simp [mem_outsO_flatten hr hc hcm] at this

theorem outs_disj {l l' : Nat} {r r' : Rule} (hr : rules[l]? = some r) (hr' : rules[l']? = some r')
    (hne : l ≠ l') (hcm : r.isCmP spine = false) {c : Nat} (hc : c ∈ r.outsL)
    (hc' : c ∈ r'.outsL) : False :=
  outs_disj_g outs_ok hr hr' hne hcm hc hc'

theorem quiet_in {l l' : Nat} {r : Rule} (hr : rules[l]? = some r) (hne : l ≠ l')
    {s : Store Nat Nat} {f : Fire Nat Nat} (hf : (G l').fire s = some f) {c : Nat}
    (hc : c ∈ r.insL) : f.1 c = 0 := by
  apply (G l').pop_ins s f c hf
  intro hi
  obtain ⟨r', hr', hc'⟩ := graph_ins hi
  exact ins_disj hr hr' hne hc hc'

theorem quiet_out {l l' : Nat} {r : Rule} (hr : rules[l]? = some r) (hne : l ≠ l')
    (hcm : r.isCmP spine = false)
    {s : Store Nat Nat} {f : Fire Nat Nat} (hf : (G l').fire s = some f) {c : Nat}
    (hc : c ∈ r.outsL) : f.2 c = [] := by
  apply (G l').push_outs s f c hf
  intro hi
  obtain ⟨r', hr', hc'⟩ := graph_outs hi
  exact outs_disj hr hr' hne hcm hc hc'

/-! ## Heads -/

theorem heads_spec {s : Store Nat Nat} : ∀ {cs : List Nat} {vs : List Nat}, heads s cs = some vs →
    vs = cs.map (fun c => (s c).headD 0) ∧ ∀ c ∈ cs, (s c).take 1 = [(s c).headD 0] := by
  intro cs
  induction cs with
  | nil => intro vs h; simp [heads] at h; subst h; simp
  | cons d ds ih =>
    intro vs h
    simp only [heads] at h
    split at h
    · cases h
    · rename_i v rest hd
      cases hh : heads s ds with
      | none => rw [hh] at h; cases h
      | some ws =>
        rw [hh] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        obtain ⟨e1, e2⟩ := ih hh
        refine ⟨by simp [hd, e1], fun c hc => ?_⟩
        rcases List.mem_cons.mp hc with rfl | hc
        · simp [hd]
        · exact e2 c hc

theorem popOf_mem {ins : List Nat} {c : Nat} (h : c ∈ ins) : popOf ins c = 1 := by simp [popOf, h]
theorem popOf_nmem {ins : List Nat} {c : Nat} (h : c ∉ ins) : popOf ins c = 0 := by simp [popOf, h]

theorem fire_strict {l : Nat} {r : Rule} (hr : rules[l]? = some r) (hm : ∀ s ds o iw, r ≠ .mux s ds o iw)
    {st : Store Nat Nat} {f : Fire Nat Nat} (hf : (G l).fire st = some f) :
    ∃ vs out, heads st r.insL = some vs ∧ r.out natVI vs = some out ∧ f = (popOf r.insL, out) := by
  rw [graph_fire hr] at hf
  have : r.fire natVI st = strictF r.insL (r.out natVI) st := by
    cases r with
    | mux s ds o iw => exact absurd rfl (hm s ds o iw)
    | _ => rfl
  rw [this] at hf
  exact strictF_some hf

/-! ## Fork -/

def FkI (i : Nat) (os : List Nat) (x : TS) : Prop := ∀ o ∈ os, x.pr o = x.cn i

theorem fk_pres {l i : Nat} {os : List Nat} (hr : rules[l]? = some (.fork i os)) : Pres (FkI i os) := by
  intro x l2 y h hx o ho
  obtain ⟨f, hf, _, hc, hp⟩ := tstep_some h
  rw [hc, hp, hx o ho]
  by_cases hl : l2 = l
  · subst hl
    obtain ⟨vs, out, hh, hout, rfl⟩ := fire_strict hr (by intros; simp) hf
    obtain ⟨e1, e2⟩ := heads_spec hh
    simp only [Rule.insL] at e1 e2 hh
    simp only [Rule.out, Option.some.injEq] at hout; subst hout
    show x.cn i ++ (if o ∈ os then List.take 1 vs else []) = x.cn i ++ (x.s i).take (popOf [i] i)
    rw [popOf_mem (by simp), e2 i (by simp), e1]; simp [ho]
  · have q1 := quiet_in hr (Ne.symm hl) hf (c := i) (by simp [Rule.insL])
    have q2 := quiet_out hr (Ne.symm hl) (by rfl) hf (c := o) (by simpa [Rule.outsL] using ho)
    simp [q1, q2]

/-! ## Comp -/

def CpI (ins : List Nat) (o : Nat) (e : E) (x : TS) : Prop :=
  ∃ n, (∀ m ∈ ins, (x.cn m).length = n) ∧
    x.pr o = (List.range n).map (fun j => e.eval (ins.map fun m => (x.cn m).getD j 0))

theorem getD_append_lt (L M : List Nat) {j : Nat} (h : j < L.length) : (L ++ M).getD j 0 = L.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_len (L : List Nat) (v : Nat) : (L ++ [v]).getD L.length 0 = v := by
  simp [List.getD_eq_getElem?_getD]

theorem cp_pres {l : Nat} {ins : List Nat} {o : Nat} {e : E} (hr : rules[l]? = some (.comp ins o e)) :
    Pres (CpI ins o e) := by
  intro x l2 y h ⟨n, hn, hpo⟩
  obtain ⟨f, hf, _, hc, hp⟩ := tstep_some h
  by_cases hl : l2 = l
  · subst hl
    obtain ⟨vs, out, hh, hout, rfl⟩ := fire_strict hr (by intros; simp) hf
    obtain ⟨e1, e2⟩ := heads_spec hh
    simp only [Rule.insL] at e1 e2 hh
    simp only [Rule.out, natVI, Option.some.injEq] at hout; subst hout
    have hc : ∀ c, y.cn c = x.cn c ++ (x.s c).take (popOf ins c) := hc
    have hp : ∀ c, y.pr c = x.pr c ++ (if c = o then [e.eval vs] else []) := hp
    refine ⟨n + 1, fun m hm => ?_, ?_⟩
    · rw [hc, popOf_mem hm, e2 m hm]; simp [hn m hm]
    · rw [hp, hpo, List.range_succ, List.map_append]
      simp only [↓reduceIte, List.map_cons, List.map_nil]
      congr 1
      · apply List.map_congr_left; intro j hj
        have hj := List.mem_range.mp hj
        congr 1; apply List.map_congr_left; intro m hm
        rw [hc, popOf_mem hm, getD_append_lt _ _ (by rw [hn m hm]; exact hj)]
      · congr 2; rw [e1]; apply List.map_congr_left; intro m hm
        rw [hc, popOf_mem hm, e2 m hm, ← hn m hm, getD_append_len]
  · refine ⟨n, fun m hm => ?_, ?_⟩
    · rw [hc, quiet_in hr (Ne.symm hl) hf hm]; simp [hn m hm]
    · rw [hp, quiet_out hr (Ne.symm hl) (by rfl) hf (c := o) (by simp [Rule.outsL]), List.append_nil, hpo]
      apply List.map_congr_left; intro j _
      congr 1; apply List.map_congr_left; intro m hm
      rw [hc, quiet_in hr (Ne.symm hl) hf hm]; simp

/-! ## Branch -/

def selL (b : Bool) (L D : List Nat) : List Nat :=
  (L.zip D).filterMap (fun p => if (p.1 % 2 == 1) = b then some p.2 else none)

def BrI (c d t f : Nat) (x : TS) : Prop :=
  (x.cn c).length = (x.cn d).length ∧ x.pr t = selL true (x.cn c) (x.cn d) ∧
    x.pr f = selL false (x.cn c) (x.cn d)

theorem selL_snoc (b : Bool) (L D : List Nat) (v y : Nat) (h : L.length = D.length) :
    selL b (L ++ [v]) (D ++ [y]) = selL b L D ++ (if (v % 2 == 1) = b then [y] else []) := by
  unfold selL
  rw [List.zip_append h, List.filterMap_append]
  simp only [List.zip_cons_cons, List.zip_nil_left, List.filterMap_cons, List.filterMap_nil]
  by_cases hb : (v % 2 == 1) = b <;> simp [hb]

theorem br_pres {l c d t f : Nat} (hr : rules[l]? = some (.branch c d t f)) (htf : t ≠ f) :
    Pres (BrI c d t f) := by
  intro x l2 y h ⟨hlen, ht, hf'⟩
  obtain ⟨g, hg, _, hc, hp⟩ := tstep_some h
  unfold BrI
  by_cases hl : l2 = l
  · subst hl
    obtain ⟨vs, out, hh, hout, rfl⟩ := fire_strict hr (by intros; simp) hg
    obtain ⟨e1, e2⟩ := heads_spec hh
    simp only [Rule.insL, List.map_cons, List.map_nil] at e1 e2
    subst e1
    simp only [Rule.out, natVI, Option.map_some, Option.some.injEq] at hout
    subst hout
    have hc : ∀ c', y.cn c' = x.cn c' ++ (x.s c').take (popOf [c, d] c') := hc
    have hp : ∀ c', y.pr c' = x.pr c' ++ (if c' = (if ((x.s c).headD 0 % 2 == 1) = true then t else f)
        then [(x.s d).headD 0] else []) := hp
    rw [hc c, hc d, hp t, hp f, popOf_mem (by simp), popOf_mem (by simp), e2 c (by simp),
      e2 d (by simp)]
    refine ⟨by simp [hlen], ?_, ?_⟩
    · rw [selL_snoc _ _ _ _ _ hlen, ht]
      cases hb : ((x.s c).headD 0 % 2 == 1) <;> simp [htf]
    · rw [selL_snoc _ _ _ _ _ hlen, hf']
      cases hb : ((x.s c).headD 0 % 2 == 1) <;> simp [Ne.symm htf]
  · have qc := quiet_in hr (Ne.symm hl) hg (c := c) (by simp [Rule.insL])
    have qd := quiet_in hr (Ne.symm hl) hg (c := d) (by simp [Rule.insL])
    have qt := quiet_out hr (Ne.symm hl) (by rfl) hg (c := t) (by simp [Rule.outsL])
    have qf := quiet_out hr (Ne.symm hl) (by rfl) hg (c := f) (by simp [Rule.outsL])
    rw [hc c, hc d, hp t, hp f, qc, qd, qt, qf]
    simp only [List.take_zero, List.append_nil]
    exact ⟨hlen, ht, hf'⟩

/-! ## Mux -/

/-- `#{j' < j : L[j'] % 2^iw = m}`. -/
def cntm (L : List Nat) (iw m j : Nat) : Nat := ((L.take j).filter (fun v => v % 2 ^ iw == m)).length

def MxI (s : Nat) (ds : List Nat) (o iw : Nat) (x : TS) : Prop :=
  (x.pr o).length = (x.cn s).length ∧
  (∀ j < (x.cn s).length, (x.cn s).getD j 0 % 2 ^ iw < ds.length ∧
    (x.pr o).getD j 0 = (x.cn (ds.getD ((x.cn s).getD j 0 % 2 ^ iw) 0)).getD
      (cntm (x.cn s) iw ((x.cn s).getD j 0 % 2 ^ iw) j) 0) ∧
  (∀ m < ds.length, (x.cn (ds.getD m 0)).length = cntm (x.cn s) iw m (x.cn s).length)

theorem cntm_snoc_le (L : List Nat) (iw m v j : Nat) (hj : j ≤ L.length) :
    cntm (L ++ [v]) iw m j = cntm L iw m j := by
  unfold cntm; rw [List.take_append_of_le_length hj]

theorem cntm_snoc_len (L : List Nat) (iw m v : Nat) :
    cntm (L ++ [v]) iw m (L.length + 1) = cntm L iw m L.length + (if v % 2 ^ iw == m then 1 else 0) := by
  unfold cntm
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp), List.filter_append]
  split <;> simp_all

theorem cntm_lt (L : List Nat) (iw : Nat) {j n : Nat} (hj : j < n) (hn : n ≤ L.length) :
    cntm L iw (L.getD j 0 % 2 ^ iw) j < cntm L iw (L.getD j 0 % 2 ^ iw) n := by
  unfold cntm
  have h1 : L.take n = L.take j ++ (L.drop j).take (n - j) := by
    rw [← List.take_append_drop j (L.take n), List.take_take, Nat.min_eq_left (by omega),
      List.drop_take]
  rw [h1, List.filter_append, List.length_append]
  have h2 : (L.drop j).take (n - j) = L.getD j 0 :: (L.drop (j + 1)).take (n - j - 1) := by
    have hl : j < L.length := by omega
    rw [List.drop_eq_getElem_cons hl]
    rw [show n - j = (n - j - 1) + 1 by omega, List.take_succ_cons]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl]
  rw [h2]; simp

theorem mx_pres {l s o iw : Nat} {ds : List Nat} (hr : rules[l]? = some (.mux s ds o iw))
    (hnd : ds.Nodup) (hs : s ∉ ds) : Pres (MxI s ds o iw) := by
  intro x l2 y h ⟨hlen, hval, hcnt⟩
  obtain ⟨g, hg, _, hc, hp⟩ := tstep_some h
  unfold MxI
  by_cases hl : l2 = l
  · subst hl
    rw [graph_fire hr] at hg
    change muxF natVI s ds o iw x.s = some g at hg
    obtain ⟨v, vs, j, d, x0, xs, hsv, hj, hd, hne, hx0, rfl⟩ := muxF_some hg
    simp only [natVI, Option.some.injEq] at hj; subst hj
    have hmlt : v % 2 ^ iw < ds.length := by
      rcases Nat.lt_or_ge (v % 2 ^ iw) ds.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hd; cases hd
    have hdd : ds.getD (v % 2 ^ iw) 0 = d := by
      simp [List.getD_eq_getElem?_getD, hd]
    have hcs : y.cn s = x.cn s ++ [v] := by rw [hc]; simp [Ne.symm hne, hsv]
    have hcd : y.cn d = x.cn d ++ [x0] := by rw [hc]; simp [hne, hx0]
    -- other inputs unchanged
    have hcm : ∀ m < ds.length, m ≠ v % 2 ^ iw → y.cn (ds.getD m 0) = x.cn (ds.getD m 0) := by
      intro m hm hmv
      have e1 : ds.getD m 0 ≠ s := by
        intro e; apply hs; rw [← e]; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
      have e2 : ds.getD m 0 ≠ d := by
        intro e; apply hmv
        rw [← hdd] at e
        exact (List.Nodup.getD_inj hm hmlt hnd).mp e
      rw [hc]
      show x.cn _ ++ List.take ((if ds.getD m 0 = s then 1 else 0) + (if ds.getD m 0 = d then 1 else 0)) _ = _
      simp only [e1, e2, ite_false]; simp
    have hpo : y.pr o = x.pr o ++ [x0] := by rw [hp]; simp
    rw [hcs, hpo]
    refine ⟨by simp [hlen], ?_, ?_⟩
    · intro j hj
      simp only [List.length_append, List.length_singleton] at hj
      rcases Nat.lt_or_ge j (x.cn s).length with hj' | hj'
      · obtain ⟨hv1, hv2⟩ := hval j hj'
        rw [getD_append_lt _ _ hj', getD_append_lt _ _ (by rw [hlen]; exact hj'),
          cntm_snoc_le _ _ _ _ _ (by omega)]
        refine ⟨hv1, ?_⟩
        rw [hv2]
        by_cases hm : (x.cn s).getD j 0 % 2 ^ iw = v % 2 ^ iw
        · have hlt := cntm_lt (x.cn s) iw hj' (Nat.le_refl _)
          have hc' := hcnt _ hmlt
          rw [hm] at hlt
          rw [hdd] at hc'
          rw [hm, hdd, hcd, getD_append_lt _ _ (by omega)]
        · rw [hcm _ hv1 hm]
      · have : j = (x.cn s).length := by omega
        subst this
        have hc' := hcnt _ hmlt; rw [hdd] at hc'
        rw [getD_append_len, cntm_snoc_le _ _ _ _ _ (Nat.le_refl _), hdd, hcd, ← hc', getD_append_len,
          ← hlen, getD_append_len]
        exact ⟨hmlt, rfl⟩
    · intro m hm
      rw [List.length_append, List.length_singleton, cntm_snoc_len, ← hcnt m hm]
      by_cases hmv : m = v % 2 ^ iw
      · subst hmv; rw [hdd, hcd]; simp
      · rw [hcm m hm hmv]
        have : (v % 2 ^ iw == m) = false := by simp; omega
        simp [this]
  · have qs := quiet_in hr (Ne.symm hl) hg (c := s) (by simp [Rule.insL])
    have qo := quiet_out hr (Ne.symm hl) (by rfl) hg (c := o) (by simp [Rule.outsL])
    have qd : ∀ m < ds.length, g.1 (ds.getD m 0) = 0 := by
      intro m hm
      exact quiet_in hr (Ne.symm hl) hg (by
        simp only [Rule.insL, List.mem_cons]
        right; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm])
    have hcs : y.cn s = x.cn s := by rw [hc, qs]; simp
    have hpo : y.pr o = x.pr o := by rw [hp, qo]; simp
    have hcd : ∀ m < ds.length, y.cn (ds.getD m 0) = x.cn (ds.getD m 0) := by
      intro m hm; rw [hc, qd m hm]; simp
    rw [hcs, hpo]
    refine ⟨hlen, fun j hj => ?_, fun m hm => by rw [hcd m hm]; exact hcnt m hm⟩
    obtain ⟨h1, h2⟩ := hval j hj
    exact ⟨h1, by rw [hcd _ h1]; exact h2⟩

/-! ## No producer -/

theorem np_pres (c : Nat) (hc : produced c = false) : Pres (fun x => x.pr c = []) := by
  intro x l y h hx
  obtain ⟨f, hf, _, _, hp⟩ := tstep_some h
  rw [hp, hx]
  have : f.2 c = [] := by
    apply (G l).push_outs x.s f c hf
    intro ho
    obtain ⟨r, hr, hcr⟩ := graph_outs ho
    have : produced c = true := List.any_eq_true.mpr ⟨r, List.mem_of_getElem? hr, by simpa using hcr⟩
    rw [hc] at this; cases this
  simp [this]

theorem nc_pres (c : Nat) (hc : consumed c = false) : Pres (fun x => x.cn c = []) := by
  intro x l y h hx
  obtain ⟨f, hf, _, hcn, _⟩ := tstep_some h
  rw [hcn, hx]
  have : f.1 c = 0 := by
    apply (G l).pop_ins x.s f c hf
    intro ho
    obtain ⟨r, hr, hcr⟩ := graph_ins ho
    have : consumed c = true := List.any_eq_true.mpr ⟨r, List.mem_of_getElem? hr, by simpa using hcr⟩
    rw [hc] at this; cases this
  simp [this]

/-! ## The complete traced run -/

theorem side_of {l : Nat} {r : Rule} (hr : rules[l]? = some r) : sideOK r = true :=
  List.all_eq_true.mp side_ok r (List.mem_of_getElem? hr)

/-- Everything the stream solution needs from one complete run. -/
structure Good (a b : Nat) (y : TS) : Prop where
  fin : y.s = final (spec a b)
  fifo : Fifo (init a b) y
  fk : ∀ (l i : Nat) (os : List Nat), rules[l]? = some (Rule.fork i os) → FkI i os y
  cp : ∀ (l : Nat) (ins : List Nat) (o : Nat) (e : E), rules[l]? = some (Rule.comp ins o e) → CpI ins o e y
  br : ∀ (l c d t f : Nat), rules[l]? = some (Rule.branch c d t f) → BrI c d t f y
  mx : ∀ (l s : Nat) (ds : List Nat) (o iw : Nat), rules[l]? = some (Rule.mux s ds o iw) → MxI s ds o iw y
  np : ∀ c, produced c = false → y.pr c = []
  nc : ∀ c, consumed c = false → y.cn c = []

theorem good_exists {a b : Nat} (hd : dom a b) : ∃ y, Good a b y := by
  obtain ⟨n, hn⟩ := good_run a b hd
  obtain ⟨ls, hls⟩ := run_exec hn
  let x0 : TS := ⟨init a b, fun _ => [], fun _ => []⟩
  obtain ⟨y, hy, hys⟩ := texec_of_exec ls x0 _ hls
  have P : ∀ {P : TS → Prop}, Pres P → P x0 → P y := fun hP h0 => texec_pres hP ls x0 y hy h0
  refine ⟨y, hys, P (fifo_pres _) (fun c => by simp [x0]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l i os hr; exact P (fk_pres hr) (fun o _ => rfl)
  · intro l ins o e hr; exact P (cp_pres hr) ⟨0, fun _ _ => rfl, rfl⟩
  · intro l c d t f hr
    have := side_of hr; simp [sideOK] at this
    exact P (br_pres hr this) ⟨rfl, rfl, rfl⟩
  · intro l s ds o iw hr
    have := side_of hr; simp [sideOK] at this
    exact P (mx_pres hr this.1 this.2) ⟨rfl, fun j hj => by simp [x0] at hj, fun m _ => by simp [x0, cntm]⟩
  · intro c hc; exact P (np_pres c hc) rfl
  · intro c hc; exact P (nc_pres c hc) rfl

end Formal.Net.KCap
