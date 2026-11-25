import Formal.Net.KernelCapWalkRun

/-!
# Kernel-parametric: H_WALK proved, and the final theorem (from C-8s's CapstoneWalk)
-/


namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open KD KP

set_option linter.unusedSectionVars false

set_option maxRecDepth 100000

variable [KD] [KP]

/-! ## Table lemmas -/

theorem sp_mem {c : Fin NC} (h : sp c = true) : c.val ∈ spN := by
  have := List.all_eq_true.mp spN_chk c.val (List.mem_range.mpr c.isLt)
  simp only [sp] at h
  rw [h] at this; simpa using this

theorem recs_eq : recs = spN.map (fun n => (n, grpL.getD n 0, rhoL.getD n 0, adjL.getD n true,
    alL.getD n [])) := by
  have := recs_chk; simpa using this

theorem rec_mem {c : Fin NC} (h : sp c = true) : (c.val, grp c, rho c, adj c, al c) ∈ recs := by
  rw [recs_eq]; exact List.mem_map.mpr ⟨c.val, sp_mem h, rfl⟩

theorem glob {c : Fin NC} (h : sp c = true) :
    grp c ∈ spine ∧ (∀ g ∈ al c, g ∈ spine) ∧ (adj c = true → al c = [grp c]) := by
  have := List.all_eq_true.mp recs_glob _ (rec_mem h)
  simp only [Bool.and_eq_true, List.contains_eq_mem, decide_eq_true_eq, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', beq_iff_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  refine ⟨h1, h2, fun ha => ?_⟩
  rcases h3 with h3 | h3
  · rw [ha] at h3; cases h3
  · exact h3

theorem cOK_of {c : Fin NC} (h : sp c = true) : cOK c = true := by
  have := List.all_eq_true.mp cOK_chk c.val (sp_mem h)
  simpa [cOKn, c.isLt] using this

theorem noend {g : Nat} (hg : g ∈ spine) : g ≠ chEnd ∧ g ≠ chOut := by
  have := List.all_eq_true.mp spine_noend g hg
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at this
  exact this

/-! ## The visit-count relation -/

def A (x : TS) (c : Fin NC) : Nat := ((al c).map fun h => (x.cn h).length).sum

def dgc (dg : Option Nat) (h : Nat) : Nat := match dg with | some g => bn (h == g) | none => 0

theorem sum_dgc (x x' : TS) (dg : Option Nat) : ∀ (L : List Nat),
    (∀ h ∈ L, (x'.cn h).length = (x.cn h).length + dgc dg h) →
    (L.map fun h => (x'.cn h).length).sum = (L.map fun h => (x.cn h).length).sum + dcount dg L := by
  intro L
  induction L with
  | nil => intro _; cases dg <;> rfl
  | cons h L ih =>
    intro hL
    simp only [List.map_cons, List.sum_cons]
    rw [hL h (by simp), ih (fun h' hh => hL h' (by simp [hh]))]
    cases dg with
    | none => simp [dgc, dcount]
    | some g =>
      simp only [dgc, dcount, List.count_cons, bn]
      by_cases e : h = g
      · subst e; simp; omega
      · have : (h == g) = false := by simp [e]
        simp [this]; omega

theorem bn_map (o : Option (Fin NC)) (c' : Fin NC) :
    bn (o.map Fin.val == some c'.val) = bn (o == some c') := by
  cases o with
  | none => rfl
  | some d =>
    by_cases e : d = c'
    · subst e; simp
    · have h1 : (some d == some c') = false := by simp [e]
      have h2 : (d.val == c'.val) = false := by simpa [Fin.ext_iff] using e
      have h3 : (some d.val == some c'.val) = false := by
        simpa using (fun h => e (Fin.ext h) : ¬ d.val = c'.val)
      simp only [Option.map_some, h1, h3]

theorem trans_step {x x' : TS} {W : Fin NC → Nat} {c : Fin NC} {o : Option (Fin NC)}
    {dg : Option Nat}
    (hR : ∀ c', sp c' = true →
      W c' + bn (some c == some c') = A x c' + Bo (some (gr c)) (grp c') (rho c') (adj c'))
    (hT : transOK c o dg = true)
    (hcn : ∀ h ∈ spine, (x'.cn h).length = (x.cn h).length + dgc dg h) :
    ∀ c', sp c' = true → (W c' + bn (some c == some c')) + bn (o == some c') =
      A x' c' + Bo (o.map gr) (grp c') (rho c') (adj c') := by
  intro c' hc'
  have ht := List.all_eq_true.mp hT _ (rec_mem hc')
  simp only [transR, beq_iff_eq] at ht
  have hA : A x' c' = A x c' + dcount dg (al c') :=
    sum_dgc x x' dg _ (fun h hh => hcn h ((glob hc').2.1 h hh))
  rw [bn_map] at ht
  rw [hR c' hc', hA]
  omega

structure Rel (x : TS) (s : WS) : Prop where
  tok : ∀ c, s.cur = some c → x.s (grp c) ≠ []
  emp : s.cur = none → ∀ h ∈ spine, x.s h = []
  cnt : ∀ c', sp c' = true →
    s.W c' + bn (s.cur == some c') = A x c' + Bo (s.cur.map gr) (grp c') (rho c') (adj c')
  accl : s.cur = some acc → ∃ v, (x.pr cidx)[(x.cn cres).length]? = some v ∧ v % 4 ≠ 2

section walkrel
variable (σ : Fin NC → Nat → Nat)

theorem rel_next {x x' : TS} {p : Nat} {c : Fin NC} {o : Option (Fin NC)} {dg : Option Nat}
    (hc : (walk σ p).cur = some c) (hR : Rel x (walk σ p))
    (hn : nxt σ c ((walk σ p).W c) = o) (hT : transOK c o dg = true)
    (hcn : ∀ h ∈ spine, (x'.cn h).length = (x.cn h).length + dgc dg h)
    (htok : ∀ c', o = some c' → x'.s (grp c') ≠ [])
    (hemp : o = none → ∀ h ∈ spine, x'.s h = [])
    (hacc : o = some acc → ∃ v, (x'.pr cidx)[(x'.cn cres).length]? = some v ∧ v % 4 ≠ 2) :
    Rel x' (walk σ (p + 1)) := by
  have hcur : (walk σ (p + 1)).cur = o := by rw [cur_succ, hc]; simpa using hn
  refine ⟨fun c' h => htok c' (hcur ▸ h), fun h => hemp (hcur ▸ h), ?_, fun h => hacc (hcur ▸ h)⟩
  intro c' hc'
  have hR' : ∀ c', sp c' = true → (walk σ p).W c' + bn (some c == some c') =
      A x c' + Bo (some (gr c)) (grp c') (rho c') (adj c') := by
    intro c' hc'; have := hR.cnt c' hc'; rw [hc] at this; simpa using this
  rw [hcur, W_succ, visB_some σ hc]
  exact trans_step hR' hT hcn c' hc'

theorem rel_stay {x : TS} {p : Nat} {c o : Fin NC}
    (hc : (walk σ p).cur = some c) (hR : Rel x (walk σ p))
    (hn : nxt σ c ((walk σ p).W c) = some o) (hs : stayOK c o = true) :
    Rel x (walk σ (p + 1)) := by
  simp only [stayOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, and_assoc] at hs
  obtain ⟨-, hg, hna, hT⟩ := hs
  refine rel_next σ hc hR hn hT (fun h _ => by simp [dgc]) ?_ (by simp) ?_
  · intro c' e; cases e; rw [hg]; exact hR.tok c hc
  · intro e; cases e; exact absurd rfl hna

theorem stay_sp {c o : Fin NC} (hs : stayOK c o = true) : sp o = true := by
  simp only [stayOK, Bool.and_eq_true] at hs; exact hs.1.1.1

end walkrel

/-! ## The simulation -/

def OnPath (a b : Nat) (y : TS) (x : TS) : Prop := RI a b x ∧ ∃ ls, texec x ls = some y

theorem applyF_ne {s : Store Nat Nat} {f : Fire Nat Nat} {c : Nat} (h : f.2 c ≠ []) :
    applyF s f c ≠ [] := by
  simp only [applyF]; intro e; exact h (List.append_eq_nil_iff.mp e).2

theorem getD_of {L : List Nat} {n v : Nat} (h : L[n]? = some v) : n < L.length ∧ L.getD n 0 = v := by
  have hn : n < L.length := by
    rcases Nat.lt_or_ge n L.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h; cases h
  exact ⟨hn, by simp [List.getD_eq_getElem?_getD, h]⟩

theorem perL_of {L : List Nat} {n v : Nat} (d : Nat) (h : L[n]? = some v) : perL L d n = v := by
  obtain ⟨hn, hv⟩ := getD_of h
  have hne : L ≠ [] := by intro e; subst e; simp at hn
  simp [perL, hne, Nat.mod_eq_of_lt hn, h]

theorem idx_app {L t : List Nat} {v : Nat} : (L ++ [v] ++ t)[L.length]? = some v := by
  simp

section sim
variable {a b : Nat} {y : TS} (hy : Good a b y)
include hy

theorem y_emp {g : Nat} (hg : g ∈ spine) : y.s g = [] := by
  rw [hy.fin]; exact final_empty _ g (noend hg).1 (noend hg).2

/-- The run's next spine-moving firing from `x` (token on `g`) is rule `l0`. -/
theorem move_run {x : TS} (hx : OnPath a b y x) {g : Nat} (hg : g ∈ spine) (hne : x.s g ≠ [])
    {l0 : Nat} {r0 : Rule} (hr0 : rules[l0]? = some r0) (hg0 : g ∈ r0.insL)
    (hm : ∀ s ds o iw, r0 ≠ .mux s ds o iw) :
    ∃ x2 x3, RI a b x2 ∧ (∀ h ∈ spine, x2.s h = x.s h ∧ x2.cn h = x.cn h) ∧
      tstep x2 l0 = some x3 ∧ OnPath a b y x3 ∧ texec x2 [l0] = some x3 ∧
      (∃ ls, texec x3 ls = some y) ∧
      ∀ h ∈ spine, (x3.cn h).length = (x.cn h).length + dgc (some g) h := by
  obtain ⟨hRI, ls, hls⟩ := hx
  obtain ⟨x2, l, x3, ls4, h2, hsp, h3, h4, r, hr, hgr⟩ := next_fire hg (y_emp hy hg) ls x hRI hne hls
  have hl : l = l0 := by
    by_cases e : l = l0
    · exact e
    · exact (ins_disj hr hr0 e hgr hg0).elim
  subst hl
  rw [hr] at hr0; cases hr0
  have hne2 : x2.s g ≠ [] := by rw [(hsp g hg).1]; exact hne
  refine ⟨x2, x3, h2, hsp, h3, ⟨ri_pres a b x2 _ x3 h3 h2, ls4, h4⟩, by simp [texec, h3], ⟨ls4, h4⟩, ?_⟩
  intro h hh
  rw [fire_cn h2 hg hne2 h3 hr hgr hm h hh, (hsp h hh).2]
  rfl

theorem texec_two {x2 x3 : TS} {l : Nat} {ls : List Nat} (h1 : tstep x2 l = some x3)
    (h2 : texec x3 ls = some y) : texec x2 (l :: ls) = some y := by
  simp [texec, h1, h2]

theorem cm_idx {x x2 : TS} {g res idx l0 i kk : Nat} (hR2 : RI a b x2)
    (hr0 : rules[l0]? = some (Rule.cm i res idx kk)) (hres : res ∈ spine) (h3 : nIn ≤ res)
    (hg : g ∈ spine) (hne : x.s g ≠ []) (hgr : res ≠ g) (hRx : GcdHw.Inv spine x.s)
    (hsp : ∀ h ∈ spine, x2.s h = x.s h ∧ x2.cn h = x.cn h) :
    (x2.pr idx).length = (x.cn res).length := by
  rw [hR2.cml _ _ _ _ _ hr0]
  have hf := hR2.fifo res
  rw [init_empty a b res h3, List.nil_append] at hf
  rw [hf, List.length_append, (hsp res hres).1, (hsp res hres).2,
    only_tok hRx hg hres hne hgr]
  simp

omit hy in
theorem condOK_spec {c : Fin NC} {gc : Nat} (h : condOK c gc = true) :
    ∃ cc dd d0, tab.d c.val = .bj (.var 0) (.lit 0) [cc, dd] ∧ tab.d cc = .hist gc d0 := by
  unfold condOK at h
  split at h
  · rename_i ec ed cc dd hd
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, h⟩ := h
    split at h
    · rename_i h0 d0 hh
      simp only [beq_iff_eq] at h; subst h; exact ⟨cc, dd, d0, hd, hh⟩
    · simp at h
  · simp at h

theorem sel_eq {c : Fin NC} {gc : Nat} (hcond : condOK c gc = true) (h3 : gc ≠ chEnd) (h250 : gc ≠ chOut)
    {k v : Nat} (hk : (y.cn gc)[k]? = some v) : sel2 (σY a b y c k) = (v % 2 == 1) := by
  obtain ⟨cc, dd, d0, hd, hh⟩ := condOK_spec hcond
  simp only [σY]
  rw [ref_bj tab _ rank_ok hd (by simp) k]
  simp only [List.map_cons, List.map_nil, E.eval, List.getD_cons_zero]
  rw [ref_hist tab _ hh nf_pos, Hh_cn hy h3 h250, perL_of d0 hk]
  simp [sel2]

omit hy in
theorem W_cur {x : TS} {p : Nat} {c : Fin NC} (hsp : sp c = true) (ha : adj c = true)
    (hcnt : ∀ c', sp c' = true → (walk (σY a b y) p).W c' + bn (some c == some c') =
      A x c' + Bo (some (gr c)) (grp c') (rho c') (adj c')) :
    (walk (σY a b y) p).W c = (x.cn (grp c)).length := by
  have h := hcnt c hsp
  rw [show A x c = (x.cn (grp c)).length by simp [A, (glob hsp).2.2 ha]] at h
  simp [Bo, gr, bn, ha] at h
  omega

omit hy in
theorem W_other {x : TS} {p : Nat} {c z : Fin NC} (hsz : sp z = true) (hgz : grp z ≠ grp c)
    (hcnt : ∀ c', sp c' = true → (walk (σY a b y) p).W c' + bn (some c == some c') =
      A x c' + Bo (some (gr c)) (grp c') (rho c') (adj c')) :
    (walk (σY a b y) p).W z = A x z := by
  have h := hcnt z hsz
  have hcz : c ≠ z := by intro e; subst e; exact hgz rfl
  have e1 : (some c == some z) = false := by simp [hcz]
  simp [Bo, gr, bn, e1, hgz] at h
  exact h

theorem step_main (p : Nat) (x : TS) (hx : OnPath a b y x) (hR : Rel x (walk (σY a b y) p))
    (c : Fin NC) (hc : (walk (σY a b y) p).cur = some c) :
    (∃ x', OnPath a b y x' ∧ Rel x' (walk (σY a b y) (p + 1))) ∧
    (∀ xx yy z w, opAt (consOf c) = .amerge xx yy z w →
      omOf a b y w ((walk (σY a b y) p).W z) = decide (c = yy)) := by
  have hsp : sp c = true := cur_sp _ p c hc
  have hok := cOK_of hsp
  have hg := (glob hsp).1
  have hne := hR.tok c hc
  have hcnt := hR.cnt
  rw [hc] at hcnt
  simp only [Option.map_some] at hcnt
  have hIx : GcdHw.Inv spine x.s := hx.1.inv
  unfold cOK at hok
  cases hop : opAt (consOf c) with
  | link i o =>
    simp only [hop] at hok
    have hn : nxt (σY a b y) c ((walk (σY a b y) p).W c) = some o := by
      simp [nxt, hop, stay_sp hok]
    exact ⟨⟨x, hx, rel_stay _ hc hR hn hok⟩, fun _ _ _ _ h => by cases h⟩
  | bjoin ins o ec ed =>
    simp only [hop] at hok
    have hn : nxt (σY a b y) c ((walk (σY a b y) p).W c) = some o := by
      simp [nxt, hop, stay_sp hok]
    exact ⟨⟨x, hx, rel_stay _ hc hR hn hok⟩, fun _ _ _ _ h => by cases h⟩
  | forkG i os =>
    simp only [hop] at hok
    cases hf : os.find? sp with
    | none => rw [hf] at hok; simp at hok
    | some o =>
      rw [hf] at hok
      have hn : nxt (σY a b y) c ((walk (σY a b y) p).W c) = some o := by simp [nxt, hop, hf]
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hok
      rcases hok with hs | ⟨hT, hF⟩
      · exact ⟨⟨x, hx, rel_stay _ hc hR hn hs⟩, fun _ _ _ _ h => by cases h⟩
      · unfold forkR at hF
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, and_assoc] at hF
        obtain ⟨hna, hgo, hF⟩ := hF
        cases hr : rules[lc c]? with
        | none => rw [hr] at hF; simp at hF
        | some r =>
          rw [hr] at hF
          cases r with
          | fork i0 hs =>
            simp only [Bool.and_eq_true, beq_iff_eq] at hF
            obtain ⟨hi0, hfil⟩ := hF
            obtain ⟨x2, x3, hR2, hsp2, h3, hx3, -, -, hcn⟩ :=
              move_run hy hx hg hne hr (by simp [Rule.insL, hi0]) (by intros; simp)
            refine ⟨⟨x3, hx3, rel_next _ hc hR hn hT hcn ?_ (by simp) (fun e => absurd (Option.some.inj e) hna)⟩,
              fun _ _ _ _ h => by cases h⟩
            intro c' e; cases e
            obtain ⟨f, hff, hs3, -, -⟩ := tstep_some h3
            rw [hs3]; apply applyF_ne
            obtain ⟨vs, out, hh, hout, rfl⟩ := fire_strict hr (by intros; simp) hff
            simp only [Rule.insL] at hh
            obtain ⟨e1, -⟩ := heads_one hh
            simp only [Rule.out, Option.some.injEq] at hout; subst hout; subst e1
            have hm : grp o ∈ hs := by
              have : grp o ∈ hs.filter (fun h => spine.contains h) := by rw [hfil]; simp
              exact (List.mem_filter.mp this).1
            simp [hm]
          | cm i0 res idx kk =>
            simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hF
            obtain ⟨hi0, hres, -⟩ := hF
            obtain ⟨x2, x3, hR2, hsp2, h3, hx3, -, -, hcn⟩ :=
              move_run hy hx hg hne hr (by simp [Rule.insL, hi0]) (by intros; simp)
            refine ⟨⟨x3, hx3, rel_next _ hc hR hn hT hcn ?_ (by simp) (fun e => absurd (Option.some.inj e) hna)⟩,
              fun _ _ _ _ h => by cases h⟩
            intro c' e; cases e
            obtain ⟨f, hff, hs3, -, -⟩ := tstep_some h3
            rw [hs3]; apply applyF_ne
            obtain ⟨-, -, e2⟩ := fire_cm hr hff
            rw [e2]; simp [hres]
          | _ => simp at hF
  | steerC j t f =>
    simp only [hop] at hok
    simp only [Bool.and_eq_true, and_assoc] at hok
    obtain ⟨hst, hTt, hTf, hS⟩ := hok
    unfold steerR at hS
    cases hr : rules[lc c]? with
    | none => rw [hr] at hS; simp at hS
    | some r =>
      rw [hr] at hS
      cases r with
      | branch gc gd gt gf =>
        simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
          List.contains_eq_mem, decide_eq_false_iff_not, and_assoc] at hS
        obtain ⟨hadj, hgd, hgt, hgf, -, -, hc3, hc250, hcond, hta, hfa, -, -⟩ := hS
        subst hgd
        obtain ⟨x2, x3, hR2, hsp2, h3, hx3, h23, ⟨ls4, h4⟩, hcn⟩ :=
          move_run hy hx hg hne hr (by simp [Rule.insL]) (by intros; simp)
        obtain ⟨ff, hff, hs3, -, -⟩ := tstep_some h3
        obtain ⟨vs, out, hh, hout, rfl⟩ := fire_strict hr (by intros; simp) hff
        simp only [Rule.insL] at hh
        obtain ⟨e1, e2⟩ := heads_spec hh
        simp only [List.map_cons, List.map_nil] at e1
        subst e1
        simp only [Rule.out, natVI, Option.map_some, Option.some.injEq] at hout
        subst hout
        -- the cond token is the final cond history's entry at the walk's visit count
        have hW := W_cur hsp hadj hcnt
        have hlen : (x2.cn gc).length = (x.cn (grp c)).length := by
          rw [(hR2.br _ _ _ _ _ hr).1, (hsp2 _ hg).2]
        have hyc : y.s gc = [] := by rw [hy.fin]; exact final_empty _ gc hc3 hc250
        obtain ⟨tt, htt⟩ := cn_pre hR2.fifo hy.fifo hyc
          (texec_pre _ x2 y (texec_two hy h3 h4) gc).1
        have hgc : (x2.s gc).take 1 = [(x2.s gc).headD 0] := e2 gc (by simp)
        have hkv : (y.cn gc)[(walk (σY a b y) p).W c]? = some ((x2.s gc).headD 0) := by
          rw [hW, ← hlen, htt]
          cases hx2 : x2.s gc with
          | nil => rw [hx2] at hgc; simp at hgc
          | cons v vs => simp
        have hsel := sel_eq hy hcond hc3 hc250 hkv
        have hn : nxt (σY a b y) c ((walk (σY a b y) p).W c) =
            some (bif ((x2.s gc).headD 0 % 2 == 1) then t else f) := by
          simp only [nxt, hop, hst, ite_true, hsel]
        refine ⟨⟨x3, hx3, ?_⟩, fun _ _ _ _ h => by cases h⟩
        cases hb : ((x2.s gc).headD 0 % 2 == 1)
        · have hb2 : ¬((x2.s gc).head?.getD 0 % 2 = 1) := by simpa using hb
          rw [hb] at hn
          refine rel_next _ hc hR hn hTf hcn ?_ (by simp) (fun e => absurd (Option.some.inj e) hfa)
          intro c' e; cases e
          rw [hs3]; apply applyF_ne
          simp [hb2, hgf]
        · have hb2 : (x2.s gc).head?.getD 0 % 2 = 1 := by simpa using hb
          rw [hb] at hn
          refine rel_next _ hc hR hn hTt hcn ?_ (by simp) (fun e => absurd (Option.some.inj e) hta)
          intro c' e; cases e
          rw [hs3]; apply applyF_ne
          simp [hb2, hgt]
      | _ => simp at hS
  | amerge xx yy z w =>
    simp only [hop] at hok
    have hn : nxt (σY a b y) c ((walk (σY a b y) p).W c) = some z := by simp [nxt, hop]
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hok
    rcases hok with ⟨hs, hA⟩ | ⟨hT, hM⟩
    · -- inside the cascade group cres: acc → z
      refine ⟨⟨x, hx, rel_stay _ hc hR hn hs⟩, ?_⟩
      intro xx' yy' z' w' e
      injection e with e1 e2 e3 e4
      subst e1 e2 e3 e4
      simp only [accOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, and_assoc] at hA
      obtain ⟨hca, hcx, hxy, halz, hw, hB⟩ := hA
      have hza : z ≠ acc := by
        simp only [stayOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs; exact hs.1.2
      have hsz := stay_sp hs
      have hWz : (walk (σY a b y) p).W z = (x.cn cres).length := by
        have h := hcnt z hsz
        have e1 : (some c == some z) = false := by simp; intro e; subst e; exact hza hca
        rw [e1, hB, show A x z = (x.cn cres).length by simp [A, halz]] at h
        simpa [bn] using h
      obtain ⟨v, hv, hv4⟩ := hR.accl (hc.trans (by rw [hca]))
      obtain ⟨-, ls, hls⟩ := hx
      obtain ⟨tt, htt⟩ := (texec_pre ls x y hls cidx).1
      have hyv : (y.pr cidx)[(x.cn cres).length]? = some v := by
        rw [htt]; exact (List.getElem?_append_left (getD_of hv).1).trans hv
      show (tab.w w).om (Hh a b y) _ = _
      rw [hw, hWz]
      simp only [W.om]
      rw [Hh_pr idx_ge, perL_of 0 hyv]
      have : c ≠ yy := by rw [hcx]; exact hxy
      simp [hv4, this]
    · -- arrival at an arbiter stage from another group: the run's next firing is its cm rule
      unfold amR at hM
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, and_assoc] at hM
      obtain ⟨hsz, hgz, hM⟩ := hM
      cases hr : rules[lc c]? with
      | none => rw [hr] at hM; simp at hM
      | some r =>
        rw [hr] at hM
        cases r with
        | cm i res idx kk =>
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true',
            List.contains_eq_mem, decide_eq_false_iff_not, decide_eq_true_eq, and_assoc] at hM
          obtain ⟨hi, hres, hidx, hri, hidx3, hres3, hidx250, hacc, hlab⟩ := hM
          subst hi; subst hres
          obtain ⟨x2, x3, hR2, hsp2, h3, hx3, h23, ⟨ls4, h4⟩, hcn⟩ :=
            move_run hy hx hg hne hr (by simp [Rule.insL]) (by intros; simp)
          obtain ⟨ff, hff, hs3, -, hp3⟩ := tstep_some h3
          obtain ⟨-, -, e2⟩ := fire_cm hr hff
          have hgzs := (glob hsz).1
          have hzg : grp z ≠ grp c := hgz
          have hidxL := cm_idx hy hR2 hr hgzs hres3 hg hne hzg hIx hsp2
          have hp3i : x3.pr idx = x2.pr idx ++ [kk] := by
            rw [hp3, e2]; simp [Ne.symm hri]
          obtain ⟨tt, htt⟩ := (texec_pre ls4 x3 y h4 idx).1
          have hyk : (y.pr idx)[(x2.pr idx).length]? = some kk := by
            rw [htt, hp3i]; simp
          have hWz := W_other hsz hgz hcnt
          refine ⟨⟨x3, hx3, rel_next _ hc hR hn hT hcn ?_ (by simp) ?_⟩, ?_⟩
          · intro c' e; cases e
            rw [hs3]; apply applyF_ne
            rw [e2]; simp
          · intro e; cases e
            simp only [true_and, Bool.or_eq_true, bne_iff_ne, ne_eq, not_true_eq_false, false_or,
              Bool.and_eq_true, beq_iff_eq] at hacc
            obtain ⟨⟨hr251, hi249⟩, hk4⟩ := hacc
            refine ⟨kk, ?_, by simpa using hk4⟩
            subst hi249
            rw [hp3i]
            have : (x3.cn cres).length = (x2.pr cidx).length := by
              rw [hidxL, ← hr251, hcn _ hgzs]
              simp [dgc, bn, hzg]
            rw [this]; simp
          · intro xx' yy' z' w' e
            injection e with e1 e2' e3 e4
            subst e1 e2' e3 e4
            show (tab.w w).om (Hh a b y) _ = _
            rw [hWz]
            cases hw : tab.w w with
            | lab2 gi =>
              rw [hw] at hlab
              simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hlab
              obtain ⟨hgi, halz, hkk⟩ := hlab
              subst hgi
              have hA : A x z = (x2.pr gi).length := by rw [hidxL]; simp [A, halz]
              simp only [W.om]
              rw [hA, Hh_pr hidx3, perL_of 0 hyk, hkk]
              by_cases e : c = yy <;> simp [e, bn]
            | lo3 gi =>
              rw [hw] at hlab
              simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hlab
              obtain ⟨hgi, hidx', halz, hkk⟩ := hlab
              subst hgi; subst hidx'
              have hA : A x z = ((x2.pr cidx).filter (fun v => v % 4 != 2)).length := by
                rw [hR2.lab, (hsp2 cq1 cq1_sp).2, (hsp2 cq2 cq2_sp).2]
                simp [A, halz]
              have hk4 : (kk % 4 != 2) = true := by
                rw [hkk]; by_cases e : c = yy <;> simp [e, bn]
              have hyf : ((y.pr cidx).filter (fun v => v % 4 != 2))[
                  ((x2.pr cidx).filter (fun v => v % 4 != 2)).length]? = some kk := by
                rw [htt, hp3i, List.filter_append, List.filter_append]
                simp [hk4]
              simp only [W.om]
              rw [hA, Hh_pr idx_ge, perL_of 0 hyf, hkk]
              by_cases e : c = yy <;> simp [e, bn]
            | hi3 gi =>
              rw [hw] at hlab
              simp only [Bool.and_eq_true, beq_iff_eq, and_assoc] at hlab
              obtain ⟨hgi, halz, hcy, hkk⟩ := hlab
              subst hgi; subst hkk
              have hA : A x z = (x2.pr gi).length := by rw [hidxL]; simp [A, halz]
              simp only [W.om]
              rw [hA, Hh_pr hidx3, perL_of 0 hyk]
              simp [hcy]
        | _ => simp at hM
  | sink i =>
    simp only [hop] at hok
    simp only [Bool.and_eq_true, sinkR, beq_iff_eq] at hok
    obtain ⟨hT, hr⟩ := hok
    have hn : nxt (σY a b y) c ((walk (σY a b y) p).W c) = none := by simp [nxt, hop]
    obtain ⟨x2, x3, hR2, hsp2, h3, hx3, -, -, hcn⟩ :=
      move_run hy hx hg hne hr (by simp [Rule.insL]) (by intros; simp)
    refine ⟨⟨x3, hx3, rel_next _ hc hR hn hT hcn (by simp) ?_ (by simp)⟩,
      fun _ _ _ _ h => by cases h⟩
    intro _ h hh
    obtain ⟨ff, hff, hs3, -, -⟩ := tstep_some h3
    obtain ⟨vs, out, -, hout, rfl⟩ := fire_strict hr (by intros; simp) hff
    simp only [Rule.out, Option.some.injEq] at hout; subst hout
    rw [hs3]; simp only [applyF, List.append_nil]
    by_cases e : h = grp c
    · subst e
      obtain ⟨v, hv⟩ := tok_one hR2.inv hg (by rw [(hsp2 _ hg).1]; exact hne)
      simp [popOf, Rule.insL, hv]
    · rw [(hsp2 h hh).1, only_tok hIx hg hh hne e]; simp
  | _ => simp only [hop] at hok; simp at hok

omit hy in
theorem A_x0 (c : Fin NC) : A (x0 a b) c = 0 := by
  unfold A
  induction al c with
  | nil => rfl
  | cons h L ih => simp only [List.map_cons, List.sum_cons]; simpa [x0] using ih

theorem rel_x0 : Rel (x0 a b) (walk (σY a b y) 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c h
    simp only [walk, Option.some.injEq] at h; subst h
    rw [grp_start]
    show init a b (nIn - 1) ≠ []
    rw [init_start]; simp
  · intro h; simp [walk] at h
  · intro c' hc'
    show 0 + bn (some start == some c') = A (x0 a b) c' + Bo (some (gr start)) (grp c') (rho c') (adj c')
    rw [A_x0]
    have := List.all_eq_true.mp init_chk _ (rec_mem hc')
    simp only [beq_iff_eq] at this
    have hgs : gr start = (nIn - 1, rhoL.getD start.val 0) := by rw [gr, grp_start]; rfl
    rw [hgs, ← this]
    by_cases e : c' = start
    · subst e; simp
    · have e1 : (some start == some c') = false := by simp [Ne.symm e]
      have e2 : (c'.val == start.val) = false := by
        simp; intro h; exact e (Fin.ext h)
      rw [e1, e2]
  · intro h; simp [walk] at h; exact absurd h start_acc

/-- **The simulation**: every walk step is matched by a state of the run on its path. -/
theorem walk_sim {ls : List Nat} (hex : texec (x0 a b) ls = some y) :
    ∀ p, ∃ x, OnPath a b y x ∧ Rel x (walk (σY a b y) p) := by
  intro p
  induction p with
  | zero => exact ⟨x0 a b, ⟨ri_x0 a b, ls, hex⟩, rel_x0 hy⟩
  | succ p ih =>
    obtain ⟨x, hx, hR⟩ := ih
    cases hc : (walk (σY a b y) p).cur with
    | none =>
      have : walk (σY a b y) (p + 1) = walk (σY a b y) p := by
        show wstep _ (walk (σY a b y) p) = _
        unfold wstep; rw [hc]
      exact ⟨x, hx, this ▸ hR⟩
    | some c => exact (step_main hy p x hx hR c hc).1

theorem walk_ok {ls : List Nat} (hex : texec (x0 a b) ls = some y) :
    WalkOK (σY a b y) (omOf a b y) := by
  intro p d xx yy z w hd hop
  obtain ⟨x, hx, hR⟩ := walk_sim hy hex p
  exact (step_main hy p x hx hR d hd).2 xx yy z w hop

end sim

/-! ## The results -/

/-- A complete traced token run from `init a b`, with the run itself (C-8m's `good_exists`,
keeping the schedule). -/
theorem good_run' {a b : Nat} (hd : dom a b) :
    ∃ y ls, Good a b y ∧ texec (x0 a b) ls = some y := by
  obtain ⟨n, hn⟩ := good_run a b hd
  obtain ⟨ls, hls⟩ := run_exec hn
  obtain ⟨y, hy, hys⟩ := texec_of_exec ls (x0 a b) _ hls
  have P : ∀ {P : TS → Prop}, Pres P → P (x0 a b) → P y :=
    fun hP h0 => texec_pres hP ls (x0 a b) y hy h0
  refine ⟨y, ls, ⟨hys, P (fifo_pres _) (fun c => by simp [x0]), ?_, ?_, ?_, ?_, ?_, ?_⟩, hy⟩
  · intro l i os hr; exact P (fk_pres hr) (fun o _ => rfl)
  · intro l ins o e hr; exact P (cp_pres hr) ⟨0, fun _ _ => rfl, rfl⟩
  · intro l c d t f hr
    have := side_of hr; simp [sideOK] at this
    exact P (br_pres hr this) ⟨rfl, rfl, rfl⟩
  · intro l s ds o iw hr
    have := side_of hr; simp [sideOK] at this
    exact P (mx_pres hr this.1 this.2) ⟨rfl, fun j hj => by simp [x0] at hj,
      fun m _ => by simp [x0, cntm]⟩
  · intro c hc; exact P (np_pres c hc) rfl
  · intro c hc; exact P (nc_pres c hc) rfl

/-- **H_WALK, proved** for every input in `dom`. -/
theorem kernel_walk (a b : Nat) (hd : dom a b) :
    ∃ y, Good a b y ∧ WalkOK (σY a b y) (omOf a b y) := by
  obtain ⟨y, ls, hy, hex⟩ := good_run' hd
  exact ⟨y, hy, walk_ok hy hex⟩

/-- **Circuit-level safety of the kernel from the gate models, bundling and a one-invocation
environment only**: for `dom a b`, every run of the concrete network whose
operators meet their gate models (H_CELLS), whose channels are bundled (H_BUNDLE) and whose
`start` channel is offered at most once (H_START_ONCE) latches only `spec a b` on `out0`. -/
theorem kernel_circuit_safe3 (a b : Nat) (hd : dom a b) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (spec a b)) :=
  kernel_circuit_safe'' a b ch H_CELLS H_BUNDLE H_START_ONCE (kernel_walk a b hd)

/-- H_CM_FORCED without H_WALK: every arbiter stage's winner is the token run's label. -/
theorem kernel_forced3 (a b : Nat) (hd : dom a b) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o) := by
  obtain ⟨y, hy, hw⟩ := kernel_walk a b hd
  exact ⟨y, hy, kernel_forced a b ch y hy H_CELLS H_BUNDLE H_START_ONCE hw⟩

/-- No free contention at any arbiter stage, without H_WALK. -/
theorem kernel_arbiters_uncontended3 (a b : Nat) (hd : dom a b)
    (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (o : Fin NO) (x u z : Fin NC) (w : Nat) (ho : opAt o = .amerge x u z w)
    (g1 g2 : Trace) (M : CM.AMerge (ch x) (ch u) (ch z) g1 g2) :
    ∀ t, (ch x).req t = true → (ch u).req t = true → g1 t = true ∨ g2 t = true := by
  obtain ⟨y, hy, hw⟩ := kernel_walk a b hd
  exact kernel_arbiters_uncontended' a b ch H_CELLS H_BUNDLE H_START_ONCE y hy hw o x u z w ho g1 g2 M

end Formal.Net.KCap
