import Formal.Net.KernelCapCutSpine

/-!
# Kernel-parametric: H_CUT from H_START_ONCE and H_WALK (from C-8r's CapstoneCut)
-/


namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open KD KP

set_option linter.unusedSectionVars false
open Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut

set_option maxRecDepth 100000

variable [KD] [KP]

/-- The stream solution of 8m (O2) on circuit channels. -/
def σY (a b : Nat) (y : TS) : Fin NC → Nat → Nat := fun c i => refT tab (Hh a b y) c.val i

theorem find_one {l : List (Fin NC)} {c : Fin NC} (hl : (l.filter sp).length = 1) (hc : c ∈ l)
    (hs : sp c = true) : l.find? sp = some c := by
  cases hf : l.find? sp with
  | none => have := List.find?_eq_none.mp hf c hc; simp [hs] at this
  | some e =>
    have he : e ∈ l.filter sp := List.mem_filter.mpr ⟨List.mem_of_find?_eq_some hf, List.find?_some hf⟩
    have hc' : c ∈ l.filter sp := List.mem_filter.mpr ⟨hc, hs⟩
    obtain ⟨u, hu⟩ := List.length_eq_one_iff.mp hl
    rw [hu] at he hc'
    simp at he hc'
    rw [he, hc']

theorem off_before {c : Chan} {k r i r' : Nat} (h : OffAt c k r) (h' : OffAt c i r') (hi : i < k) :
    r' < r := by
  rcases Nat.lt_or_ge r' r with hl | hl
  · exact hl
  · have := cnt_mono (riseB c.req) hl; rw [h.2, h'.2] at this; omega

section
variable (σ : Fin NC → Nat → Nat)

theorem nxt_link {d i o : Fin NC} {k : Nat} (h : opAt (consOf d) = .link i o) (hs : sp o = true) :
    nxt σ d k = some o := by
  simp only [nxt, h, hs, ite_true]

theorem nxt_forkG {d i : Fin NC} {os : List (Fin NC)} {k : Nat} (h : opAt (consOf d) = .forkG i os) :
    nxt σ d k = os.find? sp := by
  simp only [nxt, h]

theorem nxt_bjoin {d o : Fin NC} {ins : List (Fin NC)} {ec ed : E} {k : Nat}
    (h : opAt (consOf d) = .bjoin ins o ec ed) (hs : sp o = true) : nxt σ d k = some o := by
  simp only [nxt, h, hs, ite_true]

theorem nxt_steerC {d j t f : Fin NC} {k : Nat} (h : opAt (consOf d) = .steerC j t f) (hs : sp t = true) :
    nxt σ d k = some (bif sel2 (σ d k) then t else f) := by
  simp only [nxt, h, hs, ite_true]

theorem nxt_amerge {d x u z : Fin NC} {w k : Nat} (h : opAt (consOf d) = .amerge x u z w) :
    nxt σ d k = some z := by
  simp only [nxt, h]

/-- Transitions into a channel produced by a one-spine-input operator (link, fork, bjoin). -/
theorem hin_one {c i : Fin NC} (hins : ∀ d, sp d = true → d ∈ (opAt (prodOf c)).insC → d = i)
    (hi : i ∈ (opAt (prodOf c)).insC) (hn : ∀ k, nxt σ i k = some c) :
    ∀ d k, sp d = true → (nxt σ d k = some c ↔ d = i) := by
  intro d k hs
  constructor
  · intro h; exact hins d hs (nxt_in σ h)
  · intro h; subst h; exact hn k

end

/-- `start` is never re-entered by the walk. -/
theorem tr_start (σ : Fin NC → Nat → Nat) (p : Nat) : cnt (tr σ start) p = 0 := by
  have : ∀ q, tr σ start q = false := by
    intro q
    cases h : (walk σ q).cur with
    | none => exact tr_none σ h
    | some d =>
      rw [tr_some σ h]
      cases hn : nxt σ d ((walk σ q).W d) == some start
      · rfl
      · have := nxt_in σ (c := d) (by simpa using hn)
        rw [prod_start] at this; simp [K.insC] at this
  induction p with
  | zero => rfl
  | succ p ih => rw [cnt_succ', ih, this]; rfl

theorem cur_of_bound (σ : Fin NC → Nat → Nat) {c : Fin NC} {p : Nat} (hcs : c ≠ start)
    (hb : (walk σ p).W c + 1 ≤ cnt (tr σ c) p) : (walk σ p).cur = some c := by
  have hf := flow σ p c
  have h0 : (c == start) = false := by simp [hcs]
  rw [h0] at hf
  cases h : ((walk σ p).cur == some c)
  · rw [h] at hf; simp [bn] at hf; omega
  · simpa using h

theorem ne_start {c : Fin NC} (h : ∀ z w d, opAt (prodOf c) ≠ .src z w d) : c ≠ start := by
  intro e; subst e; exact h _ _ _ prod_start

/-! ## The hypotheses -/

section
variable (a b : Nat) (ch : Fin NC → Chan) (y : TS)

/-- The circuit's offer counts on the spine are the walk's visit counts after `p` steps. -/
def Inv (t : Nat) : Prop :=
  ∃ p, ∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) p).W c

/-- Every arbiter offer before `t` has the oracle's winner. -/
def ForcB (t : Nat) : Prop :=
  ∀ o x u z w, opAt o = .amerge x u z w → ∀ k r, r < t → OffAt (ch z) k r →
    CM.winner (ch z) k = omOf a b y w k

end

section main
variable {a b : Nat} {ch : Fin NC → Chan} {y : TS}
variable (hy : Good a b y)
variable (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
variable (H_BUNDLE : ∀ c, Held (ch c))
variable (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
variable (H_WALK : WalkOK (σY a b y) (omOf a b y))

include H_WALK in
/-- The arbiter's input counts along the walk (`am_side` instantiated). -/
theorem am_counts {o : Fin NO} {x u z : Fin NC} {w : Nat} (ho : opAt o = .amerge x u z w) (p : Nat) :
    (walk (σY a b y) p).W u = cnt (omOf a b y w) ((walk (σY a b y) p).W z) +
        bn (((walk (σY a b y) p).cur == some z) && omOf a b y w ((walk (σY a b y) p).W z)) ∧
      (walk (σY a b y) p).W x = cnt (fun i => !omOf a b y w i) ((walk (σY a b y) p).W z) +
        bn (((walk (σY a b y) p).cur == some z) && !omOf a b y w ((walk (σY a b y) p).W z)) := by
  have hs := spok o
  rw [ho] at hs
  simp only [SpOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  have hd := ops_ok o
  rw [ho] at hd
  have hzo : prodOf z = o := prod_out o z (by rw [ho]; simp [K.outsC])
  have hxo : consOf x = o := cons_in o x (by rw [ho]; simp [K.insC])
  have huo : consOf u = o := cons_in o u (by rw [ho]; simp [K.insC])
  apply am_side (σY a b y) (omOf a b y w) hs.2 (Ne.symm hd.2.1) (Ne.symm hd.2.2)
  · exact ne_start (by intro z' w' d'; rw [hzo, ho]; simp)
  · intro d k hsd
    constructor
    · intro h
      have := nxt_in _ h
      rw [hzo, ho] at this; simpa [K.insC] using this
    · intro h
      rcases h with h | h <;> subst h
      · exact nxt_amerge _ (by rw [hxo, ho])
      · exact nxt_amerge _ (by rw [huo, ho])
  · intro p d h hd'
    apply H_WALK p d x u z w h
    rcases hd' with e | e <;> subst e
    · rw [hxo, ho]
    · rw [huo, ho]

include H_CELLS H_BUNDLE H_WALK in
/-- Forcing at time `t`, from `Inv t` and the forcing before `t`. -/
theorem forc_at (t : Nat) (hinv : Inv a b ch y t) (hf : ForcB a b ch y t) : ForcB a b ch y (t + 1) := by
  intro o x u z w ho k r hr hoff
  rcases Nat.lt_or_ge r t with hlt | hge
  · exact hf o x u z w ho k r hlt hoff
  have hrt : r = t := by omega
  subst hrt
  have hp := kernel_protocol a b ch H_CELLS H_BUNDLE
  obtain ⟨p, hp'⟩ := hinv
  have hs := spok o
  rw [ho] at hs
  simp only [SpOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  have hc := H_CELLS o
  rw [ho] at hc
  obtain ⟨g1, g2, M⟩ := hc
  obtain ⟨py, px⟩ := offer_pending M (hp x) (hp u) (hp z) hoff
  have hk : cnt (riseB (ch z).req) r = k := hoff.2
  have hpre : ∀ i, i < k → CM.winner (ch z) i = omOf a b y w i := by
    intro i hi
    obtain ⟨r', hr'⟩ := Capstone.offered_below hoff hi
    exact hf o x u z w ho i r' (off_before hoff hr' hi) hr'
  have c1 : cnt (CM.winner (ch z)) k = cnt (omOf a b y w) k := CM.cnt_congr_lt k hpre
  have c0 : cnt (fun i => !CM.winner (ch z) i) k = cnt (fun i => !omOf a b y w i) k :=
    CM.cnt_congr_lt k (fun i hi => by rw [hpre i hi])
  obtain ⟨ey, ex⟩ := am_counts H_WALK ho p
  have hzk : (walk (σY a b y) p).W z = k := by rw [← hp' z hs.1.2, hk]
  rw [hzk] at ey ex
  rw [← hp' u hs.1.1.2] at ey
  rw [← hp' x hs.1.1.1] at ex
  cases hwk : CM.winner (ch z) k
  · have := px hwk; rw [c0] at this
    cases hω : omOf a b y w k
    · rfl
    · rw [hω] at ex; simp [bn] at ex; omega
  · have := py hwk; rw [c1] at this
    cases hω : omOf a b y w k
    · rw [hω] at ey; simp [bn] at ey; omega
    · rfl

include hy H_CELLS H_BUNDLE in
/-- Values at time `t`, from the values before `t` and the forcing up to `t`. -/
theorem agr_at (t : Nat) (hag : Agree ch (σY a b y) t) (hf : ForcB a b ch y (t + 1)) :
    Agree ch (σY a b y) (t + 1) := by
  intro c k r hr hoff
  rcases Nat.lt_or_ge r t with hlt | hge
  · exact hag c k r hlt hoff
  have hrt : r = t := by omega
  subst hrt
  have hp := kernel_protocol a b ch H_CELLS H_BUNDLE
  have hPH : ∀ (l : List (Fin NC)), ∀ c ∈ l, Protocol (ch c) ∧ Held (ch c) :=
    fun _ c _ => ⟨hp c, H_BUNDLE c⟩
  let o := prodOf c
  have hco : c ∈ (opAt o).outsC := prod_mem c
  have hE := eqn_sound hy rank_ok nf_pos ch (opAt o) (ops_ok o)
  have hdist := dist_of _ (ops_ok o)
  cases hk : opAt o with
  | amerge x u z w =>
    rw [hk] at hco hE hdist
    have hcz : c = z := by simpa [K.outsC] using hco
    subst hcz
    have hc := H_CELLS o
    rw [hk] at hc
    obtain ⟨g1, g2, M⟩ := hc
    exact amerge_data_upto ch x u c g1 g2 M hdist.1 hdist.2 (omOf a b y w) (hPH _) (hPH _) hoff
      (fun j r' hr' ho' => hf o x u c w hk j r' (by omega) ho') (σY a b y) hag hE
  | _ =>
    have hop := cell_op ch (omOf a b y) (srcVal a b) (opAt o) (H_CELLS o) (by rw [hk]; trivial) hdist
    exact hop.2 (hPH _) (hPH _) c hco k r hoff (σY a b y) hag hE

include H_CELLS H_BUNDLE H_START_ONCE H_WALK in
/-- A spine channel can rise at `t` only if it is the walk's next channel. -/
theorem rise_cur (t p : Nat) (hinv : ∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) p).W c)
    (hag : Agree ch (σY a b y) t) (hf : ForcB a b ch y (t + 1))
    (c : Fin NC) (hsc : sp c = true) (hr : riseB (ch c).req t = true) :
    (walk (σY a b y) p).cur = some c := by
  have hp := kernel_protocol a b ch H_CELLS H_BUNDLE
  have hct : cnt (riseB (ch c).req) (t + 1) = (walk (σY a b y) p).W c + 1 := by
    rw [cnt_succ_of hr, hinv c hsc]
  let o := prodOf c
  have hco : c ∈ (opAt o).outsC := prod_mem c
  have hs := spok o
  have hc := H_CELLS o
  have hnes : ∀ (K' : K NC), opAt o = K' → (∀ z w d, K' ≠ .src z w d) → c ≠ start := by
    intro K' hK hK'; apply ne_start; intro z w d e; exact hK' z w d (hK ▸ e)
  cases hk : opAt o with
  | forkG i os =>
    rw [hk] at hco hs hc
    simp only [K.outsC] at hco
    have hsi : sp i = true := by
      cases hsi : sp i
      · simp only [SpOK, hsi, Bool.false_eq_true, ite_false, List.all_eq_true] at hs
        have := hs c hco; simp [hsc] at this
      · rfl
    simp only [SpOK, hsi, ite_true, beq_iff_eq] at hs
    have hb := fork_strict hc (hp i) (fun o' ho' => by
      obtain ⟨c', _, e⟩ := List.mem_map.mp ho'; rw [← e]; exact hp c') (List.mem_map_of_mem hco) hr
    rw [hct, hinv i hsi] at hb
    have hin := hin_one (σY a b y) (c := c) (i := i)
      (by intro d _ hd; rw [show prodOf c = o from rfl, hk] at hd; simpa [K.insC] using hd)
      (by rw [show prodOf c = o from rfl, hk]; simp [K.insC])
      (fun k => by
        have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
        rw [nxt_forkG _ (by rw [hio, hk])]; exact find_one hs hco hsc)
    apply cur_of_bound _ (hnes _ hk (by intros; simp))
    rw [in_cp _ hin]; exact hb
  | link i o' =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    simp only [SpOK, beq_iff_eq] at hs
    have hsi : sp i = true := by rw [hs]; exact hsc
    obtain ⟨cc, L⟩ := hc
    have hb := link_strict L (hp i) (hp c) hr
    rw [hct, hinv i hsi] at hb
    have hin := hin_one (σY a b y) (c := c) (i := i)
      (by intro d _ hd; rw [show prodOf c = o from rfl, hk] at hd; simpa [K.insC] using hd)
      (by rw [show prodOf c = o from rfl, hk]; simp [K.insC])
      (fun k => by
        have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
        exact nxt_link _ (by rw [hio, hk]) hsc)
    apply cur_of_bound _ (hnes _ hk (by intros; simp))
    rw [in_cp _ hin]; exact hb
  | bjoin ins o' ec ed =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    simp only [SpOK, hsc, Bool.not_true, Bool.false_or] at hs
    match ins, hs, hc, hk with
    | [cd, i], hs, hc, hk =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
      have hb := join_strict hc (hp c) (fun i' hi' => by
        obtain ⟨c', _, e⟩ := List.mem_map.mp hi'; rw [← e]; exact hp c') (i := ch i) (by simp) hr
      rw [hct, hinv i hs.2] at hb
      have hin := hin_one (σY a b y) (c := c) (i := i)
        (by
          intro d hd hd'
          rw [show prodOf c = o from rfl, hk] at hd'
          simp only [K.insC, List.mem_cons, List.not_mem_nil, or_false] at hd'
          rcases hd' with e | e
          · subst e; rw [hs.1] at hd; exact absurd hd (by decide)
          · exact e)
        (by rw [show prodOf c = o from rfl, hk]; simp [K.insC])
        (fun k => by
          have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
          exact nxt_bjoin _ (by rw [hio, hk]) hsc)
      apply cur_of_bound _ (hnes _ hk (by intros; simp))
      rw [in_cp _ hin]; exact hb
  | steerC j tt ff =>
    rw [hk] at hco hs hc
    simp only [SpOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
    obtain ⟨⟨htj, hfj⟩, htf⟩ := hs
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hco
    have hjo : consOf j = o := cons_in o j (by rw [hk]; simp [K.insC])
    have hsj : sp j = true := by
      rcases hco with e | e
      · rw [← htj, ← e]; exact hsc
      · rw [← hfj, ← e]; exact hsc
    have hst : sp tt = true := by rw [htj]; exact hsj
    -- the output's select value
    obtain ⟨bb, hbb⟩ : ∃ bb : Bool, c = (bif bb then tt else ff) := by
      rcases hco with e | e
      · exact ⟨true, e⟩
      · exact ⟨false, e⟩
    have hb := steer_strict hc (hp j) (fun b' => hp _) (H_BUNDLE j) bb (by rw [← hbb]; exact hr)
    rw [← hbb, hct] at hb
    have hsel : selOff sel2 (ch j) bb t =
        cnt (fun i => sel2 (σY a b y j i) == bb) (cnt (riseB (ch j).req) t) :=
      cnt_offers (σ := σY a b y j) (fun v => sel2 v == bb)
        (fun i u hu ho => hag j i u hu ho) t (Nat.le_refl _)
    rw [hsel, hinv j hsj] at hb
    have hin : ∀ d k, sp d = true → (nxt (σY a b y) d k = some c ↔ d = j ∧ sel2 (σY a b y j k) = bb) := by
      intro d k hsd
      constructor
      · intro h
        have hd := nxt_in _ h
        rw [show prodOf c = o from rfl, hk] at hd
        simp only [K.insC, List.mem_singleton] at hd
        subst hd
        rw [nxt_steerC _ (by rw [hjo, hk]) hst] at h
        simp only [Option.some.injEq] at h
        refine ⟨rfl, ?_⟩
        rw [hbb] at h
        cases hb1 : sel2 (σY a b y d k) <;> cases bb <;> simp [hb1] at h ⊢ <;> exact htf (by first | exact h | exact h.symm)
      · rintro ⟨e, hsl⟩
        subst e
        rw [nxt_steerC _ (by rw [hjo, hk]) hst]
        simp [hsl, hbb]
    apply cur_of_bound _ (hnes _ hk (by intros; simp))
    rw [in_st _ hin]; exact hb
  | amerge x u z w =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    obtain ⟨g1, g2, M⟩ := hc
    have hsx : sp x = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.1
    have hsu : sp u = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.2
    have hoff : OffAt (ch c) (walk (σY a b y) p |>.W c) t := ⟨hr, hinv c hsc⟩
    have hw := hf o x u c w hk _ t (Nat.lt_succ_self _) hoff
    obtain ⟨py, px⟩ := offer_pending M (hp x) (hp u) (hp c) hoff
    have hpre : ∀ i, i < (walk (σY a b y) p).W c → CM.winner (ch c) i = omOf a b y w i := by
      intro i hi
      obtain ⟨r', hr'⟩ := Capstone.offered_below hoff hi
      exact hf o x u c w hk i r' (by have := off_before hoff hr' hi; omega) hr'
    have c1 := CM.cnt_congr_lt _ hpre
    have c0 : cnt (fun i => !CM.winner (ch c) i) ((walk (σY a b y) p).W c) =
        cnt (fun i => !omOf a b y w i) ((walk (σY a b y) p).W c) :=
      CM.cnt_congr_lt _ (fun i hi => by rw [hpre i hi])
    obtain ⟨ey, ex⟩ := am_counts H_WALK hk p
    rw [← hinv u hsu] at ey
    rw [← hinv x hsx] at ex
    cases hω : omOf a b y w ((walk (σY a b y) p).W c)
    · have := px (by rw [hw, hω]); rw [c0] at this
      rw [hω] at ex
      cases hq : ((walk (σY a b y) p).cur == some c)
      · rw [hq] at ex; simp [bn] at ex; omega
      · simpa using hq
    · have := py (by rw [hw, hω]); rw [c1] at this
      rw [hω] at ey
      cases hq : ((walk (σY a b y) p).cur == some c)
      · rw [hq] at ey; simp [bn] at ey; omega
      · simpa using hq
  | src z which d =>
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    have hcs : c = start := by
      simp [SpOK, hsc] at hs
      rcases hs with ⟨hw2, hs⟩
      rcases hs with hs | hs
      · exact absurd hw2 hs
      · exact hs
    subst hcs
    have h1 := H_START_ONCE (t + 1)
    rw [hct] at h1
    have hf' := flow (σY a b y) p start
    rw [tr_start] at hf'
    have h0 : (walk (σY a b y) p).W start = 0 := by omega
    cases hq : ((walk (σY a b y) p).cur == some start)
    · rw [hq] at hf'; simp [bn] at hf'; omega
    · simpa using hq
  | forkH i os l h d hs' =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_map] at hco
    obtain ⟨pr, hpr, e⟩ := hco
    simp only [SpOK, List.all_eq_true] at hs
    have := hs pr hpr; rw [e] at this; simp [hsc] at this
  | join ins o' e js jw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | steerD j tt ff fd sw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hco
    simp only [SpOK, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rcases hco with e | e <;> subst e
    · rw [hs.1] at hsc; exact absurd hsc (by decide)
    · rw [hs.2] at hsc; exact absurd hsc (by decide)
  | mux cc xx yy zz mw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | muxn cc x0 x1 x2 zz nw =>
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | sink i =>
    rw [hk] at hco
    simp [K.outsC] at hco

include hy H_CELLS H_BUNDLE H_START_ONCE H_WALK in
/-- **The joint induction on time.** -/
theorem main : ∀ t, Inv a b ch y t ∧ ForcB a b ch y t ∧ Agree ch (σY a b y) t := by
  intro t
  induction t with
  | zero =>
    refine ⟨⟨0, fun c _ => rfl⟩, fun _ _ _ _ _ _ _ _ h _ => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h _ => absurd h (Nat.not_lt_zero _)⟩
  | succ t ih =>
    obtain ⟨hinv, hf, hag⟩ := ih
    have hf' := forc_at H_CELLS H_BUNDLE H_WALK t hinv hf
    have hag' := agr_at hy H_CELLS H_BUNDLE t hag hf'
    refine ⟨?_, hf', hag'⟩
    obtain ⟨p, hp⟩ := hinv
    have hrc := rise_cur H_CELLS H_BUNDLE H_START_ONCE H_WALK t p hp hag hf'
    by_cases hex : ∃ c, sp c = true ∧ riseB (ch c).req t = true
    · obtain ⟨c, hsc, hr⟩ := hex
      have hcur := hrc c hsc hr
      refine ⟨p + 1, fun d hsd => ?_⟩
      rw [W_succ, cnt_succ', hp d hsd]
      unfold visB
      rw [hcur]
      by_cases hdc : d = c
      · subst hdc; simp [hr, bn]
      · have h1 : riseB (ch d).req t = false := by
          cases h : riseB (ch d).req t
          · rfl
          · have := hrc d hsd h; rw [hcur] at this; simp at this; exact absurd this.symm hdc
        have h2 : (some c == some d) = false := by simp [Ne.symm hdc]
        rw [h1, h2]
    · refine ⟨p, fun d hsd => ?_⟩
      rw [cnt_succ', hp d hsd]
      have : riseB (ch d).req t = false := by
        cases h : riseB (ch d).req t
        · rfl
        · exact absurd ⟨d, hsd, h⟩ hex
      rw [this]; rfl

end main

/-! ## The results -/

/-- **H_CM_FORCED, proved**: every arbiter stage's winner of every offered token is the token
run's label. -/
theorem kernel_forced (a b : Nat) (ch : Fin NC → Chan) (y : TS) (hy : Good a b y)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_WALK : WalkOK (σY a b y) (omOf a b y)) :
    ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o) := by
  intro o
  cases hk : opAt o with
  | amerge x u z w =>
    intro k r hoff
    exact (main hy H_CELLS H_BUNDLE H_START_ONCE H_WALK (r + 1)).2.1 o x u z w hk k r
      (Nat.lt_succ_self _) hoff
  | _ => trivial

/-- **H_CUT, proved** (8q's `CutBound` at every arbiter stage). -/
theorem kernel_cut (a b : Nat) (ch : Fin NC → Chan) (y : TS) (hy : Good a b y)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_WALK : WalkOK (σY a b y) (omOf a b y)) :
    ∀ o : Fin NO, CutOp ch (omOf a b y) (opAt o) := by
  intro o
  cases hk : opAt o with
  | amerge x u z w =>
    intro t _
    obtain ⟨p, hp⟩ := (main hy H_CELLS H_BUNDLE H_START_ONCE H_WALK t).1
    have hs := spok o
    rw [hk] at hs
    simp only [SpOK, Bool.and_eq_true] at hs
    obtain ⟨ey, ex⟩ := am_counts H_WALK hk p
    rw [← hp z hs.1.2] at ey ex
    rw [← hp u hs.1.1.2] at ey
    rw [← hp x hs.1.1.1] at ex
    constructor
    · rw [ex]; cases (walk (σY a b y) p).cur == some z <;>
        cases omOf a b y w (cnt (riseB (ch z).req) t) <;> simp [bn, Mux.b2n]
    · rw [ey]; cases (walk (σY a b y) p).cur == some z <;>
        cases omOf a b y w (cnt (riseB (ch z).req) t) <;> simp [bn, Mux.b2n]
  | _ => trivial

/-- **Circuit-level safety of gcd_hw without H_CUT / H_CM_FORCED**: under the gate models
(H_CELLS), per-channel bundling (H_BUNDLE), a one-invocation environment (H_START_ONCE) and
the token-level H_WALK, every value the circuit ever latches on `out0` is `gcd a b`. -/
theorem kernel_circuit_safe'' (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_WALK : ∃ y, Good a b y ∧ WalkOK (σY a b y) (omOf a b y)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (spec a b)) := by
  obtain ⟨y, hy, hw⟩ := H_WALK
  exact kernel_circuit_safe a b ch H_CELLS H_BUNDLE
    ⟨y, hy, kernel_forced a b ch y hy H_CELLS H_BUNDLE H_START_ONCE hw⟩

/-- **No free contention at any arbiter stage**, without H_CUT. -/
theorem kernel_arbiters_uncontended' (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (y : TS) (hy : Good a b y) (H_WALK : WalkOK (σY a b y) (omOf a b y))
    (o : Fin NO) (x u z : Fin NC) (w : Nat) (ho : opAt o = .amerge x u z w)
    (g1 g2 : Trace) (M : CM.AMerge (ch x) (ch u) (ch z) g1 g2) :
    ∀ t, (ch x).req t = true → (ch u).req t = true → g1 t = true ∨ g2 t = true :=
  kernel_arbiters_uncontended a b ch H_CELLS H_BUNDLE y
    (kernel_cut a b ch y hy H_CELLS H_BUNDLE H_START_ONCE H_WALK) o x u z w ho g1 g2 M

end Formal.Net.KCap
