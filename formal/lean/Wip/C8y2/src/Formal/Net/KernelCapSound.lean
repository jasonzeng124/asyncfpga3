import Formal.Net.KernelCapHist

/-!
# Kernel-parametric: the checker is sound (from C-8m's CapstoneNetDef / CapstoneNetSound)
-/


namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)
open KD KP

set_option linter.unusedSectionVars false

variable [KD] [KP]

/-! ## The histories of a complete run -/

def Hh (a b : Nat) (y : TS) (c : Nat) : List Nat := init a b c ++ y.pr c

theorem Hh_pr {a b : Nat} {y : TS} {c : Nat} (h : nIn ≤ c) : Hh a b y c = y.pr c := by
  simp [Hh, init_empty a b c h]

theorem Hh_cn {a b : Nat} {y : TS} (hy : Good a b y) {c : Nat} (h3 : c ≠ chEnd) (h250 : c ≠ chOut) :
    Hh a b y c = y.cn c := by
  have := hy.fifo c
  rw [hy.fin, final_empty _ c h3 h250, List.append_nil] at this
  exact this

variable {n : Nat} {a b : Nat} {y : TS} {T : Tab}

theorem getD_map_range (f : Nat → Nat) {j m : Nat} (h : j < m) : ((List.range m).map f).getD j 0 = f j := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]

theorem map_range_getD (f : Nat → Nat) (L : List Nat) :
    (List.range L.length).map (fun j => f (L.getD j 0)) = L.map f := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1)]

theorem perL_nil (d k : Nat) : perL [] d k = d := by simp [perL]

theorem perL_of_len {L : List Nat} {m : Nat} (hl : L.length = m) (hm : 0 < m) (d k : Nat) :
    perL L d k = L.getD (k % m) 0 := by
  have : L ≠ [] := by intro h; subst h; simp at hl; omega
  rw [perL_ne this, hl]

theorem cntL_lt (P : Nat → Bool) (L : List Nat) {j : Nat} (hj : j < L.length) (hp : P (L.getD j 0) = true) :
    cntL P L j < cntL P L L.length := by
  unfold cntL
  have e : L.take L.length = L.take j ++ (L.drop j) := by rw [List.take_of_length_le (Nat.le_refl _), List.take_append_drop]
  rw [e, List.filter_append, List.length_append]
  rw [List.drop_eq_getElem_cons hj]
  have : L[j] = L.getD j 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [this]; simp only [List.filter_cons, hp, ↓reduceIte, List.length_cons]; omega

theorem per_index {m : Nat} (hm : 0 < m) {q r : Nat} (hr : r < m) : (q * m + r) % m = r := by
  rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hr]

/-! ## Join inputs -/

theorem jval (hy : Good a b y) (hnf : 0 < T.nf) {ins : List Nat} {gm : Nat} {j : J}
    (hj : JOK T ins gm j) {m : Nat} (hn : (y.cn gm).length = m) (k : Nat) :
    j.σ.eval (ins.map fun c => refT T (Hh a b y) c k) =
      if m = 0 then j.dflt else (y.cn gm).getD (k % m) 0 := by
  have genv : ∀ p, p < ins.length → (ins.map fun c => refT T (Hh a b y) c k).getD p 0 =
      refT T (Hh a b y) (ins.getD p 0) k := by
    intro p hp
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hp]
  cases j with
  | direct p d =>
    obtain ⟨hp, hd, hne⟩ := hj
    simp only [J.σ, E.eval, J.dflt]
    rw [genv p hp, ref_hist T _ hd hnf, Hh_cn hy hne.1 hne.2]
    split
    · rename_i h0; subst h0; rw [List.eq_nil_of_length_eq_zero hn, perL_nil]
    · rename_i h0; exact perL_of_len hn (by omega) d k
  | fold l1 p g1 d e1 =>
    obtain ⟨hp, hr, hd, hne1, hne, hge⟩ := hj
    simp only [J.σ, J.dflt]
    rw [eval_subst]
    simp only [List.map_cons, List.map_nil, E.eval]
    rw [genv p hp, ref_hist T _ hd hnf, Hh_cn hy hne1.1 hne1.2]
    obtain ⟨n1, hn1, hpr⟩ := hy.cp l1 [g1] gm e1 hr
    have hcp : y.cn gm = y.pr gm := by rw [← Hh_cn hy hne.1 hne.2, Hh_pr hge]
    have hlen : n1 = m := by rw [← hn, hcp, hpr]; simp
    have hg1 := hn1 g1 (by simp)
    split
    · rename_i h0; subst h0
      rw [List.eq_nil_of_length_eq_zero (by omega : (y.cn g1).length = 0), perL_nil]
    · rename_i h0
      rw [perL_of_len (by omega : (y.cn g1).length = m) (by omega), hcp, hpr, hlen,
        getD_map_range _ (Nat.mod_lt _ (by omega))]
      simp
  | const l1 g1 e1 =>
    obtain ⟨hr, hvf, hne, hge⟩ := hj
    simp only [J.σ, J.dflt]
    rw [evf_eval e1 _ hvf]
    obtain ⟨n1, hn1, hpr⟩ := hy.cp l1 [g1] gm e1 hr
    have hcp : y.cn gm = y.pr gm := by rw [← Hh_cn hy hne.1 hne.2, Hh_pr hge]
    have hlen : n1 = m := by rw [← hn, hcp, hpr]; simp
    split
    · rfl
    · rename_i h0
      rw [hcp, hpr, hlen, getD_map_range _ (Nat.mod_lt _ (by omega))]
      exact (evf_eval e1 _ hvf).symm

/-! ## Per-kind soundness -/

theorem sound_forkH (hy : Good a b y) (hnf : 0 < T.nf) {i : Fin n} {os : List (Fin n × Nat)}
    {l h d : Nat} {hs : List Nat} (hc : OpChk T (.forkH i os l h d hs)) :
    Fork.forkEq i (os.map Prod.fst) (fun c k => refT T (Hh a b y) c.val k) := by
  obtain ⟨hr, hdi, hne, hos⟩ := hc
  intro o ho k
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ho
  obtain ⟨hdo, hmem, hge⟩ := hos p hp
  simp only
  rw [ref_hist T _ hdo hnf, ref_hist T _ hdi hnf, Hh_pr hge, hy.fk l h hs hr p.2 hmem,
    Hh_cn hy hne.1 hne.2]

theorem sound_join (hy : Good a b y) (hnf : 0 < T.nf) {ins : List (Fin n)} {o : Fin n} {e : E}
    {js : List J} {jw : JW} (hc : OpChk T (.join ins o e js jw)) :
    Join.joinEq (jg e js) ins o (fun c k => refT T (Hh a b y) c.val k) := by
  obtain ⟨hr, hdo, hge, hlen, hne, hjs, hdef⟩ := hc
  intro k
  obtain ⟨m, hm, hpr⟩ := hy.cp jw.l jw.gins jw.go e hr
  have env : ins.map (fun c => refT T (Hh a b y) c.val k) =
      (ins.map Fin.val).map (fun c => refT T (Hh a b y) c k) := by simp
  simp only [jg]
  rw [env, eval_subst, ref_hist T _ hdo hnf, Hh_pr hge, List.map_map]
  have hj : ∀ i, i < js.length → (js.getD i (.direct 0 0)).σ.eval
      ((ins.map Fin.val).map (fun c => refT T (Hh a b y) c k)) =
      if m = 0 then (js.getD i (.direct 0 0)).dflt else (y.cn (jw.gins.getD i 0)).getD (k % m) 0 := by
    intro i hi
    apply jval hy hnf (hjs i hi)
    apply hm
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show i < jw.gins.length by omega)]
  by_cases h0 : m = 0
  · subst h0
    simp only [List.range_zero, List.map_nil] at hpr
    rw [hpr, perL_nil, hdef]
    congr 1
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp only [List.length_map] at h1
    have := hj i h1
    simp only [↓reduceIte] at this
    simp only [List.getElem_map, Function.comp]
    have g : js[i] = js.getD i (.direct 0 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rw [g, this]
  · rw [perL_of_len (m := m) (by rw [hpr]; simp) (by omega), hpr, getD_map_range _ (Nat.mod_lt _ (by omega))]
    congr 1
    apply List.ext_getElem (by simp [hlen])
    intro i h1 h2
    simp only [List.length_map] at h1 h2
    have := hj i h2
    simp only [h0, ↓reduceIte] at this
    simp only [List.getElem_map, Function.comp]
    have g : js[i] = js.getD i (.direct 0 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    have g2 : jw.gins[i] = jw.gins.getD i 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
    rw [g, this, g2]

theorem sound_bjoin (hR : RankOK T) {ins : List (Fin n)} {o : Fin n} {ec ed : E} (hc : OpChk T (.bjoin ins o ec ed))
    (H : Nat → List Nat) :
    Join.joinEq (bg ec ed) ins o (fun c k => refT T H c.val k) := by
  obtain ⟨hd, hne⟩ := hc
  intro k
  have env : ins.map (fun c => refT T H c.val k) = (ins.map Fin.val).map (fun c => refT T H c k) := by simp
  simp only [bg]
  rw [env, ref_bj T H hR hd (by simpa using hne)]

theorem sound_steerC (hnf : 0 < T.nf) {j t f : Fin n} (hc : OpChk T (.steerC j t f)) (H : Nat → List Nat) :
    Steer.steerEq sel2 (fun _ => 0) j (fun b => bif b then t else f) (fun c k => refT T H c.val k) := by
  obtain ⟨ht, hf⟩ := hc
  intro i bb _
  cases bb
  · exact ref_zero T H hf hnf _
  · exact ref_zero T H ht hnf _

theorem two_mod (x y : Nat) : (2 * x + y % 2) % 2 = y % 2 := by omega
theorem two_div (x y : Nat) : (2 * x + y % 2) / 2 = x := by omega

/-- One side of a data steer. -/
theorem steer_side (hnf : 0 < T.nf) (H : Nat → List Nat) (bb : Bool) (fd : E) {oc gb db : Nat}
    (hdo : T.d oc = .hist gb db) (C Dl : List Nat) (hl : C.length = Dl.length)
    (hout : H gb = (sel bb C Dl).map (fun v => fd.eval [v]))
    (Cv Dv : Nat → Nat) (c0 d0 : Nat)
    (hCv : ∀ i, Cv i = if C.length = 0 then c0 else C.getD (i % C.length) 0)
    (hDv : ∀ i, Dv i = if C.length = 0 then d0 else Dl.getD (i % C.length) 0)
    (hdef : (c0 % 2 == 1) = bb → db = fd.eval [d0]) :
    ∀ i, (Cv i % 2 == 1) = bb →
      refT T H oc (cnt (fun i' => (Cv i' % 2 == 1) == bb) i) = fd.eval [Dv i] := by
  intro i hi
  rw [ref_hist T H hdo hnf]
  by_cases h0 : C.length = 0
  · have hC : C = [] := List.eq_nil_of_length_eq_zero h0
    have hD : Dl = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hout, hC, hD]
    simp only [sel, List.zip_nil_left, List.filterMap_nil, List.map_nil, perL_nil]
    rw [hCv i] at hi; simp only [h0, ↓reduceIte] at hi
    rw [hDv i]; simp only [h0, ↓reduceIte]
    exact hdef hi
  · have hne : C ≠ [] := fun h => h0 (by simp [h])
    have hcnt : cnt (fun i' => (Cv i' % 2 == 1) == bb) i = cnt (fun i' => tst bb (perL C 0 i')) i := by
      congr 1; funext i'; rw [hCv i']; simp only [h0, ↓reduceIte, tst, perL_ne hne]
    rw [hcnt, cnt_per _ hne]
    have hj : i % C.length < C.length := Nat.mod_lt _ (by omega)
    have hti : tst bb (C.getD (i % C.length) 0) = true := by
      rw [hCv i] at hi; simp only [h0, ↓reduceIte] at hi; unfold tst; rw [hi]; exact beq_self_eq_true bb
    have hlt := cntL_lt (tst bb) C hj hti
    have hsl := sel_len bb C Dl hl
    rw [hout, perL_of_len (by rw [List.length_map, hsl]) (by omega), per_index (by omega) hlt]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    have hr := sel_rank bb C Dl (i % C.length) hl hj hti
    have hlt' : cntL (tst bb) C (i % C.length) < (sel bb C Dl).length := by rw [hsl]; exact hlt
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt'] at hr
    rw [List.getElem?_eq_getElem hlt']
    simp only [Option.map_some, Option.getD_some] at hr ⊢
    rw [hr, hDv i]; simp [h0]

theorem sound_steerD (hy : Good a b y) (hR : RankOK T) (hnf : 0 < T.nf) {j t f : Fin n} {fd : E} {sw : SW}
    (hc : OpChk T (.steerD j t f fd sw)) :
    Steer.steerEq sel2 (fun v => fd.eval [v / 2]) j (fun b => bif b then t else f)
      (fun c k => refT T (Hh a b y) c.val k) := by
  obtain ⟨hr, hgc, hgd, hgt, hgf, hdj, hjne, hjc, hjd, hdef, hfold⟩ := hc
  obtain ⟨hlen, hpt, hpf⟩ := hy.br sw.l sw.gc sw.gd sw.gt sw.gf hr
  let Cv : Nat → Nat := fun i => sw.jc.σ.eval (sw.jins.map fun c => refT T (Hh a b y) c i)
  let Dv : Nat → Nat := fun i => sw.jd.σ.eval (sw.jins.map fun c => refT T (Hh a b y) c i)
  have hCv : ∀ i, Cv i = if (y.cn sw.gc).length = 0 then sw.jc.dflt else (y.cn sw.gc).getD (i % (y.cn sw.gc).length) 0 :=
    fun i => jval hy hnf hjc rfl i
  have hDv : ∀ i, Dv i = if (y.cn sw.gc).length = 0 then sw.jd.dflt else (y.cn sw.gd).getD (i % (y.cn sw.gc).length) 0 :=
    fun i => jval hy hnf hjd hlen.symm i
  have hrj : ∀ i, refT T (Hh a b y) j.val i = 2 * Dv i + Cv i % 2 := fun i => ref_bj T (Hh a b y) hR hdj hjne i
  -- the two outputs, as maps of the routed histories
  have outs : ∀ bb : Bool, ∃ gb db, T.d (bif bb then t else f).val = .hist gb db ∧
      (Hh a b y) gb = (sel bb (y.cn sw.gc) (y.cn sw.gd)).map (fun v => fd.eval [v]) ∧ db = (if bb then sw.dt else sw.df) := by
    intro bb
    rcases hfo : sw.fold with _ | ⟨lt, lf, gt', gf'⟩ <;> rw [hfo] at hfold
    · obtain ⟨hfd, hdt, hdf⟩ := hfold
      subst hfd
      have idm : (fun v : Nat => E.eval [v] (.var 0)) = id := by funext v; rfl
      cases bb
      · exact ⟨sw.gf, sw.df, hdf, by rw [Hh_pr hgf, hpf, idm, List.map_id]; rfl, rfl⟩
      · exact ⟨sw.gt, sw.dt, hdt, by rw [Hh_pr hgt, hpt, idm, List.map_id]; rfl, rfl⟩
    · rcases hfold with ⟨hlt, hlf, hnt, hnf', hgt', hgf', hdt, hdf⟩ |
        ⟨-, -, hlt, hnt, hgt', hdt, hdf, hcf⟩
      rotate_left
      · -- one-sided fold (C-8y2): the false output is the steered constant, fixed by `fd`
        cases bb
        · refine ⟨sw.gf, sw.df, hdf, ?_, rfl⟩
          have hD : ∀ v ∈ y.cn sw.gd, fd.eval [v] = v := by
            revert hcf hjd
            cases sw.jd with
            | direct _ _ => intro _ hcf; cases hcf
            | fold _ _ _ _ _ => intro _ hcf; cases hcf
            | const l1 g1 e1 =>
              intro hjd hcf
              obtain ⟨hr1, hvf, hne, hge⟩ := hjd
              obtain ⟨n1, -, hpr⟩ := hy.cp l1 [g1] sw.gd e1 hr1
              have hcp : y.cn sw.gd = y.pr sw.gd := by rw [← Hh_cn hy hne.1 hne.2, Hh_pr hge]
              intro v hv
              rw [hcp, hpr] at hv
              obtain ⟨jj, -, rfl⟩ := List.mem_map.mp hv
              rw [evf_eval e1 _ hvf]
              exact hcf
          rw [Hh_pr hgf, hpf]
          have hsub : ∀ v ∈ selL false (y.cn sw.gc) (y.cn sw.gd), v ∈ y.cn sw.gd := by
            intro v hv
            unfold selL at hv
            obtain ⟨pp, hpp, hpv⟩ := List.mem_filterMap.mp hv
            split at hpv
            · cases hpv; exact (List.of_mem_zip hpp).2
            · cases hpv
          show selL false (y.cn sw.gc) (y.cn sw.gd) =
            (selL false (y.cn sw.gc) (y.cn sw.gd)).map (fun v => fd.eval [v])
          conv => lhs; rw [← List.map_id (selL false (y.cn sw.gc) (y.cn sw.gd))]
          exact List.map_congr_left (fun v hv => (hD v (hsub v hv)).symm)
        · refine ⟨gt', sw.dt, hdt, ?_, rfl⟩
          obtain ⟨n2, hn2, hp2⟩ := hy.cp lt [sw.gt] gt' fd hlt
          have e2 : n2 = (y.cn sw.gt).length := (hn2 sw.gt (by simp)).symm
          rw [Hh_pr hgt', hp2, e2]
          simp only [List.map_cons, List.map_nil]
          rw [map_range_getD (fun v => fd.eval [v]), ← Hh_cn hy hnt.1 hnt.2, Hh_pr hgt, hpt]; rfl
      cases bb
      · refine ⟨gf', sw.df, hdf, ?_, rfl⟩
        obtain ⟨n2, hn2, hp2⟩ := hy.cp lf [sw.gf] gf' fd hlf
        have e2 : n2 = (y.cn sw.gf).length := (hn2 sw.gf (by simp)).symm
        rw [Hh_pr hgf', hp2, e2]
        simp only [List.map_cons, List.map_nil]
        rw [map_range_getD (fun v => fd.eval [v]), ← Hh_cn hy hnf'.1 hnf'.2, Hh_pr hgf, hpf]; rfl
      · refine ⟨gt', sw.dt, hdt, ?_, rfl⟩
        obtain ⟨n2, hn2, hp2⟩ := hy.cp lt [sw.gt] gt' fd hlt
        have e2 : n2 = (y.cn sw.gt).length := (hn2 sw.gt (by simp)).symm
        rw [Hh_pr hgt', hp2, e2]
        simp only [List.map_cons, List.map_nil]
        rw [map_range_getD (fun v => fd.eval [v]), ← Hh_cn hy hnt.1 hnt.2, Hh_pr hgt, hpt]; rfl
  intro i bb hsel
  obtain ⟨gb, db, hdo, hout, hdb⟩ := outs bb
  have hs : ∀ i', sel2 (refT T (Hh a b y) j.val i') = (Cv i' % 2 == 1) := by
    intro i'; rw [hrj i']; simp only [sel2, two_mod]
  have hfun : (fun i' => sel2 (refT T (Hh a b y) j.val i') == bb) = (fun i' => (Cv i' % 2 == 1) == bb) := by
    funext i'; rw [hs i']
  show refT T (Hh a b y) (bif bb then t else f).val (cnt (fun i' => sel2 (refT T (Hh a b y) j.val i') == bb) i) =
    fd.eval [refT T (Hh a b y) j.val i / 2]
  rw [hfun, hrj i, two_div]
  rw [hs i] at hsel
  apply steer_side hnf (Hh a b y) bb fd hdo (y.cn sw.gc) (y.cn sw.gd) hlen hout Cv Dv sw.jc.dflt sw.jd.dflt hCv hDv _ i hsel
  intro hb; rw [hdb, ← hdef]; cases bb <;> simp_all

/-! ## Muxes -/

theorem b2n_beq (w : Bool) : (Mux.b2n w == 1) = w := by cases w <;> rfl

theorem sel_lab2 (hR : RankOK T) (H : Nat → List Nat) {c zc xa ya w gi : Nat} (hch : chase T 32 c = zc)
    (hz : T.d zc = .cmz xa ya w) (hw : T.w w = .lab2 gi) (k : Nat) :
    sel2 (refT T H c k) = (perL (H gi) 0 k % 2 == 1) := by
  rw [ref_chase T H hR 32 c k, hch, ref_cmz T H hR hz, hw]
  simp only [W.om, sel2]
  rw [CM.b2n_mod, b2n_beq]

theorem mod2_beq0 : (fun v : Nat => v % 2 ^ 1 == 0) = (fun v => !(v % 2 == 1)) := by
  funext v; have : v % 2 = 0 ∨ v % 2 = 1 := by omega
  rcases this with h | h <;> simp [h]

theorem mod2_beq1 : (fun v : Nat => v % 2 ^ 1 == 1) = (fun v => v % 2 == 1) := by
  funext v; simp

/-- The periodic read of a selected input. -/
theorem per_pick {L X : List Nat} (P : Nat → Bool) (hX : X.length = cntL P L L.length) (k : Nat)
    (hL : L ≠ []) (hp : P (L.getD (k % L.length) 0) = true) (dx : Nat) :
    perL X dx (cnt (fun i => P (perL L 0 i)) k) = X.getD (cntL P L (k % L.length)) 0 := by
  have hj : k % L.length < L.length := Nat.mod_lt _ (len_pos hL)
  have hlt := cntL_lt P L hj hp
  rw [cnt_per _ hL, perL_of_len hX (by omega), per_index (by omega) hlt]

theorem sound_mux (hy : Good a b y) (hR : RankOK T) (hnf : 0 < T.nf) {c x y' z : Fin n} {mw : MW}
    (hc : OpChk T (.mux c x y' z mw)) :
    Mux.muxEq sel2 c x y' z (fun c k => refT T (Hh a b y) c.val k) := by
  obtain ⟨hr, hdx, hdy, hdz, hgs, hgx, hgy, hgz, hgi, hgs3, hch, hzc, hw, hfk, hdzx⟩ := hc
  obtain ⟨hlen, hval, hcnt⟩ := hy.mx mw.l mw.gs [mw.gx, mw.gy] mw.gz 1 hr
  have hHs : Hh a b y mw.gi = y.cn mw.gs := by
    rcases hfk with e | ⟨hf, hm⟩
    · rw [← e, Hh_cn hy hgs.1 hgs.2]
    · rw [Hh_cn hy hgi.1 hgi.2, ← hy.fk mw.lf mw.gi mw.hs hf mw.gs hm, ← Hh_pr hgs3, Hh_cn hy hgs.1 hgs.2]
  have hsel : ∀ k, sel2 (refT T (Hh a b y) c.val k) = (perL (y.cn mw.gs) 0 k % 2 == 1) := by
    intro k; rw [sel_lab2 hR _ hch hzc hw, hHs]
  intro k
  show refT T (Hh a b y) z.val k = if sel2 (refT T (Hh a b y) c.val k)
    then refT T (Hh a b y) y'.val (cnt (fun i => sel2 (refT T (Hh a b y) c.val i)) k)
    else refT T (Hh a b y) x.val (cnt (fun i => !sel2 (refT T (Hh a b y) c.val i)) k)
  simp only [hsel]
  rw [ref_hist T _ hdz hnf, ref_hist T _ hdx hnf, ref_hist T _ hdy hnf, Hh_pr hgz, Hh_cn hy hgx.1 hgx.2,
    Hh_cn hy hgy.1 hgy.2]
  have hc0 := hcnt 0 (by simp)
  have hc1 := hcnt 1 (by simp)
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hc0 hc1
  unfold cntm at hc0 hc1
  rw [mod2_beq0] at hc0; rw [mod2_beq1] at hc1
  change (y.cn mw.gx).length = cntL _ _ _ at hc0
  change (y.cn mw.gy).length = cntL _ _ _ at hc1
  by_cases h0 : (y.cn mw.gs).length = 0
  · have hL : y.cn mw.gs = [] := List.eq_nil_of_length_eq_zero h0
    have hz0 : y.pr mw.gz = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hx0 : y.cn mw.gx = [] := List.eq_nil_of_length_eq_zero (by rw [hc0, hL]; rfl)
    rw [hz0, hL, hx0]; simp [perL_nil, hdzx]
  · have hL : y.cn mw.gs ≠ [] := fun h => h0 (by simp [h])
    have hj : k % (y.cn mw.gs).length < (y.cn mw.gs).length := Nat.mod_lt _ (by omega)
    obtain ⟨_, hv⟩ := hval _ hj
    simp only [Nat.pow_one] at hv
    rw [perL_of_len (m := (y.cn mw.gs).length) (by omega) (by omega), hv, perL_ne hL]
    rcases (show (y.cn mw.gs).getD (k % (y.cn mw.gs).length) 0 % 2 = 0 ∨
        (y.cn mw.gs).getD (k % (y.cn mw.gs).length) 0 % 2 = 1 by omega) with e | e
    · have hp : (fun v => !(v % 2 == 1)) ((y.cn mw.gs).getD (k % (y.cn mw.gs).length) 0) = true := by
        show (!(_ % 2 == 1)) = true; rw [e]; rfl
      have hcm : cntm (y.cn mw.gs) 1 0 (k % (y.cn mw.gs).length) =
          cntL (fun v => !(v % 2 == 1)) (y.cn mw.gs) (k % (y.cn mw.gs).length) := by
        unfold cntm cntL; rw [mod2_beq0]
      simp only [e, List.getD_cons_zero, hcm]
      have := per_pick (fun v => !(v % 2 == 1)) hc0 k hL hp mw.dx
      rw [this]; rfl
    · have hp : (fun v => v % 2 == 1) ((y.cn mw.gs).getD (k % (y.cn mw.gs).length) 0) = true := by
        show (_ % 2 == 1) = true; rw [e]; rfl
      have hcm : cntm (y.cn mw.gs) 1 1 (k % (y.cn mw.gs).length) =
          cntL (fun v => v % 2 == 1) (y.cn mw.gs) (k % (y.cn mw.gs).length) := by
        unfold cntm cntL; rw [mod2_beq1]
      simp only [e, List.getD_cons_succ, List.getD_cons_zero, hcm]
      have := per_pick (fun v => v % 2 == 1) hc1 k hL hp mw.dy
      rw [this]; rfl

theorem selD_eq (hR : RankOK T) (H : Nat → List Nat) {c zc acc in2 in0 in1 w2 w1 gs : Nat} (L : List Nat)
    (hH : H gs = L) (hch : chase T 32 c = zc) (hzc : T.d zc = .cmz acc in2 w2)
    (hacc : T.d acc = .cmz in0 in1 w1) (hw2 : T.w w2 = .hi3 gs) (hw1 : T.w w1 = .lo3 gs)
    (hr3 : ∀ j, j < L.length → L.getD j 0 % 4 < 3) (i : Nat) :
    selD (refT T H c i) = perL L 0 i % 4 := by
  rw [ref_chase T H hR 32 c i, hch, ref_cmz T H hR hzc, hw2]
  simp only [W.om, hH]
  cases h2 : (perL L 0 i % 4 == 2)
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hb : Mux.b2n false = 0 := rfl
    rw [hb, Nat.add_zero, ref_cmz T H hR hacc, hw1]
    simp only [W.om, hH]
    unfold selD
    have e1 : 2 * (2 * (if perL (L.filter fun v => v % 4 != 2) 0 (cnt (fun i => !(perL L 0 i % 4 == 2)) i) % 4 == 1
        then refT T H in1 (cnt (fun k => perL (L.filter fun v => v % 4 != 2) 0 k % 4 == 1) (cnt (fun i => !(perL L 0 i % 4 == 2)) i))
        else refT T H in0 (cnt (fun k => !(perL (L.filter fun v => v % 4 != 2) 0 k % 4 == 1)) (cnt (fun i => !(perL L 0 i % 4 == 2)) i))) +
        Mux.b2n (perL (L.filter fun v => v % 4 != 2) 0 (cnt (fun i => !(perL L 0 i % 4 == 2)) i) % 4 == 1)) % 2 = 0 := by omega
    rw [if_neg (by omega), Nat.mul_div_cancel_left _ (by omega), Nat.add_comm, Nat.add_mul_mod_self_left]
    by_cases hL : L = []
    · subst hL; simp [perL_nil, Mux.b2n]
    · have hn := len_pos hL
      have hj : i % L.length < L.length := Nat.mod_lt _ hn
      have hv := hr3 _ hj
      have h2' : L.getD (i % L.length) 0 % 4 ≠ 2 := by
        rw [perL_ne hL] at h2; simpa using h2
      have hp : (fun v => v % 4 != 2) (L.getD (i % L.length) 0) = true := by
        show (_ != 2) = true; simpa using h2'
      have hf : (fun i => !(perL L 0 i % 4 == 2)) = (fun i => (fun v => v % 4 != 2) (perL L 0 i)) := rfl
      rw [hf, per_pick (fun v => v % 4 != 2) (filter_len _ L) i hL hp 0, filter_rank _ L _ hj hp, perL_ne hL]
      have : L.getD (i % L.length) 0 % 4 = 0 ∨ L.getD (i % L.length) 0 % 4 = 1 := by omega
      rcases this with e | e <;> rw [e] <;> rfl
  · simp only [↓reduceIte]
    have hb : Mux.b2n true = 1 := rfl
    rw [hb]
    unfold selD
    rw [if_pos (by omega)]
    simp at h2; omega

theorem sound_muxn (hy : Good a b y) (hR : RankOK T) (hnf : 0 < T.nf) {c x0 x1 x2 z : Fin n} {nw : NW}
    (hc : OpChk T (.muxn c x0 x1 x2 z nw)) :
    MuxN.muxnEq selD c (cx3 x0 x1 x2) z (fun c k => refT T (Hh a b y) c.val k) := by
  obtain ⟨hr, hd0, hd1, hd2, hdz, hgs, hg0, hg1, hg2, hgz, hch, hzc, hacc, hw2, hw1, hdz0⟩ := hc
  obtain ⟨hlen, hval, hcnt⟩ := hy.mx nw.l nw.gs [nw.g0, nw.g1, nw.g2] nw.gz 2 hr
  have hH : Hh a b y nw.gs = y.cn nw.gs := Hh_cn hy hgs.1 hgs.2
  have hr3 : ∀ j, j < (y.cn nw.gs).length → (y.cn nw.gs).getD j 0 % 4 < 3 := fun j hj => (hval j hj).1
  have hsel := selD_eq hR (Hh a b y) (y.cn nw.gs) hH hch hzc hacc hw2 hw1 hr3
  intro k _
  show refT T (Hh a b y) z.val k = refT T (Hh a b y) (cx3 x0 x1 x2 (selD (refT T (Hh a b y) c.val k))).val
    (cnt (fun i => selD (refT T (Hh a b y) c.val i) == selD (refT T (Hh a b y) c.val k)) k)
  simp only [hsel]
  rw [ref_hist T _ hdz hnf, Hh_pr hgz]
  have hc0 := hcnt 0 (by simp)
  simp only [List.getD_cons_zero] at hc0
  by_cases hL : y.cn nw.gs = []
  · have hz0 : y.pr nw.gz = [] := List.eq_nil_of_length_eq_zero (by rw [hlen, hL]; rfl)
    have hx0 : y.cn nw.g0 = [] := List.eq_nil_of_length_eq_zero (by rw [hc0, hL]; rfl)
    rw [hz0, hL, perL_nil, perL_nil]
    show nw.dz = refT T (Hh a b y) x0.val _
    rw [ref_hist T _ hd0 hnf, Hh_cn hy hg0.1 hg0.2, hx0, perL_nil, hdz0]
  · have hn := len_pos hL
    have hj : k % (y.cn nw.gs).length < (y.cn nw.gs).length := Nat.mod_lt _ hn
    obtain ⟨_, hv⟩ := hval _ hj
    rw [perL_of_len (m := (y.cn nw.gs).length) hlen hn, hv, perL_ne hL]
    have step : ∀ (m : Nat) (xm : Fin n) (gm dm : Nat), T.d xm.val = .hist gm dm → NoEnd gm →
        [nw.g0, nw.g1, nw.g2].getD m 0 = gm → m < 3 →
        (y.cn nw.gs).getD (k % (y.cn nw.gs).length) 0 % 4 = m →
        (y.cn gm).getD (cntm (y.cn nw.gs) 2 m (k % (y.cn nw.gs).length)) 0 =
          refT T (Hh a b y) xm.val (cnt (fun i => perL (y.cn nw.gs) 0 i % 4 == m) k) := by
      intro m xm gm dm hdm hne hgm hm3 hvm
      rw [ref_hist T _ hdm hnf, Hh_cn hy hne.1 hne.2]
      have hcm := hcnt m (by simp; omega)
      rw [hgm] at hcm
      have hp : (fun v => v % 4 == m) ((y.cn nw.gs).getD (k % (y.cn nw.gs).length) 0) = true := by
        show (_ % 4 == m) = true; rw [hvm]; simp
      have := per_pick (fun v => v % 4 == m) hcm k hL hp dm
      rw [this]; rfl
    have hv3 := hr3 _ hj
    have e2 : ∀ v : Nat, v % 2 ^ 2 = v % 4 := fun v => rfl
    rcases (show (y.cn nw.gs).getD (k % (y.cn nw.gs).length) 0 % 4 = 0 ∨
        (y.cn nw.gs).getD (k % (y.cn nw.gs).length) 0 % 4 = 1 ∨
        (y.cn nw.gs).getD (k % (y.cn nw.gs).length) 0 % 4 = 2 by omega) with e | e | e
    · rw [e2, e]; exact step 0 x0 nw.g0 nw.d0 hd0 hg0 rfl (by omega) e
    · rw [e2, e]; exact step 1 x1 nw.g1 nw.d1 hd1 hg1 rfl (by omega) e
    · rw [e2, e]; exact step 2 x2 nw.g2 nw.d2 hd2 hg2 rfl (by omega) e

/-! ## The rest, and the dispatch -/

theorem ref_same (H : Nat → List Nat) {c c' : Nat} (h : T.d c = T.d c') (k : Nat) :
    refT T H c k = refT T H c' k := by
  unfold refT
  cases T.nf with
  | zero => rfl
  | succ f => simp only [refF, h]

theorem eqn_sound (hy : Good a b y) (hR : RankOK T) (hnf : 0 < T.nf) (ch : Fin n → Chan) (k : K n)
    (hc : OpChk T k) :
    Eqn ch (fun w => (T.w w).om (Hh a b y)) (srcVal a b) k (fun c i => refT T (Hh a b y) c.val i) := by
  cases k with
  | forkG i os =>
    intro o ho k; exact ref_copy T _ hR (hc o ho) k
  | forkH i os l h d hs => exact sound_forkH hy hnf hc
  | join ins o e js jw => exact sound_join hy hnf hc
  | bjoin ins o ec ed => exact sound_bjoin hR hc _
  | steerC j t f => exact sound_steerC hnf hc _
  | steerD j t f fd sw => exact sound_steerD hy hR hnf hc
  | mux c x y' z mw => exact sound_mux hy hR hnf hc
  | muxn c x0 x1 x2 z nw => exact sound_muxn hy hR hnf hc
  | amerge x y' z w =>
    apply Capstone.amergeOff_of_eq
    intro k
    exact ref_cmz T _ hR hc.1 k
  | link i o =>
    intro k
    rcases hc with h | h
    · exact ref_same _ h k
    · exact ref_copy T _ hR h k
  | src z which d =>
    intro k
    rcases hc with ⟨hw, hd⟩ | ⟨hw, hd⟩
    · show refT T (Hh a b y) z.val k = srcVal a b which
      have h0 : Hh a b y which = [srcVal a b which] := by
        simp only [Hh, hy.np which (env_np which (by omega)), List.append_nil]; exact init_src a b which hw
      rw [ref_hist T _ hd hnf, h0]; simp [perL, Nat.mod_one]
    · subst hw
      show refT T (Hh a b y) z.val k = srcVal a b (nIn - 1)
      rw [src_start]
      exact ref_zero T _ hd hnf k
  | sink i => trivial

end Formal.Net.KCap
