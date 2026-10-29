import Formal.Net.CapstoneWalk
import Formal.Net.OpsBusyHeld

/-!
# Probe C-8x2: the gcd_hw capstone on the relaxed (busy-gated) gate models

C-8r/8s's proof (`CapstoneCut.main`, `gcd_hw_forced`, `CapstoneSafe.gcd_hw_circuit_safe`,
`CapstoneWalk.gcd_hw_circuit_safe3`) re-run with `CellB` (OpsBusy) in place of `Cell`. The text
of `forc_at`/`agr_at`/`rise_cur`/`main` is C-8r's, with each use of a cell's gate model replaced
by its relaxed counterpart: `cell_op_B` for the operator data specs, `amerge_data_upto_B` for the
arbiter, and the old-structure views `*.toOld` (output buses re-labelled, handshake wires
unchanged) for the handshake-only facts (`fork_strict`, `join_strict`, `link_strict`,
`steer_strict`, `offer_pending`; the winner stream is unchanged, `AMergeB.winner_eq`).

* `disj_ok`: no gcd_hw operator has a channel as both input and output (kernel `decide`).
* `gcd_hw_init_B`, `gcd_hw_protocol_B`: reset / four-phase protocol from the relaxed cells.
* **`gcd_hw_circuit_safe3B`**: `gcd_hw_circuit_safe3` with H_CELLS relaxed to `CellB`.
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw
open Formal.Net.CapSafe Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut Formal.Net.OpsBusy

set_option maxRecDepth 100000

theorem disj_all1 : (ops.take 120).all (fun k => decide (Disj k)) = true := by decide +kernel
theorem disj_all2 : ((ops.drop 120).take 120).all (fun k => decide (Disj k)) = true := by
  decide +kernel
theorem disj_all3 : ((ops.drop 120).drop 120).all (fun k => decide (Disj k)) = true := by
  decide +kernel

theorem disj_all : ops.all (fun k => decide (Disj k)) = true := by
  rw [← List.take_append_drop 120 ops, List.all_append, disj_all1, ← List.take_append_drop 120 (ops.drop 120),
    List.all_append, disj_all2, disj_all3]; rfl

theorem disj_ok (o : Fin NO) : Disj (opAt o) :=
  of_decide_eq_true (List.all_eq_true.mp disj_all _ getD_mem)

/-- Reset of every channel, from the relaxed gate models alone. -/
theorem gcd_hw_init_B (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o)) : ∀ c, Init (ch c) := fun c =>
  ⟨(cell_proto_B ch (srcV a b) (opAt (net.prod c)) (H_CELLS_B _) (dist_of _ (ops_ok _))
      (disj_ok _)).initOut c ((net.prod_iff c _).2 rfl),
   (cell_proto_B ch (srcV a b) (opAt (net.cons c)) (H_CELLS_B _) (dist_of _ (ops_ok _))
      (disj_ok _)).initIn c ((net.cons_iff c _).2 rfl)⟩

theorem gcd_hw_protocol_B (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) : ∀ c, Protocol (ch c) :=
  net_protocol net ch (fun o => cell_proto_B ch (srcV a b) (opAt o) (H_CELLS_B o)
    (dist_of _ (ops_ok o)) (disj_ok o)) H_BUNDLE

section mainB
variable {a b : Nat} {ch : Fin NC → Chan} {y : TS}
variable (hy : Good a b y)
variable (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
variable (H_BUNDLE : ∀ c, Held (ch c))
variable (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
variable (H_WALK : WalkOK (σY a b y) (omOf a b y))

include H_CELLS_B H_BUNDLE H_WALK in
/-- Forcing at time `t`, from `Inv t` and the forcing before `t`. -/
theorem forc_atB (t : Nat) (hinv : Inv a b ch y t) (hf : ForcB a b ch y t) : ForcB a b ch y (t + 1) := by
  intro o x u z w ho k r hr hoff
  rcases Nat.lt_or_ge r t with hlt | hge
  · exact hf o x u z w ho k r hlt hoff
  have hrt : r = t := by omega
  subst hrt
  have hp := gcd_hw_protocol_B a b ch H_CELLS_B H_BUNDLE
  obtain ⟨p, hp'⟩ := hinv
  have hs := spok o
  rw [ho] at hs
  simp only [SpOK, Bool.and_eq_true, bne_iff_ne, ne_eq] at hs
  have hc := H_CELLS_B o
  rw [ho] at hc
  obtain ⟨g1, g2, MB⟩ := hc
  obtain ⟨py, px⟩ := offer_pending MB.toOld (hp x) (hp u) (hp z) hoff
  rw [MB.winner_eq] at py px
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

include hy H_CELLS_B H_BUNDLE in
/-- Values at time `t`, from the values before `t` and the forcing up to `t`. -/
theorem agr_atB (t : Nat) (hag : Agree ch (σY a b y) t) (hf : ForcB a b ch y (t + 1)) :
    Agree ch (σY a b y) (t + 1) := by
  intro c k r hr hoff
  rcases Nat.lt_or_ge r t with hlt | hge
  · exact hag c k r hlt hoff
  have hrt : r = t := by omega
  subst hrt
  have hp := gcd_hw_protocol_B a b ch H_CELLS_B H_BUNDLE
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
    have hc := H_CELLS_B o
    rw [hk] at hc
    obtain ⟨g1, g2, M⟩ := hc
    exact amerge_data_upto_B ch x u c g1 g2 M hdist.1 hdist.2 (omOf a b y w) (hPH _) (hPH _) hoff
      (fun j r' hr' ho' => hf o x u c w hk j r' (by omega) ho') (σY a b y) hag hE
  | _ =>
    have hop := cell_op_B ch (omOf a b y) (srcV a b) (opAt o) (H_CELLS_B o) (by rw [hk]; trivial) hdist
      (disj_ok o)
    exact hop.2 (hPH _) (hPH _) c hco k r hoff (σY a b y) hag hE

include H_CELLS_B H_BUNDLE H_START_ONCE H_WALK in
/-- A spine channel can rise at `t` only if it is the walk's next channel. -/
theorem rise_curB (t p : Nat) (hinv : ∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) p).W c)
    (hag : Agree ch (σY a b y) t) (hf : ForcB a b ch y (t + 1))
    (c : Fin NC) (hsc : sp c = true) (hr : riseB (ch c).req t = true) :
    (walk (σY a b y) p).cur = some c := by
  have hp := gcd_hw_protocol_B a b ch H_CELLS_B H_BUNDLE
  have hct : cnt (riseB (ch c).req) (t + 1) = (walk (σY a b y) p).W c + 1 := by
    rw [cnt_succ_of hr, hinv c hsc]
  let o := prodOf c
  have hco : c ∈ (opAt o).outsC := prod_mem c
  have hs := spok o
  have hc := H_CELLS_B o
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
    have hb := fork_strict hc.toOld (hp i) (fun o' ho' => by
      obtain ⟨d', hd', e⟩ := List.mem_map.mp ho'
      obtain ⟨c', _, e'⟩ := List.mem_map.mp hd'
      rw [← e, ← e']; exact hp c') (List.mem_map_of_mem (List.mem_map_of_mem hco)) hr
    simp only [rel_req] at hb
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
    have hb := link_strict L.toOld (hp i) (hp c) hr
    simp only [rel_req] at hb
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
      have hb := join_strict hc.toOld (hp c) (fun i' hi' => by
        obtain ⟨c', _, e⟩ := List.mem_map.mp hi'; rw [← e]; exact hp c') (i := ch i) (by simp) hr
      simp only [rel_req] at hb
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
    have hb := steer_strict hc.toOld (hp j) (fun b' => hp _) (H_BUNDLE j) bb
      (by simp only [rel_req]; rw [← hbb]; exact hr)
    simp only [rel_req] at hb
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
    obtain ⟨g1, g2, MB⟩ := hc
    have hsx : sp x = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.1
    have hsu : sp u = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.2
    have hoff : OffAt (ch c) (walk (σY a b y) p |>.W c) t := ⟨hr, hinv c hsc⟩
    have hw := hf o x u c w hk _ t (Nat.lt_succ_self _) hoff
    obtain ⟨py, px⟩ := offer_pending MB.toOld (hp x) (hp u) (hp c) hoff
    rw [MB.winner_eq] at py px
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
      by_cases hw2 : which = 2
      · subst hw2; simpa [SpOK, hsc] using hs
      · simp [SpOK, hsc, hw2] at hs
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

include hy H_CELLS_B H_BUNDLE H_START_ONCE H_WALK in
/-- **The joint induction on time.** -/
theorem mainB : ∀ t, Inv a b ch y t ∧ ForcB a b ch y t ∧ Agree ch (σY a b y) t := by
  intro t
  induction t with
  | zero =>
    refine ⟨⟨0, fun c _ => rfl⟩, fun _ _ _ _ _ _ _ _ h _ => absurd h (Nat.not_lt_zero _),
      fun _ _ _ h _ => absurd h (Nat.not_lt_zero _)⟩
  | succ t ih =>
    obtain ⟨hinv, hf, hag⟩ := ih
    have hf' := forc_atB H_CELLS_B H_BUNDLE H_WALK t hinv hf
    have hag' := agr_atB hy H_CELLS_B H_BUNDLE t hag hf'
    refine ⟨?_, hf', hag'⟩
    obtain ⟨p, hp⟩ := hinv
    have hrc := rise_curB H_CELLS_B H_BUNDLE H_START_ONCE H_WALK t p hp hag hf'
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

end mainB

/-! ## The results -/

/-- **H_CM_FORCED, proved**: every arbiter stage's winner of every offered token is the token
run's label. -/
theorem gcd_hw_forcedB (a b : Nat) (ch : Fin NC → Chan) (y : TS) (hy : Good a b y)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_WALK : WalkOK (σY a b y) (omOf a b y)) :
    ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o) := by
  intro o
  cases hk : opAt o with
  | amerge x u z w =>
    intro k r hoff
    exact (mainB hy H_CELLS_B H_BUNDLE H_START_ONCE H_WALK (r + 1)).2.1 o x u z w hk k r
      (Nat.lt_succ_self _) hoff
  | _ => trivial


/-- 8m's `gcd_hw_circuit_safe` (modulo H_CM_FORCED) on the relaxed gate models. -/
theorem gcd_hw_circuit_safeB (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  obtain ⟨y, hy, hF⟩ := H_CM_FORCED
  have hop := fun o => cell_op_B ch (omOf a b y) (srcV a b) (opAt o) (H_CELLS_B o) (hF o)
    (dist_of _ (ops_ok o)) (disj_ok o)
  refine Capstone.latched_const net ch (fun o => Eqn ch (omOf a b y) (srcV a b) (opAt o))
    (fun o => (hop o).1) H_BUNDLE (fun o => (hop o).2) out0 (Nat.gcd a b)
    ⟨fun c i => refT tab (Hh a b y) c.val i, fun o => eqn_sound hy rank_ok nf_pos ch (opAt o) (ops_ok o),
      fun k => ?_⟩
  show refT tab (Hh a b y) out0.val k = Nat.gcd a b
  rw [ref_hist tab _ out0_desc nf_pos, out0_hist hy]
  simp [perL, Nat.mod_one]

/-- **gcd_hw circuit safety on the relaxed gate models**: for `a, b < 2^31`, every run of the
465-channel network whose operators meet the busy-gated gate models (`CellB`), whose channels
are bundled (H_BUNDLE) and whose `start` is offered at most once latches only `Nat.gcd a b` on
`out0`. Same conclusion as `gcd_hw_circuit_safe3`, weaker cell hypothesis (`cell_relax`). -/
theorem gcd_hw_circuit_safe3B (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  obtain ⟨y, hy, hw⟩ := gcd_hw_walk a b ha hb
  exact gcd_hw_circuit_safeB a b ch H_CELLS_B H_BUNDLE
    ⟨y, hy, gcd_hw_forcedB a b ch y hy H_CELLS_B H_BUNDLE H_START_ONCE hw⟩

end Formal.Net.CapNet.Gcd
