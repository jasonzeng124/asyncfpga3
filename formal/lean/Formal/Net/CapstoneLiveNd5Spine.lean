import Formal.Net.CapstoneLiveNd2

/-!
# Probe C-8z5 (1): where the control token can be stuck in a quiescent gcd_hw state

H_NO_DEADLOCK'' (C-8z2, `Nd2.NoDeadlock2`) says: before out0's first close, the circuit state
is not quiescent (`QuietQ`: no gate other than `start`'s LUT excited, `start` offered if it is
its turn, `start`'s release not pending). This file proves the spine half of route B
(C-8u/C-8z4): **the case analysis of a quiescent state on 8r's walk invariant `Inv`.**

`spine_local`: for `a, b < 2^31` and every run meeting H_CELLS, H_BUNDLE and H_START_ONCE, at
every tick `t` whose state is quiescent (`QuietQ`), with `q` the walk position given by 8r's
`Inv t` (spine offer counts = walk visit counts), either the walk has ended, or its current
channel `c` (the next spine channel to be offered) is `Blocked`:
* `c` is a **link** output: the link's input holds the token (`req` high, `ack` low, node
  low) and `c` is in its return phase (`req` low, `ack` high): `c`'s consumer has not yet
  released the previous spine token;
* `c` is a **bjoin** output: the spine (data) input holds the token, and the condition
  input has not been offered (`req` and `ack` low);
* `c` is an **arbiter** output: the pending input holds the token, and either `z` still holds
  the other input's grant (`z` requested, the other grant high), or `z` is returning
  (`req` low, `ack` high, the other input's acknowledge still high).
No other producer kind is possible: a quiescent state with the walk at a fork, steer or at
`start` does not exist (each of these would have an excited gate).

What this does NOT show: that a `Blocked` state is unreachable. Each blocked reason is a wait
on a neighbour (the consumer of `c`, a condition channel, or the other arbiter input); ruling
those out is the open data-arrival / return-to-zero part of H_NO_DEADLOCK'' (C-8z5 note).
-/

namespace Formal.Net.CapNet.Live.Nd5
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd
open Formal.Net.CapSafe (Good TS texec)
open Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut
open Formal.Cells.LinkHandshake (ctlB)
open Formal.Net.Ops.Link (ltbl LS)

set_option maxRecDepth 100000

/-- The quiescence of H_NO_DEADLOCK'' at tick `t` (`Nd2.NoDeadlock2` is `∀ t, out0 not closed
before t → ¬ QuietQ ch itr t`). -/
def QuietQ (ch : Fin NC → Chan) (itr : Itr) (t : Nat) : Prop :=
  Quiet2 (gsAt ch itr t) ∧
  (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true) ∧
  ¬ ((ch start).req t = true ∧ (ch start).ack t = true)

theorem nd2_iff (ch : Fin NC → Chan) (itr : Itr) :
    Nd2.NoDeadlock2 ch itr ↔ ∀ t, cnt (fallB (ch out0).ack) t = 0 → ¬ QuietQ ch itr t :=
  Iff.rfl

theorem quiet_gate {s : GS} (hq : Quiet2 s) {p : Fin NO} (hp : p ≠ prodOf start) {g : Gate}
    (hg : g ∈ gatesK p (opAt p)) {v : Bool} (he : g.exc v s) : g.out s = v :=
  hq p hp g (List.mem_append_left _ hg) v he

theorem quiet_grant {s : GS} (hq : Quiet2 s) {p : Fin NO} (hp : p ≠ prodOf start) {g : Gate}
    (hg : g ∈ grantsK p (opAt p)) {v : Bool} (he : g.exc v s) : g.out s = v :=
  hq p hp g (List.mem_append_right _ hg) v he

theorem ne_pstart {p : Fin NO} (h : ∀ z w d, opAt p ≠ .src z w d) : p ≠ prodOf start := by
  intro e; subst e; exact h _ _ _ prod_start

/-! ## Local tables -/

/-- A quiescent link whose output count lags its input by exactly the input's open token. -/
theorem link_quiet_tbl : ∀ e ∈ ltbl, e.c = ctlB e.ir e.oa e.c false → e.ia = e.c → e.orq = e.c →
    e.d = (if (e.ir || e.ia) = true then 1 else 0) →
    e.ir = true ∧ e.ia = false ∧ e.c = false ∧ e.orq = false ∧ e.oa = true := by
  decide

/-- Quiescence of the five gates of an arbiter stage (`z_req`, both input acknowledges, both
grants), as a property of its local state. -/
def QA (e : CM.AS) : Prop :=
  ((e.g1 || e.g2) = true → e.xa = false → e.ya = false → e.zr = true) ∧
  ((e.g1 || e.g2) = false → e.zr = false) ∧
  (e.g1 = true → e.za = true → e.xa = true) ∧ (e.g1 = false → e.za = false → e.xa = false) ∧
  (e.g2 = true → e.za = true → e.ya = true) ∧ (e.g2 = false → e.za = false → e.ya = false) ∧
  ((e.xr && !e.g2 && !e.za) = true → e.g1 = true) ∧ (e.xr = false → e.g1 = false) ∧
  ((e.yr && !e.g1 && !e.za) = true → e.g2 = true) ∧ (e.yr = false → e.g2 = false)

instance (e : CM.AS) : Decidable (QA e) := by unfold QA; exact inferInstance

/-- Why an arbiter stage with a pending token on input `x` (resp. `y`) can be quiescent: `z`
holds the other input's grant (and is unacknowledged, or both `z` and the other input are
mid-return), or `z` is returning with the other input's acknowledge still high. -/
def BlkX (xr xa yr ya g1 g2 zr za : Bool) : Prop :=
  xr = true ∧ xa = false ∧ g1 = false ∧
    ((g2 = true ∧ zr = true ∧ (za = false ∨ (yr = true ∧ ya = true))) ∨
     (g2 = false ∧ zr = false ∧ za = true ∧ yr = false ∧ ya = true))

instance (xr xa yr ya g1 g2 zr za : Bool) : Decidable (BlkX xr xa yr ya g1 g2 zr za) := by
  unfold BlkX; exact inferInstance

theorem amerge_quiet_tbl : ∀ e ∈ CM.atbl, QA e →
    (e.dx = 2 → e.dy = 1 → BlkX e.xr e.xa e.yr e.ya e.g1 e.g2 e.zr e.za) ∧
    (e.dy = 2 → e.dx = 1 → BlkX e.yr e.ya e.xr e.xa e.g2 e.g1 e.zr e.za) := by
  decide +kernel

/-! ## The blocked positions -/

/-- The walk's current channel `c` is blocked at tick `t`, for one of the three local reasons. -/
def Blocked (ch : Fin NC → Chan) (itr : Itr) (t : Nat) (c : Fin NC) : Prop :=
  (∃ p i, opAt p = .link i c ∧ (ch i).req t = true ∧ (ch i).ack t = false ∧ itr p 0 t = false ∧
      (ch c).req t = false ∧ (ch c).ack t = true) ∨
  (∃ p k d ec ed, opAt p = .bjoin [k, d] c ec ed ∧ (ch d).req t = true ∧
      (ch k).req t = false ∧ (ch k).ack t = false ∧ (ch c).req t = false ∧ (ch c).ack t = false) ∨
  (∃ p x u w, opAt p = .amerge x u c w ∧
      (BlkX ((ch x).req t) ((ch x).ack t) ((ch u).req t) ((ch u).ack t) (itr p 0 t) (itr p 1 t)
          ((ch c).req t) ((ch c).ack t) ∨
       BlkX ((ch u).req t) ((ch u).ack t) ((ch x).req t) ((ch x).ack t) (itr p 1 t) (itr p 0 t)
          ((ch c).req t) ((ch c).ack t)))


section
variable {a b : Nat} {ch : Fin NC → Chan} {itr : Itr} {y : TS}
variable (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
variable (H_BUNDLE : ∀ c, Held (ch c))
variable (H_WALK : WalkOK (σY a b y) (omOf a b y))

include H_CELLS H_BUNDLE H_WALK in
/-- **The case analysis.** At a quiescent tick, with the spine counts equal to the walk's
visit counts after `q` steps, the walk's current channel is `Blocked`. -/
theorem cur_blocked (t q : Nat)
    (hinv : ∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) q).W c)
    (hag : Agree ch (σY a b y) t) (hf : ForcB a b ch y t) (hq : QuietQ ch itr t)
    (c : Fin NC) (hcur : (walk (σY a b y) q).cur = some c) : Blocked ch itr t c := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hp := gcd_hw_protocol a b ch hC H_BUNDLE
  have hsc : sp c = true := cur_sp _ q c hcur
  have hfl := flow (σY a b y) q c
  rw [hcur] at hfl
  simp only [beq_self_eq_true, Gcd.bn, ite_true] at hfl
  let o := prodOf c
  have hco : c ∈ (opAt o).outsC := prod_mem c
  have hs := spok o
  have hc := H_CELLS o
  have hQ := hq.1
  have hcs : ∀ (K' : K NC), opAt o = K' → (∀ z w d, K' ≠ .src z w d) → c ≠ start := by
    intro K' hK hK'; apply ne_start; intro z w d e; exact hK' z w d (hK ▸ e)
  have hops : ∀ (K' : K NC), opAt o = K' → (∀ z w d, K' ≠ .src z w d) → o ≠ prodOf start := by
    intro K' hK hK'; apply ne_pstart; intro z w d e; exact hK' z w d (hK ▸ e)
  cases hk : opAt o with
  | forkG i os =>
    exfalso
    have hcs' := hcs _ hk (by intros; simp)
    have hop := hops _ hk (by intros; simp)
    rw [hk] at hco hs hc
    simp only [K.outsC] at hco
    have hsi : sp i = true := by
      cases hsi : sp i
      · simp only [SpOK, hsi, Bool.false_eq_true, ite_false, List.all_eq_true] at hs
        have := hs c hco; simp [hsc] at this
      · rfl
    simp only [SpOK, hsi, ite_true, beq_iff_eq] at hs
    have hin := hin_one (σY a b y) (c := c) (i := i)
      (by intro d _ hd; rw [show prodOf c = o from rfl, hk] at hd; simpa [K.insC] using hd)
      (by rw [show prodOf c = o from rfl, hk]; simp [K.insC])
      (fun k => by
        have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
        rw [nxt_forkG _ (by rw [hio, hk])]; exact find_one hs hco hsc)
    have h1 := in_cp _ hin q
    have hcnt := fork_cnt (hc : Fork.Fork (ch i) (os.map ch)) (hp i)
      (fun o' ho' => by obtain ⟨c', _, e⟩ := List.mem_map.mp ho'; rw [← e]; exact hp c')
      (ch c) (List.mem_map_of_mem hco) t
    rw [hinv i hsi, hinv c hsc] at hcnt
    have h0 : (c == start) = false := by simp [hcs']
    rw [h0] at hfl; simp only [Bool.false_eq_true, ite_false] at hfl
    have hb : ((ch i).req t && !(ch c).req t) = true := by
      cases hb : ((ch i).req t && !(ch c).req t)
      · rw [hb] at hcnt; simp at hcnt; omega
      · rfl
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
    have hg : gw (fun s => s.rq c) (fun s => s.rq i) ∈ gatesK o (opAt o) := by
      rw [hk]; simp only [gatesK]
      exact List.mem_append_left _ (List.mem_map_of_mem hco)
    have := quiet_gate hQ hop hg (v := true) (by simp [gw, gsAt, hb.1])
    simp [gw, gsAt, hb.2] at this
  | link i o' =>
    have hcs' := hcs _ hk (by intros; simp)
    have hop := hops _ hk (by intros; simp)
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    simp only [SpOK, beq_iff_eq] at hs
    have hsi : sp i = true := by rw [hs]; exact hsc
    have L : Link.Link (ch i) (ch c) (itr o 0) := hc
    have hin := hin_one (σY a b y) (c := c) (i := i)
      (by intro d _ hd; rw [show prodOf c = o from rfl, hk] at hd; simpa [K.insC] using hd)
      (by rw [show prodOf c = o from rfl, hk]; simp [K.insC])
      (fun k => by
        have hio : consOf i = o := cons_in o i (by rw [hk]; simp [K.insC])
        exact nxt_link _ (by rw [hio, hk]) hsc)
    have h1 := in_cp _ hin q
    have h0 : (c == start) = false := by simp [hcs']
    rw [h0] at hfl; simp only [Bool.false_eq_true, ite_false] at hfl
    obtain ⟨d, q', hm, hd1, -, -⟩ := Link.link_step L (hp i) (hp c) t
    have hri := rise_inv (hp i) t
    rw [hinv i hsi] at hri
    rw [hinv c hsc] at hd1
    have hmem := Link.lmem hm
    have g0 : itr o 0 t = ctlB ((ch i).req t) ((ch c).ack t) (itr o 0 t) false := by
      have hg : gw (fun s => s.it o 0) (fun s => ctlB (s.rq i) (s.ak c) (s.it o 0) false) ∈
          gatesK o (opAt o) := by rw [hk]; simp [gatesK]
      exact quiet_gate hQ hop hg (v := ctlB ((ch i).req t) ((ch c).ack t) (itr o 0 t) false)
        (by simp [gw, gsAt])
    have g1 : (ch i).ack t = itr o 0 t := by
      have hg : gw (fun s => s.ak i) (fun s => s.it o 0) ∈ gatesK o (opAt o) := by
        rw [hk]; simp [gatesK]
      exact quiet_gate hQ hop hg (v := itr o 0 t) (by simp [gw, gsAt])
    have g2 : (ch c).req t = itr o 0 t := by
      have hg : gw (fun s => s.rq c) (fun s => s.it o 0) ∈ gatesK o (opAt o) := by
        rw [hk]; simp [gatesK]
      exact quiet_gate hQ hop hg (v := itr o 0 t) (by simp [gw, gsAt])
    have hdd : d = (if ((ch i).req t || (ch i).ack t) = true then 1 else 0) := by
      have e1 : (walk (σY a b y) q).W c + 1 = (walk (σY a b y) q).W i := by rw [← h1]; exact hfl
      have hri' : (walk (σY a b y) q).W i = cnt (fallB (ch i).ack) t +
          (if ((ch i).req t || (ch i).ack t) = true then 1 else 0) := hri
      omega
    have K := link_quiet_tbl _ hmem g0 g1 g2 hdd
    simp only [Link.lst] at K
    exact Or.inl ⟨o, i, hk, K.1, K.2.1, K.2.2.1, K.2.2.2.1, K.2.2.2.2⟩
  | bjoin ins o' ec ed =>
    have hcs' := hcs _ hk (by intros; simp)
    have hop := hops _ hk (by intros; simp)
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    simp only [SpOK, hsc, Bool.not_true, Bool.false_or] at hs
    have h0 : (c == start) = false := by simp [hcs']
    rw [h0] at hfl; simp only [Bool.false_eq_true, ite_false] at hfl
    match ins, hs, hc, hk with
    | [cd, i], hs, hc, hk =>
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hs
      have J : Join.Join (bg ec ed) ([cd, i].map ch) (ch c) := hc
      have hcnt := join_cnt J (hp c) (fun i' hi' => by
        obtain ⟨c', _, e⟩ := List.mem_map.mp hi'; rw [← e]; exact hp c') (ch i) (by simp) t
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
      have h1 := in_cp _ hin q
      rw [hinv i hs.2, hinv c hsc] at hcnt
      have hb : (!(ch c).req t && !(ch c).ack t && (ch i).req t) = true := by
        cases hb : (!(ch c).req t && !(ch c).ack t && (ch i).req t)
        · rw [hb] at hcnt; simp at hcnt; omega
        · rfl
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨⟨hrc, hac⟩, hri⟩ := hb
      have hrk : (ch cd).req t = false := by
        cases hrk : (ch cd).req t
        · rfl
        · exfalso
          have hg : (⟨fun s => s.rq c, fun v s => ∀ x ∈ [cd, i], s.rq x = v⟩ : Gate) ∈
              gatesK o (opAt o) := by rw [hk]; simp [gatesK]
          have := quiet_gate hQ hop hg (v := true) (by simp [gsAt, hrk, hri])
          simp [gsAt, hrc] at this
      have hak : (ch cd).ack t = false := by
        have hg : gw (fun s => s.ak cd) (fun s => s.ak c) ∈ gatesK o (opAt o) := by
          rw [hk]; simp [gatesK]
        have := quiet_gate hQ hop hg (v := false) (by simp [gw, gsAt, hac])
        simpa [gw, gsAt] using this
      exact Or.inr (Or.inl ⟨o, cd, i, ec, ed, hk, hri, hrk, hak, hrc, hac⟩)
  | steerC j tt ff =>
    exfalso
    have hcs' := hcs _ hk (by intros; simp)
    have hop := hops _ hk (by intros; simp)
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
    obtain ⟨bb, hbb⟩ : ∃ bb : Bool, c = (bif bb then tt else ff) := by
      rcases hco with e | e
      · exact ⟨true, e⟩
      · exact ⟨false, e⟩
    have S : Steer.Steer sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then tt else ff)) := hc
    have hcnt := steer_cnt S (hp j) (fun b' => hp _) (H_BUNDLE j) bb t
    rw [← hbb] at hcnt
    have hsel : selOff sel2 (ch j) bb t =
        cnt (fun i => sel2 (σY a b y j i) == bb) (cnt (riseB (ch j).req) t) :=
      cnt_offers (σ := σY a b y j) (fun v => sel2 v == bb)
        (fun i u hu ho => hag j i u hu ho) t (Nat.le_refl _)
    rw [hsel, hinv j hsj, hinv c hsc] at hcnt
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
    have h1 := in_st _ hin q
    have h0 : (c == start) = false := by simp [hcs']
    rw [h0] at hfl; simp only [Bool.false_eq_true, ite_false] at hfl
    have hb : ((ch j).req t && (sel2 ((ch j).dat t) == bb) && !(ch c).req t) = true := by
      cases hb : ((ch j).req t && (sel2 ((ch j).dat t) == bb) && !(ch c).req t)
      · rw [hb] at hcnt; simp at hcnt; omega
      · rfl
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hb
    obtain ⟨⟨hrj, hsl⟩, hrc⟩ := hb
    cases bb
    · have hg : gw (fun s => s.rq ff) (fun s => s.rq j && (sel2 (s.dt j) == false)) ∈
          gatesK o (opAt o) := by rw [hk]; simp [gatesK]
      have := quiet_gate hQ hop hg (v := true) (by simp only [gw, gsAt]; rw [hrj, hsl]; rfl)
      simp only [gw, gsAt] at this
      rw [hbb] at hrc; simp at hrc; rw [hrc] at this; exact absurd this (by decide)
    · have hg : gw (fun s => s.rq tt) (fun s => s.rq j && (sel2 (s.dt j) == true)) ∈
          gatesK o (opAt o) := by rw [hk]; simp [gatesK]
      have := quiet_gate hQ hop hg (v := true) (by simp only [gw, gsAt]; rw [hrj, hsl]; rfl)
      simp only [gw, gsAt] at this
      rw [hbb] at hrc; simp at hrc; rw [hrc] at this; exact absurd this (by decide)
  | src z which d =>
    exfalso
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    have hcs2 : c = start := by
      by_cases hw2 : which = 2
      · subst hw2; simpa [SpOK, hsc] using hs
      · simp [SpOK, hsc, hw2] at hs
    subst hcs2
    have hf' := tr_start (σY a b y) q
    rw [hf'] at hfl
    simp at hfl
    have h0 := hinv start sp_start
    rw [hfl] at h0
    have hri := rise_inv (hp start) t
    rw [h0] at hri
    have hreq : (ch start).req t = false := by
      cases h : (ch start).req t
      · rfl
      · simp [inTx, h] at hri
    have hack : (ch start).ack t = false := by
      cases h : (ch start).ack t
      · rfl
      · simp [inTx, h] at hri
    have := hq.2.1 h0 hack
    rw [hreq] at this; exact absurd this (by decide)
  | forkH i os l h d hs' =>
    exfalso
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_map] at hco
    obtain ⟨pr, hpr, e⟩ := hco
    simp only [SpOK, List.all_eq_true] at hs
    have := hs pr hpr; rw [e] at this; simp [hsc] at this
  | join ins o' e js jw =>
    exfalso
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | steerD j tt ff fd sw =>
    exfalso
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hco
    simp only [SpOK, Bool.and_eq_true, Bool.not_eq_true'] at hs
    rcases hco with e | e <;> subst e
    · rw [hs.1] at hsc; exact absurd hsc (by decide)
    · rw [hs.2] at hsc; exact absurd hsc (by decide)
  | mux cc xx yy zz mw =>
    exfalso
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | muxn cc x0 x1 x2 zz nw =>
    exfalso
    rw [hk] at hco hs
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco; simp [SpOK, hsc] at hs
  | sink i =>
    exfalso
    rw [hk] at hco
    simp [K.outsC] at hco
  | amerge x u z w =>
    have hcs' := hcs _ hk (by intros; simp)
    have hop := hops _ hk (by intros; simp)
    rw [hk] at hco hs hc
    simp only [K.outsC, List.mem_singleton] at hco
    subst hco
    have M : CM.AMerge (ch x) (ch u) (ch c) (itr o 0) (itr o 1) := hc
    have hsx : sp x = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.1
    have hsu : sp u = true := by simp only [SpOK, Bool.and_eq_true] at hs; exact hs.1.1.2
    obtain ⟨dx, dy, hm, hx1, hu1⟩ := CM.amerge_inv M (hp x).1.1 (hp u).1.1 (hp c).1.2 t
      (fun s _ => ⟨((hp x).2 s).1, ((hp u).2 s).1, ((hp c).2 s).2⟩)
    obtain ⟨e0, e1⟩ := zc_eq M t
    rw [e0] at hx1; rw [e1] at hu1
    have hpre : ∀ i, i < cnt (riseB (ch c).req) t → CM.winner (ch c) i = omOf a b y w i := by
      intro i hi
      obtain ⟨r, hr⟩ := offered_lt hi
      have hrt : r < t := by
        rcases Nat.lt_or_ge r t with h | h
        · exact h
        · have := cnt_mono (riseB (ch c).req) h; rw [hr.2] at this; omega
      exact hf o x u c w hk i r hrt hr
    have c1 := CM.cnt_congr_lt _ hpre
    have c0 : cnt (fun i => !CM.winner (ch c) i) (cnt (riseB (ch c).req) t) =
        cnt (fun i => !omOf a b y w i) (cnt (riseB (ch c).req) t) :=
      CM.cnt_congr_lt _ (fun i hi => by rw [hpre i hi])
    rw [c1, hinv c hsc, hinv u hsu] at hu1
    rw [c0, hinv c hsc, hinv x hsx] at hx1
    obtain ⟨ey, ex⟩ := am_counts H_WALK hk q
    rw [hcur] at ey ex
    simp only [beq_self_eq_true, Bool.true_and] at ey ex
    -- the quiescence of the five gates
    have G : ∀ (g : Gate), g ∈ gatesK o (opAt o) ++ grantsK o (opAt o) →
        ∀ v, g.exc v (gsAt ch itr t) → g.out (gsAt ch itr t) = v := fun g hg => hQ o hop g hg
    rw [hk] at G
    simp only [gatesK, grantsK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at G
    have Gz := G _ (Or.inl (Or.inl rfl))
    have Gx := G _ (Or.inl (Or.inr (Or.inl rfl)))
    have Gy := G _ (Or.inl (Or.inr (Or.inr rfl)))
    have G1 := G _ (Or.inr (Or.inl rfl))
    have G2 := G _ (Or.inr (Or.inr rfl))
    simp only [gsAt] at Gz Gx Gy G1 G2
    have hQA : QA (CM.ast (ch x) (ch u) (ch c) (itr o 0) (itr o 1) t dx dy) := by
      simp only [QA, CM.ast]
      refine ⟨fun h1 h2 h3 => Gz true ⟨h1, fun _ => ⟨h2, h3⟩⟩, fun h1 => Gz false ⟨h1, nofun⟩,
        fun h1 h2 => Gx true ⟨h1, h2⟩, fun h1 h2 => Gx false ⟨h1, h2⟩,
        fun h1 h2 => Gy true ⟨h1, h2⟩, fun h1 h2 => Gy false ⟨h1, h2⟩,
        fun h1 => G1 true ⟨fun _ => h1, nofun⟩, fun h1 => G1 false ⟨nofun, fun _ => h1⟩,
        fun h1 => G2 true ⟨fun _ => h1, nofun⟩, fun h1 => G2 false ⟨nofun, fun _ => h1⟩⟩
    have K := amerge_quiet_tbl _ (CM.amem hm) hQA
    simp only [CM.ast] at K
    refine Or.inr (Or.inr ⟨o, x, u, w, hk, ?_⟩)
    cases hω : omOf a b y w ((walk (σY a b y) q).W c)
    · rw [hω] at ey ex
      simp [Gcd.bn] at ey ex
      exact Or.inl (K.1 (by omega) (by omega))
    · rw [hω] at ey ex
      simp [Gcd.bn] at ey ex
      exact Or.inr (K.2 (by omega) (by omega))

end

/-- **Spine localisation of a quiescent gcd_hw state.** For `a, b < 2^31` and every run meeting
H_CELLS, H_BUNDLE and H_START_ONCE: at any tick whose state is quiescent in the sense of
H_NO_DEADLOCK'' (`QuietQ`), there is a complete token run `y` and a walk position `q` such
that the spine offer counts are the walk's visit counts (8r's `Inv`) and either the walk has
ended or its current channel is `Blocked` (a link output returning, a bjoin waiting for its
condition, or an arbiter stage held by its other input / by `z`'s return). In particular the
walk is never at a fork, steer or `start` in a quiescent state. -/
theorem spine_local (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (t : Nat) (hq : QuietQ ch itr t) :
    ∃ y, Good a b y ∧ ∃ q,
      (∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) q).W c) ∧
      ((walk (σY a b y) q).cur = none ∨
        ∃ c, (walk (σY a b y) q).cur = some c ∧ Blocked ch itr t c) := by
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  have hW := walk_ok hy hex
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  obtain ⟨⟨q, hinv⟩, hf, hag⟩ := Gcd.main hy hC H_BUNDLE H_START_ONCE hW t
  refine ⟨y, hy, q, hinv, ?_⟩
  cases hcur : (walk (σY a b y) q).cur with
  | none => exact Or.inl rfl
  | some c => exact Or.inr ⟨c, rfl, cur_blocked H_CELLS H_BUNDLE hW t q hinv hag hf hq c hcur⟩

end Formal.Net.CapNet.Live.Nd5
