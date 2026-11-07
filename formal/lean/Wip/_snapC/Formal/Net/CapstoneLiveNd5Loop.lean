import Formal.Net.CapstoneLiveNd5Spine

/-!
# Probe C-8z5 (2): no loop of the control spine is ever stuck in a full return-to-zero wait

C-8z4's first (buggy) explorer reported a "deadlock" that was a cycle of return-to-zero waits
around a loop header: amerge `z` → fork → bjoin → steerC → 3 links → amerge input `y`, every
channel at `req = ack = 1`. Each channel then waits for its producer's input to fall, round the
cycle, for ever. C-8z4 noted that a liveness proof must rule such cycles out (the "capacity"
part of route B).

`no_rtz_loop` (generic) and `gcd_hw_no_rtz_loops` (the four loops of gcd_hw's spine): for
`a, b < 2^31` and every run meeting H_CELLS, H_BUNDLE and H_START_ONCE, at EVERY tick (not only
quiescent ones) at least one channel of each spine loop cycle is not in the acknowledged phase
`11`.

Proof: if all seven channels are at `11`, every operator on the cycle has passed its current
token on (the local tables give exact count equalities: fork, bjoin, the three links; the
steer's count is its input's offers with the loop-branch select; the arbiter's `y` count is
its passed-`y` count). By 8r's `Inv` these are the walk's visit counts. The steer's open
input token selects the loop branch (steer invariant + H_BUNDLE + 8m's `Agree`), so the walk's
last visit of the bjoin output went into the loop; the walk is deterministic on the cycle, so
it is now at one of the seven cycle channels, and each of the seven positions contradicts one
count equality (at `z` through H_WALK: the walk arrives from `y`, so the oracle label is `y`,
while the arbiter's count says `y`'s token has already passed).

What it does NOT show: other return-to-zero waits (partial cycles, cycles through the data
side, the mux loops of the data path), or anything about data arrival.
-/

namespace Formal.Net.CapNet.Live.Nd5
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd
open Formal.Net.CapSafe (Good TS texec)
open Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut
open Formal.Net.Ops.Link (ltbl LS)

set_option maxRecDepth 100000

/-! ## Walk transitions into a channel, by producer kind -/

section
variable (σ : Fin NC → Nat → Nat)

theorem tr_link {pl : Fin NO} {i o : Fin NC} (hk : opAt pl = .link i o) (hso : sp o = true) :
    ∀ q, cnt (tr σ o) q = (walk σ q).W i := by
  have hpo : prodOf o = pl := prod_out pl o (by rw [hk]; simp [K.outsC])
  apply in_cp
  apply hin_one σ
  · intro d _ hd; rw [hpo, hk] at hd; simpa [K.insC] using hd
  · rw [hpo, hk]; simp [K.insC]
  · intro k
    have hio : consOf i = pl := cons_in pl i (by rw [hk]; simp [K.insC])
    exact nxt_link _ (by rw [hio, hk]) hso

theorem tr_forkG {pf : Fin NO} {i o : Fin NC} {os : List (Fin NC)} (hk : opAt pf = .forkG i os)
    (ho : o ∈ os) (hso : sp o = true) : ∀ q, cnt (tr σ o) q = (walk σ q).W i := by
  have hpo : prodOf o = pf := prod_out pf o (by rw [hk]; simpa [K.outsC] using ho)
  have hs := spok pf
  rw [hk] at hs
  have hsi : sp i = true := by
    cases hsi : sp i
    · simp only [SpOK, hsi, Bool.false_eq_true, ite_false, List.all_eq_true] at hs
      have := hs o ho; simp [hso] at this
    · rfl
  simp only [SpOK, hsi, ite_true, beq_iff_eq] at hs
  apply in_cp
  apply hin_one σ
  · intro d _ hd; rw [hpo, hk] at hd; simpa [K.insC] using hd
  · rw [hpo, hk]; simp [K.insC]
  · intro k
    have hio : consOf i = pf := cons_in pf i (by rw [hk]; simp [K.insC])
    rw [nxt_forkG _ (by rw [hio, hk])]; exact find_one hs ho hso

theorem tr_bjoin {pb : Fin NO} {k d o : Fin NC} {ec ed : GcdHw.E} (hk : opAt pb = .bjoin [k, d] o ec ed)
    (hso : sp o = true) : ∀ q, cnt (tr σ o) q = (walk σ q).W d := by
  have hpo : prodOf o = pb := prod_out pb o (by rw [hk]; simp [K.outsC])
  have hs := spok pb
  rw [hk] at hs
  simp only [SpOK, hso, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hs
  apply in_cp
  apply hin_one σ
  · intro d' hd hd'
    rw [hpo, hk] at hd'
    simp only [K.insC, List.mem_cons, List.not_mem_nil, or_false] at hd'
    rcases hd' with e | e
    · subst e; rw [hs.1] at hd; exact absurd hd (by decide)
    · exact e
  · rw [hpo, hk]; simp [K.insC]
  · intro k'
    have hio : consOf d = pb := cons_in pb d (by rw [hk]; simp [K.insC])
    exact nxt_bjoin _ (by rw [hio, hk]) hso

theorem tr_steerC {ps : Fin NO} {j tt ff : Fin NC} (hk : opAt ps = .steerC j tt ff) (hsj : sp j = true)
    (bb : Bool) :
    ∀ q, cnt (tr σ (bif bb then tt else ff)) q = cnt (fun k => sel2 (σ j k) == bb) ((walk σ q).W j) := by
  have hs := spok ps
  rw [hk] at hs
  simp only [SpOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hs
  obtain ⟨⟨htj, hfj⟩, htf⟩ := hs
  have hjo : consOf j = ps := cons_in ps j (by rw [hk]; simp [K.insC])
  have hst : sp tt = true := by rw [htj]; exact hsj
  have hpo : prodOf (bif bb then tt else ff) = ps :=
    prod_out ps _ (by rw [hk]; cases bb <;> simp [K.outsC])
  apply in_st
  intro d k hsd
  constructor
  · intro h
    have hd := nxt_in _ h
    rw [hpo, hk] at hd
    simp only [K.insC, List.mem_singleton] at hd
    subst hd
    rw [nxt_steerC _ (by rw [hjo, hk]) hst] at h
    simp only [Option.some.injEq] at h
    refine ⟨rfl, ?_⟩
    cases hb1 : sel2 (σ d k) <;> cases bb <;> simp [hb1] at h ⊢ <;>
      exact htf (by first | exact h | exact h.symm)
  · rintro ⟨e, hsl⟩
    subst e
    rw [nxt_steerC _ (by rw [hjo, hk]) hst]
    simp [hsl]

end


/-! ## Walk steps -/

theorem step_cur {σ : Fin NC → Nat → Nat} {p : Nat} {c c' : Fin NC} (hc : (walk σ p).cur = some c)
    (hn : ∀ k, nxt σ c k = some c') : (walk σ (p + 1)).cur = some c' := by
  rw [cur_succ, hc]; exact hn _

theorem step_W {σ : Fin NC → Nat → Nat} {p : Nat} {c d : Fin NC} (hc : (walk σ p).cur = some c)
    (hne : c ≠ d) : (walk σ (p + 1)).W d = (walk σ p).W d := by
  rw [W_succ, visB_some σ hc]
  have : (some c == some d) = false := by simp [hne]
  rw [this]; rfl

theorem step_W_self {σ : Fin NC → Nat → Nat} {p : Nat} {c : Fin NC} (hc : (walk σ p).cur = some c) :
    (walk σ (p + 1)).W c = (walk σ p).W c + 1 := by
  rw [W_succ, visB_some σ hc]; simp [Gcd.bn]

theorem flow_cur {σ : Fin NC → Nat → Nat} {p : Nat} {c : Fin NC} (hc : (walk σ p).cur = some c)
    (hcs : c ≠ start) : (walk σ p).W c + 1 = cnt (tr σ c) p := by
  have := flow σ p c
  rw [hc] at this
  have h0 : (c == start) = false := by simp [hcs]
  simp only [beq_self_eq_true, h0] at this
  simpa [Gcd.bn] using this

theorem W_mono' (σ : Fin NC → Nat → Nat) (c : Fin NC) {p p' : Nat} (h : p ≤ p') :
    (walk σ p).W c ≤ (walk σ p').W c := by
  rw [W_eq, W_eq]; exact cnt_mono _ h

theorem ne_start_of {c : Fin NC} {p : Fin NO} (h : prodOf c = p) (hk : ∀ z w d, opAt p ≠ .src z w d) :
    c ≠ start := ne_start (by rw [h]; exact hk)

/-! ## Local count equalities when both sides are acknowledged -/

theorem link_11_tbl : ∀ e ∈ ltbl, e.ir = true → e.ia = true → e.orq = true → e.oa = true →
    e.d = 2 := by decide

theorem amerge_11_tbl : ∀ e ∈ CM.atbl, e.yr = true → e.ya = true → e.zr = true → e.za = true →
    e.dy = 1 := by decide +kernel

theorem link_11 {i o : Chan} {c : Trace} (L : Link.Link i o c) (hpi : Protocol i) (hpo : Protocol o)
    {t : Nat} (h1 : i.req t = true) (h2 : i.ack t = true) (h3 : o.req t = true) (h4 : o.ack t = true) :
    cnt (riseB o.req) t = cnt (riseB i.req) t := by
  obtain ⟨d, q, hm, hd1, -, -⟩ := Link.link_step L hpi hpo t
  have K := link_11_tbl _ (Link.lmem hm) h1 h2 h3 h4
  simp only [Link.lst] at K
  have hri := rise_inv hpi t
  simp only [inTx, h1, Bool.true_or, ite_true] at hri
  omega

/-- The acknowledged phase `11` (offer acknowledged, request not yet withdrawn). -/
def Ack11 (c : Chan) (t : Nat) : Prop := c.req t = true ∧ c.ack t = true

section
variable {a b : Nat} {ch : Fin NC → Chan} {y : TS}
variable (hy : Good a b y)
variable (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
variable (H_BUNDLE : ∀ c, Held (ch c))
variable (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
variable (H_WALK : WalkOK (σY a b y) (omOf a b y))

include hy H_CELLS H_BUNDLE H_START_ONCE H_WALK in
/-- **No full return-to-zero wait around a spine loop** (generic loop shape: arbiter `z` →
fork → bjoin → steerC loop branch → 3 links → arbiter input `yy`). -/
theorem no_rtz_loop
    {pa pf pb ps pl1 pl2 pl3 : Fin NO} {x yy z s j k tt ff l1 l2 : Fin NC} {w : Nat}
    {os : List (Fin NC)} {ec ed : GcdHw.E} (bb : Bool)
    (hA : opAt pa = .amerge x yy z w) (hF : opAt pf = .forkG z os) (hs : s ∈ os)
    (hB : opAt pb = .bjoin [k, s] j ec ed) (hS : opAt ps = .steerC j tt ff)
    (hL1 : opAt pl1 = .link (bif bb then tt else ff) l1) (hL2 : opAt pl2 = .link l1 l2)
    (hL3 : opAt pl3 = .link l2 yy)
    (hss : sp s = true) (hsj : sp j = true) (hsl1 : sp l1 = true) (hsl2 : sp l2 = true)
    (hd : j ≠ (bif bb then tt else ff) ∧ j ≠ l1 ∧ j ≠ l2 ∧ j ≠ yy ∧ j ≠ z ∧ j ≠ s)
    (t : Nat) :
    ¬ (Ack11 (ch z) t ∧ Ack11 (ch s) t ∧ Ack11 (ch j) t ∧ Ack11 (ch (bif bb then tt else ff)) t ∧
       Ack11 (ch l1) t ∧ Ack11 (ch l2) t ∧ Ack11 (ch yy) t) := by
  rintro ⟨⟨hz1, hz2⟩, ⟨hs1, hs2⟩, ⟨hj1, hj2⟩, ⟨ht1, ht2⟩, ⟨h11, h12⟩, ⟨h21, h22⟩, ⟨hy1, hy2⟩⟩
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE
  obtain ⟨⟨q, hinv⟩, hf, hag⟩ := Gcd.main hy H_CELLS H_BUNDLE H_START_ONCE H_WALK t
  -- spine facts
  have hsA := spok pa
  rw [hA] at hsA
  simp only [SpOK, Bool.and_eq_true] at hsA
  have hsz : sp z = true := hsA.1.2
  have hsy : sp yy = true := hsA.1.1.2
  have hsS := spok ps
  rw [hS] at hsS
  simp only [SpOK, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hsS
  have hst : sp tt = true := by rw [hsS.1.1]; exact hsj
  have hstc : sp (bif bb then tt else ff) = true := by
    cases bb
    · show sp ff = true; rw [hsS.1.2]; exact hsj
    · exact hst
  -- (1) fork
  have e1 : cnt (riseB (ch z).req) t = cnt (riseB (ch s).req) t := by
    have F : Fork.Fork (ch z) (os.map ch) := by have := H_CELLS pf; rw [hF] at this; exact this
    have := fork_cnt F (hp z) (fun o' ho' => by obtain ⟨c', _, e⟩ := List.mem_map.mp ho'; rw [← e]; exact hp c')
      (ch s) (List.mem_map_of_mem hs) t
    simp [hs1] at this; exact this
  -- (2) bjoin
  have e2 : cnt (riseB (ch s).req) t = cnt (riseB (ch j).req) t := by
    have J : Join.Join (bg ec ed) ([k, s].map ch) (ch j) := by
      have := H_CELLS pb; rw [hB] at this; exact this
    have := join_cnt J (hp j) (fun i' hi' => by
      obtain ⟨c', _, e⟩ := List.mem_map.mp hi'; rw [← e]; exact hp c') (ch s) (by simp) t
    simp [hj1] at this; exact this
  -- (3) steer
  have S : Steer.Steer sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then tt else ff)) := by
    have := H_CELLS ps; rw [hS] at this; exact this
  have e3 : cnt (riseB (ch (bif bb then tt else ff)).req) t =
      cnt (fun i => sel2 (σY a b y j i) == bb) (cnt (riseB (ch j).req) t) := by
    have h := steer_cnt S (hp j) (fun b' => hp _) (H_BUNDLE j) bb t
    have hsel : selOff sel2 (ch j) bb t =
        cnt (fun i => sel2 (σY a b y j i) == bb) (cnt (riseB (ch j).req) t) :=
      cnt_offers (σ := σY a b y j) (fun v => sel2 v == bb)
        (fun i u hu ho => hag j i u hu ho) t (Nat.le_refl _)
    have h0 : ((ch (bif bb then tt else ff)).req t) = true := ht1
    simp only [h0, Bool.not_true, Bool.and_false, Bool.false_eq_true, ite_false, Nat.add_zero] at h
    rw [← h, hsel]
  -- (4) links
  have e41 : cnt (riseB (ch l1).req) t = cnt (riseB (ch (bif bb then tt else ff)).req) t := by
    have := H_CELLS pl1; rw [hL1] at this; obtain ⟨cc, L⟩ := this
    exact link_11 L (hp _) (hp _) ht1 ht2 h11 h12
  have e42 : cnt (riseB (ch l2).req) t = cnt (riseB (ch l1).req) t := by
    have := H_CELLS pl2; rw [hL2] at this; obtain ⟨cc, L⟩ := this
    exact link_11 L (hp _) (hp _) h11 h12 h21 h22
  have e43 : cnt (riseB (ch yy).req) t = cnt (riseB (ch l2).req) t := by
    have := H_CELLS pl3; rw [hL3] at this; obtain ⟨cc, L⟩ := this
    exact link_11 L (hp _) (hp _) h21 h22 hy1 hy2
  -- (5) arbiter: every `yy` token offered has passed
  have e5 : cnt (riseB (ch yy).req) t = cnt (omOf a b y w) (cnt (riseB (ch z).req) t) := by
    have := H_CELLS pa; rw [hA] at this; obtain ⟨g1, g2, M⟩ := this
    obtain ⟨dx, dy, hm, -, hu1⟩ := CM.amerge_inv M (hp x).1.1 (hp yy).1.1 (hp z).1.2 t
      (fun s _ => ⟨((hp x).2 s).1, ((hp yy).2 s).1, ((hp z).2 s).2⟩)
    have K := amerge_11_tbl _ (CM.amem hm) hy1 hy2 hz1 hz2
    simp only [CM.ast] at K
    obtain ⟨-, e1'⟩ := zc_eq M t
    have hpre : ∀ i, i < cnt (riseB (ch z).req) t → CM.winner (ch z) i = omOf a b y w i := by
      intro i hi
      obtain ⟨r, hr⟩ := offered_lt hi
      have hrt : r < t := by
        rcases Nat.lt_or_ge r t with h | h
        · exact h
        · have := cnt_mono (riseB (ch z).req) h; rw [hr.2] at this; omega
      exact hf pa x yy z w hA i r hrt hr
    rw [e1', CM.cnt_congr_lt _ hpre] at hu1
    omega
  -- (6) the steer's open token selects the loop branch
  obtain ⟨r, kk, hr, ho, hRj, hFj, -⟩ := open_offer (hp j) hj1
  have hsel : sel2 (σY a b y j kk) = bb := by
    have hv := hag j kk r hr ho
    have hh := held_at (hp j) (H_BUNDLE j) ho hr hFj
    rw [hv, ← hh]
    have hI := Steer.steer_inv S (hp j).1.1 (fun b => (hp _).1.2) (H_BUNDLE j) t
      (fun s _ => ⟨hp j |>.2 s, fun b => (hp _).2 s⟩)
    cases bb
    · have hf0 : (ch ff).req t = true := ht1
      cases hsl : sel2 ((ch j).dat t)
      · rfl
      · rw [hsl] at hI; simp [Steer.SInv, hf0] at hI
    · have ht0 : (ch tt).req t = true := ht1
      cases hsl : sel2 ((ch j).dat t)
      · rw [hsl] at hI; simp [Steer.SInv, ht0] at hI
      · rfl
  -- (7) the walk: its last visit of `j` went into the loop, and it is deterministic on the cycle
  have hWj : (walk (σY a b y) q).W j = kk + 1 := by rw [← hinv j hsj, hRj]
  obtain ⟨e, he, hve, hce⟩ := cnt_witness (visB (σY a b y) j) q kk (by rw [← W_eq]; exact hWj)
  have hce' : (walk (σY a b y) e).W j = kk := by rw [W_eq]; exact hce
  have c0 : (walk (σY a b y) e).cur = some j := by simpa [visB] using hve
  have hcj : consOf j = ps := cons_in ps j (by rw [hS]; simp [K.insC])
  have hct : consOf (bif bb then tt else ff) = pl1 := cons_in pl1 _ (by rw [hL1]; simp [K.insC])
  have hcl1 : consOf l1 = pl2 := cons_in pl2 _ (by rw [hL2]; simp [K.insC])
  have hcl2 : consOf l2 = pl3 := cons_in pl3 _ (by rw [hL3]; simp [K.insC])
  have hcy : consOf yy = pa := cons_in pa _ (by rw [hA]; simp [K.insC])
  have hcz : consOf z = pf := cons_in pf _ (by rw [hF]; simp [K.insC])
  have hcs : consOf s = pb := cons_in pb _ (by rw [hB]; simp [K.insC])
  have n2 : ∀ k', nxt (σY a b y) (bif bb then tt else ff) k' = some l1 :=
    fun k' => nxt_link _ (by rw [hct, hL1]) hsl1
  have n3 : ∀ k', nxt (σY a b y) l1 k' = some l2 := fun k' => nxt_link _ (by rw [hcl1, hL2]) hsl2
  have n4 : ∀ k', nxt (σY a b y) l2 k' = some yy := fun k' => nxt_link _ (by rw [hcl2, hL3]) hsy
  have n5 : ∀ k', nxt (σY a b y) yy k' = some z := fun k' => nxt_amerge _ (by rw [hcy, hA])
  have n6 : ∀ k', nxt (σY a b y) z k' = some s := by
    intro k'
    have hsF := spok pf
    rw [hF] at hsF
    simp only [SpOK, hsz, ite_true, beq_iff_eq] at hsF
    rw [nxt_forkG _ (by rw [hcz, hF])]; exact find_one hsF hs hss
  have n7 : ∀ k', nxt (σY a b y) s k' = some j := fun k' => nxt_bjoin _ (by rw [hcs, hB]) hsj
  have c1 : (walk (σY a b y) (e + 1)).cur = some (bif bb then tt else ff) := by
    rw [cur_succ, c0]
    show nxt (σY a b y) j ((walk (σY a b y) e).W j) = _
    rw [nxt_steerC _ (by rw [hcj, hS]) hst, hce', hsel]
  have c2 : (walk (σY a b y) (e + 2)).cur = some l1 := step_cur c1 n2
  have c3 : (walk (σY a b y) (e + 3)).cur = some l2 := step_cur c2 n3
  have c4 : (walk (σY a b y) (e + 4)).cur = some yy := step_cur c3 n4
  have c5 : (walk (σY a b y) (e + 5)).cur = some z := step_cur c4 n5
  have c6 : (walk (σY a b y) (e + 6)).cur = some s := step_cur c5 n6
  have c7 : (walk (σY a b y) (e + 7)).cur = some j := step_cur c6 n7
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hd
  have w1 : (walk (σY a b y) (e + 1)).W j = kk + 1 := by rw [step_W_self c0, hce']
  have w2 : (walk (σY a b y) (e + 2)).W j = kk + 1 := by rw [step_W c1 (Ne.symm d1), w1]
  have w3 : (walk (σY a b y) (e + 3)).W j = kk + 1 := by rw [step_W c2 (Ne.symm d2), w2]
  have w4 : (walk (σY a b y) (e + 4)).W j = kk + 1 := by rw [step_W c3 (Ne.symm d3), w3]
  have w5 : (walk (σY a b y) (e + 5)).W j = kk + 1 := by rw [step_W c4 (Ne.symm d4), w4]
  have w6 : (walk (σY a b y) (e + 6)).W j = kk + 1 := by rw [step_W c5 (Ne.symm d5), w5]
  have w7 : (walk (σY a b y) (e + 7)).W j = kk + 1 := by rw [step_W c6 (Ne.symm d6), w6]
  have w8 : (walk (σY a b y) (e + 8)).W j = kk + 2 := by rw [step_W_self c7, w7]
  have hq8 : q < e + 8 := by
    rcases Nat.lt_or_ge q (e + 8) with h | h
    · exact h
    · have := W_mono' (σY a b y) j h; omega
  -- the counts at `q`
  rw [hinv z hsz, hinv s hss] at e1
  rw [hinv s hss, hinv j hsj] at e2
  rw [hinv _ hstc, hinv j hsj] at e3
  rw [hinv l1 hsl1, hinv _ hstc] at e41
  rw [hinv l2 hsl2, hinv l1 hsl1] at e42
  rw [hinv yy hsy, hinv l2 hsl2] at e43
  rw [hinv yy hsy, hinv z hsz] at e5
  have hprod : ∀ c (p : Fin NO), c ∈ (opAt p).outsC → prodOf c = p := fun c p h => prod_out p c h
  have hq : q = e + 1 ∨ q = e + 2 ∨ q = e + 3 ∨ q = e + 4 ∨ q = e + 5 ∨ q = e + 6 ∨ q = e + 7 := by
    omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have := flow_cur c1 (ne_start_of (hprod _ ps (by rw [hS]; cases bb <;> simp [K.outsC]))
      (by rw [hS]; intros; simp))
    rw [tr_steerC _ hS hsj bb] at this
    omega
  · have := flow_cur c2 (ne_start_of (hprod _ pl1 (by rw [hL1]; simp [K.outsC])) (by rw [hL1]; intros; simp))
    rw [tr_link _ hL1 hsl1] at this
    omega
  · have := flow_cur c3 (ne_start_of (hprod _ pl2 (by rw [hL2]; simp [K.outsC])) (by rw [hL2]; intros; simp))
    rw [tr_link _ hL2 hsl2] at this
    omega
  · have := flow_cur c4 (ne_start_of (hprod _ pl3 (by rw [hL3]; simp [K.outsC])) (by rw [hL3]; intros; simp))
    rw [tr_link _ hL3 hsy] at this
    omega
  · -- at `z`: the walk arrived from `yy`, so the oracle names `yy`, but `yy`'s token has passed
    have hyz : yy ≠ z := fun h => nxt_ne (σY a b y) (n5 0) h.symm
    have hω := H_WALK (e + 4) yy x yy z w c4 (by rw [hcy, hA])
    simp only [decide_true] at hω
    rw [← step_W c4 hyz] at hω
    obtain ⟨ey, -⟩ := am_counts H_WALK hA (e + 5)
    rw [c5, hω] at ey
    simp [Gcd.bn] at ey
    omega
  · have := flow_cur c6 (ne_start_of (hprod _ pf (by rw [hF]; simpa [K.outsC] using hs))
      (by rw [hF]; intros; simp))
    rw [tr_forkG _ hF hs hss] at this
    omega
  · have := flow_cur c7 (ne_start_of (hprod _ pb (by rw [hB]; simp [K.outsC])) (by rw [hB]; intros; simp))
    rw [tr_bjoin _ hB hsj] at this
    omega

end

/-- The four loop cycles of gcd_hw's control spine (arbiter output, fork's spine output, bjoin
output, the steer's loop branch, three links, the arbiter's back-edge input). -/
def rtzLoops : List (List (Fin NC)) :=
  [[456, 101, 431, 103, 104, 105, 106], [458, 182, 435, 184, 185, 186, 187],
   [459, 238, 440, 240, 241, 242, 243], [461, 380, 454, 382, 383, 384, 385]]

/-- **No spine loop of gcd_hw is ever in a full return-to-zero wait.** For `a, b < 2^31` and
every run meeting H_CELLS, H_BUNDLE and H_START_ONCE, at every tick, some channel of each of
the four spine loop cycles is not in the acknowledged phase `11`. -/
theorem gcd_hw_no_rtz_loops (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    ∀ L ∈ rtzLoops, ∀ t, ¬ ∀ c ∈ L, Ack11 (ch c) t := by
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  have hW := walk_ok hy hex
  intro L hL t hall
  simp only [rtzLoops, List.mem_cons, List.not_mem_nil, or_false] at hL
  rcases hL with rfl | rfl | rfl | rfl
  · exact no_rtz_loop hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 167) (pf := 168) (pb := 55)
      (ps := 56) (pl1 := 230) (pl2 := 231) (pl3 := 232) (x := 77) (s := 101) (k := 122) (ff := 132)
      true rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t (by simpa using hall)
  · exact no_rtz_loop hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 171) (pf := 172) (pb := 76)
      (ps := 77) (pl1 := 270) (pl2 := 271) (pl3 := 272) (x := 151) (s := 182) (k := 190) (tt := 205)
      false rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t (by simpa using hall)
  · exact no_rtz_loop hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 174) (pf := 175) (pb := 97)
      (ps := 98) (pl1 := 295) (pl2 := 296) (pl3 := 297) (x := 207) (s := 238) (k := 246) (tt := 255)
      false rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t (by simpa using hall)
  · exact no_rtz_loop hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 180) (pf := 181) (pb := 154)
      (ps := 155) (pl1 := 352) (pl2 := 353) (pl3 := 354) (x := 342) (s := 380) (k := 388) (tt := 290)
      false rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t (by simpa using hall)

end Formal.Net.CapNet.Live.Nd5
