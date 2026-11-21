import Formal.Net.CapstoneLiveNd5Loop

/-!
# Probe C-8z5 (3): H_NO_DEADLOCK'' narrowed to the blocked spine configurations

* `nd2_iff_noblock`: under H_CELLS, H_BUNDLE, H_START_ONCE and `a, b < 2^31`, H_NO_DEADLOCK''
  (`Nd2.NoDeadlock2`) is EQUIVALENT to `NoBlock`: no quiescent tick before out0's close has
  the walk ended or its current channel `Blocked` (`CapstoneLiveNd5Spine`). So the open
  obligation only has to refute the three blocked configurations (and the ended walk), not an
  arbitrary quiescent state.
* `gcd_hw_live_final3`: `gcd_hw_live_final2` with H_NO_DEADLOCK'' replaced by `NoBlock`.
* Two sub-cases of `Blocked` are refuted outright:
  - `link_chain_excl`: the walk is never blocked at a link output whose consumer is a link
    whose consumer is again a link (counts along the chain contradict the walk);
  - `rtz_header_excl` / `gcd_hw_rtz_header`: at the four loop headers, a quiescent state never
    has both the arbiter output `z` and the back-edge input `yy` in phase `11` (quiescence
    propagates `11` round the loop, which `no_rtz_loop` forbids). This removes the
    "z held by the back edge, mid-return" form of the arbiter-blocked case at the loop headers.
-/

namespace Formal.Net.CapNet.Live.Nd5
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd
open Formal.Net.CapSafe (Good TS texec)
open Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut
open Formal.Cells.LinkHandshake (ctlB)
open Formal.Net.Ops.Link (ltbl LS)

set_option maxRecDepth 100000

/-! ## The narrowed obligation -/

/-- **H_NO_BLOCK**: no quiescent tick before out0's first close has the control walk ended or
blocked, for any complete token run `y` whose walk meets H_WALK and any walk position `q`
matching the spine counts. -/
def NoBlock (a b : Nat) (ch : Fin NC → Chan) (itr : Itr) : Prop :=
  ∀ t, cnt (fallB (ch out0).ack) t = 0 → QuietQ ch itr t →
    ∀ y, Good a b y → WalkOK (σY a b y) (omOf a b y) →
    ∀ q, (∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) q).W c) →
      (walk (σY a b y) q).cur ≠ none ∧
      ∀ c, (walk (σY a b y) q).cur = some c → ¬ Blocked ch itr t c

theorem nd2_iff_noblock (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    Nd2.NoDeadlock2 ch itr ↔ NoBlock a b ch itr := by
  constructor
  · intro h t h0 hq
    exact absurd hq (h t h0)
  · intro h t h0 hq
    have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
    obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
    have hW := walk_ok hy hex
    obtain ⟨⟨q, hinv⟩, hf, hag⟩ := Gcd.main hy hC H_BUNDLE H_START_ONCE hW t
    have hn := h t h0 hq y hy hW q hinv
    cases hcur : (walk (σY a b y) q).cur with
    | none => exact hn.1 hcur
    | some c => exact hn.2 c hcur (cur_blocked H_CELLS H_BUNDLE hW t q hinv hag hf hq c hcur)

/-- **gcd_hw circuit liveness with the narrowed obligation.** -/
theorem gcd_hw_live_final3 (a b H : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_BOUNDED_DELAY' : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (H_START_ENV : StartEnv H (ch start))
    (H_START_REL : Nd2.StartRel H (ch start))
    (H_ARB_UNCONTESTED_BOUNDED : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbUnc H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    (H_NO_BLOCK : NoBlock a b ch itr) :
    ∃ y, Good a b y ∧ ∃ e, e < (1168 * (8 * Lrun y + 23) + 1) * (H + 1) ∧ TokAt (ch out0) 0 e ∧
      (ch out0).dat e = Nat.gcd a b :=
  Nd2.gcd_hw_live_final2 a b H ha hb ch itr H_CELLS H_BUNDLE H_START_ONCE H_BOUNDED_DELAY'
    H_START_ENV H_START_REL H_ARB_UNCONTESTED_BOUNDED
    ((nd2_iff_noblock a b ha hb ch itr H_CELLS H_BUNDLE H_START_ONCE).mpr H_NO_BLOCK)

/-! ## Quiescent links -/

/-- A link is quiescent: node, input acknowledge and output request all settled. -/
def LQ (e : LS) : Prop := e.c = ctlB e.ir e.oa e.c false ∧ e.ia = e.c ∧ e.orq = e.c

instance (e : LS) : Decidable (LQ e) := by unfold LQ; exact inferInstance

theorem lq_ret : ∀ e ∈ ltbl, LQ e → e.ir = false → e.ia = true →
    e.d = 2 ∧ e.orq = true ∧ e.oa = false := by decide

theorem lq_req : ∀ e ∈ ltbl, LQ e → e.ir = true → e.ia = false → e.d = 1 := by decide

theorem lq_back11 : ∀ e ∈ ltbl, LQ e → e.orq = true → e.oa = true → e.ir = true ∧ e.ia = true := by
  decide

theorem link_quiet {ch : Fin NC → Chan} {itr : Itr} {t : Nat} (hQ : Quiet2 (gsAt ch itr t))
    {p : Fin NO} {i o : Fin NC} (hk : opAt p = .link i o) :
    LQ ⟨(ch i).req t, (ch i).ack t, itr p 0 t, (ch o).req t, (ch o).ack t, 0, 0⟩ := by
  have hop : p ≠ prodOf start := ne_pstart (by rw [hk]; intros; simp)
  refine ⟨?_, ?_, ?_⟩
  · have hg : gw (fun s => s.it p 0) (fun s => ctlB (s.rq i) (s.ak o) (s.it p 0) false) ∈
        gatesK p (opAt p) := by rw [hk]; simp [gatesK]
    exact quiet_gate hQ hop hg (v := ctlB ((ch i).req t) ((ch o).ack t) (itr p 0 t) false)
      (by simp [gw, gsAt])
  · have hg : gw (fun s => s.ak i) (fun s => s.it p 0) ∈ gatesK p (opAt p) := by
      rw [hk]; simp [gatesK]
    exact quiet_gate hQ hop hg (v := itr p 0 t) (by simp [gw, gsAt])
  · have hg : gw (fun s => s.rq o) (fun s => s.it p 0) ∈ gatesK p (opAt p) := by
      rw [hk]; simp [gatesK]
    exact quiet_gate hQ hop hg (v := itr p 0 t) (by simp [gw, gsAt])

/-- The link state of `link_step` with the quiescence facts. -/
theorem link_quiet_step {ch : Fin NC → Chan} {itr : Itr} {t : Nat} (hQ : Quiet2 (gsAt ch itr t))
    {p : Fin NO} {i o : Fin NC} (hk : opAt p = .link i o) (L : Link.Link (ch i) (ch o) (itr p 0))
    (hpi : Protocol (ch i)) (hpo : Protocol (ch o)) :
    ∃ e ∈ ltbl, LQ e ∧ e.ir = (ch i).req t ∧ e.ia = (ch i).ack t ∧ e.c = itr p 0 t ∧
      e.orq = (ch o).req t ∧ e.oa = (ch o).ack t ∧
      cnt (riseB (ch o).req) t + 1 = cnt (fallB (ch i).ack) t + e.d := by
  obtain ⟨d, q, hm, hd1, -, -⟩ := Link.link_step L hpi hpo t
  have hq := link_quiet hQ hk
  exact ⟨_, Link.lmem hm, hq, rfl, rfl, rfl, rfl, rfl, hd1⟩

/-! ## Excluded sub-cases of `Blocked` -/

section
variable {a b : Nat} {ch : Fin NC → Chan} {itr : Itr} {y : TS}
variable (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
variable (H_BUNDLE : ∀ c, Held (ch c))

include H_CELLS H_BUNDLE in
/-- **Link chains.** The walk is never blocked at a returning link output `c` whose consumer
is a link `c → o2` whose consumer is a link `o2 → o3`. -/
theorem link_chain_excl (t q : Nat)
    (hinv : ∀ c, sp c = true → cnt (riseB (ch c).req) t = (walk (σY a b y) q).W c)
    (hQ : Quiet2 (gsAt ch itr t)) (c : Fin NC) (hcur : (walk (σY a b y) q).cur = some c)
    (hc1 : (ch c).req t = false) (hc2 : (ch c).ack t = true)
    {p2 p3 : Fin NO} {o2 o3 : Fin NC} (hk2 : opAt p2 = .link c o2) (hk3 : opAt p3 = .link o2 o3) :
    False := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hp := gcd_hw_protocol a b ch hC H_BUNDLE
  have hsc : sp c = true := cur_sp _ q c hcur
  have hso2 : sp o2 = true := by
    have := spok p2; rw [hk2] at this; simp only [SpOK, beq_iff_eq] at this; rw [← this]; exact hsc
  have hso3 : sp o3 = true := by
    have := spok p3; rw [hk3] at this; simp only [SpOK, beq_iff_eq] at this; rw [← this]; exact hso2
  have L2 : Link.Link (ch c) (ch o2) (itr p2 0) := by have := H_CELLS p2; rw [hk2] at this; exact this
  have L3 : Link.Link (ch o2) (ch o3) (itr p3 0) := by have := H_CELLS p3; rw [hk3] at this; exact this
  obtain ⟨e2, hm2, hq2, ir2, ia2, -, or2, oa2, hd2⟩ := link_quiet_step hQ hk2 L2 (hp c) (hp o2)
  obtain ⟨d2e, orq2, oak2⟩ := lq_ret e2 hm2 hq2 (by rw [ir2, hc1]) (by rw [ia2, hc2])
  obtain ⟨e3, hm3, hq3, ir3, ia3, -, -, -, hd3⟩ := link_quiet_step hQ hk3 L3 (hp o2) (hp o3)
  have d3e := lq_req e3 hm3 hq3 (by rw [ir3, ← or2, orq2]) (by rw [ia3, ← oa2, oak2])
  have hrc := rise_inv (hp c) t
  have hro2 := rise_inv (hp o2) t
  have hx : inTx (ch c) t = true := by simp [inTx, hc2]
  have hx2 : inTx (ch o2) t = true := by simp [inTx, ← or2, orq2]
  rw [hx] at hrc; rw [hx2] at hro2
  simp only [ite_true] at hrc hro2
  rw [d2e] at hd2; rw [d3e] at hd3
  rw [hinv c hsc] at hrc
  rw [hinv o2 hso2] at hd2 hro2
  rw [hinv o3 hso3] at hd3
  have f2 := flow (σY a b y) q o2
  have f3 := flow (σY a b y) q o3
  rw [tr_link _ hk2 hso2] at f2
  rw [tr_link _ hk3 hso3] at f3
  rw [hcur] at f2 f3
  have hns2 : o2 ≠ start := ne_start_of (prod_out p2 o2 (by rw [hk2]; simp [K.outsC]))
    (by rw [hk2]; intros; simp)
  have hns3 : o3 ≠ start := ne_start_of (prod_out p3 o3 (by rw [hk3]; simp [K.outsC]))
    (by rw [hk3]; intros; simp)
  have hco2 : c ≠ o2 := fun h => noloop c (by
    rw [prod_out p2 c (by rw [hk2, ← h]; simp [K.outsC]), cons_in p2 c (by rw [hk2]; simp [K.insC])])
  simp only [Gcd.bn, beq_iff_eq, Option.some.injEq, hns2, hns3, ite_false, Nat.add_zero, hco2]
    at f2 f3
  by_cases h3 : c = o3
  · subst h3
    simp at f3
    omega
  · simp [h3] at f3
    omega

end

section
variable {a b : Nat} {ch : Fin NC → Chan} {itr : Itr} {y : TS}
variable (hy : Good a b y)
variable (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
variable (H_BUNDLE : ∀ c, Held (ch c))
variable (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
variable (H_WALK : WalkOK (σY a b y) (omOf a b y))

include hy H_CELLS H_BUNDLE H_START_ONCE H_WALK in
/-- **Loop headers.** In a quiescent state, the arbiter output `z` and the back-edge input
`yy` of a spine loop are never both in phase `11`: quiescence would propagate `11` back round
the loop (links, steer, bjoin acknowledge, fork wire), which `no_rtz_loop` forbids. -/
theorem rtz_header_excl
    {pa pf pb ps pl1 pl2 pl3 : Fin NO} {x yy z s j k tt ff l1 l2 : Fin NC} {w : Nat}
    {os : List (Fin NC)} {ec ed : GcdHw.E} (bb : Bool)
    (hA : opAt pa = .amerge x yy z w) (hF : opAt pf = .forkG z os) (hs : s ∈ os)
    (hB : opAt pb = .bjoin [k, s] j ec ed) (hS : opAt ps = .steerC j tt ff)
    (hL1 : opAt pl1 = .link (bif bb then tt else ff) l1) (hL2 : opAt pl2 = .link l1 l2)
    (hL3 : opAt pl3 = .link l2 yy)
    (hss : sp s = true) (hsj : sp j = true) (hsl1 : sp l1 = true) (hsl2 : sp l2 = true)
    (hd : j ≠ (bif bb then tt else ff) ∧ j ≠ l1 ∧ j ≠ l2 ∧ j ≠ yy ∧ j ≠ z ∧ j ≠ s)
    (t : Nat) (hQ : Quiet2 (gsAt ch itr t)) (hz : Ack11 (ch z) t) (hyy : Ack11 (ch yy) t) : False := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hp := gcd_hw_protocol a b ch hC H_BUNDLE
  have back : ∀ {pl : Fin NO} {i o : Fin NC}, opAt pl = .link i o → Ack11 (ch o) t → Ack11 (ch i) t := by
    intro pl i o hk ho
    have L : Link.Link (ch i) (ch o) (itr pl 0) := by have := H_CELLS pl; rw [hk] at this; exact this
    obtain ⟨e, hm, hq, ir, ia, -, or', oa, -⟩ := link_quiet_step hQ hk L (hp i) (hp o)
    have := lq_back11 e hm hq (by rw [or', ho.1]) (by rw [oa, ho.2])
    exact ⟨by rw [← ir]; exact this.1, by rw [← ia]; exact this.2⟩
  have h2 := back hL3 hyy
  have h1 := back hL2 h2
  have ht := back hL1 h1
  have hopS : ps ≠ prodOf start := ne_pstart (by rw [hS]; intros; simp)
  have hopF : pf ≠ prodOf start := ne_pstart (by rw [hF]; intros; simp)
  have hopB : pb ≠ prodOf start := ne_pstart (by rw [hB]; intros; simp)
  -- the steer: its loop-branch request is the input request with the loop select
  have hj1 : (ch j).req t = true := by
    cases bb
    · have hg : gw (fun s => s.rq ff) (fun s => s.rq j && (sel2 (s.dt j) == false)) ∈
          gatesK ps (opAt ps) := by rw [hS]; simp [gatesK]
      have := quiet_gate hQ hopS hg (v := ((ch j).req t && (sel2 ((ch j).dat t) == false)))
        (by simp [gw, gsAt])
      have h0 : (ch ff).req t = true := ht.1
      simp only [gw, gsAt, h0] at this
      cases hj : (ch j).req t
      · rw [hj] at this; simp at this
      · rfl
    · have hg : gw (fun s => s.rq tt) (fun s => s.rq j && (sel2 (s.dt j) == true)) ∈
          gatesK ps (opAt ps) := by rw [hS]; simp [gatesK]
      have := quiet_gate hQ hopS hg (v := ((ch j).req t && (sel2 ((ch j).dat t) == true)))
        (by simp [gw, gsAt])
      have h0 : (ch tt).req t = true := ht.1
      simp only [gw, gsAt, h0] at this
      cases hj : (ch j).req t
      · rw [hj] at this; simp at this
      · rfl
  have hj2 : (ch j).ack t = true := by
    have hg : gw (fun s => s.ak j) (fun s => s.ak tt || s.ak ff) ∈ gatesK ps (opAt ps) := by
      rw [hS]; simp [gatesK]
    have := quiet_gate hQ hopS hg (v := ((ch tt).ack t || (ch ff).ack t)) (by simp [gw, gsAt])
    simp only [gw, gsAt] at this
    rw [this]
    cases bb
    · have h0 : (ch ff).ack t = true := ht.2
      simp [h0]
    · have h0 : (ch tt).ack t = true := ht.2
      simp [h0]
  have hs1 : (ch s).req t = true := by
    have hg : gw (fun s' => s'.rq s) (fun s' => s'.rq z) ∈ gatesK pf (opAt pf) := by
      rw [hF]; simp only [gatesK]; exact List.mem_append_left _ (List.mem_map_of_mem hs)
    have := quiet_gate hQ hopF hg (v := (ch z).req t) (by simp [gw, gsAt])
    simp only [gw, gsAt] at this
    rw [this]; exact hz.1
  have hs2 : (ch s).ack t = true := by
    have hg : gw (fun s' => s'.ak s) (fun s' => s'.ak j) ∈ gatesK pb (opAt pb) := by
      rw [hB]; simp [gatesK]
    have := quiet_gate hQ hopB hg (v := (ch j).ack t) (by simp [gw, gsAt])
    simp only [gw, gsAt] at this
    rw [this]; exact hj2
  exact no_rtz_loop hy hC H_BUNDLE H_START_ONCE H_WALK bb hA hF hs hB hS hL1 hL2 hL3 hss hsj hsl1
    hsl2 hd t ⟨hz, ⟨hs1, hs2⟩, ⟨hj1, hj2⟩, ht, h1, h2, hyy⟩

end

/-- The (arbiter output, back-edge input) pairs of the four spine loop headers. -/
def headers : List (Fin NC × Fin NC) := [(456, 106), (458, 187), (459, 243), (461, 385)]

/-- **gcd_hw loop headers.** For `a, b < 2^31` and every run meeting H_CELLS, H_BUNDLE and
H_START_ONCE, no quiescent state has a loop header's output and back-edge input both in `11`. -/
theorem gcd_hw_rtz_header (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (itr : Itr) (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c)) (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    ∀ h ∈ headers, ∀ t, Quiet2 (gsAt ch itr t) → ¬ (Ack11 (ch h.1) t ∧ Ack11 (ch h.2) t) := by
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  have hW := walk_ok hy hex
  intro h hh t hQ ⟨h1, h2⟩
  simp only [headers, List.mem_cons, List.not_mem_nil, or_false] at hh
  rcases hh with rfl | rfl | rfl | rfl
  · exact rtz_header_excl hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 167) (pf := 168) (pb := 55)
      (ps := 56) (pl1 := 230) (pl2 := 231) (pl3 := 232) (x := 77) (s := 101) (k := 122) (ff := 132)
      true rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t hQ h1 h2
  · exact rtz_header_excl hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 171) (pf := 172) (pb := 76)
      (ps := 77) (pl1 := 270) (pl2 := 271) (pl3 := 272) (x := 151) (s := 182) (k := 190) (tt := 205)
      false rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t hQ h1 h2
  · exact rtz_header_excl hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 174) (pf := 175) (pb := 97)
      (ps := 98) (pl1 := 295) (pl2 := 296) (pl3 := 297) (x := 207) (s := 238) (k := 246) (tt := 255)
      false rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t hQ h1 h2
  · exact rtz_header_excl hy H_CELLS H_BUNDLE H_START_ONCE hW (pa := 180) (pf := 181) (pb := 154)
      (ps := 155) (pl1 := 352) (pl2 := 353) (pl3 := 354) (x := 342) (s := 380) (k := 388) (tt := 290)
      false rfl rfl (by decide) rfl rfl rfl rfl rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) t hQ h1 h2

end Formal.Net.CapNet.Live.Nd5
