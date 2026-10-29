import Formal.Net.OpsBusy3
import Formal.Net.CapstoneRefine3Fn

/-!
# Probe C-8x4 (1): composing lemmas for every cell kind (link, mux, 3-input mux, arbiter stage)

C-8x3 composed C-8x's `sampled_eq_zd` (tcheck row + H_TXWIN), H_FN and H_LAUNCH into the relaxed
data field for join, fork and steer. Here the same is done for the remaining kinds, and all of
them are put behind one per-channel interface:

* `field_of_tx` (generic): the observed bus at a busy instant `t` is `F t`, given the row and
  "`zdBus` of transaction `m` = `F (r+1)`" at its offer `r` and "`F` is constant over the
  transaction".
* Stability of the inputs over an output transaction, per kind, from 8f/8j/8l's reachable sets:
  - `mux_busy` (kernel `decide` over 8f's 132-state `tbl`): while `z` is busy, the select
    channel and the input named by the select are busy; `stab_mux`;
  - `muxn_busy` (kernel `decide` over 8l's state code, 4 × 8192 states): the same for the
    3-input mux when the select is < 3; `stab_muxn`;
  - `stab_amerge` (C-8x3's `amerge_busy`, `amerge_won_stable`): the index bit `won` and the
    input it names are constant over an output transaction;
  - `link_open_stable` (8l's table, `link_stepT`): if the latch is open at `t` inside an output
    transaction, it was open since the offer and the input was busy and bundled all along, so the
    input bus at `t` is the one at the offer;
  - `stab_fork`, `stab_join`, `stab_steer` (8w's FInv/JInv/SInv).
* `Row ch sv k w c`: the physical data of a SAMPLED output channel `c`: a tcheck row (`TxWin` +
  separation, a DAG or cert verdict), the launch values `vin m` (input buses) and `vb m` (the
  arbiter's index bit) of each transaction, **H_FN** (`zdBus` of transaction `m` = the cell
  function `fnOf` of the launch values) and **H_LAUNCH** (the launch values are the input buses
  (and index bit) right after the output's offer).
* **`fieldOf_row`**: handshake half + protocol and bundling of every channel + `Row` for output
  `c` ⇒ `FieldOf` for `c`, for EVERY cell kind (link: open and hold fields).
* Standalone forms (task (1)): `linkB_field_of_phys`, `muxB_field_of_phys`,
  `muxnB_field_of_phys`, `amergeB_field_of_phys` on plain channels.
-/

namespace Formal.Net.OpsBusy3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.OpsBusy2 Formal.Timing Formal.Net.CapstoneRefine
open Formal.Net.CapstoneBundle (tx_of_jinv tx_of_finv tx_of_sinv)

/-! ## Generic: the field from a row -/

/-- **The observed bus equals `F t` at every busy instant**, given the row, `zdBus = F` at the
offer, and `F` constant over each transaction. -/
theorem field_of_tx {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ m, Run net (sig m))
    (X : TxWin P sig data R)
    (hsep : ∀ m v, R m v → ∀ d ∈ data, ∀ s, changes (sig m d) s → s ≤ v)
    (hinit : Init P) (hrecv : ∀ t, RecvStep P t) (F : Nat → Nat) (C : Nat → Prop)
    (H_ZD : ∀ m r, OffAt P m r → zdBus runs data m = F (r + 1))
    (H_STABLE : ∀ r t, r < t → (∀ s, r < s → s ≤ t → inTx P s = true) → C t → F t = F (r + 1)) :
    ∀ t, inTx P t = true → C t → P.dat t = F t := by
  intro t ht hc
  obtain ⟨m, r, ho, hr, hs⟩ := busy_cover hinit hrecv t ht
  rw [sampled_eq_zd hwf runs X hsep ho hr hs, H_ZD m r ho, H_STABLE r t hr hs hc]

theorem const_busy {d : Chan} (hh : Held d) {r t : Nat} (hrt : r < t)
    (hb : ∀ s, r < s → s ≤ t → inTx d s = true) : d.dat t = d.dat (r + 1) :=
  held_const hh (by omega) (fun s h1 h2 => hb s (by omega) h2)

/-! ## Stability per kind (plain channels) -/

theorem stab_fork {a : Chan} {os : List Chan} (B : ForkB a os) (hpa : Protocol a)
    (hpo : ∀ o ∈ os, Protocol o) (hh : Held a) {o : Chan} (ho : o ∈ os) {r t : Nat} (hrt : r < t)
    (hb : ∀ s, r < s → s ≤ t → inTx o s = true) : a.dat t = a.dat (r + 1) := by
  have F := B.toOld
  have hinv : ∀ u, Fork.FInv (a.req u) (a.ack u) (o.req u) (o.ack u) = true := by
    intro u
    exact Fork.fork_inv F hpa.1.1
      (fun o' ho' => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hpo c hc).1.2) u
      (fun s _ => ⟨hpa.2 s, fun o' ho' => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hpo c hc).2 s⟩)
      (rel o a.dat) (List.mem_map_of_mem ho)
  exact const_busy hh hrt (fun s h1 h2 => tx_of_finv (hinv s) (hb s h1 h2))

theorem stab_join {g : List Nat → Nat} {is : List Chan} {o : Chan} (B : JoinB g is o)
    (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i) (hh : ∀ i ∈ is, Held i) {r t : Nat}
    (hrt : r < t) (hb : ∀ s, r < s → s ≤ t → inTx o s = true) :
    ∀ i ∈ is, i.dat t = i.dat (r + 1) := by
  have J := B.toOld
  have hinv : ∀ u, ∀ i ∈ is, Join.JInv (o.req u) (o.ack u) (i.req u) (i.ack u) = true :=
    fun u => Join.join_inv J hpo.1.2 (fun i hi => (hpi i hi).1.1) u
      (fun s _ => ⟨hpo.2 s, fun i hi => (hpi i hi).2 s⟩)
  intro i hi
  exact const_busy (hh i hi) hrt (fun s h1 h2 => tx_of_jinv (hinv s i hi) (hb s h1 h2))

theorem stab_steer {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (B : SteerB sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b)) (hh : Held j)
    (b : Bool) {r t : Nat} (hrt : r < t) (hb : ∀ s, r < s → s ≤ t → inTx (out b) s = true) :
    j.dat t = j.dat (r + 1) := by
  have S := B.toOld
  have hinv := fun u => Steer.steer_inv S hpj.1.1 (fun b => (hpo b).1.2) hh u
    (fun s _ => ⟨hpj.2 s, fun b => (hpo b).2 s⟩)
  refine const_busy hh hrt (fun s h1 h2 => ?_)
  apply tx_of_sinv (hinv s) b
  have := hb s h1 h2
  cases b <;> simpa [inTx, rel] using this

section mux
open Formal.Net.Ops.Mux

set_option maxRecDepth 100000 in
/-- In every reachable mux state with `z` busy, the select channel and the selected input are
busy. -/
theorem mux_busy : ∀ e ∈ tbl, (e.zr || e.za) = true →
    (e.cr || e.ca) = true ∧ (if e.s then (e.yr || e.ya) else (e.xr || e.xa)) = true := by
  decide +kernel

theorem stab_mux {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace} (B : MuxB sel x y c z j0 j1)
    (hpx : Protocol x) (hpy : Protocol y) (hpc : Protocol c) (hpz : Protocol z)
    (hhx : Held x) (hhy : Held y) (hhc : Held c) {r t : Nat} (hrt : r < t)
    (hb : ∀ s, r < s → s ≤ t → inTx z s = true) :
    (if sel (c.dat t) then y.dat t else x.dat t) =
      (if sel (c.dat (r + 1)) then y.dat (r + 1) else x.dat (r + 1)) := by
  have M : Mux sel x y c (rel z (fun u => if sel (c.dat u) then y.dat u else x.dat u)) j0 j1 :=
    ⟨B.cj0, B.cj1, B.zr, B.xa, B.ya, B.ca, fun _ => rfl, B.i0, B.i1, B.iz, B.ix, B.iy, B.ic⟩
  have hbusy : ∀ u, inTx z u = true → inTx c u = true ∧
      (if sel (c.dat u) then inTx y u else inTx x u) = true := by
    intro u hu
    obtain ⟨dc, dxo, dyo, hm, -⟩ := mux_inv M hpx.1.1 hpy.1.1 hpc.1.1 hpz.1.2 hhc u
      (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpc.2 s).1, (hpz.2 s).2⟩)
    have := mux_busy _ (mem_of_contains hm) (by simpa [st, inTx] using hu)
    simp only [st] at this
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    cases hs : sel (c.dat u) <;> simp only [hs, Bool.false_eq_true, ↓reduceIte] at h2 ⊢ <;>
      exact h2
  have hc : c.dat t = c.dat (r + 1) := const_busy hhc hrt (fun s h1 h2 => (hbusy s (hb s h1 h2)).1)
  have hcs : ∀ s, r < s → s ≤ t → c.dat s = c.dat (r + 1) := fun s h1 h2 =>
    const_busy hhc h1 (fun u a b => (hbusy u (hb u a (by omega))).1)
  rw [hc]
  cases hs : sel (c.dat (r + 1))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    refine const_busy hhx hrt (fun s h1 h2 => ?_)
    have := (hbusy s (hb s h1 h2)).2
    rwa [hcs s h1 h2, hs] at this
  · simp only [↓reduceIte]
    refine const_busy hhy hrt (fun s h1 h2 => ?_)
    have := (hbusy s (hb s h1 h2)).2
    rwa [hcs s h1 h2, hs] at this

end mux

section muxn
open Formal.Net.Ops.MuxN

/-- The busy fact for the 3-input mux, one select value. -/
def BusyN (s0 : Nat) : Prop :=
  ∀ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Bool,
    mem ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩ = true →
    (e8 || e9) = true → (e6 || e7) = true ∧
      (s0 < 3 → (rq ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩ s0 ||
        ak ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩ s0) = true)

instance (s0 : Nat) : Decidable (BusyN s0) := by unfold BusyN; exact inferInstance

set_option maxRecDepth 100000 in
theorem busyN0 : BusyN 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem busyN1 : BusyN 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem busyN2 : BusyN 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem busyN3 : BusyN 3 := by decide +kernel

/-- In every reachable 3-input-mux state with `z` busy, the select channel is busy, and so is the
selected input when the select is < 3. -/
theorem muxn_busy (e : MS) (hs : e.s < 4) (hm : mem e = true) (hz : (e.zr || e.za) = true) :
    (e.cr || e.ca) = true ∧ (e.s < 3 → (rq e e.s || ak e e.s) = true) := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩ := e
  simp only at hs
  rcases (show s0 = 0 ∨ s0 = 1 ∨ s0 = 2 ∨ s0 = 3 by omega) with rfl | rfl | rfl | rfl
  · exact busyN0 _ _ _ _ _ _ _ _ _ _ _ _ _ hm hz
  · exact busyN1 _ _ _ _ _ _ _ _ _ _ _ _ _ hm hz
  · exact busyN2 _ _ _ _ _ _ _ _ _ _ _ _ _ hm hz
  · exact busyN3 _ _ _ _ _ _ _ _ _ _ _ _ _ hm hz

theorem stab_muxn {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}
    (B : MuxNB sel xs c z j) (hpx : ∀ m, m < 3 → Protocol (xs m)) (hpc : Protocol c)
    (hpz : Protocol z) (hhx : ∀ m, m < 3 → Held (xs m)) (hhc : Held c) {r t : Nat} (hrt : r < t)
    (hb : ∀ s, r < s → s ≤ t → inTx z s = true) (h3 : sel (c.dat t) < 3) :
    sel (c.dat t) = sel (c.dat (r + 1)) ∧
      (xs (sel (c.dat t))).dat t = (xs (sel (c.dat t))).dat (r + 1) := by
  have M : MuxN sel xs c (rel z (fun u => if sel (c.dat u) < 3 then (xs (sel (c.dat u))).dat u
      else 0)) j :=
    ⟨B.cj, B.zr, B.xa, B.ca, fun u hu => by simp [rel, hu], B.ij, B.iz, B.ix, B.ic⟩
  have hbusy : ∀ u, inTx z u = true → inTx c u = true ∧
      (sel (c.dat u) < 3 → inTx (xs (sel (c.dat u))) u = true) := by
    intro u hu
    obtain ⟨hm, -⟩ := muxn_inv M (fun m hm => (hpx m hm).1.1) hpc.1.1 hpz.1.2 hhc u
      (fun s _ => ⟨fun m hm => ((hpx m hm).2 s).1, (hpc.2 s).1, (hpz.2 s).2⟩)
    obtain ⟨h1, h2⟩ := muxn_busy _ (clip_lt _) hm (by simpa [st, inTx] using hu)
    refine ⟨by simpa [st, inTx] using h1, fun hlt => ?_⟩
    have hcl : clip (sel (c.dat u)) = sel (c.dat u) := by unfold clip; simp [hlt]
    have := h2 (show clip (sel (c.dat u)) < 3 by rw [hcl]; exact hlt)
    change (rq (st sel xs c _ j u) (clip (sel (c.dat u))) ||
      ak (st sel xs c _ j u) (clip (sel (c.dat u)))) = true at this
    rw [hcl, rq_st u _ hlt, ak_st u _ hlt] at this
    exact this
  have hcs : ∀ s, r < s → s ≤ t → c.dat s = c.dat (r + 1) := fun s h1 h2 =>
    const_busy hhc h1 (fun u a b => (hbusy u (hb u a (by omega))).1)
  have hc : c.dat t = c.dat (r + 1) := hcs t hrt (Nat.le_refl _)
  refine ⟨by rw [hc], ?_⟩
  refine const_busy (hhx _ h3) hrt (fun s h1 h2 => ?_)
  have e : sel (c.dat s) = sel (c.dat t) := by rw [hcs s h1 h2, hc]
  have := (hbusy s (hb s h1 h2)).2 (by rw [e]; exact h3)
  rwa [e] at this

end muxn

section amerge
open Formal.Net.Ops.CM

theorem stab_amerge {x y z : Chan} {g1 g2 : Trace} (B : AMergeB x y z g1 g2) (hpx : Protocol x)
    (hpy : Protocol y) (hpz : Protocol z) (hhx : Held x) (hhy : Held y) {r t : Nat} (hrt : r < t)
    (hb : ∀ s, r < s → s ≤ t → inTx z s = true) :
    (g2 t || y.ack t) = (g2 (r + 1) || y.ack (r + 1)) ∧
      (if (g2 t || y.ack t) then y.dat t else x.dat t) =
        (if (g2 (r + 1) || y.ack (r + 1)) then y.dat (r + 1) else x.dat (r + 1)) := by
  have M := B.toOld
  have inv := fun u => amerge_inv M hpx.1.1 hpy.1.1 hpz.1.2 u
    (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpz.2 s).2⟩)
  -- `won` is constant on `[r+1, t]`
  have wstep : ∀ u, r < u → u < t → (g2 (u + 1) || y.ack (u + 1)) = (g2 u || y.ack u) := by
    intro u h1 h2
    obtain ⟨dx, dy, hm, -⟩ := inv u
    obtain ⟨sx, -⟩ := hpx.2 u
    obtain ⟨sy, -⟩ := hpy.2 u
    obtain ⟨-, rz⟩ := hpz.2 u
    have hst := amerge_won_stable _ (amem hm) (x.req (u + 1)) sx (y.req (u + 1)) sy
      (z.ack (u + 1)) rz (g1 (u + 1)) (M.H_ARB1 u) (g2 (u + 1)) (M.H_ARB2 u)
      (M.H_ARB_EXCL (u + 1)) (z.req (u + 1)) (M.zr u) (M.H_AMERGE_RTZ u) (x.ack (u + 1)) (M.xa u)
      (y.ack (u + 1)) (M.ya u) (hb u h1 (by omega)) (hb (u + 1) (by omega) (by omega))
    simpa [ast, rel_req, rel_ack] using hst
  have wc : ∀ s, r < s → s ≤ t → (g2 s || y.ack s) = (g2 (r + 1) || y.ack (r + 1)) := by
    intro s h1 h2
    have : ∀ d, r + 1 + d ≤ s → (g2 (r + 1 + d) || y.ack (r + 1 + d)) =
        (g2 (r + 1) || y.ack (r + 1)) := by
      intro d
      induction d with
      | zero => intro _; rfl
      | succ d ih =>
        intro hd
        rw [show r + 1 + (d + 1) = r + 1 + d + 1 by omega, wstep _ (by omega) (by omega),
          ih (by omega)]
    have := this (s - (r + 1)) (by omega)
    rwa [show r + 1 + (s - (r + 1)) = s by omega] at this
  have hsel : ∀ s, r < s → s ≤ t →
      (if (g2 (r + 1) || y.ack (r + 1)) then inTx y s else inTx x s) = true := by
    intro s h1 h2
    obtain ⟨dx, dy, hm, -⟩ := inv s
    have := amerge_busy _ (amem hm) (by simpa [ast, inTx] using hb s h1 h2)
    simp only [ast, rel_req, rel_ack] at this
    have e := wc s h1 h2
    cases hw : (g2 (r + 1) || y.ack (r + 1)) <;> rw [hw] at e <;>
      simp only [e, Bool.false_eq_true, ↓reduceIte] at this ⊢ <;> exact this
  refine ⟨wc t hrt (Nat.le_refl _), ?_⟩
  rw [wc t hrt (Nat.le_refl _)]
  cases hw : (g2 (r + 1) || y.ack (r + 1))
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact const_busy hhx hrt (fun s h1 h2 => by have := hsel s h1 h2; rwa [hw] at this)
  · simp only [↓reduceIte]
    exact const_busy hhy hrt (fun s h1 h2 => by have := hsel s h1 h2; rwa [hw] at this)

end amerge

section link
open Formal.Net.Ops.Link

/-- **The latch-open stretch inside an output transaction starts at the offer**: if the enable is
high at `t` and the output is busy on `(r, t]`, the input bus at `t` is the one at `r + 1`. -/
theorem link_open_stable {i o : Chan} {c : Trace} (B : LinkB i o c) (hpi : Protocol i)
    (hpo : Protocol o) (hh : Held i) {r t : Nat} (hrt : r < t)
    (hb : ∀ s, r < s → s ≤ t → inTx o s = true) (hc : c t = true) :
    i.dat t = i.dat (r + 1) := by
  have L := B.toOld
  have key : ∀ d, d ≤ t - (r + 1) → c (t - d) = true ∧ i.dat (t - d) = i.dat t := by
    intro d
    induction d with
    | zero => intro _; exact ⟨hc, rfl⟩
    | succ d ih =>
      intro hd
      obtain ⟨hcd, hid⟩ := ih (by omega)
      have hu : t - d = (t - (d + 1)) + 1 := by omega
      obtain ⟨_, _, _, _, _, KK⟩ := link_stepT L hpi.1.1 hpo.1.2 (t - (d + 1))
        (fun s _ => ⟨(hpi.2 s).1, (hpo.2 s).2⟩)
      have KH := KK.2.2.2.2
      simp only [lst, rel_req, rel_ack] at KH
      have h0 := hb (t - (d + 1)) (by omega) (by omega)
      have h1 := hb (t - d) (by omega) (by omega)
      rw [hu] at h1 hcd hid
      obtain ⟨hct, ht0, ht1⟩ := KH (by simpa [inTx] using h0) (by simpa [inTx] using h1) hcd
      refine ⟨hct, ?_⟩
      rw [← hid, hh _ (by simpa [inTx] using ht0) (by simpa [inTx] using ht1)]
  have := (key (t - (r + 1)) (Nat.le_refl _)).2
  rwa [show t - (t - (r + 1)) = r + 1 by omega, eq_comm] at this

end link

/-! ## The per-channel physical data of a sampled output -/

variable {n : Nat}

/-- **The physical data of a sampled output channel `c` of operator `k`**: a tcheck row
(`TxWin` + separation), the launch values of each transaction, H_FN and H_LAUNCH. -/
inductive Row (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (w : Nat → Trace) (c : Fin n) : Prop
  | mk (net : Netlist) (hwf : net.WF) (sig : Nat → Nat → Trace) (data : List Nat)
      (R : Nat → Nat → Prop) (runs : ∀ m, Run net (sig m)) (X : TxWin (ch c) sig data R)
      (hsep : ∀ m v, R m v → ∀ d ∈ data, ∀ s, changes (sig m d) s → s ≤ v)
      (vin : Nat → Fin n → Nat) (vb : Nat → Bool)
      (H_FN : ∀ m, zdBus runs data m = fnOf sv k (vin m) (vb m))
      (H_LAUNCH : ∀ m r, OffAt (ch c) m r →
        (∀ i ∈ k.insC, vin m i = (ch i).dat (r + 1)) ∧ vb m = wonOf ch k w (r + 1)) :
      Row ch sv k w c

/-- A row gives the channel's bundling step by step (receiver rule up to `t`). -/
theorem Row.heldStep {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    {c : Fin n} (row : Row ch sv k w c) (hinit : Init (ch c)) {t : Nat}
    (hrecv : ∀ s, s ≤ t → RecvStep (ch c) s) : HeldStep (ch c) t := by
  obtain ⟨net, hwf, sig, data, R, runs, X, hsep, -, -, -, -⟩ := row
  exact heldStep_of_txwin hwf runs X hsep hinit hrecv

/-- The non-link fields from a row, given stability of `fval` over transactions. -/
theorem field_fin {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace} {c : Fin n}
    (row : Row ch sv k w c) (hp : Protocol (ch c))
    (hst : ∀ r t, r < t → (∀ s, r < s → s ≤ t → inTx (ch c) s = true) → fcond ch k t →
      fval ch sv k w t = fval ch sv k w (r + 1)) :
    ∀ t, inTx (ch c) t = true → fcond ch k t → (ch c).dat t = fval ch sv k w t := by
  obtain ⟨net, hwf, sig, data, R, runs, X, hsep, vin, vb, H_FN, H_LAUNCH⟩ := row
  refine field_of_tx hwf runs X hsep hp.1 (fun t => (hp.2 t).2) (fval ch sv k w) (fcond ch k)
    (fun m r ho => ?_) hst
  obtain ⟨h1, h2⟩ := H_LAUNCH m r ho
  rw [H_FN m, h2]
  exact fnOf_congr sv k _ h1

/-- **The composing lemma, every kind.** Handshake half, protocol and bundling on every
channel, and the row of output `c` ⇒ the data field of `c`. -/
theorem fieldOf_row {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (hj : Disj k) (h : HS ch sv k w) (hP : ∀ c, Protocol (ch c)) (hH : ∀ c, Held (ch c))
    {c : Fin n} (hc : c ∈ k.outsC) (row : Row ch sv k w c) : FieldOf ch sv k w c := by
  have hm : ∀ i ∈ k.insC, modC ch k.outsC (zdD ch sv k w) i = ch i :=
    fun i hi => modC_out (hj i hi)
  have hHm : ∀ i ∈ k.insC, Held (modC ch k.outsC (zdD ch sv k w) i) :=
    fun i hi => by rw [hm i hi]; exact hH i
  cases k with
  | forkG i os =>
    refine field_fin row (hP c) (fun r t hrt hb _ => ?_)
    have := stab_fork (h : ForkB _ _) (hP i) (fun o ho => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 ho; exact hP d) (hHm i (by simp [K.insC]))
      (List.mem_map_of_mem hc) hrt hb
    rw [hm i (by simp [K.insC])] at this
    exact this
  | forkH i os l hh d hs =>
    refine field_fin row (hP c) (fun r t hrt hb _ => ?_)
    have := stab_fork (h : ForkB _ _) (hP i) (fun o ho => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 ho; exact hP d) (hHm i (by simp [K.insC]))
      (List.mem_map_of_mem hc) hrt hb
    rw [hm i (by simp [K.insC])] at this
    exact this
  | join ins o e js jw =>
    refine field_fin row (hP c) (fun r t hrt hb _ => ?_)
    have hco : c = o := List.mem_singleton.1 hc
    subst hco
    have := stab_join (h : JoinB _ _ _) (hP c) (fun i hi => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 hi; exact hP d)
      (fun i hi => by obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hi; exact hHm d hd) hrt hb
    show jg e js (ins.map _) = jg e js (ins.map _)
    exact congrArg (jg e js) (List.map_congr_left (fun i hi => by
      have := this _ (List.mem_map_of_mem hi)
      rwa [hm i hi] at this))
  | bjoin ins o ec ed =>
    refine field_fin row (hP c) (fun r t hrt hb _ => ?_)
    have hco : c = o := List.mem_singleton.1 hc
    subst hco
    have := stab_join (h : JoinB _ _ _) (hP c) (fun i hi => by
      obtain ⟨d, _, rfl⟩ := List.mem_map.1 hi; exact hP d)
      (fun i hi => by obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hi; exact hHm d hd) hrt hb
    show bg ec ed (ins.map _) = bg ec ed (ins.map _)
    exact congrArg (bg ec ed) (List.map_congr_left (fun i hi => by
      have := this _ (List.mem_map_of_mem hi)
      rwa [hm i hi] at this))
  | steerC j tt f =>
    exact field_fin row (hP c) (fun r t _ _ _ => rfl)
  | steerD j tt f fd sw =>
    refine field_fin row (hP c) (fun r t hrt hb _ => ?_)
    have hb' : ∀ b, c = (bif b then tt else f) → ∀ s, r < s → s ≤ t →
        inTx (modC ch [tt, f] (zdD ch sv (.steerD j tt f fd sw) w) (bif b then tt else f)) s
          = true := by
      intro b e s h1 h2; rw [← e]; exact hb s h1 h2
    have hcb : ∃ b, c = (bif b then tt else f) := by
      simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with e | e
      · exact ⟨true, e⟩
      · exact ⟨false, e⟩
    obtain ⟨b, eb⟩ := hcb
    have := stab_steer (h : SteerB _ _ _ _) (hP j) (fun b => hP _) (hHm j (by simp [K.insC])) b
      hrt (hb' b eb)
    rw [hm j (by simp [K.insC])] at this
    show fd.eval [(ch j).dat t / 2] = fd.eval [(ch j).dat (r + 1) / 2]
    rw [this]
  | mux cc x y z mw =>
    refine field_fin row (hP c) (fun r t hrt hb _ => ?_)
    have hco : c = z := List.mem_singleton.1 hc
    subst hco
    have := stab_mux (h : MuxB _ _ _ _ _ _ _) (hP x) (hP y) (hP cc) (hP c)
      (hHm x (by simp [K.insC])) (hHm y (by simp [K.insC])) (hHm cc (by simp [K.insC])) hrt hb
    rw [hm x (by simp [K.insC]), hm y (by simp [K.insC]), hm cc (by simp [K.insC])] at this
    exact this
  | muxn cc x0 x1 x2 z nw =>
    refine field_fin row (hP c) (fun r t hrt hb h3 => ?_)
    have hco : c = z := List.mem_singleton.1 hc
    subst hco
    have hxm : ∀ m, cx3 x0 x1 x2 m ∈ (K.muxn cc x0 x1 x2 c nw).insC := by
      intro m
      have hm' := cx3_mem x0 x1 x2 m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm'
      simp only [K.insC, List.mem_cons, List.not_mem_nil, or_false]
      rcases hm' with e | e | e <;> simp [e]
    have h3' : selD ((modC ch (K.muxn cc x0 x1 x2 c nw).outsC (zdD ch sv (.muxn cc x0 x1 x2 c nw) w) cc).dat t) < 3 := by
      rw [hm cc (by simp [K.insC])]; exact h3
    obtain ⟨e1, e2⟩ := stab_muxn (h : MuxNB _ _ _ _ _) (fun m _ => hP _) (hP cc) (hP c)
      (fun m _ => hHm _ (hxm m)) (hHm cc (by simp [K.insC])) hrt hb h3'
    rw [hm cc (by simp [K.insC])] at e1 e2
    rw [hm _ (hxm _)] at e2
    show (ch (cx3 x0 x1 x2 (selD ((ch cc).dat t)))).dat t =
      (ch (cx3 x0 x1 x2 (selD ((ch cc).dat (r + 1))))).dat (r + 1)
    rw [← e1]; exact e2
  | amerge x y z ww =>
    refine field_fin row (hP c) (fun r t hrt hb _ => ?_)
    have hco : c = z := List.mem_singleton.1 hc
    subst hco
    obtain ⟨e1, e2⟩ := stab_amerge (h : AMergeB _ _ _ _ _) (hP x) (hP y) (hP c)
      (hHm x (by simp [K.insC])) (hHm y (by simp [K.insC])) hrt hb
    rw [hm x (by simp [K.insC]), hm y (by simp [K.insC])] at e2
    show 2 * (if (w 1 t || (ch y).ack t) then (ch y).dat t else (ch x).dat t) +
        Mux.b2n (w 1 t || (ch y).ack t) =
      2 * (if (w 1 (r + 1) || (ch y).ack (r + 1)) then (ch y).dat (r + 1) else (ch x).dat (r + 1))
        + Mux.b2n (w 1 (r + 1) || (ch y).ack (r + 1))
    rw [e2]
    exact congrArg (fun b => _ + Mux.b2n b) e1
  | link i o =>
    have hco : c = o := List.mem_singleton.1 hc
    subst hco
    obtain ⟨net, hwf, sig, data, R, runs, X, hsep, vin, vb, H_FN, H_LAUNCH⟩ := row
    refine ⟨fun t hw ht => ?_, fun t _ h0 h1 => ?_⟩
    · obtain ⟨m, r, ho, hr, hs⟩ := busy_cover (hP c).1 (fun t => ((hP c).2 t).2) t ht
      rw [sampled_eq_zd hwf runs X hsep ho hr hs, H_FN m]
      have := link_open_stable (h : LinkB _ _ _) (hP i) (hP c) (hHm i (by simp [K.insC])) hr hs hw
      rw [hm i (by simp [K.insC])] at this
      rw [this]
      exact (H_LAUNCH m r ho).1 i (by simp [K.insC])
    · exact heldStep_of_txwin hwf runs X hsep (hP c).1 (fun s _ => ((hP c).2 s).2) h0 h1
  | src z which d =>
    exact field_fin row (hP c) (fun r t _ _ _ => rfl)
  | sink i => simp [K.outsC] at hc

end Formal.Net.OpsBusy3
