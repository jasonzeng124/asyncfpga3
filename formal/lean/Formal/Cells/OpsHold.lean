import Formal.Cells.OpsTimed2
import Formal.Cells.MuxN3Timed
import Formal.Cells.LinkTimed
open Formal.Core.LutList

/-!
# Shard B Phase 3, probe G3: operator data held until the consumer's ack FALL

Gap G3 of `formal/notes/B-contracts.md`: C's `Held` (H_BUNDLE, `Formal/Net/Ops.lean`)
needs a channel's bus stable from req↑ until the ack↓ that closes the same token.
B's operator data theorems (`mux_data_ok`, `merge_data_ok`, `muxn3_data_ok`) prove
the output bit stable only until the server's ack RISE plus a margin, because
their sender contracts (`H_*_HOLD`) only promise the inputs until the senders
have seen their acknowledges RISE ("early" four-phase data protocol).

This file closes the gap on B's side (option (a) of the probe): with the
sender contracts strengthened to the library's own promise (BROAD=1, the
`bd_link` header: "data_out holds until ack_out has fallen"), the same gate
models give the output bit stable until the server's ack FALL plus a margin
that is a sum of MIN delays (no new setup obligation; for the merge one new
handover obligation on `usel`, `S_SEL_HO`). The strengthened sender contract
is then DERIVED for a `bd_link` sender from probe 6d's `stage_token`
(`link_hold_fall`, `link_holds_until`).

Main theorems:
* `mux_data_hold_fall`  — `bd_mux` (2-way), output = selected token's bit on
  `[Z(2k) - Mz, ζ(2k+1) + holdM k]`;
* `muxn3_data_hold_fall` — `bd_muxn` (3-way LUT5 data path), on
  `[Z(2k) - Mz, ζ(2k+1) + Hm]`;
* `merge_data_hold_fall` — `bd_merge` (usel + datamux), on
  `[Z(2k) - Mz, ζ(2k+1) + HmF]`;
* `link_hold_fall` / `link_holds_until` — a `bd_link` sender's output bit holds its
  token until (at least) the receiver's ack fall at the link's `ack_out` pin.

All gate models, INITs and run structures are the existing ones (read-only
imports); nothing shared is redefined.
-/

namespace Formal.Cells.OpsHold
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.Bundling (StableOn Gate)
open Formal.Cells.ConstraintsMux (DmRel dm_settles)

/-! ## 1. The 2-way mux -/

/-- **Sender contracts, hold-to-fall form** (the library's BROAD=1 promise).
Each sender keeps its data until it has SEEN its acknowledge FALL:
* **H_S_HOLDF**: the control sender sees ctl_ack (= z_ack through its wire
  `Wzc`) fall;
* **H_X_HOLDF / H_Y_HOLDF**: client x (y) sees x_ack (y_ack) fall at its pin
  for the control token `κ0 m` (`κ1 m`) that consumes its token `m`.
GLS test: on every token, the sender's data net changes only after the
falling edge of its ack at the sender's pin. For a `bd_link` sender this is
`link_holds_until` below. -/
structure MuxHoldF (P : MuxRun) (Wzc : Ret) (sE xE yE : Nat → Nat) : Prop where
  H_S_HOLDF : ∀ k, Wzc.fst (P.ζ (2 * k + 1)) ≤ sE k
  H_X_HOLDF : ∀ m, P.XA (2 * P.κ0 m + 1) ≤ xE m
  H_Y_HOLDF : ∀ m, P.YA (2 * P.κ1 m + 1) ≤ yE m

/-- **`mux_data_hold_fall`**: under the hold-to-fall sender contracts, the mux
output bit equals the selected token's bit from `Mz` before z_req reaches the
server until `holdM k` after the server's z_ack FALL (`ζ (2k+1)`); same
`holdM` (MIN delays only) and same setup obligations as `mux_data_ok`. -/
theorem mux_data_hold_fall {P : MuxRun} {Wzc : Ret} {s a b z : Trace}
    {slo shi alo ahi blo bhi wo Mz Ls Lx Ly : Nat} {sS sE xS xE yS yE : Nat → Nat}
    {xv yv : Nat → Bool}
    (hR : DmRel s a b z slo shi alo ahi blo bhi) (hsw : slo ≤ shi) (haw : alo ≤ ahi) (hbw : blo ≤ bhi)
    (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (D : MuxDataEnv P Wzc s a b sS sE xS xE yS yE xv yv Ls Lx Ly)
    (F : MuxHoldF P Wzc sE xE yE)
    (S : MuxDataStatic P wo shi ahi bhi Mz Ls Lx Ly) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k + 1) + P.holdM Wzc slo alo blo k →
      z t = P.zv xv yv k := by
  intro k t h1 h2
  have hγ : ∀ j, 1 ≤ P.γ j := fun j => (D.H_POS j).1
  have hζ1 := (D.H_POS (2 * k + 1)).2.2.2
  have hCE := C_le_E hE0 hE1 hγ (2 * k)
  rw [show 2 * k / 2 = k by omega] at hCE
  have hsE : P.ζ (2 * k + 1) + Wzc.lo ≤ sE k := by
    have := fl Wzc hζ1; have := F.H_S_HOLDF k; omega
  have hsS := D.H_S_LEAD k
  have hS := D.H_S_DATA k
  have hWO := S.H_WO
  cases hk : P.sv k
  · -- x selected
    have hm := κ_idx hE0 (k := k) (by simp [hk])
    have hxE := mux_xreq_le_E (fun j => (D.H_POS j).2.1) k hk
    have hc := (hCE.2 hk)
    have hc0 : P.γ (2 * k) + P.Wc0.lo ≤ P.C0 (2 * k) := by unfold MuxRun.C0; exact fl P.Wc0 (hγ _)
    have hEZ := mux_E_le_Z hWO (2 * k) (by omega)
    have hXA := mux_ζ_le_XA (2 * k + 1) hζ1
    have hxH := F.H_X_HOLDF (idx P.κ0 k)
    rw [hm] at hxH
    have hxS := D.H_X_LEAD (idx P.κ0 k)
    rw [hk] at hS
    have st := dm_settles hR hsw haw hbw false (xv (idx P.κ0 k)) (sS k) (sE k)
      (xS (idx P.κ0 k)) (xE (idx P.κ0 k)) hS (D.H_X_DATA (idx P.κ0 k))
    have hh : P.holdM Wzc slo alo blo k = min (Wzc.lo + slo) (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo + alo) := by
      unfold MuxRun.holdM; rw [hk]; rfl
    rw [hh] at h2
    have hv : P.zv xv yv k = xv (idx P.κ0 k) := by unfold MuxRun.zv; rw [hk]; rfl
    rw [hv]
    have := S.S_Z_S0; have := S.S_Z_X
    exact st t (by simp only [Bool.false_eq_true, ite_false]; omega)
      (by simp only [Bool.false_eq_true, ite_false]; omega)
  · -- y selected
    have hm := κ_idx hE1 (k := k) hk
    have hyE := mux_yreq_le_E (fun j => (D.H_POS j).2.2.1) k hk
    have hc := (hCE.1 hk)
    have hc1 : P.γ (2 * k) + P.Wc1.lo ≤ P.C1 (2 * k) := by unfold MuxRun.C1; exact fl P.Wc1 (hγ _)
    have hEZ := mux_E_le_Z hWO (2 * k) (by omega)
    have hYA := mux_ζ_le_YA (2 * k + 1) hζ1
    have hyH := F.H_Y_HOLDF (idx P.κ1 k)
    rw [hm] at hyH
    have hyS := D.H_Y_LEAD (idx P.κ1 k)
    rw [hk] at hS
    have st := dm_settles hR hsw haw hbw true (yv (idx P.κ1 k)) (sS k) (sE k)
      (yS (idx P.κ1 k)) (yE (idx P.κ1 k)) hS (D.H_Y_DATA (idx P.κ1 k))
    have hh : P.holdM Wzc slo alo blo k = min (Wzc.lo + slo) (P.Wzy.lo + P.Lya.lo + P.Wya.lo + blo) := by
      unfold MuxRun.holdM; rw [hk]; rfl
    rw [hh] at h2
    have hv : P.zv xv yv k = yv (idx P.κ1 k) := by unfold MuxRun.zv; rw [hk]; rfl
    rw [hv]
    have := S.S_Z_S1; have := S.S_Z_Y
    exact st t (by simp only [ite_true]; omega) (by simp only [ite_true]; omega)

/-! ## 2. The 3-way mux (`bd_muxn`, LUT5 data path) -/

section mn3
open Formal.Cells.MuxN3Timed
open Formal.Cells.Bundling (winK win_of_stable)
open Formal.Cells.AMergeGates (DM5)

/-- **H_D_HOLDF** (hold-to-fall, client side): client `i` keeps its token `m`'s
data until it has seen in_i_ack FALL at its pin for the control token
`κ i m` that consumes it. (`MN3DataEnv.H_S_HOLD` already has the control
sender hold until ctl_ack falls.) GLS test as for `MuxHoldF`. -/
structure MN3HoldF (P : MN3Run) (dE : Nat → Nat → Nat) : Prop where
  H_D_HOLDF : ∀ i, i < 3 → ∀ m, P.XA i (2 * P.κ i m + 1) ≤ dE i m

/-- **`muxn3_data_hold_fall`**: as `muxn3_data_ok` (REAL INIT `32'hF0AA_CCF0`,
same obligations `MN3DataStatic`, same margin `Hm`), but with the clients
holding until their ack falls the output bit is the selected token's until
`Hm` after the server's z_ack FALL. -/
theorem muxn3_data_hold_fall {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl : Nat}
    {s0d s1d z : Trace} {d : Nat → Trace} {sS sE : Nat → Nat} {dS dE : Nat → Nat → Nat}
    {xv : Nat → Nat → Bool} {Lsd Ld sl0 sh0 sl1 sh1 Mz Hm : Nat} {dl dh : Nat → Nat}
    (hz : Gate DM5 [(d 2, dl 2, dh 2), (d 1, dl 1, dh 1), (d 0, dl 0, dh 0), (s0d, sl0, sh0),
      (s1d, sl1, sh1)] z)
    (hw : sl0 ≤ sh0 ∧ sl1 ≤ sh1 ∧ ∀ i, i < 3 → dl i ≤ dh i)
    (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N)
    (D : MN3DataEnv P Wzc s0d s1d d sS sE dS dE xv Lsd Ld) (F : MN3HoldF P dE)
    (SD : MN3DataStatic P Wzc wc ls wsj lj wo Dl sl0 sh0 sl1 sh1 Mz Hm Lsd Ld dl dh) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k + 1) + Hm →
      z t = xv (P.sv k) (idx (P.κ (P.sv k)) k) := by
  intro k t h1 h2
  have hv := hR k
  have he := hE _ hv
  have hm := κ_idx he (k := k) (by unfold MN3Run.g; simp)
  -- request-path lower bounds
  have hEZ := E_le_Z hE hR Cs.H_POS (fun i hi => (S.H_MIN i hi).2.2.2.2) S.H_DL0 S.H_DLT hN (2 * k)
  have GE := GE_min hE hR Cs S (2 * k)
  have EZ := EZ_min hE hR Cs S hN (2 * k)
  have EZ1 := EZ_min hE hR Cs S hN (2 * k + 1)
  have ZE := ZE_min hE hR Cs S hN (2 * k)
  have hz0 : 1 ≤ P.ζ (2 * k) := by have := Cs.H_POS (2 * k); omega
  have hz1 : 1 ≤ P.ζ (2 * k + 1) := by have := Cs.H_POS (2 * k); omega
  -- the index pins
  have hsH := D.H_S_HOLD k; have hsL := D.H_S_LEAD k
  have hzc := fl Wzc hz1
  have s0st : StableOn s0d (b0 (P.sv k)) (sS k) (sE k) := fun u a b => (D.H_S_DATA k u a b).1
  have s1st : StableOn s1d (b1 (P.sv k)) (sS k) (sE k) := fun u a b => (D.H_S_DATA k u a b).2
  obtain ⟨hw0, hw1, hwd⟩ := hw
  obtain ⟨hm0, hm1, hmd⟩ := SD.S_HM
  have w0 : winK s0d sl0 sh0 t = K3.ofBool (b0 (P.sv k)) :=
    win_of_stable hw0 s0st (by have := SD.S_Z_S; omega) (by omega)
  have w1 : winK s1d sl1 sh1 t = K3.ofBool (b1 (P.sv k)) :=
    win_of_stable hw1 s1st (by have := SD.S_Z_S; omega) (by omega)
  -- the selected data pin
  have hE2 : P.E (2 * k) = P.τ (P.sv k) (2 * idx (P.κ (P.sv k)) k) := by
    unfold MN3Run.E; rw [show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega, Nat.add_zero]
  have hX : P.Xp (P.sv k) (2 * idx (P.κ (P.sv k)) k) + (P.Lj (P.sv k)).lo ≤ P.E (2 * k) := by
    rw [hE2]; unfold MN3Run.τ
    have hx1 := (P.Wx (P.sv k)).fst_ge (P.ξ (P.sv k) (2 * idx (P.κ (P.sv k)) k))
    have hx2 := D.H_XPOS _ hv (2 * idx (P.κ (P.sv k)) k)
    have := fl (P.Lj (P.sv k)) (c := P.c (P.sv k) (2 * idx (P.κ (P.sv k)) k)) (by
      show 1 ≤ max (P.Xp (P.sv k) (2 * idx (P.κ (P.sv k)) k)) (P.D (P.sv k) (2 * idx (P.κ (P.sv k)) k))
      unfold MN3Run.Xp; omega)
    have : P.Xp (P.sv k) (2 * idx (P.κ (P.sv k)) k) ≤ P.c (P.sv k) (2 * idx (P.κ (P.sv k)) k) := by
      unfold MN3Run.c; omega
    omega
  have hxp := fl (P.Wx (P.sv k)) (D.H_XPOS _ hv (2 * idx (P.κ (P.sv k)) k))
  have hdL := D.H_D_LEAD _ hv (idx (P.κ (P.sv k)) k)
  have hdH := F.H_D_HOLDF _ hv (idx (P.κ (P.sv k)) k)
  rw [hm] at hdH
  have hXA : P.ζ (2 * k + 1) + (P.Wza (P.sv k)).lo + (P.La (P.sv k)).lo + (P.Wak (P.sv k)).lo ≤
      P.XA (P.sv k) (2 * k + 1) := by
    have a := fl (P.Wza (P.sv k)) hz1
    have hc : P.ZA (P.sv k) (2 * k + 1) ≤ P.cx (P.sv k) (2 * k + 1) := by unfold MN3Run.cx; omega
    have hZ : P.ZA (P.sv k) (2 * k + 1) = (P.Wza (P.sv k)).fst (P.ζ (2 * k + 1)) := rfl
    have b := fl (P.La (P.sv k)) (c := P.cx (P.sv k) (2 * k + 1)) (by omega)
    have c := fl (P.Wak (P.sv k)) (c := (P.La (P.sv k)).fst (P.cx (P.sv k) (2 * k + 1))) (by omega)
    show _ ≤ (P.Wak (P.sv k)).fst ((P.La (P.sv k)).fst (P.cx (P.sv k) (2 * k + 1))); omega
  have dst : StableOn (d (P.sv k)) (xv (P.sv k) (idx (P.κ (P.sv k)) k))
      (dS (P.sv k) (idx (P.κ (P.sv k)) k)) (dE (P.sv k) (idx (P.κ (P.sv k)) k)) :=
    fun u a b => D.H_D_DATA _ hv _ u a b
  have wd : winK (d (P.sv k)) (dl (P.sv k)) (dh (P.sv k)) t =
      K3.ofBool (xv (P.sv k) (idx (P.κ (P.sv k)) k)) :=
    win_of_stable (hwd _ hv) dst (by have := SD.S_Z_D _ hv; unfold MN3Run.Xp at hX; omega)
      (by have := hmd _ hv; omega)
  apply hz t
  show lutK DM5 [winK (d 2) (dl 2) (dh 2) t, winK (d 1) (dl 1) (dh 1) t, winK (d 0) (dl 0) (dh 0) t,
    winK s0d sl0 sh0 t, winK s1d sl1 sh1 t] = _
  rw [w0, w1]
  apply dm5_sel (P.sv k) hv
  obtain h | h | h : P.sv k = 0 ∨ P.sv k = 1 ∨ P.sv k = 2 := by omega
  · rw [h] at wd ⊢; simpa using wd
  · rw [h] at wd ⊢; simpa using wd
  · rw [h] at wd ⊢; simpa using wd

end mn3

/-! ## 3. A `bd_link` sender meets the hold-to-fall contract

Probe 6d (`LinkTimed.stage_token`) proves that latch bit `i` of a `bd_link`
stage (REAL `bd_c2n` controller INIT, enable fanout windows, Kleene latch
LUT) holds token `k` until `cph(2k+2) + dlmin + elo i`, where
`cph(2k+2) = max (ρ (k+1)) (β k)` and `β k` is the fall of `ack_out` at the
controller's I1 pin. So the stage's output holds its token until AFTER it has
seen its acknowledge fall: this is the library's BROAD=1 promise, derived,
not assumed. `link_hold_fall` states it in `StableOn` form; `link_x_sender`
packages it as the mux's x-client fields (`H_X_DATA`, `H_X_HOLDF`). -/

section link
open Formal.Cells.LinkTimed
variable {req ack rst O qp : LinkTimed.Trace} {ρ φ α β : Nat → Nat}
  {dlmin dlmax dwmin dwmax E t0 : Nat}
  {d q : Nat → Bundling.Sig} {val : Nat → Nat → Bool} {dS dE : Nat → Nat}
  {dlo dhi elo ehi flo fhi : Nat → Nat} {W Erel Sdr Lag : Nat}

/-- **`link_hold_fall`**: a `bd_link` output bit holds token `k` from its
capture until at least the instant its `ack_out` pin sees the receiver's
acknowledge fall (`β k`), and in fact `dlmin + elo i - 1` beyond.
`hpos` (**H_EN_POS**): the controller LUT arc plus the bit's enable branch
take at least one tick (a positive physical delay; prjxray minima). -/
theorem link_hold_fall (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    (k i : Nat) (hi : i < W) (hpos : 1 ≤ dlmin + elo i) :
    StableOn (q i) (val k i) (max (cph ρ φ α β (2 * k) + dlmax + ehi i) (dS k + dhi i))
      (β k + (dlmin + elo i) - 1) := by
  intro t h1 h2
  have hb : β k ≤ cph ρ φ α β (2 * k + 1 + 1) := by rw [cph_e1]; exact Nat.le_max_right _ _
  exact stage_token C D k i hi t h1 (by omega)

/-- **`link_x_sender`**: if client x of a `bd_mux` is latch bit `i` of a
`bd_link` stage whose `m`-th output token is x's `m`-th token, and the mux's
x_ack fall at x's pin for that token is no later than the link's `ack_out`
pin sees it (`hXA`; equality when both name the same pin, the G2
observation-point convention), then x meets the data and hold-to-fall
fields of the mux contract with `xS m = max (…)` and `xE m = β m + dlmin + elo i - 1`. -/
theorem link_x_sender {P : MuxRun}
    (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    (i : Nat) (hi : i < W) (hpos : 1 ≤ dlmin + elo i)
    (hXA : ∀ m, P.XA (2 * P.κ0 m + 1) ≤ β m) :
    (∀ m, StableOn (q i) (val m i) (max (cph ρ φ α β (2 * m) + dlmax + ehi i) (dS m + dhi i))
      (β m + (dlmin + elo i) - 1)) ∧
    (∀ m, P.XA (2 * P.κ0 m + 1) ≤ β m + (dlmin + elo i) - 1) :=
  ⟨fun m => link_hold_fall C D m i hi hpos, fun m => by have := hXA m; omega⟩

end link

/-! ## 4. The merge (`bd_merge`: usel + datamux)

`sel = x_req | x_ack` (`usel`, REAL `4'hE`), `z = sel ? x : y`. Until the
server's z_ack RISE (`merge_data_ok`) `sel` is held by x_req alone (x owner)
or by x_req and x_ack both low (y owner). Holding to the z_ack FALL needs:
* x owner: x_req falls during the return-to-zero, so `sel` must be HANDED
  OVER to x_ack (uxa's node), which stays high until after z_ack falls.
  Without a gap this needs x_ack's rise to reach usel's output no later than
  x_req's fall does: **S_SEL_HO** `hq ≤ Wxa.lo + Eo + lr` (x_req falls at
  least `Wxa.lo + Eo` after uxa's node rose: the node → client wire plus the
  client's reaction; `bd_merge.isochronic_forks`' x_ack branch, timed);
  then **S_HMF_SEL_X** `Hm + 1 ≤ Wzx.lo + Lxa.lo + lq + sl` (x_ack's fall,
  which follows z_ack's fall through uxa, reaches the datamux select after
  the hold margin).
* y owner: x_req and x_ack stay low until the NEXT merged request (H_OWN:
  after y_ack's fall), which is after z_ack's fall: the existing
  `S_HM_SEL_Y` already covers it.
The data obligations `S_HM_X`, `S_HM_Y` are unchanged (sums of MIN delays from
z_ack's FALL to the client's ack fall). -/

open Formal.Cells.ConstraintsMux (usel_kleene usel_high)
open Formal.Cells.LibCtlMergeMux (c2B c2_spec)
open Formal.Cells.Bundling (win_of_stable winK)

/-- usel high through its SECOND pin (x_ack). -/
theorem usel_high2 {xr xa sel : Trace} {lo hi lo' hi' : Nat}
    (hg : Gate 0xE [(xr, lo, hi), (xa, lo', hi')] sel) (hw' : lo' ≤ hi') (T T' : Nat)
    (ha : StableOn xa true T T') : StableOn sel true (T + hi') (T' + lo') := by
  intro t h1 h2
  apply hg t true
  show lutK 0xE [winK xr lo hi t, winK xa lo' hi' t] = _
  rw [win_of_stable hw' ha (by omega) (by omega), usel_kleene]; simp [K3.ofBool]

/-- Two overlapping (or abutting) stable windows make one. -/
theorem stable_union {x : Trace} {v : Bool} {A B C D : Nat}
    (h1 : StableOn x v A B) (h2 : StableOn x v C D) (hC : C ≤ B + 1) : StableOn x v A D := by
  intro t a b
  by_cases h : t ≤ B
  · exact h1 t a h
  · exact h2 t (by omega) b

/-- **Hold-to-fall contracts of the merge's clients**: the owner of merged
token `k` keeps its data until it has seen its ack FALL at its pin. -/
structure MergeHoldF (P : MergeRun) (xE yE : Nat → Nat) : Prop where
  H_X_HOLDF : ∀ k, P.sv k = false → P.XA (2 * k + 1) ≤ xE k
  H_Y_HOLDF : ∀ k, P.sv k = true → P.YA (2 * k + 1) ≤ yE k

/-- **The two new per-arc obligations** (see the section comment). -/
structure MergeHoldStatic (P : MergeRun) (Eo lr lq hq sl Hm : Nat) : Prop where
  /-- **S_SEL_HO** (sel handover x_req → x_ack, x owner). -/
  S_SEL_HO : hq ≤ P.Wxa.lo + Eo + lr
  /-- **S_HMF_SEL_X** (x_ack's fall reaches the datamux select after `Hm`). -/
  S_HMF_SEL_X : Hm + 1 ≤ P.Wzx.lo + P.Lxa.lo + lq + sl

/-- **`merge_data_hold_fall`**: under the clients' hold-to-fall contracts and
the two new obligations, the merge output bit equals the owner's bit for
merged token `k` from `Mz` before z_req reaches the server until `Hm` after
the server's z_ack FALL. Same gate model (REAL `usel` and datamux INITs,
window relation), same control environment and data obligations as
`merge_data_ok`. -/
theorem merge_data_hold_fall {P : MergeRun} {R Eo Es wo wz la wa : Nat}
    {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak sel xd yd z : Trace}
    {lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly : Nat} {xS xE yS yE : Nat → Nat} {xv yv : Nat → Bool}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0)
    (hU : Gate 0xE [(x, lr, hr), (xa, lq, hq)] sel) (hlr : lr ≤ hr) (hlq : lq ≤ hq)
    (hR : DmRel sel yd xd z sl sh yl yh xl xh) (hsw : sl ≤ sh) (hyw : yl ≤ yh) (hxw : xl ≤ xh)
    (D : MergeDataEnv P xd yd xS xE yS yE xv yv Lx Ly) (F : MergeHoldF P xE yE)
    (SD : MergeDataStatic P Eo Es wo wz la wa lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly)
    (SH : MergeHoldStatic P Eo lr lq hq sl Hm) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k + 1) + Hm →
      z t = (if P.sv k then yv k else xv k) := by
  have TM := merge_timing_of_static Cs S hRL hRE
  obtain ⟨_, _, _, _, r5, _⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, _, _⟩ := TM.H_RST_EARLY
  have ax : Tok R xc P.AX (fun k => !P.sv k) := (V.H_X.fifo P.Wxc G.H_WXC).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl xc zx rst xa qa (fun t => c2B (xc t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u1 u2 TM.H_DEP_XA)
  have hp := Cs.H_POS
  have RZ := merge_RZ Cs S
  have ZR := merge_ZR Cs S
  have RM := merge_ρ_mono Cs S
  have hWO := S.H_WO; have hWZ := S.H_WZ; have hLA := S.H_LA; have hWA := S.H_WA
  intro k t h1 h2
  have hz : 1 ≤ P.ζ (2 * k) := by have := RZ (2 * k); have := hp (2 * k); omega
  have hz1 : 1 ≤ P.ζ (2 * k + 1) := by have := RZ (2 * k + 1); have := hp (2 * k + 1); omega
  have hown := Cs.H_OWN (2 * k)
  rw [show 2 * k / 2 = k by omega] at hown
  have hZ := merge_ρ_le_Z hp k
  have hρ1 := hp (2 * k + 1)
  cases hk : P.sv k
  · -- x owns token k: sel high through x_req, then handed over to x_ack
    rw [hk] at hown; simp only [Bool.false_eq_true, ite_false] at hown
    have hZk := hZ.1 hk
    have hxr : StableOn x true (P.ρ (2 * k)) (P.ρ (2 * k + 1) - 1) := fun u u1 u2 => by
      have := V.H_X.hi k u (Nat.zero_le _) u1 (by omega); rw [this, hk]; rfl
    have hsel1 := usel_high hU hlr _ _ hxr
    -- uxa's node: high on [N(2k), N(2k+1))
    have hxa : StableOn xa true (P.Lxa.fst (max (P.AX (2 * k)) (P.ZA0 (2 * k))))
        (P.Lxa.fst (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1))) - 1) := fun u u1 u2 => by
      have hT : P.Lxa.hi ≤ P.Lxa.fst (max (P.AX (2 * k)) (P.ZA0 (2 * k))) := by
        have a1 := fst_mono P.Wxc (RM 0 (2 * k) (Nat.zero_le _))
        have a2 := P.Lxa.fst_ge (max (P.AX (2 * k)) (P.ZA0 (2 * k)))
        have := hRE.1
        unfold MergeRun.AX at *; omega
      have hN1p : 1 ≤ P.Lxa.fst (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1))) := by
        have := P.Lxa.fst_ge (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1)))
        have := P.Wzx.fst_ge (P.ζ (2 * k + 1))
        unfold MergeRun.ZA0 at *; omega
      have := nx.hi k u (by omega) u1 (by omega)
      rw [this, hk]; rfl
    have hsel2 := usel_high2 hU hlq _ _ hxa
    -- handover: the node's rise + hq is no later than x_req's fall + lr
    have hN0 : P.Lxa.fst (max (P.AX (2 * k)) (P.ZA0 (2 * k))) + P.Wxa.lo ≤ P.XA (2 * k) := by
      unfold MergeRun.XA MergeRun.cx
      have := P.Lxa.fst_ge (max (P.AX (2 * k)) (P.ZA0 (2 * k)))
      have := P.Wzx.fst_ge (P.ζ (2 * k))
      exact fl P.Wxa (by unfold MergeRun.ZA0 at *; omega)
    have hho := SH.S_SEL_HO
    have hsel := stable_union hsel1 hsel2 (by omega)
    -- x_ack's node falls after z_ack's fall
    have hN1 : P.ζ (2 * k + 1) + P.Wzx.lo + P.Lxa.lo ≤
        P.Lxa.fst (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1))) := by
      have a := fl P.Wzx hz1
      have b := fl P.Lxa (c := max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1))) (by
        unfold MergeRun.ZA0; omega)
      unfold MergeRun.ZA0 at b ⊢; omega
    have hXA := merge_ζ_le_XA (2 * k + 1) hz1
    have st := dm_settles hR hsw hyw hxw true (xv k) _ _ (xS k) (xE k) hsel (D.H_X_DATA k hk)
    have := D.H_X_LEAD k hk; have := F.H_X_HOLDF k hk
    have := SD.S_ZM_SEL_X; have := SD.S_ZM_X; have := SH.S_HMF_SEL_X; have := SD.S_HM_X
    simp only [ite_true] at st
    simp only [Bool.false_eq_true, ite_false]
    exact st t (by omega) (by omega)
  · -- y owns token k: sel low (x_req and x_ack both low) until the next merged request
    rw [hk] at hown; simp only [ite_true] at hown
    have hZk := hZ.2 hk
    have hown1 := Cs.H_OWN (2 * k + 1)
    rw [show (2 * k + 1) / 2 = k by omega, hk] at hown1; simp only [ite_true] at hown1
    rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at hown1
    have hYA1 := merge_ζ_le_YA (2 * k + 1) hz1
    have hρ2 := hp (2 * k + 2)
    -- x_ack's next rise is after x_req's next edge
    have hXN : P.ρ (2 * k + 2) ≤ P.Lxa.fst (max (P.AX (2 * k + 2)) (P.ZA0 (2 * k + 2))) := by
      have := P.Lxa.fst_ge (max (P.AX (2 * k + 2)) (P.ZA0 (2 * k + 2)))
      have : P.ρ (2 * k + 2) ≤ P.AX (2 * k + 2) := P.Wxc.fst_ge _
      omega
    have sl0 : Tok.SlotLow (fun k => !P.sv k) (2 * k) := Tok.slotLow_even (by simp [hk])
    have sl0' : Tok.SlotLow (fun k => !P.sv k && true) (2 * k) := Tok.slotLow_even (by simp [hk])
    have hS0 := SD.H_SEL_START
    have hmono := RM 0 (2 * k) (Nat.zero_le _)
    obtain ⟨T1, T2, hx0, ha0, hb1, hb2⟩ : ∃ T1 T2, StableOn x false T1 (P.ρ (2 * k + 2) - 1) ∧
        StableOn xa false T2 (P.ρ (2 * k + 2) - 1) ∧
        T1 + hr + sh + Mz ≤ P.ρ (2 * k) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) ∧
        T2 + hq + sh + Mz ≤ P.ρ (2 * k) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) := by
      cases k with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add] at *
        refine ⟨0, P.Lxa.hi, fun u u1 u2 => ?_, fun u u1 u2 => ?_, by omega, by omega⟩
        · exact V.H_X.low_pre 2 u (fun j hj => by
            rcases (show j = 0 ∨ j = 1 by omega) with r | r
            · subst r; exact sl0
            · subst r; exact Tok.slotLow_odd _ 0) (Nat.zero_le _) (by omega)
        · exact nx.low_pre 2 u (fun j hj => by
            rcases (show j = 0 ∨ j = 1 by omega) with r | r
            · subst r; exact sl0'
            · subst r; exact Tok.slotLow_odd _ 0) u1 (by omega)
      | succ k' =>
        have e1 : 2 * (k' + 1) = 2 * k' + 1 + 1 := by omega
        have r1 := RZ (2 * k' + 1); have z1 := ZR (2 * k' + 1)
        rw [← e1] at z1
        have hc : max (P.AX (2 * k' + 1)) (P.ZA0 (2 * k' + 1)) ≤
            max (P.ρ (2 * k' + 1) + P.Wxc.hi) (P.ζ (2 * k' + 1) + P.Wzx.hi) := by
          have := P.Wxc.fst_le (P.ρ (2 * k' + 1)); have := P.Wzx.fst_le (P.ζ (2 * k' + 1))
          unfold MergeRun.AX MergeRun.ZA0; omega
        have hN := P.Lxa.fst_le (max (P.AX (2 * k' + 1)) (P.ZA0 (2 * k' + 1)))
        have slo : ∀ g : Nat → Bool, Tok.SlotLow g (2 * (k' + 1)) →
            ∀ j, 2 * k' + 1 ≤ j → j < 2 * (k' + 1) + 2 → Tok.SlotLow g j := fun g hg j hj1 hj2 => by
          rcases (show j = 2 * k' + 1 ∨ j = 2 * (k' + 1) ∨ j = 2 * (k' + 1) + 1 by omega) with r | r | r
          · subst r; exact Tok.slotLow_odd g k'
          · subst r; exact hg
          · subst r; exact Tok.slotLow_odd g (k' + 1)
        refine ⟨P.ρ (2 * k' + 1), max P.Lxa.hi (P.Lxa.fst (max (P.AX (2 * k' + 1)) (P.ZA0 (2 * k' + 1)))),
          fun u u1 u2 => ?_, fun u u1 u2 => ?_, ?_, ?_⟩
        · exact V.H_X.low_range (2 * (k' + 1) + 2) (2 * k' + 1) u (by omega) (slo _ sl0)
            (Nat.zero_le _) u1 (by omega)
        · exact nx.low_range (2 * (k' + 1) + 2) (2 * k' + 1) u (by omega) (slo _ sl0')
            (by omega) (by omega) (by omega)
        · have := SD.S_SEL_XR; omega
        · have := SD.S_SEL_XA_Z; have := SD.S_SEL_XA_R; omega
    have hsel := usel_low2 hU hlr hlq T1 T2 _ hx0 ha0
    have st := dm_settles hR hsw hyw hxw false (yv k) _ _ (yS k) (yE k) hsel (D.H_Y_DATA k hk)
    have := D.H_Y_LEAD k hk; have := F.H_Y_HOLDF k hk
    have := SD.S_ZM_Y; have := SD.S_HM_SEL_Y; have := SD.S_HM_Y
    simp only [Bool.false_eq_true, ite_false] at st
    simp only [ite_true]
    exact st t (by omega) (by omega)

/-! ## 5. Non-vacuity of `mux_data_hold_fall` (Probe Lt's unit-delay mux run)

Same run (`MuxWit.run`: tokens alternate x, y; every arc one tick), same
client data (`MuxWit.xd`, `yd`: x's `m`-th token carries `m` even, y's `m`
odd). The control sender's select is re-timed (`sF`: token `k` on
`[18k+8, 18k+25]`, settled AT the control request, `Ls = 0`) so that it holds
until it has seen ctl_ack fall (`18k+24` at the server, `18k+25` at the
sender). Only the data theorem's hypotheses are instantiated (the control
side's `MuxGates` reads the old select `sx`; `mux_data_hold_fall` does not
take the gates). -/
namespace MuxHoldWit
open Formal.Cells.OpsTimed.MuxWit
open Formal.Cells.ConstraintsMux (DM_ODD dm_odd_rel)
open Formal.Cells.Bundling (transport_gate)

def sF (t : Nat) : Bool := svW ((t - 8) / 18)
def zF (t : Nat) : Bool := lutB DM_ODD [sF (t - 1), xd (t - 1), yd (t - 1)]

theorem zF_rel : DmRel sF xd yd zF 1 1 1 1 1 1 :=
  dm_odd_rel (transport_gate DM_ODD [(sF, 1, 1, 1), (xd, 1, 1, 1), (yd, 1, 1, 1)] zF
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MuxDataEnv run uW sF xd yd (fun k => 18 * k + 8) (fun k => 18 * k + 25)
    (fun m => 36 * m) (fun m => 36 * m + 35) (fun m => 36 * m + 18) (fun m => 36 * m + 53)
    xvW yvW 0 4 4 where
  H_S_DATA k t h1 h2 := by
    show svW ((t - 8) / 18) = svW k; rw [show (t - 8) / 18 = k by omega]
  H_X_DATA m t h1 h2 := by show xvW (t / 36) = xvW m; rw [show t / 36 = m by omega]
  H_Y_DATA m t h1 h2 := by show yvW ((t - 18) / 36) = yvW m; rw [show (t - 18) / 36 = m by omega]
  H_S_LEAD k := by show _ ≤ 18 * (2 * k / 2) + 8 + 8 * (2 * k % 2); omega
  H_X_LEAD m := by show _ ≤ 36 * (2 * m / 2) + 4 + 14 * (2 * m % 2); omega
  H_Y_LEAD m := by show _ ≤ 36 * (2 * m / 2) + 22 + 14 * (2 * m % 2); omega
  H_S_HOLD k := by
    show uW.fst (18 * (2 * k / 2) + 14 + 10 * (2 * k % 2)) ≤ _
    rw [fuW _ (by omega)]; omega
  H_X_HOLD m := by
    rw [(XA_eq _).1]; show 18 * (2 * (2 * m) / 2) + 17 + 10 * (2 * (2 * m) % 2) ≤ _; omega
  H_Y_HOLD m := by
    rw [(XA_eq _).2]; show 18 * (2 * (2 * m + 1) / 2) + 17 + 10 * (2 * (2 * m + 1) % 2) ≤ _; omega
  H_POS j := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 ≤ 18 * (j / 2) + 8 + 8 * (j % 2); omega
    · show 1 ≤ 36 * (j / 2) + 4 + 14 * (j % 2); omega
    · show 1 ≤ 36 * (j / 2) + 22 + 14 * (j % 2); omega
    · show 1 ≤ 18 * (j / 2) + 14 + 10 * (j % 2); omega

theorem hold_fall : MuxHoldF run uW (fun k => 18 * k + 25) (fun m => 36 * m + 35)
    (fun m => 36 * m + 53) where
  H_S_HOLDF k := by
    show uW.fst (18 * ((2 * k + 1) / 2) + 14 + 10 * ((2 * k + 1) % 2)) ≤ _
    rw [fuW _ (by omega)]; omega
  H_X_HOLDF m := by
    rw [(XA_eq _).1]; show 18 * ((2 * (2 * m) + 1) / 2) + 17 + 10 * ((2 * (2 * m) + 1) % 2) ≤ _
    omega
  H_Y_HOLDF m := by
    rw [(XA_eq _).2]
    show 18 * ((2 * (2 * m + 1) + 1) / 2) + 17 + 10 * ((2 * (2 * m + 1) + 1) % 2) ≤ _
    omega

theorem data_static : MuxDataStatic run 1 1 1 1 0 0 4 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Non-vacuity of `mux_data_hold_fall`.** -/
theorem witness : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k + 1) + run.holdM uW 1 1 1 k →
    zF t = run.zv xvW yvW k :=
  mux_data_hold_fall zF_rel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) enum0 enum1
    data_env hold_fall data_static

/-- Not degenerate: token 0 (x, bit 1) is still delivered at 26, two ticks
after z_ack FELL at the server (`ζ 1 = 24`), i.e. 10 ticks beyond the old
window's end `ζ 0 + holdM = 16`, while the unselected y carries 0; token 1
(y, bit 0) then delivers 0. -/
theorem witness_values :
    run.ζ 0 = 14 ∧ run.ζ 1 = 24 ∧ zF 26 = true ∧ yd 25 = false ∧ zF 34 = false ∧ xd 33 = true := by
  refine ⟨rfl, rfl, by decide, by decide, by decide, by decide⟩

/-- **Negative control: the old ("early", ack-rise) select contract does NOT
give the hold-to-fall window.** `MuxWit.zW` (OpsTimed2's witness, select `sx`
released at 18k+22, after ctl_ack ROSE but before it fell) satisfies every
hypothesis of `mux_data_ok`; inside the hold-to-fall window of token 0
(`26 ≤ ζ 1 + holdM = 26`) its output is already the NEXT token's select
reading y (0), not token 0's bit (1). So the strengthened sender contract is
load-bearing, and C's `Held` is not implied by B's old theorem. -/
theorem early_release_breaks :
    run.Z 0 ≤ 26 ∧ 26 ≤ run.ζ 1 + run.holdM uW 1 1 1 0 ∧ run.zv xvW yvW 0 = true ∧
      MuxWit.zW 26 = false := by
  refine ⟨?_, ?_, by decide, by decide⟩
  · rw [Z_eq, E_eq]; decide
  · show 26 ≤ 24 + min (1 + 1) (1 + 1 + 1 + 1); decide

end MuxHoldWit

/-! ## 6. Non-vacuity of `merge_data_hold_fall` (Probe Lt's unit-delay merge run)

`MergeWit.run` (merged tokens alternate x, y; every arc one tick; the REAL
`usel` and datamux INITs with unit transport delay). The clients' data are
re-timed so that each holds its token until it has seen its ack FALL
(`XA (2k+1) = 16k+19`): token `k` on `[16k+4, 16k+19]`, settled at the
request (`Lx = Ly = 0`). Every hypothesis, control and data, old and new
(`S_SEL_HO`, `S_HMF_SEL_X`), is instantiated. -/
namespace MergeHoldWit
open Formal.Cells.OpsTimed.MergeWit
open Formal.Cells.ConstraintsMux (DM_ODD dm_odd_rel)
open Formal.Cells.Bundling (transport_gate)

def xdF (t : Nat) : Bool := xvW ((t - 4) / 16)
def ydF (t : Nat) : Bool := yvW ((t - 4) / 16)
def zmF (t : Nat) : Bool := lutB DM_ODD [selW (t - 1), ydF (t - 1), xdF (t - 1)]

theorem zmF_rel : DmRel selW ydF xdF zmF 1 1 1 1 1 1 :=
  dm_odd_rel (transport_gate DM_ODD [(selW, 1, 1, 1), (ydF, 1, 1, 1), (xdF, 1, 1, 1)] zmF
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MergeDataEnv run xdF ydF (fun k => 16 * k + 4) (fun k => 16 * k + 19)
    (fun k => 16 * k + 4) (fun k => 16 * k + 19) xvW yvW 0 0 where
  H_X_DATA k _ t h1 h2 := by
    show xvW ((t - 4) / 16) = xvW k; rw [show (t - 4) / 16 = k by omega]
  H_Y_DATA k _ t h1 h2 := by
    show yvW ((t - 4) / 16) = yvW k; rw [show (t - 4) / 16 = k by omega]
  H_X_LEAD k _ := by show _ ≤ 8 * (2 * k) + 4; omega
  H_Y_LEAD k _ := by show _ ≤ 8 * (2 * k) + 4; omega
  H_X_HOLD k _ := by rw [(XA_eq _).1]; show _ ≤ 16 * k + 19; omega
  H_Y_HOLD k _ := by rw [(XA_eq _).2]; show _ ≤ 16 * k + 19; omega

theorem hold_fall : MergeHoldF run (fun k => 16 * k + 19) (fun k => 16 * k + 19) where
  H_X_HOLDF k _ := by rw [(XA_eq _).1]; show _ ≤ 16 * k + 19; omega
  H_Y_HOLDF k _ := by rw [(XA_eq _).2]; show _ ≤ 16 * k + 19; omega

theorem data_static : MergeDataStatic run 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 2 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem hold_static : MergeHoldStatic run 1 1 1 1 1 2 := ⟨by decide, by decide⟩

/-- **Non-vacuity of `merge_data_hold_fall`.** -/
theorem witness : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k + 1) + 2 →
    zmF t = (if run.sv k then yvW k else xvW k) :=
  merge_data_hold_fall gates env causal static (by decide) (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega)
    selW_gate (Nat.le_refl _) (Nat.le_refl _) zmF_rel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    data_env hold_fall data_static hold_static

set_option maxRecDepth 8000 in
/-- Not degenerate: token 0 (x, bit 1) is delivered at 18 = `ζ 1 + 2` (z_ack
fell at 16), through the usel handover (x_req is already low at usel's
input: `x 16 = false`), while y carries 0; token 2 (x, bit 0) at 50 while y
carries 1. -/
theorem witness_values :
    run.ζ 1 = 16 ∧ zmF 18 = true ∧ x 16 = false ∧ ydF 17 = false ∧
      zmF 50 = false ∧ ydF 49 = true := by
  refine ⟨rfl, by decide, by decide, by decide, by decide, by decide⟩

/-- **Negative control**: OpsTimed2's merge witness (clients release at
`16k+15`, after their ack ROSE, before it fell) satisfies all of
`merge_data_ok`'s hypotheses, yet inside token 0's hold-to-fall window
(`18 ≤ ζ 1 + 2`) its output is 0, not token 0's bit 1. -/
theorem early_release_breaks :
    run.Z 0 ≤ 18 ∧ 18 ≤ run.ζ 1 + 2 ∧ (if run.sv 0 then yvW 0 else xvW 0) = true ∧
      zmW 18 = false := by
  refine ⟨?_, by decide, by decide, by decide⟩
  rw [Z_eq]; decide

end MergeHoldWit

/-! ## 7. Non-vacuity of `muxn3_data_hold_fall` (probe M3's unit-delay 3-way run)

`Mn3Wit.run`: control token `k` selects input `k % 3`, every arc one tick.
Its data contract already holds each client's token for 60 ticks, i.e.
past the client's ack fall (`XA i (2k+1) = 20k + 49`), so the existing
`data_env` plus `MN3HoldF` instantiate the new theorem: the LUT5 delivers the
selected bit until 2 ticks after z_ack FALLS. -/
namespace Mn3HoldWit
open Formal.Cells.MuxN3Timed Formal.Cells.MuxN3Timed.Mn3Wit

theorem hold_fall : MN3HoldF run (fun i m => 60 * m + 20 * i + 69) where
  H_D_HOLDF i _ m := by
    rw [XA_eq]
    show 20 * ((2 * (3 * m + i) + 1) / 2) + 39 + 10 * ((2 * (3 * m + i) + 1) % 2) ≤ _
    omega

/-- **Non-vacuity of `muxn3_data_hold_fall`.** -/
theorem witness : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k + 1) + 2 →
    zW t = xvW (k % 3) (idx (run.κ (k % 3)) k) :=
  muxn3_data_hold_fall zW_gate ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => Nat.le_refl _⟩ enum
    env.H_RANGE causal static (Nat.le_refl 1) data_env hold_fall data_static

set_option maxRecDepth 100000 in
/-- Not degenerate: token 0 (input 0, bit 1) is still delivered at 48 =
`ζ 1 + 2` (z_ack fell at 46; the old window ended at `ζ 0 + 2 = 38`), while
input 1 carries 0. -/
theorem witness_values : run.ζ 0 = 36 ∧ run.ζ 1 = 46 ∧ zW 48 = true ∧ dW 1 47 = false := by
  refine ⟨rfl, rfl, by decide, by decide⟩

end Mn3HoldWit

end Formal.Cells.OpsHold
