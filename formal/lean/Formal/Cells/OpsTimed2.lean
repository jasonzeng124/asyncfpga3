import Formal.Cells.OpsTimedWit
import Formal.Cells.ConstraintsMux
open Formal.Core.LutList

/-!
# Shard B Phase 2, probe Lt2 (part 1): the mux's DATA path, timed

Probe Lt (`OpsTimed`, `OpsTimedMux`, `OpsTimedWit`) proved the control half
of `bd_mux`: one server transaction per control token, the right client
acknowledged. This file proves the value half:

> for every control token `k`, from the moment `z_req` rises at the server
> (less a consumer margin `Mz`) until the server raises `z_ack` (plus a hold
> margin), every bit of `z_data` equals the corresponding bit of the token
> the control selected: `x`'s `idx κ0 k`-th token if `sv k = 0`, `y`'s
> `idx κ1 k`-th if `sv k = 1`.

Gate model of `bd_datamux` (`cells/rtl/bd_latch.v`): the REAL INITs `8'hE4`
(odd bit) and `64'hFFAA_5500_E4E4_E4E4` (pair; O5 bit i, O6 bit i+1) through
Bundling's window relation (`Gate`, Kleene closure, H_KLEENE_LUT): each pin
is `(driving net, lo, hi)` where `[lo, hi]` covers the routed wire, the site
pin and the LUT arc. `ConstraintsMux.dm_odd_rel` / `dm_pair_o5_rel` /
`dm_pair_o6_rel` turn each output bit's `Gate` into `DmRel` (the Kleene mux
`s ? b : a` over the windows); the theorem here is stated on `DmRel`, so it
covers all three LUT shapes, one bit at a time (bits are independent: the
other bit of a pair never reaches an output, by the `*_kleene` lemmas).

The control-side event times are probe Lt's (`MuxRun`: `γ` ctl_req, `ξ`, `η`
the clients' requests, `ζ` the server's z_ack, `E` the selected join's node
edges, `Z` z_req at the server, `XA`, `YA` the acknowledges at the clients),
so the theorem composes with `mux_ok` / `mux_ok_static` (`mux_value_ok_static`).

Sender contracts (named, `MuxDataEnv`): each sender holds its data (the
control sender: `s`) from at least `L*` before its request rises at its port
(H_*_LEAD, the upstream's own bundling) until it has SEEN its acknowledge
rise (H_*_HOLD, the early four-phase data protocol: ctl_ack = z_ack through
the control sender's wire `Wzc`; x_ack, y_ack at the clients' pins).

Obligations (`MuxDataStatic`, all per-arc EndpointOK forms):
* **S_Z_S0 / S_Z_S1** (`bd_mux.bundled_z_s`): `s` through the udat select
  pin (`shi`) plus `Mz` no later than ctl_req through its wire to the
  selected join, the join, the join→uor wire, uor and the delay line (+ the
  sender's lead `Ls`).
* **S_Z_X / S_Z_Y** (`bd_mux.bundled_z_x/y`): the client's data through the
  udat data pin (`ahi`/`bhi`) plus `Mz` no later than the client's request
  through its wire, the join, uor and the delay line (+ lead `Lx`/`Ly`).
* The HOLD side needs no inequality: the senders hold until they see their
  acknowledge, which is after the server's z_ack rise (`mux_data_ok`'s hold
  margin `holdM` is a sum of MIN delays).
-/

namespace Formal.Cells.OpsTimed
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.Bundling (StableOn Gate Transport transport_gate)
open Formal.Cells.ConstraintsMux (DmRel dm_settles DM_ODD dm_odd_rel)

/-! ## 1. Event-time lemmas for the mux (lower bounds along the request path) -/

section muxev
variable {P : MuxRun}

/-- z_req at the server follows the selected join's node edge by at least
`wo + Lor.lo + Dz.lo`. -/
theorem mux_E_le_Z {wo : Nat} (hWO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo) (j : Nat) (hE : 1 ≤ P.E j) :
    P.E j + (wo + P.Lor.lo + P.Dz.lo) ≤ P.Z j := by
  unfold MuxRun.Z orEdges MuxRun.O0 MuxRun.O1
  split
  · have a := fl P.W0o hE
    have b := fl P.Lor (c := P.W0o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W0o.fst (P.E j))) (by omega)
    omega
  · have a := fl P.W1o hE
    have b := fl P.Lor (c := P.W1o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W1o.fst (P.E j))) (by omega)
    omega

/-- A control token selecting x: its join edge follows x's request (of the
consumed x token) through the x wire and the join. -/
theorem mux_xreq_le_E (hξ : ∀ j, 1 ≤ P.ξ j) (k : Nat) (hk : P.sv k = false) :
    P.ξ (2 * idx P.κ0 k) + P.Wx.lo + P.Lj0.lo ≤ P.E (2 * k) := by
  have hE : P.E (2 * k) = P.τ0 (2 * idx P.κ0 k) := by
    unfold MuxRun.E
    rw [show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega, hk]
    simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
  rw [hE]; unfold MuxRun.τ0 MuxRun.c0 MuxRun.Xp
  have a0 := hξ (2 * idx P.κ0 k)
  have a := fl P.Wx (hξ (2 * idx P.κ0 k))
  have b := fl P.Lj0 (c := max (P.Wx.fst (P.ξ (2 * idx P.κ0 k))) (P.D0 (2 * idx P.κ0 k)))
    (by omega)
  omega

theorem mux_yreq_le_E (hη : ∀ j, 1 ≤ P.η j) (k : Nat) (hk : P.sv k = true) :
    P.η (2 * idx P.κ1 k) + P.Wy.lo + P.Lj1.lo ≤ P.E (2 * k) := by
  have hE : P.E (2 * k) = P.τ1 (2 * idx P.κ1 k) := by
    unfold MuxRun.E
    rw [show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega, hk]
    simp only [ite_true, Nat.add_zero]
  rw [hE]; unfold MuxRun.τ1 MuxRun.c1 MuxRun.Yp
  have a0 := hη (2 * idx P.κ1 k)
  have a := fl P.Wy (hη (2 * idx P.κ1 k))
  have b := fl P.Lj1 (c := max (P.Wy.fst (P.η (2 * idx P.κ1 k))) (P.D1 (2 * idx P.κ1 k)))
    (by omega)
  omega

/-- x's acknowledge at its pin follows the server's z_ack edge by at least
`Wzx.lo + Lxa.lo + Wxa.lo` (and y's likewise). -/
theorem mux_ζ_le_XA (j : Nat) (hζ : 1 ≤ P.ζ j) :
    P.ζ j + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo) ≤ P.XA j := by
  unfold MuxRun.XA MuxRun.cx MuxRun.ZA0
  have a := fl P.Wzx hζ
  have b := fl P.Lxa (c := max (P.A0 j) (P.Wzx.fst (P.ζ j))) (by omega)
  have c := fl P.Wxa (c := P.Lxa.fst (max (P.A0 j) (P.Wzx.fst (P.ζ j)))) (by omega)
  omega

theorem mux_ζ_le_YA (j : Nat) (hζ : 1 ≤ P.ζ j) :
    P.ζ j + (P.Wzy.lo + P.Lya.lo + P.Wya.lo) ≤ P.YA j := by
  unfold MuxRun.YA MuxRun.cy MuxRun.ZA1
  have a := fl P.Wzy hζ
  have b := fl P.Lya (c := max (P.A1 j) (P.Wzy.fst (P.ζ j))) (by omega)
  have c := fl P.Wya (c := P.Lya.fst (max (P.A1 j) (P.Wzy.fst (P.ζ j)))) (by omega)
  omega

end muxev

/-! ## 2. The mux's data contracts, static obligations and theorem -/

/-- **The data contracts of the mux's three senders** (one data bit: `a` is
x_data's bit at x's driver, `b` y_data's, `s` the select at the control
sender's driver; bd_mux wires `udat (.a(x_data), .b(y_data), .s(s))`). -/
structure MuxDataEnv (P : MuxRun) (Wzc : Ret) (s a b : Trace) (sS sE xS xE yS yE : Nat → Nat)
    (xv yv : Nat → Bool) (Ls Lx Ly : Nat) : Prop where
  /-- **H_S_DATA**: the control sender drives `s = sv k` on `[sS k, sE k]`. -/
  H_S_DATA : ∀ k, StableOn s (P.sv k) (sS k) (sE k)
  /-- **H_X_DATA / H_Y_DATA**: x drives its `m`-th token's bit `xv m` on
  `[xS m, xE m]` (y likewise). -/
  H_X_DATA : ∀ m, StableOn a (xv m) (xS m) (xE m)
  H_Y_DATA : ∀ m, StableOn b (yv m) (yS m) (yE m)
  /-- **H_*_LEAD** (the upstream's own bundling, an environment fact): each
  sender's data is settled at its driver at least `L*` before its request
  rises at its port (`L* = 0`: no later than the request). -/
  H_S_LEAD : ∀ k, sS k + Ls ≤ P.γ (2 * k)
  H_X_LEAD : ∀ m, xS m + Lx ≤ P.ξ (2 * m)
  H_Y_LEAD : ∀ m, yS m + Ly ≤ P.η (2 * m)
  /-- **H_*_HOLD** (early four-phase data protocol, causal): each sender keeps
  its data until it has seen its acknowledge rise (the control sender sees
  ctl_ack = z_ack through its wire `Wzc`; x and y see x_ack / y_ack at their
  pins; the x token `m` is consumed by control token `κ0 m`). Testable on GLS
  as "data changes only after the ack rise at the sender's pin". -/
  H_S_HOLD : ∀ k, Wzc.fst (P.ζ (2 * k)) ≤ sE k
  H_X_HOLD : ∀ m, P.XA (2 * P.κ0 m) ≤ xE m
  H_Y_HOLD : ∀ m, P.YA (2 * P.κ1 m) ≤ yE m
  /-- Edges are after time 0 (truncated-subtraction corner only). -/
  H_POS : ∀ j, 1 ≤ P.γ j ∧ 1 ≤ P.ξ j ∧ 1 ≤ P.η j ∧ 1 ≤ P.ζ j

/-- **The mux's bundled-data obligations, per arc** (EndpointOK forms; `shi`,
`ahi`, `bhi` are the udat pins' upper windows: wire + site pin + LUT arc;
`Mz` the consumer's margin, 0 if the consumer only needs data at the server
pin when z_req arrives there). -/
structure MuxDataStatic (P : MuxRun) (wo shi ahi bhi Mz Ls Lx Ly : Nat) : Prop where
  H_WO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo
  /-- **S_Z_S0** (`bd_mux.bundled_z_s`, x selected): launch = `s` settled at
  its driver. -/
  S_Z_S0 : shi + Mz ≤ Ls + P.Wc0.lo + P.Lj0.lo + wo + P.Lor.lo + P.Dz.lo
  /-- **S_Z_S1** (`bd_mux.bundled_z_s`, y selected). -/
  S_Z_S1 : shi + Mz ≤ Ls + P.Wc1.lo + P.Lj1.lo + wo + P.Lor.lo + P.Dz.lo
  /-- **S_Z_X** (`bd_mux.bundled_z_x`): launch = x_data settled at x's driver. -/
  S_Z_X : ahi + Mz ≤ Lx + P.Wx.lo + P.Lj0.lo + wo + P.Lor.lo + P.Dz.lo
  /-- **S_Z_Y** (`bd_mux.bundled_z_y`). -/
  S_Z_Y : bhi + Mz ≤ Ly + P.Wy.lo + P.Lj1.lo + wo + P.Lor.lo + P.Dz.lo

namespace MuxRun
variable (P : MuxRun)
/-- The value control token `k` must deliver. -/
def zv (xv yv : Nat → Bool) (k : Nat) : Bool :=
  if P.sv k then yv (idx P.κ1 k) else xv (idx P.κ0 k)
/-- The hold margin after the server's z_ack rise (MIN delays only). -/
def holdM (Wzc : Ret) (slo alo blo : Nat) (k : Nat) : Nat :=
  min (Wzc.lo + slo)
    (if P.sv k then P.Wzy.lo + P.Lya.lo + P.Wya.lo + blo else P.Wzx.lo + P.Lxa.lo + P.Wxa.lo + alo)
end MuxRun

/-- **`mux_data_ok`: the mux delivers the selected token's value.** For every
control token `k`, `z` (one output bit of `bd_datamux`) equals the selected
input's bit for that token at every instant from `Mz` before z_req's rise
reaches the server until `holdM k` after the server raises z_ack. Uses the
datamux's REAL INIT through `DmRel`, the senders' contracts and the per-arc
setup obligations; the hold side needs none. -/
theorem mux_data_ok {P : MuxRun} {Wzc : Ret} {s a b z : Trace}
    {slo shi alo ahi blo bhi wo Mz Ls Lx Ly : Nat} {sS sE xS xE yS yE : Nat → Nat}
    {xv yv : Nat → Bool}
    (hR : DmRel s a b z slo shi alo ahi blo bhi) (hsw : slo ≤ shi) (haw : alo ≤ ahi) (hbw : blo ≤ bhi)
    (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (D : MuxDataEnv P Wzc s a b sS sE xS xE yS yE xv yv Ls Lx Ly)
    (S : MuxDataStatic P wo shi ahi bhi Mz Ls Lx Ly) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k) + P.holdM Wzc slo alo blo k →
      z t = P.zv xv yv k := by
  intro k t h1 h2
  have hγ : ∀ j, 1 ≤ P.γ j := fun j => (D.H_POS j).1
  have hζ := (D.H_POS (2 * k)).2.2.2
  have hCE := C_le_E hE0 hE1 hγ (2 * k)
  rw [show 2 * k / 2 = k by omega] at hCE
  have hsE : P.ζ (2 * k) + Wzc.lo ≤ sE k := by have := fl Wzc hζ; have := D.H_S_HOLD k; omega
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
    have hXA := mux_ζ_le_XA (2 * k) hζ
    have hxH := D.H_X_HOLD (idx P.κ0 k)
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
    have hYA := mux_ζ_le_YA (2 * k) hζ
    have hyH := D.H_Y_HOLD (idx P.κ1 k)
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

/-- **`mux_value_ok_static`**: the whole mux contract, control AND value, from
port-level causal partners, the control-side per-arc obligations
(`MuxStatic`), reset sequencing, the senders' data contracts and the
data-side per-arc obligations (`MuxDataStatic`): one server transaction per
control token, the right client acknowledged once, and the value on `z`
during that transaction the selected token's. -/
theorem mux_value_ok_static {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo R : Nat}
    {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak
      s a b z : Trace}
    {slo shi alo ahi blo bhi wo' Mz Ls Lx Ly : Nat} {sS sE xS xE yS yE : Nat → Nat}
    {xv yv : Nat → Bool}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (hRL : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
      P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
      P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
      P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
      R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0)
    (hR : DmRel s a b z slo shi alo ahi blo bhi) (hsw : slo ≤ shi) (haw : alo ≤ ahi) (hbw : blo ≤ bhi)
    (D : MuxDataEnv P Wzc s a b sS sE xS xE yS yE xv yv Ls Lx Ly)
    (SD : MuxDataStatic P wo' shi ahi bhi Mz Ls Lx Ly) :
    (Tok P.Tz zr P.Z (fun _ => true) ∧
      Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Tx xak (rx P.XA P.κ0) (fun _ => true) ∧
      Tok P.Ty yak P.YA P.sv ∧ Tok P.Ty yak (rx P.YA P.κ1) (fun _ => true)) ∧
    (∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k) + P.holdM Wzc slo alo blo k →
      z t = P.zv xv yv k) :=
  ⟨mux_ok_static G V Cs S hRL hRE, mux_data_ok hR hsw haw hbw V.H_ENUM0 V.H_ENUM1 D SD⟩

/-! ## 3. Non-vacuity of the mux data theorem (Probe Lt's unit-delay mux run)

`MuxWit.run`: control tokens alternate x, y, x, y; the select `sx` is the
control sender's driver; x's `m`-th token carries bit `m` even, y's `m` odd,
so in every transaction the two inputs carry DIFFERENT values (a datamux
that ignored `s` would fail). `zW` is one `bd_datamux` odd bit (REAL INIT
`8'hE4`) with unit transport delay on every pin, which satisfies the window
relation by `Bundling.transport_gate`. -/
namespace MuxWit

def xvW (m : Nat) : Bool := decide (m % 2 = 0)
def yvW (m : Nat) : Bool := decide (m % 2 = 1)
def xd (t : Nat) : Bool := xvW (t / 36)
def yd (t : Nat) : Bool := yvW ((t - 18) / 36)
def zW (t : Nat) : Bool := lutB DM_ODD [sx (t - 1), xd (t - 1), yd (t - 1)]

theorem zW_rel : DmRel sx xd yd zW 1 1 1 1 1 1 :=
  dm_odd_rel (transport_gate DM_ODD [(sx, 1, 1, 1), (xd, 1, 1, 1), (yd, 1, 1, 1)] zW
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MuxDataEnv run uW sx xd yd (fun k => 18 * k + 4) (fun k => 18 * k + 21)
    (fun m => 36 * m) (fun m => 36 * m + 35) (fun m => 36 * m + 18) (fun m => 36 * m + 53)
    xvW yvW 4 4 4 where
  H_S_DATA k t h1 h2 := by
    show svW ((t - 4) / 18) = svW k; rw [show (t - 4) / 18 = k by omega]
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

theorem data_static : MuxDataStatic run 1 1 1 1 0 4 4 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Non-vacuity of `mux_value_ok_static`**: the unit-delay run satisfies
every hypothesis, control and data. -/
theorem value_witness :
    (Tok run.Tz zr run.Z (fun _ => true) ∧
      Tok run.Tx xak run.XA (fun k => !run.sv k) ∧ Tok run.Tx xak (rx run.XA run.κ0) (fun _ => true) ∧
      Tok run.Ty yak run.YA run.sv ∧ Tok run.Ty yak (rx run.YA run.κ1) (fun _ => true)) ∧
    (∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + run.holdM uW 1 1 1 k →
      zW t = run.zv xvW yvW k) :=
  mux_value_ok_static gates env causal static (by decide) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Xp_eq]; omega
    · rw [D0_eq]; omega
    · rw [Yp_eq]; omega
    · rw [D1_eq]; omega
    · rw [A0_eq, E_eq]; omega
    · rw [(ZA_eq 0).1]; omega
    · rw [A1_eq, E_eq]; omega
    · rw [(ZA_eq 0).2]; omega)
    zW_rel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) data_env data_static

/-- Not degenerate: in tokens 0..3 (x, y, x, y) the delivered bit is
`1, 0, 0, 1`, and in tokens 0, 1 and 3 the unselected input carries the
opposite bit at that instant. -/
theorem value_witness_values :
    zW 14 = true ∧ yd 13 = false ∧ zW 32 = false ∧ xd 31 = true ∧
    zW 50 = false ∧ zW 68 = true ∧ xd 67 = false ∧
    run.Z 0 = 13 ∧ run.Z 2 = 31 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    ?_, ?_⟩
  · rw [Z_eq, E_eq]
  · rw [Z_eq, E_eq]

end MuxWit

/-! ## 4. The merge's data path: `usel` and `bd_datamux`

`cells/rtl/bd_merge.v`: `usel = LUT2 4'hE (x_req, x_ack)` (`sel = x_req |
x_ack`), `udat = bd_datamux (.a(y_data), .b(x_data), .s(sel))`, so
`z = sel ? x : y`. Gate model: both through Bundling's window relation
(`Gate`, REAL INITs). `usel`'s pins read the x client's request net `x` (at
its driver) with window `[lr, hr]` and the uxa output net `xa` with window
`[lq, hq]`; udat's select pin reads the usel output with `[sl, sh]`, its
data pins x_data `[xl, xh]` and y_data `[yl, yh]`.

* In an x token, `sel` is held high by `x_req` alone through the whole
  transaction (the early protocol needs no x_ack term); obligation
  **S_ZM_SEL_X** is exactly the JSON's `bd_merge.bundled_z` form (launch x_req
  rise: usel + datamux select vs x_req→uor + uor + delay line).
* In a y token, `sel` must be LOW: both `x_req` and `x_ack` low long enough
  before z_req reaches the server. `x_req` is low since the previous token's
  request fall (**S_SEL_XR**); `x_ack` (the uxa node) falls only after the
  previous token's z_ack fall crossed uxa (**S_SEL_XA_Z**) or its request
  fall did (**S_SEL_XA_R**). These two are the timed form of the JSON's
  `bd_merge.isochronic_forks` x_ack branch ("x_ack -> {usel, client}, broad
  window"): the fork is not isochronic; what is needed is that x_ack's fall
  reaches usel and the datamux select before the NEXT owner's request
  reaches the server.
-/

open Formal.Cells.LibCtlMergeMux (c2B c2_spec)
open Formal.Cells.Bundling (win_of_stable)
open Formal.Cells.ConstraintsMux (usel_kleene usel_high)

/-- `usel` low with separate start times per pin. -/
theorem usel_low2 {xr xa sel : Trace} {lo hi lo' hi' : Nat}
    (hg : Gate 0xE [(xr, lo, hi), (xa, lo', hi')] sel) (hw : lo ≤ hi) (hw' : lo' ≤ hi')
    (T1 T2 T' : Nat) (hx : StableOn xr false T1 T') (ha : StableOn xa false T2 T') :
    StableOn sel false (max (T1 + hi) (T2 + hi')) (T' + min lo lo') := by
  intro t h1 h2
  apply hg t false
  show lutK 0xE [Bundling.winK xr lo hi t, Bundling.winK xa lo' hi' t] = _
  rw [win_of_stable hw hx (by omega) (by omega), win_of_stable hw' ha (by omega) (by omega),
    usel_kleene]; rfl

section mergeev
variable {P : MergeRun} {Eo Es wo wz la wa : Nat}

theorem merge_RZ (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa) (j : Nat) :
    P.ρ j + (wo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
  have hWO := S.H_WO
  have hs := Cs.H_SRV j; have hp := Cs.H_POS j
  unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO at hs
  split at hs
  · have a := fl P.Wxo hp
    have b := fl P.Lor (c := P.Wxo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wxo.fst (P.ρ j))) (by omega)
    omega
  · have a := fl P.Wyo hp
    have b := fl P.Lor (c := P.Wyo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wyo.fst (P.ρ j))) (by omega)
    omega

theorem merge_ζ_le_XA (j : Nat) (hz : 1 ≤ P.ζ j) :
    P.ζ j + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo) ≤ P.XA j := by
  unfold MergeRun.XA MergeRun.cx MergeRun.ZA0
  have a := fl P.Wzx hz
  have b := fl P.Lxa (c := max (P.AX j) (P.Wzx.fst (P.ζ j))) (by omega)
  have c := fl P.Wxa (c := P.Lxa.fst (max (P.AX j) (P.Wzx.fst (P.ζ j)))) (by omega)
  omega

theorem merge_ζ_le_YA (j : Nat) (hz : 1 ≤ P.ζ j) :
    P.ζ j + (P.Wzy.lo + P.Lya.lo + P.Wya.lo) ≤ P.YA j := by
  unfold MergeRun.YA MergeRun.cy MergeRun.ZA1
  have a := fl P.Wzy hz
  have b := fl P.Lya (c := max (P.AY j) (P.Wzy.fst (P.ζ j))) (by omega)
  have c := fl P.Wya (c := P.Lya.fst (max (P.AY j) (P.Wzy.fst (P.ζ j)))) (by omega)
  omega

theorem merge_ZR (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa) (j : Nat) :
    P.ζ j + (wz + la + wa + Eo) ≤ P.ρ (j + 1) := by
  have hWZ := S.H_WZ; have hLA := S.H_LA; have hWA := S.H_WA
  have ho := Cs.H_OWN j
  have hz : 1 ≤ P.ζ j := by have := merge_RZ Cs S j; have := Cs.H_POS j; omega
  split at ho
  · have := merge_ζ_le_YA j hz; omega
  · have := merge_ζ_le_XA j hz; omega

theorem merge_ρ_mono (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa) :
    ∀ a b, a ≤ b → P.ρ a ≤ P.ρ b := by
  have step : ∀ j, P.ρ j ≤ P.ρ (j + 1) := fun j => by
    have := merge_RZ Cs S j; have := merge_ZR Cs S j; omega
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    by_cases h' : a ≤ b
    · have := ih h'; have := step b; omega
    · have : a = b + 1 := by omega
      subst this; omega

/-- z_req at the server follows the owner's request edge. -/
theorem merge_ρ_le_Z (hp : ∀ j, 1 ≤ P.ρ j) (k : Nat) :
    (P.sv k = false → P.ρ (2 * k) + (P.Wxo.lo + P.Lor.lo + P.Dz.lo) ≤ P.Z (2 * k)) ∧
    (P.sv k = true → P.ρ (2 * k) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) ≤ P.Z (2 * k)) := by
  have h1 := hp (2 * k)
  unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO
  rw [show 2 * k / 2 = k by omega]
  constructor
  · intro hk; simp only [hk, Bool.not_false, ite_true]
    have a := fl P.Wxo h1
    have b := fl P.Lor (c := P.Wxo.fst (P.ρ (2 * k))) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wxo.fst (P.ρ (2 * k)))) (by omega)
    omega
  · intro hk; simp only [hk, Bool.not_true, Bool.false_eq_true, ite_false]
    have a := fl P.Wyo h1
    have b := fl P.Lor (c := P.Wyo.fst (P.ρ (2 * k))) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wyo.fst (P.ρ (2 * k)))) (by omega)
    omega

end mergeev

/-- **The data contracts of the merge's two clients** (one bit, indexed by
the MERGED token `k`, owner `sv k`): x drives `xv k` on `[xS k, xE k]` for
its tokens, from `Lx` before its request rise (H_X_LEAD) until it has seen
x_ack rise (H_X_HOLD, early protocol); y likewise. -/
structure MergeDataEnv (P : MergeRun) (xd yd : Trace) (xS xE yS yE : Nat → Nat)
    (xv yv : Nat → Bool) (Lx Ly : Nat) : Prop where
  H_X_DATA : ∀ k, P.sv k = false → StableOn xd (xv k) (xS k) (xE k)
  H_Y_DATA : ∀ k, P.sv k = true → StableOn yd (yv k) (yS k) (yE k)
  H_X_LEAD : ∀ k, P.sv k = false → xS k + Lx ≤ P.ρ (2 * k)
  H_Y_LEAD : ∀ k, P.sv k = true → yS k + Ly ≤ P.ρ (2 * k)
  H_X_HOLD : ∀ k, P.sv k = false → P.XA (2 * k) ≤ xE k
  H_Y_HOLD : ∀ k, P.sv k = true → P.YA (2 * k) ≤ yE k

/-- **The merge's data-path obligations, per arc.** Windows: `[lr, hr]`
usel.I0 (x_req), `[lq, hq]` usel.I1 (x_ack), `[sl, sh]` udat select (from
usel's output), `[xl, xh]` / `[yl, yh]` udat data pins; `Mz`, `Hm` the
consumer's setup and hold margins around `[z_req at the server, z_ack]`. -/
structure MergeDataStatic (P : MergeRun) (Eo Es wo wz la wa lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly : Nat) :
    Prop where
  /-- **S_ZM_SEL_X** = `bd_merge.bundled_z` (launch x_req rise). -/
  S_ZM_SEL_X : hr + sh + Mz ≤ P.Wxo.lo + P.Lor.lo + P.Dz.lo
  /-- **S_ZM_X / S_ZM_Y** (`bd_merge.bundled_z_data`): launch = data settled at the client. -/
  S_ZM_X : xh + Mz ≤ Lx + P.Wxo.lo + P.Lor.lo + P.Dz.lo
  S_ZM_Y : yh + Mz ≤ Ly + P.Wyo.lo + P.Lor.lo + P.Dz.lo
  /-- **S_SEL_XR** (`bd_merge.sel_low_xreq`): launch = previous token's request fall. -/
  S_SEL_XR : hr + sh + Mz ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) +
    (P.Wyo.lo + P.Lor.lo + P.Dz.lo)
  /-- **S_SEL_XA_Z** (`bd_merge.sel_low_xack`, z_ack form): launch = the
  previous token's z_ack fall at the server; data path z_ack→uxa, uxa,
  x_ack→usel (+site pin+arc), udat select; request path through the
  owner's ack C-element and client, the next owner's request, uor, delay. -/
  S_SEL_XA_Z : P.Wzx.hi + P.Lxa.hi + hq + sh + Mz ≤ (wz + la + wa + Eo) +
    (P.Wyo.lo + P.Lor.lo + P.Dz.lo)
  /-- **S_SEL_XA_R** (`bd_merge.sel_low_xack`, request form): launch = the
  previous token's request fall. -/
  S_SEL_XA_R : P.Wxc.hi + P.Lxa.hi + hq + sh + Mz ≤ (wo + P.Lor.lo + P.Dz.lo + Es) +
    (wz + la + wa + Eo) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo)
  /-- **S_HM_SEL_X / Y, S_HM_X / Y** (hold margins: `Hm` after z_ack rise;
  pure lower bounds). -/
  S_HM_SEL_X : Hm + 1 ≤ P.Wzx.lo + P.Lxa.lo + P.Wxa.lo + Eo + lr + sl
  S_HM_SEL_Y : Hm + 1 ≤ P.Wzy.lo + P.Lya.lo + P.Wya.lo + Eo + min lr lq + sl
  S_HM_X : Hm ≤ P.Wzx.lo + P.Lxa.lo + P.Wxa.lo + xl
  S_HM_Y : Hm ≤ P.Wzy.lo + P.Lya.lo + P.Wya.lo + yl
  /-- **H_SEL_START** (start-up): the first token's window starts after
  uxa's output is defined and usel has read x_req's reset level. -/
  H_SEL_START : max hr (P.Lxa.hi + hq) + sh + Mz ≤ P.ρ 0 + (P.Wyo.lo + P.Lor.lo + P.Dz.lo)

/-- **`merge_data_ok`: the merge delivers its requester's value.** For every
merged token `k`, `z` (one output bit) equals the owner's bit for that token
from `Mz` before z_req's rise reaches the server until `Hm` after the server
raises z_ack. Uses `usel`'s and the datamux's REAL INITs through the window
relation, the control-side theorem's own environment (`merge_ok`'s, with the
uxa node's token trace), the clients' data contracts and `MergeDataStatic`. -/
theorem merge_data_ok {P : MergeRun} {R Eo Es wo wz la wa : Nat}
    {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak sel xd yd z : Trace}
    {lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly : Nat} {xS xE yS yE : Nat → Nat} {xv yv : Nat → Bool}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0)
    (hU : Gate 0xE [(x, lr, hr), (xa, lq, hq)] sel) (hlr : lr ≤ hr) (hlq : lq ≤ hq)
    (hR : DmRel sel yd xd z sl sh yl yh xl xh) (hsw : sl ≤ sh) (hyw : yl ≤ yh) (hxw : xl ≤ xh)
    (D : MergeDataEnv P xd yd xS xE yS yE xv yv Lx Ly)
    (SD : MergeDataStatic P Eo Es wo wz la wa lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k) + Hm →
      z t = (if P.sv k then yv k else xv k) := by
  have TM := merge_timing_of_static Cs S hRL hRE
  obtain ⟨_, _, _, _, r5, _⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, _, _⟩ := TM.H_RST_EARLY
  -- the uxa node as a token trace (as in `merge_ok`)
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
  have hown := Cs.H_OWN (2 * k)
  rw [show 2 * k / 2 = k by omega] at hown
  have hZ := merge_ρ_le_Z hp k
  have hρ1 := hp (2 * k + 1)
  cases hk : P.sv k
  · -- x owns token k: sel high through x_req
    rw [hk] at hown; simp only [Bool.false_eq_true, ite_false] at hown
    have hXA := merge_ζ_le_XA (2 * k) hz
    have hZk := hZ.1 hk
    have hxr : StableOn x true (P.ρ (2 * k)) (P.ρ (2 * k + 1) - 1) := fun u u1 u2 => by
      have := V.H_X.hi k u (Nat.zero_le _) u1 (by omega); rw [this, hk]; rfl
    have hsel := usel_high hU hlr _ _ hxr
    have st := dm_settles hR hsw hyw hxw true (xv k) _ _ (xS k) (xE k) hsel (D.H_X_DATA k hk)
    have := D.H_X_LEAD k hk; have := D.H_X_HOLD k hk
    have := SD.S_ZM_SEL_X; have := SD.S_ZM_X; have := SD.S_HM_SEL_X; have := SD.S_HM_X
    simp only [ite_true] at st
    simp only [Bool.false_eq_true, ite_false]
    exact st t (by omega) (by omega)
  · -- y owns token k: sel low (x_req and x_ack both low)
    rw [hk] at hown; simp only [ite_true] at hown
    have hYA := merge_ζ_le_YA (2 * k) hz
    have hZk := hZ.2 hk
    -- x_ack's next rise is after x_req's next edge
    have hXN : P.ρ (2 * k + 1) ≤ P.Lxa.fst (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1))) := by
      have := P.Lxa.fst_ge (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1)))
      have : P.ρ (2 * k + 1) ≤ P.AX (2 * k + 1) := P.Wxc.fst_ge _
      omega
    have sl0 : Tok.SlotLow (fun k => !P.sv k) (2 * k) := Tok.slotLow_even (by simp [hk])
    have sl0' : Tok.SlotLow (fun k => !P.sv k && true) (2 * k) := Tok.slotLow_even (by simp [hk])
    have hS0 := SD.H_SEL_START
    have hmono := RM 0 (2 * k) (Nat.zero_le _)
    -- the low windows of x_req and x_ack, and the bound on their starts
    obtain ⟨T1, T2, hx0, ha0, hb1, hb2⟩ : ∃ T1 T2, StableOn x false T1 (P.ρ (2 * k + 1) - 1) ∧
        StableOn xa false T2 (P.ρ (2 * k + 1) - 1) ∧
        T1 + hr + sh + Mz ≤ P.ρ (2 * k) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) ∧
        T2 + hq + sh + Mz ≤ P.ρ (2 * k) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) := by
      cases k with
      | zero =>
        simp only [Nat.mul_zero, Nat.zero_add] at *
        refine ⟨0, P.Lxa.hi, fun u u1 u2 => ?_, fun u u1 u2 => ?_, by omega, by omega⟩
        · exact V.H_X.low_pre 1 u (fun j hj => by
            have : j = 0 := by omega
            subst this; exact sl0) (Nat.zero_le _) (by omega)
        · exact nx.low_pre 1 u (fun j hj => by
            have : j = 0 := by omega
            subst this; exact sl0') u1 (by omega)
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
            ∀ j, 2 * k' + 1 ≤ j → j < 2 * (k' + 1) + 1 → Tok.SlotLow g j := fun g hg j hj1 hj2 => by
          rcases (show j = 2 * k' + 1 ∨ j = 2 * (k' + 1) by omega) with r | r
          · subst r; exact Tok.slotLow_odd g k'
          · subst r; exact hg
        refine ⟨P.ρ (2 * k' + 1), max P.Lxa.hi (P.Lxa.fst (max (P.AX (2 * k' + 1)) (P.ZA0 (2 * k' + 1)))),
          fun u u1 u2 => ?_, fun u u1 u2 => ?_, ?_, ?_⟩
        · exact V.H_X.low_range (2 * (k' + 1) + 1) (2 * k' + 1) u (by omega) (slo _ sl0)
            (Nat.zero_le _) u1 (by omega)
        · exact nx.low_range (2 * (k' + 1) + 1) (2 * k' + 1) u (by omega) (slo _ sl0')
            (by omega) (by omega) (by omega)
        · have := SD.S_SEL_XR; omega
        · have := SD.S_SEL_XA_Z; have := SD.S_SEL_XA_R; omega
    have hsel := usel_low2 hU hlr hlq T1 T2 _ hx0 ha0
    have st := dm_settles hR hsw hyw hxw false (yv k) _ _ (yS k) (yE k) hsel (D.H_Y_DATA k hk)
    have := D.H_Y_LEAD k hk; have := D.H_Y_HOLD k hk
    have := SD.S_ZM_Y; have := SD.S_HM_SEL_Y; have := SD.S_HM_Y
    simp only [Bool.false_eq_true, ite_false] at st
    simp only [ite_true]
    exact st t (by omega) (by omega)

/-! ## 5. Non-vacuity of the merge data theorem (Probe Lt's unit-delay merge run)

`MergeWit.run`: merged tokens alternate x, y, x, y; `selW` is `usel` and
`zmW` one datamux odd bit, both REAL INITs with unit transport delay on
every pin. Each client changes its data every 16 ticks; in each of the
first four tokens the two inputs carry DIFFERENT bits, and the delivered
bits are `1, 1, 0, 0`. -/
namespace MergeWit

def xvW (k : Nat) : Bool := decide (k % 4 = 0 ∨ k % 4 = 3)
def yvW (k : Nat) : Bool := decide (k % 4 = 1 ∨ k % 4 = 2)
def xd (t : Nat) : Bool := xvW (t / 16)
def yd (t : Nat) : Bool := yvW (t / 16)
def selW (t : Nat) : Bool := lutB 0xE [x (t - 1), xa (t - 1)]
def zmW (t : Nat) : Bool := lutB DM_ODD [selW (t - 1), yd (t - 1), xd (t - 1)]

theorem selW_gate : Gate 0xE [(x, 1, 1), (xa, 1, 1)] selW :=
  transport_gate 0xE [(x, 1, 1, 1), (xa, 1, 1, 1)] selW
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl)

theorem zmW_rel : DmRel selW yd xd zmW 1 1 1 1 1 1 :=
  dm_odd_rel (transport_gate DM_ODD [(selW, 1, 1, 1), (yd, 1, 1, 1), (xd, 1, 1, 1)] zmW
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MergeDataEnv run xd yd (fun k => 16 * k) (fun k => 16 * k + 15)
    (fun k => 16 * k) (fun k => 16 * k + 15) xvW yvW 4 4 where
  H_X_DATA k _ t h1 h2 := by show xvW (t / 16) = xvW k; rw [show t / 16 = k by omega]
  H_Y_DATA k _ t h1 h2 := by show yvW (t / 16) = yvW k; rw [show t / 16 = k by omega]
  H_X_LEAD k _ := by show _ ≤ 8 * (2 * k) + 4; omega
  H_Y_LEAD k _ := by show _ ≤ 8 * (2 * k) + 4; omega
  H_X_HOLD k _ := by rw [(XA_eq _).1]; show _ ≤ 16 * k + 15; omega
  H_Y_HOLD k _ := by rw [(XA_eq _).2]; show _ ≤ 16 * k + 15; omega

theorem data_static : MergeDataStatic run 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 1 0 2 4 4 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Non-vacuity of `merge_data_ok`.** -/
theorem value_witness : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + 2 →
    zmW t = (if run.sv k then yvW k else xvW k) :=
  merge_data_ok gates env causal static (by decide) (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega)
    selW_gate (Nat.le_refl _) (Nat.le_refl _) zmW_rel (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)
    data_env data_static

/-- Not degenerate: tokens 0..3 (x, y, x, y) deliver `1, 1, 0, 0`; at each
instant the unselected input carries the opposite bit. -/
theorem value_witness_values :
    zmW 8 = true ∧ yd 7 = false ∧ zmW 24 = true ∧ xd 23 = false ∧
    zmW 40 = false ∧ yd 39 = true ∧ zmW 56 = false ∧ xd 55 = true ∧ run.Z 0 = 7 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, ?_⟩
  rw [Z_eq]

end MergeWit

/-! ## 6. `bd_steer`: causal partners and per-arc static obligations

Probe Lt left two of `SteerEnv`'s fields in event form (H_S_PIN,
H_ACK_SKEW). Here, as for the mux and the merge, they are DERIVED from
port-level causality of the partners (`SteerCausal`) and per-arc static
inequalities (`SteerStatic`); `steer_ok_static` is `steer_ok` under those.

The select `s` reaches `u.I1` through its own FIFO wire `Ws` from the
sender's driver. Sender contract: `s = sv k` on `[sS k, sE k)`, settled `Ls`
before the request rises (H_S_LEAD) and held `Hs` after it falls
(H_S_HOLD). The library's contract (bd_ctl.v: "holds it still from
req-rise until ack-fall") gives H_S_HOLD with `Hs` = a whole round trip
(`steer_hold_of_ackfall`). -/

section steerstatic
variable {P : SteerRun}

theorem steer_K_ge (Wm : Nat) (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (j : Nat) (hA : 1 ≤ P.A j) :
    P.A j + Wm + P.La.lo + P.Wk.lo ≤ P.K j := by
  unfold SteerRun.K SteerRun.au orEdges
  dsimp only
  split
  · have a := P.Wa0.fst_lo hA
    have b := P.La.fst_lo (c := P.Wa0.fst (P.A j)) (by omega)
    have c := P.Wk.fst_lo (c := P.La.fst (P.Wa0.fst (P.A j))) (by omega)
    omega
  · have a := P.Wa1.fst_lo hA
    have b := P.La.fst_lo (c := P.Wa1.fst (P.A j)) (by omega)
    have c := P.Wk.fst_lo (c := P.La.fst (P.Wa1.fst (P.A j))) (by omega)
    omega

theorem steer_R_ge (Lm : Nat) (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) (j : Nat)
    (hρ : 1 ≤ P.ρ j) : P.ρ j + P.Wq.lo + Lm ≤ P.Rsel j := by
  unfold SteerRun.Rsel SteerRun.R0 SteerRun.R1 SteerRun.qr
  have a := P.Wq.fst_lo hρ
  split
  · have b := P.L6.fst_lo (c := P.Wq.fst (P.ρ j)) (by omega)
    have c := P.W1.fst_lo (c := P.L6.fst (P.Wq.fst (P.ρ j))) (by omega)
    omega
  · have b := P.L5.fst_lo (c := P.Wq.fst (P.ρ j)) (by omega)
    have c := P.W0.fst_lo (c := P.L5.fst (P.Wq.fst (P.ρ j))) (by omega)
    omega

/-- **Port-level causality of the steer's partners** and the select's
sender contract. -/
structure SteerCausal (P : SteerRun) (sS sE : Nat → Nat) (Er Es Ls Hs : Nat) : Prop where
  /-- **H_RCV_CAUSAL**: the routed receiver answers `Er` after seeing its request edge. -/
  H_RCV : ∀ j, P.Rsel j + Er ≤ P.A j
  /-- **H_SND_CAUSAL**: the sender moves its request `Es` after seeing its acknowledge edge. -/
  H_SND : ∀ j, P.K j + Es ≤ P.ρ (j + 1)
  /-- **H_S_LEAD**: `s` settled at its driver `Ls` before the request rises at the sender. -/
  H_S_LEAD : ∀ k, sS k + Ls ≤ P.ρ (2 * k)
  /-- **H_S_HOLD**: `s` held at its driver at least `Hs` after the request falls. -/
  H_S_HOLD : ∀ k, P.ρ (2 * k + 1) + Hs ≤ sE k
  H_POS : ∀ j, 1 ≤ P.ρ j ∧ 1 ≤ P.A j

/-- **The steer's per-arc static obligations.** `Loop` = min delay from an
acknowledge edge at `uack` back to the next one through the sender. -/
structure SteerStatic (P : SteerRun) (Ws : Ret) (Er Es Lm Wm Ls Hs : Nat) : Prop where
  H_LM : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo
  H_WM : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo
  /-- **S_S_SETUP** (`bd_steer.bundled_s_setup`, lumped LUT arc): launch = `s`
  settled at its driver; `s` wire (hi) vs the sender's lead + req wire (lo). -/
  S_S_SETUP : Ws.hi ≤ Ls + P.Wq.lo
  /-- **S_S_HOLD** (`bd_steer.bundled_s_hold`): launch = req fall at the sender;
  req wire (hi) vs the sender's hold + `s` wire (lo). -/
  S_S_HOLD : P.Wq.hi ≤ Hs + Ws.lo
  /-- **S_ACK_SKEW** (`bd_steer.ack_or_skew`): uack's pin skew below one
  sender round trip. -/
  S_ACK : P.Wa0.hi ≤ (Wm + P.La.lo + P.Wk.lo + Es + P.Wq.lo + Lm + Er) + P.Wa1.lo ∧
    P.Wa1.hi ≤ (Wm + P.La.lo + P.Wk.lo + Es + P.Wq.lo + Lm + Er) + P.Wa0.lo

theorem steer_gap_causal {sS sE : Nat → Nat} {Er Es Ls Hs : Nat} (Cs : SteerCausal P sS sE Er Es Ls Hs)
    (Lm Wm : Nat) (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (j : Nat) :
    P.A j + (Wm + P.La.lo + P.Wk.lo + Es + P.Wq.lo + Lm + Er) ≤ P.A (j + 1) := by
  have := steer_K_ge Wm hWm j (Cs.H_POS j).2
  have := steer_R_ge Lm hLm (j + 1) (Cs.H_POS (j + 1)).1
  have := Cs.H_SND j; have := Cs.H_RCV (j + 1)
  omega

/-- The library's select contract (held until the sender sees ack fall)
implies H_S_HOLD with a whole round trip as `Hs`. -/
theorem steer_hold_of_ackfall {sE : Nat → Nat} {Er : Nat} (Lm Wm : Nat)
    (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo)
    (hRCV : ∀ j, P.Rsel j + Er ≤ P.A j) (hpos : ∀ j, 1 ≤ P.ρ j ∧ 1 ≤ P.A j)
    (hK : ∀ k, P.K (2 * k + 1) ≤ sE k) :
    ∀ k, P.ρ (2 * k + 1) + (P.Wq.lo + Lm + Er + Wm + P.La.lo + P.Wk.lo) ≤ sE k := by
  intro k
  have := steer_K_ge Wm hWm (2 * k + 1) (hpos _).2
  have := steer_R_ge Lm hLm (2 * k + 1) (hpos _).1
  have := hRCV (2 * k + 1); have := hK k
  omega

/-- **`SteerEnv` from causality and the static obligations.** -/
theorem steer_env_of_static {req su a0 a1 s : Trace} {Tr Ta Er Es Lm Wm Ls Hs : Nat}
    (Ws : Ret) (sS sE : Nat → Nat)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    (hs : ∀ k t, sS k ≤ t → t < sE k → s t = P.sv k)
    (hreq : Tok Tr req P.ρ (fun _ => true))
    (h0 : Tok Ta a0 P.A (fun k => !P.sv k)) (h1 : Tok Ta a1 P.A P.sv)
    (Cs : SteerCausal P sS sE Er Es Ls Hs) (S : SteerStatic P Ws Er Es Lm Wm Ls Hs) :
    SteerEnv P req su a0 a1 Tr Ta Er Es where
  H_REQ := hreq
  H_S_PIN := steer_s_pin_of_wire Ws sS sE hw hs (fun k => (Cs.H_POS (2 * k)).1)
    (fun k => by have := Cs.H_S_LEAD k; have := S.S_S_SETUP; omega)
    (fun k => by have := Cs.H_S_HOLD k; have := S.S_S_HOLD; omega)
  H_A0 := h0
  H_A1 := h1
  H_RCV := Cs.H_RCV
  H_SND := Cs.H_SND
  H_ACK_SKEW j := by
    have g := steer_gap_causal Cs Lm Wm S.H_LM S.H_WM j
    have hA := (Cs.H_POS (j + 1)).2
    have sk := S.S_ACK
    exact ⟨fst_order P.Wa0 P.Wa1 hA (by omega), fst_order P.Wa1 P.Wa0 hA (by omega)⟩

/-- **`steer_ok_static`**: `steer_ok` with every timing obligation given as a
per-arc static inequality under port-level causal partners. -/
theorem steer_ok_static {req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack s : Trace}
    {Tr Ta Er Es Lm Wm Ls Hs : Nat} (Ws : Ret) (sS sE : Nat → Nat)
    (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    (hs : ∀ k t, sS k ≤ t → t < sE k → s t = P.sv k)
    (hreq : Tok Tr req P.ρ (fun _ => true))
    (h0 : Tok Ta a0 P.A (fun k => !P.sv k)) (h1 : Tok Ta a1 P.A P.sv)
    (Cs : SteerCausal P sS sE Er Es Ls Hs) (S : SteerStatic P Ws Er Es Lm Wm Ls Hs) :
    Tok (P.T1 Tr) r0 P.R0 (fun k => !P.sv k) ∧ Tok (P.T1 Tr) r1 P.R1 P.sv ∧
    Tok (P.T2 Ta) ack P.K (fun _ => true) ∧
    (∀ j, P.ρ j ≤ P.Rsel j ∧ P.Rsel j + Er ≤ P.A j ∧ P.A j ≤ P.K j ∧ P.K j + Es ≤ P.ρ (j + 1)) :=
  steer_ok G (steer_env_of_static Ws sS sE hw hs hreq h0 h1 Cs S)

end steerstatic

namespace SteerWit

/-- The select at the sender's driver, one wire (`u`) before `u.I1`. -/
def sdrv (t : Nat) : Bool := sv ((t + 5) / 16)

theorem causal : SteerCausal run (fun k => 16 * k - 5) (fun k => 16 * k + 11) 1 1 1 2 where
  H_RCV j := by unfold SteerRun.Rsel; rw [R0_eq, R1_eq]; show _ ≤ 8 * j + 5; split <;> omega
  H_SND j := by rw [K_eq]; show _ ≤ 8 * (j + 1) + 1; omega
  H_S_LEAD k := by show _ ≤ 8 * (2 * k) + 1; omega
  H_S_HOLD k := by show 8 * (2 * k + 1) + 1 + 2 ≤ _; omega
  H_POS j := ⟨by show 1 ≤ 8 * j + 1; omega, by show 1 ≤ 8 * j + 5; omega⟩

theorem static : SteerStatic run u 1 1 2 1 1 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Non-vacuity of `steer_ok_static`** (causal partners, static
obligations by `decide`). -/
theorem static_witness :
    Tok (run.T1 0) r0 run.R0 (fun k => !run.sv k) ∧ Tok (run.T1 0) r1 run.R1 run.sv ∧
    Tok (run.T2 6) ack run.K (fun _ => true) ∧
    (∀ j, run.ρ j ≤ run.Rsel j ∧ run.Rsel j + 1 ≤ run.A j ∧ run.A j ≤ run.K j ∧
      run.K j + 1 ≤ run.ρ (j + 1)) :=
  steer_ok_static (s := sdrv) u (fun k => 16 * k - 5) (fun k => 16 * k + 11) gates
    (fun t ht => by
      show sv ((t + 4) / 16) = sv ((u.σ t + 5) / 16)
      have h1 : u.σ t = t - 1 := rfl
      rw [h1, show (t - 1 + 5) / 16 = (t + 4) / 16 by
        have : (1 : Nat) ≤ t := ht
        omega])
    (fun k t h1 h2 => by show sv ((t + 5) / 16) = sv k; rw [show (t + 5) / 16 = k by omega])
    req_tok a0_tok a1_tok causal static

end SteerWit

/-! ## 7. Non-empty pulses

`Tok` allows a slot of zero length (a FIFO channel may swallow a pulse
narrower than its spread). A slot `[e j, e (j+1))` is non-empty iff
`e j < e (j+1)`, and then the trace shows the slot's value at `e j`
(`Tok.at_edge`). So "exactly one NON-EMPTY pulse per token" is strict
monotonicity of the derived edge sequence. For signals whose both edges are
launched through the SAME path from one edge sequence (z_req at the server)
this follows from causality alone (`mux_Z_step`, `merge_Z_step`: each phase
lasts at least a whole round trip). For a C-element node fed by two
sequences (x_ack) it needs a pulse-width-vs-spread condition
(**S_XA_PW**: the spread of the path from the server's z_ack edge to the
client's pin is below one round trip; `mux_XA_step`, `merge_XA_step`). -/

theorem Tok.at_edge {T : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool} (h : Tok T x e g)
    (k : Nat) (hT : T ≤ e (2 * k)) (hlt : e (2 * k) < e (2 * k + 1)) :
    x (e (2 * k)) = g k ∧ ∃ t, e (2 * k) ≤ t ∧ t < e (2 * k + 1) ∧ x t = g k :=
  ⟨h.hi k _ hT (Nat.le_refl _) hlt, e (2 * k), Nat.le_refl _, hlt, h.hi k _ hT (Nat.le_refl _) hlt⟩

theorem Tok.at_gap {T : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool} (h : Tok T x e g)
    (k : Nat) (hT : T ≤ e (2 * k + 1)) (hlt : e (2 * k + 1) < e (2 * k + 2)) :
    x (e (2 * k + 1)) = false := h.lo k _ hT (Nat.le_refl _) hlt

theorem mono_of_step (f : Nat → Nat) (h : ∀ j, f j ≤ f (j + 1)) : ∀ a b, a ≤ b → f a ≤ f b := by
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    by_cases h' : a ≤ b
    · have := ih h'; have := h b; omega
    · have : a = b + 1 := by omega
      subst this; omega

section pulses
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}

/-- **z_req's phases at the server each last a whole round trip.** -/
theorem mux_Z_step (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo) (j : Nat) :
    P.Z j + (Es + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo)) ≤ P.Z (j + 1) := by
  have h1 := Cs.H_SRV j
  have h2 := ζ_le_E hE0 hE1 Cs S j
  have h3 := mux_E_le_Z S.H_WO (j + 1) (γ_le_E hE0 hE1 Cs.H_POS S (j + 1)).2
  omega

/-- **x_ack's phases at the client are non-empty** under **S_XA_PW** (the
spread of `z_ack → uxa → client` and of `j0 → uxa → client` below one round
trip). -/
theorem mux_XA_step (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (S_XA_PW : P.Wzx.hi + P.Lxa.hi + P.Wxa.hi <
        (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo) ∧
      P.W0x.hi + P.Lxa.hi + P.Wxa.hi <
        (Wzc.lo + Ec + wc + lj) + 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo))
    (j : Nat) : P.XA j < P.XA (j + 1) := by
  have EZ := E_le_ζ hE0 hE1 Cs S j
  have ZE := ζ_le_E hE0 hE1 Cs S j
  have EZ1 := E_le_ζ hE0 hE1 Cs S (j + 1)
  have hz1 : 1 ≤ P.ζ (j + 1) := by have := (γ_le_E hE0 hE1 Cs.H_POS S (j + 1)).2; omega
  have lo1 := mux_ζ_le_XA (j + 1) hz1
  have u1 := P.W0x.fst_le (P.E j); have u2 := P.Wzx.fst_le (P.ζ j)
  have u3 := P.Lxa.fst_le (P.cx j); have u4 := P.Wxa.fst_le (P.Lxa.fst (P.cx j))
  have := S_XA_PW
  have e1 : P.XA j = P.Wxa.fst (P.Lxa.fst (P.cx j)) := rfl
  have e2 : P.cx j = max (P.A0 j) (P.ZA0 j) := rfl
  have e3 : P.A0 j = P.W0x.fst (P.E j) := rfl
  have e4 : P.ZA0 j = P.Wzx.fst (P.ζ j) := rfl
  omega

theorem mux_YA_step (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (S_YA_PW : P.Wzy.hi + P.Lya.hi + P.Wya.hi <
        (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzy.lo + P.Lya.lo + P.Wya.lo) ∧
      P.W1y.hi + P.Lya.hi + P.Wya.hi <
        (Wzc.lo + Ec + wc + lj) + 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzy.lo + P.Lya.lo + P.Wya.lo))
    (j : Nat) : P.YA j < P.YA (j + 1) := by
  have EZ := E_le_ζ hE0 hE1 Cs S j
  have ZE := ζ_le_E hE0 hE1 Cs S j
  have EZ1 := E_le_ζ hE0 hE1 Cs S (j + 1)
  have hz1 : 1 ≤ P.ζ (j + 1) := by have := (γ_le_E hE0 hE1 Cs.H_POS S (j + 1)).2; omega
  have lo1 := mux_ζ_le_YA (j + 1) hz1
  have u1 := P.W1y.fst_le (P.E j); have u2 := P.Wzy.fst_le (P.ζ j)
  have u3 := P.Lya.fst_le (P.cy j); have u4 := P.Wya.fst_le (P.Lya.fst (P.cy j))
  have := S_YA_PW
  have e1 : P.YA j = P.Wya.fst (P.Lya.fst (P.cy j)) := rfl
  have e2 : P.cy j = max (P.A1 j) (P.ZA1 j) := rfl
  have e3 : P.A1 j = P.W1y.fst (P.E j) := rfl
  have e4 : P.ZA1 j = P.Wzy.fst (P.ζ j) := rfl
  omega

/-- **`mux_pulses`: one NON-EMPTY pulse per token.** With a server that takes
at least one tick (`1 ≤ Es`) and the start-up condition that the first edges
come after the cell's traces are clean (`H_START`), z_req at the server is
high at the start of every token's high slot and low at the start of every
return-to-zero slot; under S_XA_PW / S_YA_PW, x_ack (y_ack) at the client
pulses, non-empty, in every token that selects x (y). -/
theorem mux_pulses {R : Nat} {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y
      zx zy xa qa ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (hRL : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
      P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
      P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
      P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
      R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0)
    (hEs : 1 ≤ Es)
    (H_START : P.Tz ≤ P.Z 0 ∧ P.Tx ≤ P.XA 0 ∧ P.Ty ≤ P.YA 0)
    (S_XA_PW : P.Wzx.hi + P.Lxa.hi + P.Wxa.hi <
        (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo) ∧
      P.W0x.hi + P.Lxa.hi + P.Wxa.hi <
        (Wzc.lo + Ec + wc + lj) + 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo))
    (S_YA_PW : P.Wzy.hi + P.Lya.hi + P.Wya.hi <
        (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzy.lo + P.Lya.lo + P.Wya.lo) ∧
      P.W1y.hi + P.Lya.hi + P.Wya.hi <
        (Wzc.lo + Ec + wc + lj) + 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzy.lo + P.Lya.lo + P.Wya.lo)) :
    (∀ j, P.Z j < P.Z (j + 1)) ∧ (∀ j, P.XA j < P.XA (j + 1)) ∧ (∀ j, P.YA j < P.YA (j + 1)) ∧
    (∀ k, zr (P.Z (2 * k)) = true ∧ zr (P.Z (2 * k + 1)) = false) ∧
    (∀ m, xak (P.XA (2 * P.κ0 m)) = true ∧ xak (P.XA (2 * P.κ0 m + 1)) = false) ∧
    (∀ m, yak (P.YA (2 * P.κ1 m)) = true ∧ yak (P.YA (2 * P.κ1 m + 1)) = false) := by
  have hE0 := V.H_ENUM0; have hE1 := V.H_ENUM1
  have ok := mux_ok_static G V Cs S hRL hRE
  have Zs : ∀ j, P.Z j < P.Z (j + 1) := fun j => by have := mux_Z_step hE0 hE1 Cs S j; omega
  have Xs := mux_XA_step hE0 hE1 Cs S S_XA_PW
  have Ys := mux_YA_step hE0 hE1 Cs S S_YA_PW
  have Zm := mono_of_step P.Z (fun j => Nat.le_of_lt (Zs j))
  have Xm := mono_of_step P.XA (fun j => Nat.le_of_lt (Xs j))
  have Ym := mono_of_step P.YA (fun j => Nat.le_of_lt (Ys j))
  obtain ⟨hs1, hs2, hs3⟩ := H_START
  refine ⟨Zs, Xs, Ys, fun k => ⟨?_, ?_⟩, fun m => ⟨?_, ?_⟩, fun m => ⟨?_, ?_⟩⟩
  · exact (ok.1.at_edge k (by have := Zm 0 (2 * k) (Nat.zero_le _); omega) (Zs _)).1
  · exact ok.1.at_gap k (by have := Zm 0 (2 * k + 1) (Nat.zero_le _); omega) (Zs _)
  · have := (ok.2.1.at_edge (P.κ0 m) (by have := Xm 0 (2 * P.κ0 m) (Nat.zero_le _); omega) (Xs _)).1
    rw [this]; have := hE0.hit m; simpa using this
  · exact ok.2.1.at_gap (P.κ0 m) (by have := Xm 0 (2 * P.κ0 m + 1) (Nat.zero_le _); omega) (Xs _)
  · have := (ok.2.2.2.1.at_edge (P.κ1 m) (by have := Ym 0 (2 * P.κ1 m) (Nat.zero_le _); omega) (Ys _)).1
    rw [this]; exact hE1.hit m
  · exact ok.2.2.2.1.at_gap (P.κ1 m) (by have := Ym 0 (2 * P.κ1 m + 1) (Nat.zero_le _); omega) (Ys _)

end pulses

section mergepulses
variable {P : MergeRun} {Eo Es wo wz la wa : Nat}

theorem merge_ρ_le_Z' (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa) (j : Nat) :
    P.ρ j + (wo + P.Lor.lo + P.Dz.lo) ≤ P.Z j := by
  have hWO := S.H_WO; have hp := Cs.H_POS j
  unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO
  split
  · have a := fl P.Wxo hp
    have b := fl P.Lor (c := P.Wxo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wxo.fst (P.ρ j))) (by omega)
    omega
  · have a := fl P.Wyo hp
    have b := fl P.Lor (c := P.Wyo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wyo.fst (P.ρ j))) (by omega)
    omega

/-- The merge's z_req phases at the server each last a whole round trip. -/
theorem merge_Z_step (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa) (j : Nat) :
    P.Z j + (Es + (wz + la + wa + Eo) + (wo + P.Lor.lo + P.Dz.lo)) ≤ P.Z (j + 1) := by
  have := Cs.H_SRV j; have := merge_ZR Cs S j; have := merge_ρ_le_Z' Cs S (j + 1)
  omega

/-- The merge's x_ack phases at the client are non-empty under **S_XA_PW**. -/
theorem merge_XA_step (Cs : MergeCausal P Eo Es) (S : MergeStatic P Eo Es wo wz la wa)
    (S_XA_PW : P.Wzx.hi + P.Lxa.hi + P.Wxa.hi <
        (wz + la + wa + Eo) + (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo) ∧
      P.Wxc.hi + P.Lxa.hi + P.Wxa.hi <
        (wz + la + wa + Eo) + 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (P.Wzx.lo + P.Lxa.lo + P.Wxa.lo))
    (j : Nat) : P.XA j < P.XA (j + 1) := by
  have RZ := merge_RZ Cs S j; have ZR := merge_ZR Cs S j; have RZ1 := merge_RZ Cs S (j + 1)
  have hz1 : 1 ≤ P.ζ (j + 1) := by have := Cs.H_POS (j + 1); omega
  have lo1 := merge_ζ_le_XA (j + 1) hz1
  have u1 := P.Wxc.fst_le (P.ρ j); have u2 := P.Wzx.fst_le (P.ζ j)
  have u3 := P.Lxa.fst_le (P.cx j); have u4 := P.Wxa.fst_le (P.Lxa.fst (P.cx j))
  have := S_XA_PW
  have e1 : P.XA j = P.Wxa.fst (P.Lxa.fst (P.cx j)) := rfl
  have e2 : P.cx j = max (P.AX j) (P.ZA0 j) := rfl
  have e3 : P.AX j = P.Wxc.fst (P.ρ j) := rfl
  have e4 : P.ZA0 j = P.Wzx.fst (P.ζ j) := rfl
  omega

end mergepulses

namespace MuxWit

/-- **Non-vacuity of `mux_pulses`** on the unit-delay mux run. -/
theorem pulses_witness :
    (∀ j, run.Z j < run.Z (j + 1)) ∧ (∀ j, run.XA j < run.XA (j + 1)) ∧
    (∀ j, run.YA j < run.YA (j + 1)) ∧
    (∀ k, zr (run.Z (2 * k)) = true ∧ zr (run.Z (2 * k + 1)) = false) ∧
    (∀ m, xak (run.XA (2 * run.κ0 m)) = true ∧ xak (run.XA (2 * run.κ0 m + 1)) = false) ∧
    (∀ m, yak (run.YA (2 * run.κ1 m)) = true ∧ yak (run.YA (2 * run.κ1 m + 1)) = false) :=
  mux_pulses gates env causal static (by decide) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Xp_eq]; omega
    · rw [D0_eq]; omega
    · rw [Yp_eq]; omega
    · rw [D1_eq]; omega
    · rw [A0_eq, E_eq]; omega
    · rw [(ZA_eq 0).1]; omega
    · rw [A1_eq, E_eq]; omega
    · rw [(ZA_eq 0).2]; omega) (Nat.le_refl 1)
    (by refine ⟨?_, ?_, ?_⟩
        · rw [Z_eq, E_eq]; decide
        · rw [(XA_eq 0).1]; decide
        · rw [(XA_eq 0).2]; decide)
    (by decide) (by decide)

end MuxWit

/-! ## 8. FASTFALL = 1 delay lines on the request path

`bd_delay #(.FASTFALL(1))` (cells/rtl/bd_latch.v; bdc emits it with
`BDC_LINK_FASTFALL=1`): stage 0 is a LUT1 buffer on the chain; stage
`i ∈ [1, N)` is a LUT2 AND (`4'h8`) of the previous stage (I0, through the
hop) and the line's input (I1, through tap `i`). In the binary FIFO model
(H_LUT_FIFO, H_WIRE_FIFO) each stage is `s (i+1) t = s i (H i).σ t && a
((Tp i).σ t)` where `H i` (hop + I0 arc) and `Tp i` (tap + I1 arc) are FIFO
paths (`PipeTimed.fifo_comp` composes wire and arc; the LUT arc is a read
map, so it distributes over the AND). The line is NOT a FIFO channel (a
fall overtakes a pending rise), so probe Lt assumed FASTFALL = 0.

* `and_tok`: the AND of two clean four-phase traces is a clean four-phase
  trace whose rise is the LATER rise and whose fall is the EARLIER fall,
  provided each input's fall precedes the other's next rise (the flush).
* `ff_tok`: by induction over the stages, the FASTFALL line's every stage is
  a clean four-phase trace on `ffE` (rise: the slowest path, fall: the
  fastest), under **H_FLUSH_STAGE** per stage and token: stage `i`'s fall,
  through hop `i`, arrives no later than the input's next rise through tap
  `i` (and the tap's fall no later than stage `i`'s next rise through the
  hop). This is ConstraintsFastFall's per-stage condition
  (`bd_delay[FASTFALL].flush_per_stage`) in the FIFO world.
* `mux_ok_fastfall`: `mux_ok` with the line replaced: instantiate the run's
  `Dz` as the identity (`Ret.shift 0`, then `H_DZ` is `rfl`) so that
  `mux_ok`'s z_req trace IS uor's output, and feed it to the FASTFALL line.
  None of `MuxTiming`'s fields mentions `Dz`, so the control proof is
  unchanged; the server sees one clean transaction per control token on
  `ffE … P.Z N`.
-/

/-- Edges of an AND of two four-phase traces: rise = later, fall = earlier. -/
def andEdges (e e' : Nat → Nat) (j : Nat) : Nat :=
  if j % 2 = 0 then max (e j) (e' j) else min (e j) (e' j)

theorem and_tok {T : Nat} {a b : Trace} {e e' : Nat → Nat}
    (ha : Tok T a e (fun _ => true)) (hb : Tok T b e' (fun _ => true))
    (hs1 : ∀ k, e (2 * k + 1) ≤ e' (2 * k + 2)) (hs2 : ∀ k, e' (2 * k + 1) ≤ e (2 * k + 2)) :
    Tok T (fun t => a t && b t) (andEdges e e') (fun _ => true) := by
  have q0 : andEdges e e' 0 = max (e 0) (e' 0) := by unfold andEdges; split <;> omega
  have qe : ∀ k, andEdges e e' (2 * k) = max (e (2 * k)) (e' (2 * k)) := fun k => by
    unfold andEdges; split <;> omega
  have qo : ∀ k, andEdges e e' (2 * k + 1) = min (e (2 * k + 1)) (e' (2 * k + 1)) := fun k => by
    unfold andEdges; split <;> omega
  have qe2 : ∀ k, andEdges e e' (2 * k + 2) = max (e (2 * k + 2)) (e' (2 * k + 2)) := fun k => by
    unfold andEdges; split <;> omega
  refine ⟨fun t hT h2 => ?_, fun k t hT h1 h2 => ?_, fun k t hT h1 h2 => ?_⟩
  · rw [q0] at h2
    by_cases h : t < e 0
    · simp [ha.pre t hT h]
    · simp [hb.pre t hT (by omega)]
  · rw [qe] at h1; rw [qo] at h2
    simp [ha.hi k t hT (by omega) (by omega), hb.hi k t hT (by omega) (by omega)]
  · rw [qo] at h1; rw [qe2] at h2
    have s1 := hs1 k; have s2 := hs2 k
    by_cases c1 : e (2 * k + 1) ≤ t ∧ t < e (2 * k + 2)
    · simp [ha.lo k t hT c1.1 c1.2]
    · by_cases c2 : e' (2 * k + 1) ≤ t ∧ t < e' (2 * k + 2)
      · simp [hb.lo k t hT c2.1 c2.2]
      · exfalso; omega

/-- **A FASTFALL line in the FIFO model.** `s 0 = a` is the line input;
`H i`, `Tp i` the hop and tap paths (FIFO) of stage `i`. -/
structure FFLine (a : Trace) (s : Nat → Trace) (H Tp : Nat → Ret) (N : Nat) : Prop where
  /-- stage 0: LUT1 buffer (**H_LUT_FIFO** + hop wire). -/
  H_S0 : ∀ t, (H 0).hi ≤ t → s 1 t = a ((H 0).σ t)
  /-- stage `i ∈ [1, N)`: LUT2 `4'h8` (AND), REAL INIT via `Bundling.ff_bin`,
  pins through FIFO paths. -/
  H_SI : ∀ i, 1 ≤ i → i < N → ∀ t, (H i).hi + (Tp i).hi ≤ t →
    s (i + 1) t = (s i ((H i).σ t) && a ((Tp i).σ t))

/-- Edges of stage `i` of a FASTFALL line fed by edges `e`. -/
def ffE (H Tp : Nat → Ret) (e : Nat → Nat) : Nat → Nat → Nat
  | 0 => e
  | 1 => fun j => (H 0).fst (e j)
  | i + 2 => andEdges (fun j => (H (i + 1)).fst (ffE H Tp e (i + 1) j)) (fun j => (Tp (i + 1)).fst (e j))

/-- Start of stage `i`'s clean window. -/
def ffT (H Tp : Nat → Ret) (T : Nat) : Nat → Nat
  | 0 => T
  | i + 1 => ffT H Tp T i + (H i).hi + (Tp i).hi

theorem ffT_ge (H Tp : Nat → Ret) (T : Nat) : ∀ i, T ≤ ffT H Tp T i
  | 0 => Nat.le_refl _
  | i + 1 => by have := ffT_ge H Tp T i; show T ≤ ffT H Tp T i + (H i).hi + (Tp i).hi; omega

/-- **`ff_tok`: every stage of a FASTFALL line is a clean four-phase trace**
(one pulse per input pulse; rise by the slowest path, fall by the fastest),
under **H_FLUSH_STAGE**. -/
theorem ff_tok {a : Trace} {s : Nat → Trace} {H Tp : Nat → Ret} {N T : Nat} {e : Nat → Nat}
    (L : FFLine a s H Tp N) (ha : Tok T a e (fun _ => true))
    (H_FLUSH_STAGE : ∀ i, 1 ≤ i → i < N → ∀ k,
      (H i).fst (ffE H Tp e i (2 * k + 1)) ≤ (Tp i).fst (e (2 * k + 2)) ∧
      (Tp i).fst (e (2 * k + 1)) ≤ (H i).fst (ffE H Tp e i (2 * k + 2))) :
    ∀ i, 1 ≤ i → i ≤ N → Tok (ffT H Tp T i) (s i) (ffE H Tp e i) (fun _ => true) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hiN
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      exact ((ha.fifo (H 0) L.H_S0).mono (by show T + (H 0).hi ≤ T + (H 0).hi + (Tp 0).hi; omega))
    · have IH := ih hpos (by omega)
      have hT := ffT_ge H Tp T i
      have p1 : Tok (ffT H Tp T (i + 1)) (fun t => s i ((H i).σ t))
          (fun j => (H i).fst (ffE H Tp e i j)) (fun _ => true) :=
        (IH.fifo (H i) (fun _ _ => rfl)).mono
          (by show ffT H Tp T i + (H i).hi ≤ ffT H Tp T i + (H i).hi + (Tp i).hi; omega)
      have p2 : Tok (ffT H Tp T (i + 1)) (fun t => a ((Tp i).σ t))
          (fun j => (Tp i).fst (e j)) (fun _ => true) :=
        (ha.fifo (Tp i) (fun _ _ => rfl)).mono
          (by show T + (Tp i).hi ≤ ffT H Tp T i + (H i).hi + (Tp i).hi; omega)
      have hand := and_tok p1 p2 (fun k => (H_FLUSH_STAGE i hpos (by omega) k).1)
        (fun k => (H_FLUSH_STAGE i hpos (by omega) k).2)
      obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      refine (hand.trace_congr (fun t ht => ?_))
      have : (H (i' + 1)).hi + (Tp (i' + 1)).hi ≤ t := by
        show _ ≤ t
        have : ffT H Tp T (i' + 1 + 1) = ffT H Tp T (i' + 1) + (H (i' + 1)).hi + (Tp (i' + 1)).hi := rfl
        omega
      exact L.H_SI (i' + 1) hpos (by omega) t this

/-- **`mux_ok_fastfall`**: the mux with a FASTFALL = 1 delay line. The run's
`Dz` is the identity (`zr := ei` in the gates; with `Dz := Ret.shift 0`
`H_DZ` holds by `rfl`), so `mux_ok`'s z_req trace is uor's output `ei`; the
FASTFALL line `s` (with `s 0 = ei`, `s N` = z_req at the server, the last
wire folded into the last stage's paths) then delivers one clean
transaction per control token, under H_FLUSH_STAGE. -/
theorem mux_ok_fastfall {P : MuxRun} {R : Nat} {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1
      ei j0x j1y zx zy xa qa ya qb xak yak : Trace} {s : Nat → Trace} {H Tp : Nat → Ret} {N : Nat}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei ei j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (TM : MuxTiming P R)
    (L : FFLine ei s H Tp N) (hN : 1 ≤ N)
    (H_FLUSH_STAGE : ∀ i, 1 ≤ i → i < N → ∀ k,
      (H i).fst (ffE H Tp P.Z i (2 * k + 1)) ≤ (Tp i).fst (P.Z (2 * k + 2)) ∧
      (Tp i).fst (P.Z (2 * k + 1)) ≤ (H i).fst (ffE H Tp P.Z i (2 * k + 2))) :
    Tok (ffT H Tp P.Tz N) (s N) (ffE H Tp P.Z N) (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Ty yak P.YA P.sv :=
  have h := mux_ok G V TM
  ⟨ff_tok L h.2.2.1 H_FLUSH_STAGE N hN (Nat.le_refl _), h.2.2.2.1, h.2.2.2.2.2.1⟩

/-- Static sufficient form of one H_FLUSH_STAGE instance (`fst_order`): the
stage's fall `f` (an upper bound on `ffE … i (2k+1)`) through the hop's MAX
arrives no later than the next input rise through the tap's MIN. -/
theorem flush_stage_static (Hi Ti : Ret) {f e2 : Nat} (hf : 1 ≤ e2)
    (h : f + Hi.hi ≤ e2 + Ti.lo) : Hi.fst f ≤ Ti.fst e2 := fst_order Hi Ti hf h

end Formal.Cells.OpsTimed
