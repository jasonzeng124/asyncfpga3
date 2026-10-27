import Formal.Cells.ContractsB
import Formal.Cells.OpsHold

/-!
# Probe G5a: the 2-way and 3-way mux contracts in C's interface

Shard B, Phase 3, gap G5 of `formal/notes/B-contracts.md` for `bd_mux` and
`bdc_muxn3`. Same style as `ContractsB.steer_contract`: from B's timed cell
theorems (`mux_ok_static` + `OpsHold.mux_data_hold_fall`;
`muxn3_ok_static` + `OpsHold.muxn3_data_hold_fall`) and NAMED identification
hypotheses, derive

* the FULL `Port` of the output channel `cz` (request = the cell's z_req at
  the server's pin, acknowledge = the server's z_ack, strict interleaving, and
  the data window `[ρ(2k), α(2k+1))` = C's `Held`, from the hold-to-fall data
  theorem, assembled over the bus bits);
* on every input channel (`cx`, `cy`, resp. `cxs i`), the half the mux drives
  (the acknowledge, re-indexed on that input's own tokens, a clean `Tok 0`
  wire) and the strict interleaving of request and acknowledge;
* on the control channel, the strict interleaving of ctl_req and ctl_ack as
  seen by the control sender (through `Wzc`);
* C's event contract `MuxEv` / `MuxNEv` (ContractsOps), verbatim, hence by
  `mux_spec` / `muxn_spec` C's `OpProto ∧ OpData (muxEq …)` / `(muxnEq …)`.

The new lemma the probe asked for is `idx_cnt`: on an enumerated token,
B's `idx κ k` (position of `k` in the enumeration) equals C's counter
`cnt g k` (number of earlier tokens with the same select).

## Observation points (G2)

Convention used throughout: **every channel is observed at its consumer's
pins; each cell owns its output wires.** Applied to B's mux model this means:
* the mux's driven traces `zr` (z_req at the server's pin, `Dz` includes the
  wire), `xak`, `yak` (acks at the clients' pins, `Wxa`, `Wya`) are channel
  traces as they stand;
* B's input traces `x`, `y`, `ctl`, `za` are read as the channel traces at
  their observation point, and B's input arcs `Wx`, `Wy`, `Wc0`, `Wc1`,
  `Wzx`, `Wzy` (resp. `Wx i`, `Wc i`, `Wza i`) as the residual arc from that
  point to the physical LUT pin (zero for a single-pin input; for ctl_req and
  z_ack, which fan out to two (three) LUT pins inside the cell, the in-cell
  fork skew from the reference pin);
* the control channel's acknowledge is the server's z_ack observed at the
  CONTROL SENDER's pin: `Wzc.fst ∘ ζ` (the server owns that branch of its
  net; the mux does not drive it).
The hypotheses `hρ*`, `hα*`, `hreqz`, `hackz` state these identifications.

## Bus values

B's data theorems are per bit. `W` is the bus width; the channel's value is a
`Nat` whose bit `n < W` is the bit-`n` trace (`H_BUS`), with values `< 2^W`
(`H_X_W`, …). `H_X_VAL` identifies the senders' per-bit token values with C's
`v`; `H_Z_TOKVAL` DEFINES the output token's value as the bus value at its
offer instant (C's `offer_val` reading), not a physical assumption.
-/

namespace Formal.Cells.Contracts
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret)
open Formal.Net.Ops.CM (cnt_congr_lt)
open Formal.Cells.ConstraintsMux (DmRel)
open Formal.Cells.OpsHold

/-! ## Generic lemmas -/

/-- **`idx = cnt`**: on an enumerated token `k` (`g k`), its index in the
enumeration is the number of earlier `g`-tokens. -/
theorem idx_cnt {g : Nat → Bool} {κ : Nat → Nat} (hE : Enum g κ) {k : Nat} (hk : g k = true) :
    idx κ k = cnt g k := by
  have h2 := enum_cnt hE (idx κ k)
  rw [κ_idx hE hk] at h2
  exact h2.symm

/-- Two `W`-bit values with the same low `W` bits are equal. -/
theorem bus_eq {W d w : Nat} {bit : Nat → Bool} (hd : d < 2 ^ W) (hw : w < 2 ^ W)
    (hdb : ∀ n, n < W → d.testBit n = bit n) (hwb : ∀ n, n < W → w.testBit n = bit n) : d = w :=
  Nat.eq_of_testBit_eq fun n => by
    by_cases h : n < W
    · rw [hdb n h, hwb n h]
    · have p : 2 ^ W ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
      rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-- Strict interleaving of a two-edge-sequence handshake from its four
half-steps. -/
theorem order_of_steps {r a : Nat → Nat}
    (h0 : ∀ m, r (2 * m) < a (2 * m)) (h1 : ∀ m, a (2 * m) < r (2 * m + 1))
    (h2 : ∀ m, r (2 * m + 1) < a (2 * m + 1)) (h3 : ∀ m, a (2 * m + 1) < r (2 * m + 2)) :
    ∀ j, r j < a j ∧ a j < r (j + 1) := by
  intro j
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
    exact ⟨h0 m, h1 m⟩
  · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
    exact ⟨h2 m, h3 m⟩

/-! ## The 2-way mux (`bd_mux`) -/

section mux
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}

/-- Input x's request edge (x-indexed) is no later than the selected join's
node edge for the control token consuming it. -/
theorem mux_x_le_E (hE0 : Enum (fun k => !P.sv k) P.κ0) (m r : Nat) (hr : r < 2) :
    P.ξ (2 * m + r) ≤ P.E (2 * P.κ0 m + r) := by
  have e := E_rx0 hE0 (2 * m + r)
  unfold rx at e
  rw [show (2 * m + r) / 2 = m by omega, show (2 * m + r) % 2 = r by omega] at e
  rw [e]; unfold MuxRun.τ0 MuxRun.c0 MuxRun.Xp
  have := P.Lj0.fst_ge (max (P.Wx.fst (P.ξ (2 * m + r))) (P.D0 (2 * m + r)))
  have := P.Wx.fst_ge (P.ξ (2 * m + r))
  omega

theorem mux_y_le_E (hE1 : Enum P.sv P.κ1) (m r : Nat) (hr : r < 2) :
    P.η (2 * m + r) ≤ P.E (2 * P.κ1 m + r) := by
  have e := E_rx1 hE1 (2 * m + r)
  unfold rx at e
  rw [show (2 * m + r) / 2 = m by omega, show (2 * m + r) % 2 = r by omega] at e
  rw [e]; unfold MuxRun.τ1 MuxRun.c1 MuxRun.Yp
  have := P.Lj1.fst_ge (max (P.Wy.fst (P.η (2 * m + r))) (P.D1 (2 * m + r)))
  have := P.Wy.fst_ge (P.η (2 * m + r))
  omega

/-- The selected join's node edge strictly precedes z_req at the server
(`H_FWD_POS`: the join → uor → delay line → server path has a positive
minimum delay). -/
theorem mux_E_lt_Z (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (H_FWD_POS : 1 ≤ wo + P.Lor.lo + P.Dz.lo) (j : Nat) : P.E j < P.Z j := by
  have := mux_E_le_Z S.H_WO j (γ_le_E hE0 hE1 Cs.H_POS S j).2
  omega

/-- **The edge chain of the mux's own handshakes**: `γ j < E j < Z j < ζ j
< E (j+1)`, and the control sender's view of ctl_ack lies strictly between
consecutive ctl_req edges. -/
theorem mux_chain (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (H_ES : 1 ≤ Es) (H_EC : 1 ≤ Ec) (H_FWD_POS : 1 ≤ wo + P.Lor.lo + P.Dz.lo) (j : Nat) :
    P.γ j ≤ P.E j ∧ P.E j < P.Z j ∧ P.Z j < P.ζ j ∧ P.ζ j < P.Z (j + 1) ∧
    P.γ j < Wzc.fst (P.ζ j) ∧ Wzc.fst (P.ζ j) < P.γ (j + 1) := by
  have a := (γ_le_E hE0 hE1 Cs.H_POS S j).1
  have b := mux_E_lt_Z hE0 hE1 Cs S H_FWD_POS j
  have b1 := mux_E_lt_Z hE0 hE1 Cs S H_FWD_POS (j + 1)
  have c := Cs.H_SRV j
  have d := ζ_le_E hE0 hE1 Cs S j
  have e := Wzc.fst_ge (P.ζ j)
  have f := Cs.H_CTL_C j
  refine ⟨by omega, b, by omega, by omega, by omega, by omega⟩

/-- **Input x's channel interleaves strictly**: `ξ j < XA' j < ξ (j+1)` with
`XA' = rx XA κ0` (x_ack at x's pin, on x's own tokens). -/
theorem mux_x_order (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (H_ES : 1 ≤ Es) (H_EC : 1 ≤ Ec) (H_EX : 1 ≤ Ex) (H_FWD_POS : 1 ≤ wo + P.Lor.lo + P.Dz.lo) :
    ∀ j, P.ξ j < rx P.XA P.κ0 j ∧ rx P.XA P.κ0 j < P.ξ (j + 1) := by
  have EX : ∀ j, P.E j < P.XA j := fun j => by
    have := mux_chain hE0 hE1 Cs S H_ES H_EC H_FWD_POS j
    have := mux_ζ_le_XA (P := P) j (by omega)
    omega
  apply order_of_steps
  · intro m; rw [rx_e]; have := mux_x_le_E hE0 m 0 (by omega); have := EX (2 * P.κ0 m)
    simp only [Nat.add_zero] at *; omega
  · intro m; rw [rx_e]; have := Cs.H_XC_FALL m; omega
  · intro m; rw [rx_o]; have := mux_x_le_E hE0 m 1 (by omega); have := EX (2 * P.κ0 m + 1); omega
  · intro m; rw [rx_o]; have := Cs.H_XC_RISE m; omega

theorem mux_y_order (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo)
    (H_ES : 1 ≤ Es) (H_EC : 1 ≤ Ec) (H_EY : 1 ≤ Ey) (H_FWD_POS : 1 ≤ wo + P.Lor.lo + P.Dz.lo) :
    ∀ j, P.η j < rx P.YA P.κ1 j ∧ rx P.YA P.κ1 j < P.η (j + 1) := by
  have EY : ∀ j, P.E j < P.YA j := fun j => by
    have := mux_chain hE0 hE1 Cs S H_ES H_EC H_FWD_POS j
    have := mux_ζ_le_YA (P := P) j (by omega)
    omega
  apply order_of_steps
  · intro m; rw [rx_e]; have := mux_y_le_E hE1 m 0 (by omega); have := EY (2 * P.κ1 m)
    simp only [Nat.add_zero] at *; omega
  · intro m; rw [rx_e]; have := Cs.H_YC_FALL m; omega
  · intro m; rw [rx_o]; have := mux_y_le_E hE1 m 1 (by omega); have := EY (2 * P.κ1 m + 1); omega
  · intro m; rw [rx_o]; have := Cs.H_YC_RISE m; omega

/-- A strictly interleaved edge sequence is monotone from its first edge. -/
theorem first_le_of_order {r a : Nat → Nat} (h : ∀ j, r j < a j ∧ a j < r (j + 1)) :
    ∀ j, a 0 ≤ a j := by
  have hs : Strict a := fun j => Nat.lt_trans (h j).2 (h (j + 1)).1
  exact fun j => (Strict.le_iff hs).2 (Nat.zero_le j)

/-- **The packaged `bd_mux` contract (C's interface, from B's theorems).**

From exactly `mux_ok_static`'s hypotheses (gates with REAL INITs, clean
partners, `MuxCausal`, `MuxStatic`, reset sequencing) and, per bus bit
`n < W`, exactly `mux_data_hold_fall`'s (REAL `bd_datamux` INITs via
`DmRel`, the senders' data contracts `MuxDataEnv`, the hold-to-fall sender
contracts `MuxHoldF` (G3), the setup obligations `MuxDataStatic`), plus the
named hypotheses below, it proves:
1. the output channel `cz` is a full `Port` (req = z_req, ack = z_ack,
   interleaving, data window to the ack FALL);
2. x_ack, y_ack on their own tokens are clean wires from time 0;
3. the input channels' and the control channel's edges interleave strictly;
4. C's `MuxEv`, hence (`mux_spec`) `OpProto ∧ OpData (muxEq …)`.

Named hypotheses added (beyond B's theorems):
* `H_ES`, `H_EC`, `H_EX`, `H_EY` (≥ 1): the server's, control sender's and
  clients' handshake latencies are positive (SDF minima; GLS: no zero-delay
  response at any partner).
* `H_FWD_POS : 1 ≤ wo + Lor.lo + Dz.lo`: the join → uor → bd_delay → server
  path has a positive minimum delay (it contains at least the DELAY LUT1s).
* `H_QUIET_Z`, `H_QUIET_XA`, `H_QUIET_YA` with `H_TZ`, `H_TX`, `H_TY`: reset
  quiet. Each mux-driven wire is low before B's clean window starts (`Tz`,
  `Tx`, `Ty`), and that window starts before its first edge. GLS: the wire is
  0 from power-up until its first edge (`ResetGcd` proves the control nets
  settle low under reset; not yet tied to these traces).
* G2 identifications (module doc): `hρc hρx hρy hρz hαz`, `hreqz`, `hackz`.
* `H_SEL_VAL`: B's select bit of control token `k` is C's `sel` of the
  control token's value.
* Bus: `H_BUS` (the output bus value's bit `n < W` is the bit-`n` LUT output
  `z n`, and the value is `< 2^W`), `H_X_VAL`/`H_Y_VAL` (sender bit values are
  the bits of C's token values), `H_X_W`/`H_Y_W` (input values fit in `W`
  bits), `H_Z_TOKVAL` (the output token's value is the bus at its offer). -/
theorem mux_contract {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo R : Nat}
    {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak
      yak : Trace}
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
    -- data path, per bus bit `n < W` (`mux_data_hold_fall`'s hypotheses)
    {W : Nat} {s : Trace} {sS sE : Nat → Nat} {Ls wo' : Nat}
    {a b z : Nat → Trace} {xS xE yS yE : Nat → Nat → Nat} {xv yv : Nat → Nat → Bool}
    {slo shi alo ahi blo bhi Mz Lx Ly : Nat → Nat}
    (hR : ∀ n, n < W → DmRel s (a n) (b n) (z n) (slo n) (shi n) (alo n) (ahi n) (blo n) (bhi n))
    (hwin : ∀ n, n < W → slo n ≤ shi n ∧ alo n ≤ ahi n ∧ blo n ≤ bhi n)
    (D : ∀ n, n < W → MuxDataEnv P Wzc s (a n) (b n) sS sE (xS n) (xE n) (yS n) (yE n) (xv n) (yv n)
      Ls (Lx n) (Ly n))
    (F : ∀ n, n < W → MuxHoldF P Wzc sE (xE n) (yE n))
    (SD : ∀ n, n < W → MuxDataStatic P wo' (shi n) (ahi n) (bhi n) (Mz n) Ls (Lx n) (Ly n))
    -- positivity
    (H_ES : 1 ≤ Es) (H_EC : 1 ≤ Ec) (H_EX : 1 ≤ Ex) (H_EY : 1 ≤ Ey)
    (H_FWD_POS : 1 ≤ wo + P.Lor.lo + P.Dz.lo)
    -- reset quiet
    (H_QUIET_Z : ∀ t, t < P.Tz → zr t = false) (H_TZ : P.Tz ≤ P.Z 0)
    (H_QUIET_XA : ∀ t, t < P.Tx → xak t = false) (H_TX : P.Tx ≤ P.XA (2 * P.κ0 0))
    (H_QUIET_YA : ∀ t, t < P.Ty → yak t = false) (H_TY : P.Ty ≤ P.YA (2 * P.κ1 0))
    -- C's side and the identifications
    {C : Type} {ch : C → Chan} {ρ α v : C → Nat → Nat} {sel : Nat → Bool} {cc cx cy cz : C}
    (hρc : ρ cc = P.γ) (hρx : ρ cx = P.ξ) (hρy : ρ cy = P.η) (hρz : ρ cz = P.Z) (hαz : α cz = P.ζ)
    (hreqz : (ch cz).req = zr) (hackz : (ch cz).ack = za)
    (H_SEL_VAL : ∀ k, P.sv k = sel (v cc k))
    (H_X_VAL : ∀ n m, n < W → xv n m = (v cx m).testBit n)
    (H_Y_VAL : ∀ n m, n < W → yv n m = (v cy m).testBit n)
    (H_X_W : ∀ m, v cx m < 2 ^ W) (H_Y_W : ∀ m, v cy m < 2 ^ W)
    (H_BUS : ∀ t, (ch cz).dat t < 2 ^ W ∧ ∀ n, n < W → ((ch cz).dat t).testBit n = z n t)
    (H_Z_TOKVAL : ∀ k, v cz k = (ch cz).dat (P.Z (2 * k))) :
    Port (ch cz) (ρ cz) (α cz) (v cz) ∧
    Tok 0 xak (rx P.XA P.κ0) (fun _ => true) ∧ Tok 0 yak (rx P.YA P.κ1) (fun _ => true) ∧
    (∀ j, P.ξ j < rx P.XA P.κ0 j ∧ rx P.XA P.κ0 j < P.ξ (j + 1)) ∧
    (∀ j, P.η j < rx P.YA P.κ1 j ∧ rx P.YA P.κ1 j < P.η (j + 1)) ∧
    (∀ j, P.γ j < Wzc.fst (P.ζ j) ∧ Wzc.fst (P.ζ j) < P.γ (j + 1)) ∧
    MuxEv ρ v sel cc cx cy cz := by
  have hE0 := V.H_ENUM0
  have hE1 := V.H_ENUM1
  obtain ⟨hz, _, hxa, _, hya⟩ := mux_ok_static G V Cs S hRL hRE
  have hc := mux_chain hE0 hE1 Cs S H_ES H_EC H_FWD_POS
  have ox := mux_x_order hE0 hE1 Cs S H_ES H_EC H_EX H_FWD_POS
  have oy := mux_y_order hE0 hE1 Cs S H_ES H_EC H_EY H_FWD_POS
  have hγ := Cs.H_POS
  -- the selected input's value, and the output bus over the hold-to-fall window
  let mval : Nat → Nat := fun k => if P.sv k then v cy (idx P.κ1 k) else v cx (idx P.κ0 k)
  have hdat : ∀ k t, P.Z (2 * k) ≤ t → t < P.ζ (2 * k + 1) → (ch cz).dat t = mval k := by
    intro k t h1 h2
    have hb : ∀ n, n < W → ((ch cz).dat t).testBit n = (mval k).testBit n := by
      intro n hn
      have hw := hwin n hn
      have hz := mux_data_hold_fall (hR n hn) hw.1 hw.2.1 hw.2.2 hE0 hE1 (D n hn) (F n hn) (SD n hn)
        k t (by omega) (by omega)
      rw [(H_BUS t).2 n hn, hz]
      unfold MuxRun.zv
      show _ = (if P.sv k then v cy (idx P.κ1 k) else v cx (idx P.κ0 k)).testBit n
      cases P.sv k
      · simp only [Bool.false_eq_true, ite_false]; exact H_X_VAL n _ hn
      · simp only [ite_true]; exact H_Y_VAL n _ hn
    have hm : mval k < 2 ^ W := by
      show (if P.sv k then v cy (idx P.κ1 k) else v cx (idx P.κ0 k)) < 2 ^ W
      cases P.sv k
      · exact H_X_W _
      · exact H_Y_W _
    exact bus_eq (H_BUS t).1 hm hb (fun _ _ => rfl)
  have hvz : ∀ k, v cz k = mval k := fun k => by
    rw [H_Z_TOKVAL k]
    have := hc (2 * k); have := hc (2 * k + 1)
    exact hdat k _ (Nat.le_refl _) (by omega)
  refine ⟨?_, ?_, ?_, ox, oy, fun j => ⟨(hc j).2.2.2.2.1, (hc j).2.2.2.2.2⟩, ?_⟩
  · -- the output port
    rw [hρz, hαz]
    refine ⟨?_, ?_, ?_, fun j => (hc j).2.2.1, fun j => (hc j).2.2.2.1, fun k t h1 h2 => ?_⟩
    · rw [hreqz]
      have hs : Strict P.Z := fun j => Nat.lt_trans (hc j).2.2.1 (hc j).2.2.2.1
      exact tok_from0 hz H_QUIET_Z H_TZ (fun j => (Strict.le_iff hs).2 (Nat.zero_le j))
    · rw [hackz]; exact V.H_ZA
    · have := (hc 0).1; have := (hc 0).2.1; have := hγ 0; omega
    · rw [hdat k t h1 h2, hvz]
  · exact tok_from0 hxa H_QUIET_XA (by rw [rx_0]; exact H_TX) (first_le_of_order ox)
  · exact tok_from0 hya H_QUIET_YA (by rw [rx_0]; exact H_TY) (first_le_of_order oy)
  · -- C's event contract
    refine ⟨?_, fun k => ?_, fun k => ?_⟩
    · rw [hρc]; exact fun j => Nat.lt_trans (hc j).2.2.2.2.1 (hc j).2.2.2.2.2
    · rw [hρc, hρz]; have := hc (2 * k); omega
    · have c1 : cnt (fun i => sel (v cc i)) k = cnt P.sv k :=
        cnt_congr_lt k fun i _ => by rw [H_SEL_VAL]
      have c0 : cnt (fun i => !sel (v cc i)) k = cnt (fun i => !P.sv i) k :=
        cnt_congr_lt k fun i _ => by rw [H_SEL_VAL]
      rw [c1, c0, ← H_SEL_VAL, hvz, hρz]
      cases hk : P.sv k
      · simp only [Bool.false_eq_true, ite_false]
        rw [hρx, ← idx_cnt hE0 (by simp [hk])]
        refine ⟨?_, by show (if P.sv k then _ else _) = _; rw [hk]; rfl⟩
        have hm := κ_idx hE0 (k := k) (by simp [hk])
        have := mux_x_le_E hE0 (idx P.κ0 k) 0 (by omega)
        rw [Nat.add_zero, Nat.add_zero, hm] at this
        have := (hc (2 * k)).2.1; omega
      · simp only [ite_true]
        rw [hρy, ← idx_cnt hE1 hk]
        refine ⟨?_, by show (if P.sv k then _ else _) = _; rw [hk]; rfl⟩
        have hm := κ_idx hE1 (k := k) hk
        have := mux_y_le_E hE1 (idx P.κ1 k) 0 (by omega)
        rw [Nat.add_zero, Nat.add_zero, hm] at this
        have := (hc (2 * k)).2.1; omega

end mux

/-! ## The 3-way mux (`bdc_muxn3`) -/

section mn3
open Formal.Cells.MuxN3Timed
open Formal.Cells.Bundling (Gate)
open Formal.Cells.AMergeGates (DM5)
variable {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl : Nat}

/-- Input `i`'s request edge (i-indexed) is no later than the selected join's
node edge for the control token consuming it. -/
theorem mn3_x_le_E (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) {i : Nat} (hi : i < 3) (m r : Nat)
    (hr : r < 2) : P.ξ i (2 * m + r) ≤ P.E (2 * P.κ i m + r) := by
  have e := E_rx (hE i hi) (2 * m + r)
  unfold rx at e
  rw [show (2 * m + r) / 2 = m by omega, show (2 * m + r) % 2 = r by omega] at e
  rw [e]; unfold MN3Run.τ MN3Run.c MN3Run.Xp
  have := (P.Lj i).fst_ge (max ((P.Wx i).fst (P.ξ i (2 * m + r))) (P.D i (2 * m + r)))
  have := (P.Wx i).fst_ge (P.ξ i (2 * m + r))
  omega

/-- The server's z_ack edge is no later than in_i_ack's at client `i`. -/
theorem mn3_ζ_le_XA (i j : Nat) : P.ζ j ≤ P.XA i j := by
  unfold MN3Run.XA MN3Run.cx MN3Run.ZA
  have := (P.Wza i).fst_ge (P.ζ j)
  have := (P.La i).fst_ge (max (P.A i j) ((P.Wza i).fst (P.ζ j)))
  have := (P.Wak i).fst_ge ((P.La i).fst (max (P.A i j) ((P.Wza i).fst (P.ζ j))))
  omega

/-- **The edge chain of the 3-way mux's own handshakes** (`H_FWD_POS`: the
`|j` → line → server path has a positive minimum delay). -/
theorem mn3_chain (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N)
    (H_EC : 1 ≤ Ec) (H_FWD_POS : 1 ≤ wo + P.Lo.lo + Dl) (j : Nat) :
    P.γ j ≤ P.E j ∧ P.E j < P.Z j ∧ P.Z j < P.ζ j ∧ P.ζ j < P.Z (j + 1) ∧
    P.γ j < Wzc.fst (P.ζ j) ∧ Wzc.fst (P.ζ j) < P.γ (j + 1) := by
  have EZ : ∀ j, P.E j < P.Z j := fun j => by
    have := E_le_Z hE hR Cs.H_POS (fun i hi => (S.H_MIN i hi).2.2.2.2) S.H_DL0 S.H_DLT hN j
    omega
  have a := GE_min hE hR Cs S j
  have b := EZ j; have b1 := EZ (j + 1)
  have c := Cs.H_SRV j; have := Cs.H_ES
  have d := ZE_min hE hR Cs S hN j
  have e := Wzc.fst_ge (P.ζ j)
  have f := Cs.H_CTL_C j
  refine ⟨by omega, b, by omega, by omega, by omega, by omega⟩

/-- **Input `i`'s channel interleaves strictly** (in_i_ack at client `i`, on
input `i`'s own tokens). -/
theorem mn3_x_order (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N)
    (H_EC : 1 ≤ Ec) (H_EX : 1 ≤ Ex) (H_FWD_POS : 1 ≤ wo + P.Lo.lo + Dl) {i : Nat} (hi : i < 3) :
    ∀ j, P.ξ i j < rx (P.XA i) (P.κ i) j ∧ rx (P.XA i) (P.κ i) j < P.ξ i (j + 1) := by
  have EX : ∀ j, P.E j < P.XA i j := fun j => by
    have := mn3_chain hE hR Cs S hN H_EC H_FWD_POS j
    have := mn3_ζ_le_XA (P := P) i j
    omega
  apply order_of_steps
  · intro m; rw [rx_e]; have := mn3_x_le_E hE hi m 0 (by omega); have := EX (2 * P.κ i m)
    simp only [Nat.add_zero] at *; omega
  · intro m; rw [rx_e]; have := Cs.H_XC_FALL i hi m; omega
  · intro m; rw [rx_o]; have := mn3_x_le_E hE hi m 1 (by omega); have := EX (2 * P.κ i m + 1); omega
  · intro m; rw [rx_o]; have := Cs.H_XC_RISE i hi m; omega

/-- **The packaged `bdc_muxn3` contract (C's interface, from B's theorems).**

From exactly `muxn3_ok_static`'s hypotheses (gates with REAL INITs, clean
partners, H_S_RANGE, `MN3Causal`, `MN3Static`, reset sequencing, the line's
flush) and, per bus bit `n < W`, exactly `muxn3_data_hold_fall`'s (REAL LUT5
`32'hF0AA_CCF0` via `Gate`, `MN3DataEnv`, the hold-to-fall client contract
`MN3HoldF` (G3), `MN3DataStatic`), plus the named hypotheses below:
1. the output channel `cz` is a full `Port`;
2. each in_i_ack, on input `i`'s tokens, is a clean wire from time 0;
3. every input channel and the control channel interleave strictly;
4. C's `MuxNEv`, hence (`muxn_spec`) `OpProto ∧ OpData (muxnEq …)`.

Named hypotheses added: as `mux_contract` (`H_EC`, `H_EX ≥ 1`; `H_FWD_POS :
1 ≤ wo + Lo.lo + Dl`; reset quiet `H_QUIET_Z`, `H_QUIET_A` with `H_TZ`,
`H_TA`; the G2 identifications `hρc hρx hρz hαz hreqz hackz`; `H_SEL_VAL`:
B's index `sv k` = C's `sel (v cc k)`; the bus facts `H_BUS`, `H_X_VAL`,
`H_X_W`, `H_Z_TOKVAL`). `H_ES` is already in `MN3Causal`. -/
theorem muxn3_contract {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl R : Nat}
    {rst ctl za orj : Trace} {x xj cp s0p s1p sl sj j q jo ln ja zx a qa ak : Nat → Trace}
    (G : MN3Gates P rst ctl za x xj cp s0p s1p sl sj j q jo orj ln ja zx a qa ak)
    (V : MN3Env P rst ctl za x s0p s1p R) (Cs : MN3Causal P Wzc Ex Ec Es)
    (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl)
    (hRL : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R)
    (hRE : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.A i 0 ∧ R ≤ P.ZA i 0)
    (hFL : ∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2)))
    (hN : 1 ≤ P.N)
    -- data path, per bus bit `n < W` (`muxn3_data_hold_fall`'s hypotheses)
    {W : Nat} {s0d s1d : Trace} {sS sE : Nat → Nat} {Lsd : Nat}
    {d : Nat → Nat → Trace} {z : Nat → Trace} {dS dE : Nat → Nat → Nat → Nat}
    {xv : Nat → Nat → Nat → Bool} {sl0 sh0 sl1 sh1 Mz Hm Ld : Nat → Nat} {dl dh : Nat → Nat → Nat}
    (hz : ∀ n, n < W → Gate DM5 [(d n 2, dl n 2, dh n 2), (d n 1, dl n 1, dh n 1),
      (d n 0, dl n 0, dh n 0), (s0d, sl0 n, sh0 n), (s1d, sl1 n, sh1 n)] (z n))
    (hw : ∀ n, n < W → sl0 n ≤ sh0 n ∧ sl1 n ≤ sh1 n ∧ ∀ i, i < 3 → dl n i ≤ dh n i)
    (D : ∀ n, n < W → MN3DataEnv P Wzc s0d s1d (d n) sS sE (dS n) (dE n) (xv n) Lsd (Ld n))
    (F : ∀ n, n < W → MN3HoldF P (dE n))
    (SD : ∀ n, n < W → MN3DataStatic P Wzc wc ls wsj lj wo Dl (sl0 n) (sh0 n) (sl1 n) (sh1 n)
      (Mz n) (Hm n) Lsd (Ld n) (dl n) (dh n))
    -- positivity
    (H_EC : 1 ≤ Ec) (H_EX : 1 ≤ Ex) (H_FWD_POS : 1 ≤ wo + P.Lo.lo + Dl)
    -- reset quiet
    (H_QUIET_Z : ∀ t, t < ffT P.H P.Tp P.To P.N → ln P.N t = false)
    (H_TZ : ffT P.H P.Tp P.To P.N ≤ P.Z 0)
    (H_QUIET_A : ∀ i, i < 3 → ∀ t, t < P.Ta i → ak i t = false)
    (H_TA : ∀ i, i < 3 → P.Ta i ≤ P.XA i (2 * P.κ i 0))
    -- C's side and the identifications
    {C : Type} {ch : C → Chan} {ρ α v : C → Nat → Nat} {sel : Nat → Nat} {cc : C} {cxs : Nat → C}
    {cz : C}
    (hρc : ρ cc = P.γ) (hρx : ∀ i, i < 3 → ρ (cxs i) = P.ξ i) (hρz : ρ cz = P.Z) (hαz : α cz = P.ζ)
    (hreqz : (ch cz).req = ln P.N) (hackz : (ch cz).ack = za)
    (H_SEL_VAL : ∀ k, P.sv k = sel (v cc k))
    (H_X_VAL : ∀ n i m, n < W → i < 3 → xv n i m = (v (cxs i) m).testBit n)
    (H_X_W : ∀ i m, i < 3 → v (cxs i) m < 2 ^ W)
    (H_BUS : ∀ t, (ch cz).dat t < 2 ^ W ∧ ∀ n, n < W → ((ch cz).dat t).testBit n = z n t)
    (H_Z_TOKVAL : ∀ k, v cz k = (ch cz).dat (P.Z (2 * k))) :
    Port (ch cz) (ρ cz) (α cz) (v cz) ∧
    (∀ i, i < 3 → Tok 0 (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true)) ∧
    (∀ i, i < 3 → ∀ j, P.ξ i j < rx (P.XA i) (P.κ i) j ∧ rx (P.XA i) (P.κ i) j < P.ξ i (j + 1)) ∧
    (∀ j, P.γ j < Wzc.fst (P.ζ j) ∧ Wzc.fst (P.ζ j) < P.γ (j + 1)) ∧
    MuxNEv ρ v sel cc cxs cz := by
  have hE := V.H_ENUM
  have hR := V.H_RANGE
  obtain ⟨_, hzt, hak⟩ := muxn3_ok_static G V Cs S hRL hRE hFL hN
  have hc := mn3_chain hE hR Cs S hN H_EC H_FWD_POS
  have ox : ∀ i, i < 3 → _ := fun i hi => mn3_x_order hE hR Cs S hN H_EC H_EX H_FWD_POS hi
  have hγ := Cs.H_POS
  let mval : Nat → Nat := fun k => v (cxs (P.sv k)) (idx (P.κ (P.sv k)) k)
  have hdat : ∀ k t, P.Z (2 * k) ≤ t → t < P.ζ (2 * k + 1) → (ch cz).dat t = mval k := by
    intro k t h1 h2
    have hb : ∀ n, n < W → ((ch cz).dat t).testBit n = (mval k).testBit n := by
      intro n hn
      have hzv := muxn3_data_hold_fall (hz n hn) (hw n hn) hE hR Cs S hN (D n hn) (F n hn) (SD n hn)
        k t (by omega) (by omega)
      rw [(H_BUS t).2 n hn, hzv]
      exact H_X_VAL n _ _ hn (hR k)
    exact bus_eq (H_BUS t).1 (H_X_W _ _ (hR k)) hb (fun _ _ => rfl)
  have hvz : ∀ k, v cz k = mval k := fun k => by
    rw [H_Z_TOKVAL k]
    have := hc (2 * k); have := hc (2 * k + 1)
    exact hdat k _ (Nat.le_refl _) (by omega)
  refine ⟨?_, fun i hi => ?_, ox, fun j => ⟨(hc j).2.2.2.2.1, (hc j).2.2.2.2.2⟩, ?_⟩
  · -- the output port
    rw [hρz, hαz]
    refine ⟨?_, ?_, ?_, fun j => (hc j).2.2.1, fun j => (hc j).2.2.2.1, fun k t h1 h2 => ?_⟩
    · rw [hreqz]
      have hs : Strict P.Z := fun j => Nat.lt_trans (hc j).2.2.1 (hc j).2.2.2.1
      exact tok_from0 hzt H_QUIET_Z H_TZ (fun j => (Strict.le_iff hs).2 (Nat.zero_le j))
    · rw [hackz]; exact V.H_ZA
    · have := (hc 0).1; have := (hc 0).2.1; have := hγ 0; omega
    · rw [hdat k t h1 h2, hvz]
  · exact tok_from0 (hak i hi).2 (H_QUIET_A i hi) (by rw [rx_0]; exact H_TA i hi)
      (first_le_of_order (ox i hi))
  · -- C's event contract
    refine ⟨?_, fun k => ?_, fun k => by rw [← H_SEL_VAL]; exact hR k, fun k => ?_⟩
    · rw [hρc]; exact fun j => Nat.lt_trans (hc j).2.2.2.2.1 (hc j).2.2.2.2.2
    · rw [hρc, hρz]; have := hc (2 * k); omega
    · have hv := hR k
      have hg : P.g (P.sv k) k = true := by unfold MN3Run.g; simp
      have c1 : cnt (fun i => sel (v cc i) == sel (v cc k)) k = cnt (P.g (P.sv k)) k :=
        cnt_congr_lt k fun i _ => by
          rw [← H_SEL_VAL, ← H_SEL_VAL]; unfold MN3Run.g
          cases h : (P.sv i == P.sv k) <;> simp_all
      rw [c1, ← H_SEL_VAL, hvz, hρz, hρx _ hv, ← idx_cnt (hE _ hv) hg]
      refine ⟨?_, rfl⟩
      have hm := κ_idx (hE _ hv) hg
      have := mn3_x_le_E hE hv (idx (P.κ (P.sv k)) k) 0 (by omega)
      rw [Nat.add_zero, Nat.add_zero, hm] at this
      have := (hc (2 * k)).2.1; omega

end mn3

/-! ## Non-vacuity: both contracts on the unit-delay witness runs

Every hypothesis of `mux_contract` (resp. `muxn3_contract`) is discharged on
probe Lt's unit-delay mux run (`OpsTimed.MuxWit`) with G3's hold-to-fall data
(`OpsHold.MuxHoldWit`), resp. probe M3's 3-way run (`MuxN3Timed.Mn3Wit`,
`OpsHold.Mn3HoldWit`), with a 1-bit bus (`W = 1`) and C's channels named by
`Nat` (0 = ctl, 1/2 = inputs (3-way: 0..2 shifted to 1..3), last = output).
The control side and the data side read DIFFERENT select drivers in the 2-way
witness (`sx` at the joins, `sF` at the datamux); the theorem's hypotheses do
not link them, which is itself a gap (see notes). -/

/-- One bit as a value. -/
def b2 (b : Bool) : Nat := if b then 1 else 0

theorem b2_lt (b : Bool) : b2 b < 2 ^ 1 := by cases b <;> decide
theorem b2_bit (b : Bool) : (b2 b).testBit 0 = b := by cases b <;> decide

namespace MuxContractWit
open Formal.Cells.OpsTimed.MuxWit
open Formal.Cells.OpsHold.MuxHoldWit

def wch : Nat → Chan
  | 3 => ⟨zr, za, fun t => b2 (zF t)⟩
  | _ => ⟨fun _ => false, fun _ => false, fun _ => 0⟩
def wρ : Nat → Nat → Nat
  | 0 => run.γ
  | 1 => run.ξ
  | 2 => run.η
  | _ => run.Z
def wα : Nat → Nat → Nat := fun _ => run.ζ
def wv : Nat → Nat → Nat
  | 0 => fun k => b2 (svW k)
  | 1 => fun m => b2 (xvW m)
  | 2 => fun m => b2 (yvW m)
  | _ => fun k => b2 (zF (run.Z (2 * k)))
def wsel (n : Nat) : Bool := n == 1

set_option maxRecDepth 4000 in
/-- **Non-vacuity of `mux_contract`.** -/
theorem witness : Port (wch 3) (wρ 3) (wα 3) (wv 3) ∧ MuxEv wρ wv wsel 0 1 2 3 := by
  have h := mux_contract (W := 1) (a := fun _ => xd) (b := fun _ => yd) (z := fun _ => zF)
    (xS := fun _ m => 36 * m) (xE := fun _ m => 36 * m + 35)
    (yS := fun _ m => 36 * m + 18) (yE := fun _ m => 36 * m + 53)
    (xv := fun _ => xvW) (yv := fun _ => yvW)
    (slo := fun _ => 1) (shi := fun _ => 1) (alo := fun _ => 1) (ahi := fun _ => 1)
    (blo := fun _ => 1) (bhi := fun _ => 1) (Mz := fun _ => 0) (Lx := fun _ => 4) (Ly := fun _ => 4)
    (ch := wch) (ρ := wρ) (α := wα) (v := wv) (sel := wsel) (cc := 0) (cx := 1) (cy := 2) (cz := 3)
    gates env causal static (by decide) (by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [Xp_eq]; omega
      · rw [D0_eq]; omega
      · rw [Yp_eq]; omega
      · rw [D1_eq]; omega
      · rw [A0_eq, E_eq]; omega
      · rw [(ZA_eq 0).1]; omega
      · rw [A1_eq, E_eq]; omega
      · rw [(ZA_eq 0).2]; omega)
    (fun _ _ => zF_rel) (fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ _ => data_env) (fun _ _ => hold_fall) (fun _ _ => data_static)
    (Nat.le_refl 1) (Nat.le_refl 1) (Nat.le_refl 1) (Nat.le_refl 1) (by decide)
    (by decide) (by rw [Z_eq, E_eq]; decide)
    (by decide) (by rw [(XA_eq _).1]; decide)
    (by decide) (by rw [(XA_eq _).2]; decide)
    rfl rfl rfl rfl rfl rfl rfl
    (fun k => by show svW k = (b2 (svW k) == 1); cases svW k <;> rfl)
    (fun n m hn => by
      obtain rfl : n = 0 := by omega
      exact (b2_bit _).symm)
    (fun n m hn => by
      obtain rfl : n = 0 := by omega
      exact (b2_bit _).symm)
    (fun m => b2_lt _) (fun m => b2_lt _)
    (fun t => ⟨b2_lt _, fun n hn => by obtain rfl : n = 0 := by omega
                                       exact b2_bit _⟩)
    (fun k => rfl)
  exact ⟨h.1, h.2.2.2.2.2.2⟩

set_option maxRecDepth 4000 in
/-- Not degenerate: the output tokens 0..3 (x, y, x, y) carry 1, 0, 0, 1. -/
theorem witness_values : wv 3 0 = 1 ∧ wv 3 1 = 0 ∧ wv 3 2 = 0 ∧ wv 3 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (show b2 (zF (run.Z _)) = _; rw [Z_eq, E_eq]; decide)

end MuxContractWit

namespace Mn3ContractWit
open Formal.Cells.MuxN3Timed Formal.Cells.MuxN3Timed.Mn3Wit
open Formal.Cells.OpsHold.Mn3HoldWit

def wch : Nat → Chan
  | 4 => ⟨line run.N, za, fun t => b2 (zW t)⟩
  | _ => ⟨fun _ => false, fun _ => false, fun _ => 0⟩
def wρ : Nat → Nat → Nat
  | 0 => run.γ
  | 1 => run.ξ 0
  | 2 => run.ξ 1
  | 3 => run.ξ 2
  | _ => run.Z
def wα : Nat → Nat → Nat := fun _ => run.ζ
def wv : Nat → Nat → Nat
  | 0 => fun k => svW k
  | 1 => fun m => b2 (xvW 0 m)
  | 2 => fun m => b2 (xvW 1 m)
  | 3 => fun m => b2 (xvW 2 m)
  | _ => fun k => b2 (zW (run.Z (2 * k)))

set_option maxRecDepth 100000 in
/-- **Non-vacuity of `muxn3_contract`.** -/
theorem witness : Port (wch 4) (wρ 4) (wα 4) (wv 4) ∧ MuxNEv wρ wv (fun n => n) 0 (fun i => i + 1) 4 := by
  have h := muxn3_contract (W := 1) (d := fun _ => dW) (z := fun _ => zW)
    (dS := fun _ i m => 60 * m + 20 * i + 10) (dE := fun _ i m => 60 * m + 20 * i + 69)
    (xv := fun _ => xvW) (sl0 := fun _ => 1) (sh0 := fun _ => 1) (sl1 := fun _ => 1)
    (sh1 := fun _ => 1) (Mz := fun _ => 0) (Hm := fun _ => 2) (Ld := fun _ => 0)
    (dl := fun _ _ => 1) (dh := fun _ _ => 1)
    (ch := wch) (ρ := wρ) (α := wα) (v := wv) (sel := fun n => n) (cc := 0) (cxs := fun i => i + 1)
    (cz := 4)
    gates env causal static
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)
    (fun i _ => ⟨by rw [Xp_eq]; omega, by rw [D_eq]; omega, by rw [A_eq, E_eq]; omega,
      by rw [ZA_eq]; omega⟩)
    (fun i h1 h2 => by have : (1 : Nat) ≤ i := h1; have : i < 1 := h2; omega)
    (Nat.le_refl 1)
    (fun _ _ => zW_gate) (fun _ _ => ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => Nat.le_refl _⟩)
    (fun _ _ => data_env) (fun _ _ => hold_fall) (fun _ _ => data_static)
    (Nat.le_refl 1) (Nat.le_refl 1) (by decide)
    (by decide) (by rw [Z_eq, E_eq]; decide)
    (fun i hi => by
      obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      all_goals decide)
    (fun i hi => by rw [XA_eq]; show 1 + 1 ≤ 20 * (2 * (3 * 0 + i) / 2) + 39 + 10 * (2 * (3 * 0 + i) % 2); omega)
    rfl (fun i hi => by obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
                        all_goals rfl) rfl rfl rfl rfl
    (fun k => rfl)
    (fun n i m hn hi => by
      obtain rfl : n = 0 := by omega
      obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      all_goals exact (b2_bit _).symm)
    (fun i m hi => by
      obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      all_goals exact b2_lt _)
    (fun t => ⟨b2_lt _, fun n hn => by obtain rfl : n = 0 := by omega
                                       exact b2_bit _⟩)
    (fun k => rfl)
  exact ⟨h.1, h.2.2.2.2⟩

set_option maxRecDepth 100000 in
/-- Not degenerate: output tokens 0..3 (inputs 0, 1, 2, 0) carry 1, 0, 1, 0. -/
theorem witness_values : wv 4 0 = 1 ∧ wv 4 1 = 0 ∧ wv 4 2 = 1 ∧ wv 4 3 = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (show b2 (zW (run.Z _)) = _; rw [Z_eq, E_eq]; decide)

end Mn3ContractWit

end Formal.Cells.Contracts
