import Formal.Cells.Necessity4Mux

/-!
# Necessity6Mux: the uj1 boundary of `bd_mux.uj1_env_latency_req_max`

Probe Bnx6 (shard B). Necessity4Mux proved the max form of the join env
latency through the client sufficient for BOTH joins (`mux_ok_staticN`), and
necessary at the boundary on the uj0 side only (`fail10`, `claimX1_false`).
The JSON row `bd_mux.uj1_env_latency_req_max` stayed `sufficient` because the
symmetric uj1 run was not built. This file builds it.

    S_J1_YR : Lj1.hi + wj1h ≤ Lj1.lo + max W1y.lo (W1o.lo + Lor.lo + Dz.lo + Es + Wzy.lo)
                              + Lya.lo + Wya.lo + Ey + Wy.lo + s1

## Result

* `ClaimY s1`: `mux_ok_staticN` with `S_J1_YR` weakened by `s1`, every other
  hypothesis (gates, environment, causal partners, every other `MuxStaticN`
  field, reset sequencing) verbatim. `claimY0 : ClaimY 0` is the shipped
  theorem.
* `failY10`, `claimY1_false : ¬ ClaimY 1`: Necessity4Mux's run family
  (`N4.run`: unit LUTs and wires, tokens alternating x / y, x and y clients
  tight `Ex = Ey = 1`, control sender `Ec = 6`, server `Es = 1`) with uj0's
  feedback net back to 1 tick and **uj1's** feedback net 10 ticks
  (`N6.run 10`). Every `MuxStaticN … 0 1` field holds, `S_J1_YR` itself
  fails by exactly one (`11 = 10 + 1`), reset sequencing holds, and the
  conclusion fails: j1 is 0 at 58 inside its token-1 window
  `[E 2, E 3) = [48, 61)` (y_req's fall reaches uj1 at 57, one tick before
  the 10-tick net shows j1's rise), and z_req is 0 at 61 inside its window
  `[Z 2, Z 3) = [51, 64)`. In this run the max is taken by the z_ack branch
  (`5 > W1y.lo = 1`).
* `passY9`: the same family at 9 ticks meets every hypothesis (S_J1_YR with
  equality) and `mux_ok`'s conclusion: the boundary is between 9 and 10.

So `bd_mux.uj1_env_latency_req_max` is **sufficient + necessary_at_boundary**
(one parameter point, binary `≤` form; the JSON carries the strict `+1`, so
the refuted point is 2 ticks from the JSON form, as for the uj0 row).

## Assumed / proved / NOT covered

Assumed: OpsTimedMux's model (lumped FIFO LUT arcs, window wires, FIFO line,
port-level causal partners with minimum latencies), real INITs of
uj0 / uj1 / uor / bd_c2.
Proved: as above (real INITs, every gate relation for all `t`).
NOT covered: an iff over the box (one point); per-pin LUT arcs; the strict
`+1` (Kleene X window) of the JSON form.
-/

namespace Formal.Cells.Necessity6Mux
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B)
open Formal.Cells.Necessity4Mux

/-- The claim at slack `s1` on the y branch: `mux_ok_staticN` with
`S_J1_YR` weakened by `s1`, every other hypothesis verbatim. -/
def ClaimY (s1 : Nat) : Prop :=
  ∀ (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo R : Nat)
    (rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak : Trace),
    MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak →
    MuxEnv P rst x y ctl za sx0 sx1 R → MuxCausal P Wzc Ex Ey Ec Es →
    MuxStaticN P Wzc Ex Ey Ec Es lj wc wo 0 s1 → MuxRst P R → MuxConcl P j0 j1 zr xak yak

theorem claimY0 : ClaimY 0 := by
  intro P Wzc Ex Ey Ec Es lj wc wo R rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x
    j1y zx zy xa qa ya qb xak yak G V Cs S hR
  exact mux_ok_staticN G V Cs S hR

namespace N6
open N4 (rst x y ctl za sx xj yj cj zx rst_hi rst_lo)

/-- `N4.run` with uj0's feedback net 1 tick and uj1's `W` ticks. -/
def run (W : Nat) : MuxRun := { N4.run 1 with wj1l := W, wj1h := W }

/-- uj0 with a 1-tick feedback net. -/
def j0 : Nat → Bool
  | 0 => false
  | 1 => j0B (xj 0) (cj 0) (sx 0) false (rst 0)
  | t + 2 => j0B (xj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j0 t) (rst (t + 1))
def q0 (t : Nat) : Bool := j0 (t - 1)
/-- uj1's feedback pin: j1 through the `W`-tick net. -/
def q1 (W : Nat) (J : Trace) (t : Nat) : Bool := J (t - W)
def e0 (t : Nat) : Bool := j0 (t - 1)
def e1 (J : Trace) (t : Nat) : Bool := J (t - 1)
def ei (J : Trace) (t : Nat) : Bool := or2B (e0 (t - 1)) (e1 J (t - 1))
def zr (J : Trace) (t : Nat) : Bool := ei J (t - 1)
def j0x (t : Nat) : Bool := j0 (t - 1)
def j1y (J : Trace) (t : Nat) : Bool := J (t - 1)
def xa : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x 0) (zx 0) false (rst 0)
  | t + 2 => c2B (j0x (t + 1)) (zx (t + 1)) (xa t) (rst (t + 1))
def qa (t : Nat) : Bool := xa (t - 1)
def ya (J : Trace) : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y J 0) (zx 0) false (rst 0)
  | t + 2 => c2B (j1y J (t + 1)) (zx (t + 1)) (ya J t) (rst (t + 1))
def qb (J : Trace) (t : Nat) : Bool := ya J (t - 1)
def xak (t : Nat) : Bool := xa (t - 1)
def yak (J : Trace) (t : Nat) : Bool := ya J (t - 1)

/-- uj1's gate relation through a `W`-tick feedback net. -/
def JoinEq1 (W : Nat) (J : Trace) : Prop :=
  ∀ t, 1 ≤ t → J t = j1B (yj (t - 1)) (cj (t - 1)) (sx (t - 1)) (J (t - 1 - W)) (rst (t - 1))

/-- uj1 with a 9-tick feedback net (loop 10). -/
def j1p : Nat → Bool
  | t + 10 => j1B (yj (t + 9)) (cj (t + 9)) (sx (t + 9)) (j1p t) (rst (t + 9))
  | _ => false
/-- uj1 with a 10-tick feedback net (loop 11). -/
def j1f : Nat → Bool
  | t + 11 => j1B (yj (t + 10)) (cj (t + 10)) (sx (t + 10)) (j1f t) (rst (t + 10))
  | _ => false

theorem j1p_eq : JoinEq1 9 j1p := by
  intro t ht
  match t, ht with
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | t + 10, _ => rfl

theorem j1f_eq : JoinEq1 10 j1f := by
  intro t ht
  match t, ht with
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | t + 11, _ => rfl

theorem gates (W : Nat) (J : Trace) (hJ : JoinEq1 W J) :
    MuxGates (run W) rst x y ctl za xj yj cj cj sx sx j0 q0 J (q1 W J) e0 (e1 J) (ei J) (zr J)
      j0x (j1y J) zx zx xa qa (ya J) (qb J) xak (yak J) where
  H_WX _ _ := rfl
  H_WY _ _ := rfl
  H_WC0 _ _ := rfl
  H_WC1 _ _ := rfl
  H_UJ0 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ0_FB := win11 (fun _ _ => rfl)
  H_UJ0_POS := Nat.le_of_ble_eq_true rfl
  H_UJ1 t ht := hJ t ht
  H_UJ1_FB := fun t ht => by
    have h : W ≤ t := ht
    exact ⟨t - W, by show t ≤ t - W + W; omega, by show t - W + W ≤ t; omega, rfl⟩
  H_UJ1_POS := by show 1 ≤ 1 + W; omega
  H_W0O _ _ := rfl
  H_W1O _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_W0X _ _ := rfl
  H_W1Y _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UXA_FB := win11 (fun _ _ => rfl)
  H_UXA_POS := Nat.le_of_ble_eq_true rfl
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := Nat.le_of_ble_eq_true rfl
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

section closed
variable (W : Nat)

/-- The event times of `run W` are those of `N4.run 1` (the feedback nets
enter no event time). -/
theorem E_eq (j : Nat) : (run W).E j = 26 * (j / 2) + 22 + 13 * (j % 2) := N4.E_eq 1 j
theorem Z_eq (j : Nat) : (run W).Z j = (run W).E j + 3 := N4.Z_eq 1 j

theorem env : MuxEnv (run W) rst x y ctl za sx sx 12 :=
  ⟨(N4.env 1).H_RST_HI, (N4.env 1).H_RST_LO, (N4.env 1).H_X, (N4.env 1).H_Y, (N4.env 1).H_CTL,
    (N4.env 1).H_ZA, (N4.env 1).H_ENUM0, (N4.env 1).H_ENUM1, (N4.env 1).H_S_PIN0,
    (N4.env 1).H_S_PIN1⟩

theorem causal : MuxCausal (run W) uW 1 1 6 1 :=
  ⟨(N4.causal 1).H_XC_FALL, (N4.causal 1).H_XC_RISE, (N4.causal 1).H_YC_FALL,
    (N4.causal 1).H_YC_RISE, (N4.causal 1).H_CTL_C, (N4.causal 1).H_SRV, (N4.causal 1).H_POS⟩

theorem rstOK (hW : W ≤ 11) : MuxRst (run W) 12 := by
  have h := N4.rstOK 1 (by omega)
  obtain ⟨⟨a1, a2, a3, a4, a5, _, a7, a8, a9, a10, a11, a12⟩, b⟩ := h
  exact ⟨⟨a1, a2, a3, a4, a5, by show 1 + W ≤ 12; omega, a7, a8, a9, a10, a11, a12⟩, b⟩

/-- Every max-form static obligation, `S_J1_YR` at slack `s1`, holds as long
as `1 + W ≤ 10 + s1` (and `W ≤ 12` for `S_J1_C`). -/
theorem staticN (s1 : Nat) (h1 : 1 + W ≤ 10 + s1) (h2 : W ≤ 12) :
    MuxStaticN (run W) uW 1 1 6 1 1 1 1 0 s1 where
  H_LJ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WC := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WO := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_J0_XR := Nat.le_of_ble_eq_true rfl
  S_J1_YR := by show 1 + W ≤ 1 + max 1 (1 + 1 + 1 + 1 + 1) + 1 + 1 + 1 + 1 + s1; omega
  S_J0_C := Nat.le_of_ble_eq_true rfl
  S_J1_C := by show 1 + W ≤ 1 + (1 + 1 + 1 + 1) + 1 + 6 + 1; omega
  S_OR := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_XA_FORK := Nat.le_of_ble_eq_true rfl
  S_YA_FORK := Nat.le_of_ble_eq_true rfl
  S_XA_RTZ := Nat.le_of_ble_eq_true rfl
  S_YA_RTZ := Nat.le_of_ble_eq_true rfl
  S_XA_J := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_YA_J := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

end closed
end N6

open N6

/-- **Next to the boundary the shipped theorem applies.** With a 9-tick uj1
net, `S_J1_YR` holds with equality and the run meets `mux_ok`'s whole
conclusion; j1 rises at 48 and holds until 61. -/
theorem passY9 :
    (N6.run 9).Lj1.hi + (N6.run 9).wj1h = (N6.run 9).Lj1.lo +
      max (N6.run 9).W1y.lo ((N6.run 9).W1o.lo + (N6.run 9).Lor.lo + (N6.run 9).Dz.lo + 1 + (N6.run 9).Wzy.lo) +
      (N6.run 9).Lya.lo + (N6.run 9).Wya.lo + 1 + (N6.run 9).Wy.lo ∧
    MuxConcl (N6.run 9) N6.j0 j1p (N6.zr j1p) N6.xak (N6.yak j1p) ∧
    j1p 47 = false ∧ j1p 48 = true ∧ j1p 60 = true ∧ j1p 61 = false ∧ N6.yak j1p 56 = true := by
  refine ⟨by decide, mux_ok_staticN (N6.gates 9 j1p j1p_eq) (N6.env 9) (N6.causal 9)
    (N6.staticN 9 0 (by omega) (by omega)) (N6.rstOK 9 (by omega)), ?_⟩
  decide +kernel

/-- **The max form is necessary at the boundary on the uj1 side** (its z_ack
branch). With a 10-tick uj1 feedback net: every `MuxStaticN … 0 1` field
holds (S_J1_YR weakened by one tick), S_J1_YR itself fails by exactly one
(`11 = 10 + 1`), the max is the z_ack branch, reset sequencing holds, and the
conclusion fails: j1 is 0 at 58 inside `[E 2, E 3) = [48, 61)` and z_req is 0
at 61 inside `[Z 2, Z 3) = [51, 64)`. -/
theorem failY10 :
    MuxStaticN (N6.run 10) uW 1 1 6 1 1 1 1 0 1 ∧
    (N6.run 10).Lj1.hi + (N6.run 10).wj1h = (N6.run 10).Lj1.lo +
      max (N6.run 10).W1y.lo ((N6.run 10).W1o.lo + (N6.run 10).Lor.lo + (N6.run 10).Dz.lo + 1 + (N6.run 10).Wzy.lo) +
      (N6.run 10).Lya.lo + (N6.run 10).Wya.lo + 1 + (N6.run 10).Wy.lo + 1 ∧
    (N6.run 10).W1y.lo < (N6.run 10).W1o.lo + (N6.run 10).Lor.lo + (N6.run 10).Dz.lo + 1 + (N6.run 10).Wzy.lo ∧
    MuxRst (N6.run 10) 12 ∧
    (N6.run 10).E 2 = 48 ∧ (N6.run 10).E 3 = 61 ∧ (N6.run 10).Z 2 = 51 ∧ (N6.run 10).Z 3 = 64 ∧
    j1f 47 = false ∧ j1f 48 = true ∧ N4.yj 57 = false ∧
    j1f 58 = false ∧ N6.zr j1f 61 = false ∧
    ¬ Tok (N6.run 10).Lj1.hi j1f (N6.run 10).E (N6.run 10).sv ∧
    ¬ Tok (N6.run 10).Tz (N6.zr j1f) (N6.run 10).Z (fun _ => true) ∧
    ¬ MuxConcl (N6.run 10) N6.j0 j1f (N6.zr j1f) N6.xak (N6.yak j1f) := by
  have hE2 : (N6.run 10).E 2 = 48 := by rw [N6.E_eq]
  have hE3 : (N6.run 10).E 3 = 61 := by rw [N6.E_eq]
  have hZ2 : (N6.run 10).Z 2 = 51 := by rw [N6.Z_eq, N6.E_eq]
  have hZ3 : (N6.run 10).Z 3 = 64 := by rw [N6.Z_eq, N6.E_eq]
  have v : j1f 47 = false ∧ j1f 48 = true ∧ N4.yj 57 = false ∧ j1f 58 = false ∧
      N6.zr j1f 61 = false := by decide +kernel
  have nj : ¬ Tok (N6.run 10).Lj1.hi j1f (N6.run 10).E (N6.run 10).sv := by
    intro h
    have := h.hi 1 58 (by decide) (by rw [show 2 * 1 = 2 from rfl, hE2]; omega)
      (by rw [show 2 * 1 + 1 = 3 from rfl, hE3]; omega)
    rw [v.2.2.2.1] at this; exact absurd this (by decide)
  have nz : ¬ Tok (N6.run 10).Tz (N6.zr j1f) (N6.run 10).Z (fun _ => true) := by
    intro h
    have := h.hi 1 61 (by decide) (by rw [show 2 * 1 = 2 from rfl, hZ2]; omega)
      (by rw [show 2 * 1 + 1 = 3 from rfl, hZ3]; omega)
    rw [v.2.2.2.2] at this; exact absurd this (by decide)
  exact ⟨N6.staticN 10 1 (by omega) (by omega), by decide, by decide, N6.rstOK 10 (by omega),
    hE2, hE3, hZ2, hZ3, v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2, nj, nz, fun h => nz h.2.2.1⟩

/-- The counter-run meets every other hypothesis of `mux_ok_staticN`, so
`ClaimY 1` is false: weakening the uj1 max form by one tick is unsound. -/
theorem claimY1_false : ¬ ClaimY 1 := by
  intro h
  exact failY10.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (h (N6.run 10) uW 1 1 6 1 1 1 1 12 N4.rst N4.x N4.y N4.ctl N4.za N4.xj N4.yj N4.cj N4.cj N4.sx N4.sx
      N6.j0 N6.q0 j1f (N6.q1 10 j1f) N6.e0 (N6.e1 j1f) (N6.ei j1f) (N6.zr j1f) N6.j0x (N6.j1y j1f)
      N4.zx N4.zx N6.xa N6.qa (N6.ya j1f) (N6.qb j1f) N6.xak (N6.yak j1f)
      (N6.gates 10 j1f j1f_eq) (N6.env 10) (N6.causal 10) failY10.1 (N6.rstOK 10 (by omega)))

end Formal.Cells.Necessity6Mux
