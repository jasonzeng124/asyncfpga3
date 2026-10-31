import Formal.Cells.Necessity7Mux

/-!
# Necessity7MuxRuns: the bd_mux runs for `isochronic_forks` and `S_XA_J.1`

Probe Bnx7 (shard B). Runs for the gate-aware static form `MuxStaticG`
(`Necessity7Mux`). Every run: real INITs of uj0 / uj1 / uor / bd_c2, every
gate relation for ALL `t` (each trace defined by structural recursion on its
own gate equation), an open-loop periodic environment (control tokens
alternate x, y; period 23 per control token), reset high on `[0, 12)`,
partners `Ex = Ey = Ec = Es = 1`, `Wzc = uW`, every LUT and wire one tick
except the arc named. `Kc = Wzc.lo + Ec + wc + lj = 4`, `Kz = 4`.

* `RA.run d W`: the z_ack → uxa wire is `d` ticks (`Wzx = shift d`), the
  j0 → uxa wire is `W`. The x and y clients drop their requests 15 ticks
  after ctl_req rises (slack), the server's fall answer has slack, so the
  schedule does not depend on `d`.
  - `RA.run 5 uW` (`passA5`): `S_XA_FORK` fails (`5 + 2 ≤ 5` is false), every
    `MuxStaticG` field holds, `S_XA_SEQ` with equality (`5 ≤ 5`): the run
    meets `mux_ok_gs` and so `mux_ok`'s whole conclusion. At the y → x
    hand-over z_ack's fall and j0's rise reach uxa at the same tick (69).
  - `RA.run 6 uW` (`failSEQ6`, `claimSEQ1_false`): `S_XA_SEQ` off by exactly
    one (`6 = 5 + 1`), every other field holds; z_ack (still high from the
    y token) and j0 (the x token) overlap at uxa at 69, uxa fires inside the
    y token: x_ack is 1 at 71, in `[XA 2, XA 3) = [57, 72)`.
* `RN.run w`: uxa's feedback net is `w` ticks; the clients are tight
  (`Ex = Ey = 1`, they drop 10 ticks after ctl_req rises).
  - `RN.run 5` (`passN5`): `S_XA_FORK` fails (`1 + 6 ≤ 5`), the left disjunct
    `S_XA_N` of `S_XA_R` holds with equality (`6 ≤ 6`): passes.
  - `RN.run 6` (`failR6`, `claimR1_false`): `S_XA_R` off by exactly one in
    BOTH disjuncts (`S_XA_N`: `7 = 6 + 1`; the fork pair fails by more), every
    other field holds; j0's fall (x_req dropped by the client) reaches uxa
    before uxa's 6-tick feedback shows x_ack's rise: x_ack is 0 at 35, in
    `[XA 0, XA 1) = [29, 44)`.
* `RB.run`: `RA`'s schedule with `Wzx = uW` and a j0 → uxa wire with
  rise / fall spread (1 tick on j0's rises, 8 on its falls, `Rx`).
  `passB` : `S_XA_J.1` fails (`8 + 2 ≤ 4 + 4 + 1` is false), every
  `MuxStaticG` field holds: passes.

All forms are the binary Lean `≤`.

## Assumed / proved / NOT covered

Assumed: OpsTimedMux's model, as in `Necessity7Mux`.
Proved: as above, each at one parameter point.
NOT covered: the uya mirrors (stated symmetrically in `MuxStaticG`, runs not
built); an iff over the box; the Kleene X `+1` of the JSON (the SEQ and N
boundaries are at the binary `≤`: the refuted point is one tick from the
binary form, the passing point is at equality).
-/

namespace Formal.Cells.Necessity7Mux
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B)
open Formal.Cells.Necessity4Mux (MuxConcl)

/-! ## 0. The weakened claims -/

/-- `MuxStaticG` with `S_XA_SEQ` weakened by `sq` and `S_XA_R` (both
disjuncts, every inequality) by `sr`. Every other field verbatim. -/
structure MuxStaticW (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo sq sr : Nat) : Prop where
  H_LJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo
  H_WC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo
  H_WO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo
  S_J0_X : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + P.W0x.lo + P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo
  S_J1_Y : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + P.W1y.lo + P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo
  S_J0_C : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc0.lo
  S_J1_C : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc1.lo
  S_XA_RTZ : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_RTZ : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_XA_J2 : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzx.lo
  S_YA_J2 : P.W1y.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzy.lo
  S_XA_R : P.Lxa.hi + P.wxah ≤ P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo + P.Lj0.lo + P.W0x.lo + sr ∨
    (P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo + sr ∧
     P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0x.lo + sr)
  S_YA_R : P.Lya.hi + P.wyah ≤ P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo + P.Lj1.lo + P.W1y.lo ∨
    (P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo ∧
     P.W1y.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1y.lo)
  S_XA_SEQ : P.Wzx.hi ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo + sq
  S_YA_SEQ : P.Wzy.hi ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo

theorem MuxStaticW.toG {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}
    (S : MuxStaticW P Wzc Ex Ey Ec Es lj wc wo 0 0) : MuxStaticG P Wzc Ex Ey Ec Es lj wc wo :=
  ⟨S.H_LJ, S.H_WC, S.H_WO, S.S_J0_X, S.S_J1_Y, S.S_J0_C, S.S_J1_C, S.S_XA_RTZ, S.S_YA_RTZ,
    S.S_XA_J2, S.S_YA_J2, S.S_XA_R, S.S_YA_R, S.S_XA_SEQ, S.S_YA_SEQ⟩

/-- The claim with `S_XA_SEQ` weakened by `s`: `mux_ok_gs`, every other
hypothesis verbatim. -/
def ClaimSEQ (s : Nat) : Prop :=
  ∀ (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo R : Nat)
    (rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak : Trace),
    MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak →
    MuxEnv P rst x y ctl za sx0 sx1 R → MuxCausal P Wzc Ex Ey Ec Es → 1 ≤ Es →
    MuxStaticW P Wzc Ex Ey Ec Es lj wc wo s 0 → MuxRstG P R → MuxConcl P j0 j1 zr xak yak

/-- The claim with `S_XA_R` weakened by `s`. -/
def ClaimR (s : Nat) : Prop :=
  ∀ (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo R : Nat)
    (rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak : Trace),
    MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak →
    MuxEnv P rst x y ctl za sx0 sx1 R → MuxCausal P Wzc Ex Ey Ec Es → 1 ≤ Es →
    MuxStaticW P Wzc Ex Ey Ec Es lj wc wo 0 s → MuxRstG P R → MuxConcl P j0 j1 zr xak yak

theorem claimSEQ0 : ClaimSEQ 0 := by
  intro P Wzc Ex Ey Ec Es lj wc wo R rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x
    j1y zx zy xa qa ya qb xak yak G V Cs hEs S hR
  exact mux_ok_gs G V Cs hEs S.toG hR

theorem claimR0 : ClaimR 0 := by
  intro P Wzc Ex Ey Ec Es lj wc wo R rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x
    j1y zx zy xa qa ya qb xak yak G V Cs hEs S hR
  exact mux_ok_gs G V Cs hEs S.toG hR

/-! ## 1. Family `RA`: a `d`-tick z_ack → uxa wire -/
namespace RA

def run (d : Nat) (W : Ret) : MuxRun where
  Wx := uW
  Wy := uW
  Wc0 := uW
  Wc1 := uW
  Lj0 := uW
  Lj1 := uW
  wj0l := 1
  wj0h := 1
  wj1l := 1
  wj1h := 1
  W0o := uW
  W1o := uW
  W0x := W
  W1y := uW
  Lor := uW
  Dz := uW
  Wzx := Ret.shift d
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := 1
  wxah := 1
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ξ j := 46 * (j / 2) + 17 + 18 * (j % 2)
  η j := 46 * (j / 2) + 40 + 18 * (j % 2)
  γ j := 23 * (j / 2) + 20 + 8 * (j % 2)
  ζ j := 23 * (j / 2) + 26 + 15 * (j % 2)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

def rst (t : Nat) : Bool := decide (t < 12)
theorem rst_hi : ∀ t, t < 12 → rst t = true := fun t h => by simp [rst, h]
theorem rst_lo : ∀ t, 12 ≤ t → rst t = false := fun t h => by simp [rst]; omega

-- environment
def x (t : Nat) : Bool := decide (17 ≤ t ∧ (t - 17) % 46 < 18)
def y (t : Nat) : Bool := decide (40 ≤ t ∧ (t - 40) % 46 < 18)
def ctl (t : Nat) : Bool := decide (20 ≤ t ∧ (t - 20) % 23 < 8)
def za (t : Nat) : Bool := decide (26 ≤ t ∧ (t - 26) % 23 < 15)
def sx (t : Nat) : Bool := svW ((t - 20) / 23)
-- the cell
def xj (t : Nat) : Bool := x (t - 1)
def yj (t : Nat) : Bool := y (t - 1)
def cj (t : Nat) : Bool := ctl (t - 1)
def j0 : Nat → Bool
  | 0 => false
  | 1 => j0B (xj 0) (cj 0) (sx 0) false (rst 0)
  | t + 2 => j0B (xj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j0 t) (rst (t + 1))
def q0 (t : Nat) : Bool := j0 (t - 1)
def j1 : Nat → Bool
  | 0 => false
  | 1 => j1B (yj 0) (cj 0) (sx 0) false (rst 0)
  | t + 2 => j1B (yj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j1 t) (rst (t + 1))
def q1 (t : Nat) : Bool := j1 (t - 1)
def e0 (t : Nat) : Bool := j0 (t - 1)
def e1 (t : Nat) : Bool := j1 (t - 1)
def ei (t : Nat) : Bool := or2B (e0 (t - 1)) (e1 (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
/-- j0 at uxa through the wire `W`. -/
def j0x (W : Ret) (t : Nat) : Bool := j0 (W.σ t)
def j1y (t : Nat) : Bool := j1 (t - 1)
/-- z_ack at uxa through the `d`-tick wire. -/
def zx (d : Nat) (t : Nat) : Bool := za (t - d)
def zy (t : Nat) : Bool := za (t - 1)
def xa (W : Ret) (d : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x W 0) (zx d 0) false (rst 0)
  | t + 2 => c2B (j0x W (t + 1)) (zx d (t + 1)) (xa W d t) (rst (t + 1))
def qa (W : Ret) (d : Nat) (t : Nat) : Bool := xa W d (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zy 0) false (rst 0)
  | t + 2 => c2B (j1y (t + 1)) (zy (t + 1)) (ya t) (rst (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (W : Ret) (d : Nat) (t : Nat) : Bool := xa W d (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates (d : Nat) (W : Ret) :
    MuxGates (run d W) rst x y ctl za xj yj cj cj sx sx j0 q0 j1 q1 e0 e1 ei zr
      (j0x W) j1y (zx d) zy (xa W d) (qa W d) ya qb (xak W d) yak where
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
  H_UJ1 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ1_FB := win11 (fun _ _ => rfl)
  H_UJ1_POS := Nat.le_of_ble_eq_true rfl
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
variable (d : Nat) (W : Ret)

theorem enum0 : Enum (fun k => !(run d W).sv k) (run d W).κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum (run d W).sv (run d W).κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

theorem Xp_eq (j : Nat) : (run d W).Xp j = 46 * (j / 2) + 18 + 18 * (j % 2) := by
  show uW.fst (46 * (j / 2) + 17 + 18 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : (run d W).Yp j = 46 * (j / 2) + 41 + 18 * (j % 2) := by
  show uW.fst (46 * (j / 2) + 40 + 18 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : (run d W).C0 j = 23 * (j / 2) + 21 + 8 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 20 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C1_eq (j : Nat) : (run d W).C1 j = 23 * (j / 2) + 21 + 8 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 20 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem D0_eq (j : Nat) : (run d W).D0 j = 46 * (j / 2) + 21 + 8 * (j % 2) := by
  show (run d W).C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [C0_eq]; omega
theorem D1_eq (j : Nat) : (run d W).D1 j = 46 * (j / 2) + 44 + 8 * (j % 2) := by
  show (run d W).C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C1_eq]; omega
theorem c0_eq (j : Nat) : (run d W).c0 j = 46 * (j / 2) + 21 + 15 * (j % 2) := by
  show max ((run d W).Xp j) ((run d W).D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : (run d W).c1 j = 46 * (j / 2) + 44 + 15 * (j % 2) := by
  show max ((run d W).Yp j) ((run d W).D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : (run d W).τ0 j = 46 * (j / 2) + 22 + 15 * (j % 2) := by
  show uW.fst ((run d W).c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : (run d W).τ1 j = 46 * (j / 2) + 45 + 15 * (j % 2) := by
  show uW.fst ((run d W).c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : (run d W).E j = 23 * (j / 2) + 22 + 15 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : (run d W).sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx (run d W).κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum0 d W) (j / 2 / 2)
      rw [show (run d W).κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega
  · have hs : (run d W).sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx (run d W).κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum1 d W) (j / 2 / 2)
      rw [show (run d W).κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega

theorem O0_eq (j : Nat) : (run d W).O0 j = (run d W).E j + 1 := by
  show uW.fst ((run d W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : (run d W).O1 j = (run d W).E j + 1 := by
  show uW.fst ((run d W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : (run d W).A1 j = (run d W).E j + 1 := by
  show uW.fst ((run d W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA0_eq (j : Nat) : (run d W).ZA0 j = 23 * (j / 2) + 26 + 15 * (j % 2) + d := by
  show (Ret.shift d).fst (23 * (j / 2) + 26 + 15 * (j % 2)) = _; rw [Ret.fst_shift _ _ (by omega)]
theorem ZA1_eq (j : Nat) : (run d W).ZA1 j = 23 * (j / 2) + 27 + 15 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 26 + 15 * (j % 2)) = _; rw [fuW _ (by omega)]; omega

theorem Z_eq (j : Nat) : (run d W).Z j = (run d W).E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show (run d W).Lor = uW from rfl, show (run d W).Dz = uW from rfl]
  have hE := E_eq d W j
  split
  · rw [O0_eq, fuW ((run d W).E j + 1) (by omega), fuW ((run d W).E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW ((run d W).E j + 1) (by omega), fuW ((run d W).E j + 1 + 1) (by omega)]

theorem YA_eq (j : Nat) : (run d W).YA j = 23 * (j / 2) + 29 + 15 * (j % 2) := by
  show uW.fst (uW.fst (max ((run d W).A1 j) ((run d W).ZA1 j))) = _
  rw [A1_eq, ZA1_eq, E_eq, show max (23 * (j / 2) + 22 + 15 * (j % 2) + 1) (23 * (j / 2) + 27 + 15 * (j % 2))
    = 23 * (j / 2) + 27 + 15 * (j % 2) by omega, fuW (23 * (j / 2) + 27 + 15 * (j % 2)) (by omega),
    fuW (23 * (j / 2) + 27 + 15 * (j % 2) + 1) (by omega)]; omega

theorem env : MuxEnv (run d W) rst x y ctl za sx sx 12 where
  H_RST_HI := rst_hi
  H_RST_LO := rst_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 46 * (0 / 2) + 17 + 18 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 46 * (2 * k / 2) + 17 + 18 * (2 * k % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 1) / 2) + 17 + 18 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 46 * ((2 * k + 1) / 2) + 17 + 18 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 2) / 2) + 17 + 18 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 46 * (0 / 2) + 40 + 18 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 46 * (2 * k / 2) + 40 + 18 * (2 * k % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 1) / 2) + 40 + 18 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 46 * ((2 * k + 1) / 2) + 40 + 18 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 2) / 2) + 40 + 18 * ((2 * k + 2) % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 23 * (0 / 2) + 20 + 8 * (0 % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : 23 * (2 * k / 2) + 20 + 8 * (2 * k % 2) ≤ t := h1
      have h2 : t < 23 * ((2 * k + 1) / 2) + 20 + 8 * ((2 * k + 1) % 2) := h2
      simp only [ctl, decide_eq_true_eq]; omega
    · have h1 : 23 * ((2 * k + 1) / 2) + 20 + 8 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 23 * ((2 * k + 2) / 2) + 20 + 8 * ((2 * k + 2) % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 23 * (0 / 2) + 26 + 15 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 23 * (2 * k / 2) + 26 + 15 * (2 * k % 2) ≤ t := h1
      have h2 : t < 23 * ((2 * k + 1) / 2) + 26 + 15 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 23 * ((2 * k + 1) / 2) + 26 + 15 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 23 * ((2 * k + 2) / 2) + 26 + 15 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_ENUM0 := enum0 d W
  H_ENUM1 := enum1 d W
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq] at h1 h2
    show svW ((t - 20) / 23) = svW k
    rw [show (t - 20) / 23 = k by omega]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq] at h1 h2
    show svW ((t - 20) / 23) = svW k
    rw [show (t - 20) / 23 = k by omega]

end closed

section uw
variable (d : Nat)

theorem A0_eq (j : Nat) : (run d uW).A0 j = (run d uW).E j + 1 := by
  show uW.fst ((run d uW).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]

theorem XA_eq (j : Nat) : (run d uW).XA j = 23 * (j / 2) + 28 + 15 * (j % 2) + d := by
  show uW.fst (uW.fst (max ((run d uW).A0 j) ((run d uW).ZA0 j))) = _
  rw [A0_eq, ZA0_eq, E_eq, show max (23 * (j / 2) + 22 + 15 * (j % 2) + 1)
    (23 * (j / 2) + 26 + 15 * (j % 2) + d) = 23 * (j / 2) + 26 + 15 * (j % 2) + d by omega,
    fuW (23 * (j / 2) + 26 + 15 * (j % 2) + d) (by omega),
    fuW (23 * (j / 2) + 26 + 15 * (j % 2) + d + 1) (by omega)]; omega

/-- The partners are causal (the control sender and the server's rise are
tight; the x client is tight at `d = 6`). -/
theorem causal (hd : d ≤ 6) : MuxCausal (run d uW) uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [XA_eq]; show _ ≤ 46 * ((2 * m + 1) / 2) + 17 + 18 * ((2 * m + 1) % 2)
    show 23 * (2 * (2 * m) / 2) + 28 + 15 * (2 * (2 * m) % 2) + d + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [XA_eq]; show _ ≤ 46 * ((2 * m + 2) / 2) + 17 + 18 * ((2 * m + 2) % 2)
    show 23 * ((2 * (2 * m) + 1) / 2) + 28 + 15 * ((2 * (2 * m) + 1) % 2) + d + 1 ≤ _; omega
  H_YC_FALL m := by
    rw [YA_eq]; show _ ≤ 46 * ((2 * m + 1) / 2) + 40 + 18 * ((2 * m + 1) % 2)
    show 23 * (2 * (2 * m + 1) / 2) + 29 + 15 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [YA_eq]; show _ ≤ 46 * ((2 * m + 2) / 2) + 40 + 18 * ((2 * m + 2) % 2)
    show 23 * ((2 * (2 * m + 1) + 1) / 2) + 29 + 15 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (23 * (j / 2) + 26 + 15 * (j % 2)) + 1 ≤ 23 * ((j + 1) / 2) + 20 + 8 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 23 * (j / 2) + 26 + 15 * (j % 2); omega
  H_POS j := by show 1 ≤ 23 * (j / 2) + 20 + 8 * (j % 2); omega

theorem rstOK (hd : d ≤ 12) : MuxRstG (run d uW) 12 := by
  have b : ∀ {a c : Nat}, Nat.ble a c = true → a ≤ c := fun h => Nat.le_of_ble_eq_true h
  refine ⟨⟨b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, by show d ≤ 12; omega,
    b rfl, b rfl, b rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [ZA0_eq]; omega
  · rw [ZA1_eq]; omega

/-- Every field holds; `S_XA_SEQ` needs `d ≤ 5 + sq`. -/
theorem staticW (sq : Nat) (h1 : d ≤ 5 + sq) : MuxStaticW (run d uW) uW 1 1 1 1 1 1 1 sq 0 where
  H_LJ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WC := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WO := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_J0_X := Nat.le_of_ble_eq_true rfl
  S_J1_Y := Nat.le_of_ble_eq_true rfl
  S_J0_C := Nat.le_of_ble_eq_true rfl
  S_J1_C := Nat.le_of_ble_eq_true rfl
  S_XA_RTZ := by show d + (1 + 1) ≤ d + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1); omega
  S_YA_RTZ := Nat.le_of_ble_eq_true rfl
  S_XA_J2 := by show 1 + (1 + 1) ≤ 2 * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + d; omega
  S_YA_J2 := Nat.le_of_ble_eq_true rfl
  S_XA_R := Or.inl (Nat.le_of_ble_eq_true rfl)
  S_YA_R := Or.inl (Nat.le_of_ble_eq_true rfl)
  S_XA_SEQ := by show d ≤ (1 + 1 + 1 + 1) + 1 + sq; omega
  S_YA_SEQ := Nat.le_of_ble_eq_true rfl

end uw
end RA

/-- **`S_XA_FORK` is not necessary** (row `bd_mux.isochronic_forks`). With a
5-tick z_ack → uxa wire the shipped `S_XA_FORK` fails (`5 + 2 ≤ 4 + 1` is
false; with the strict `+1` it fails by 3), `S_XA_SEQ` holds with equality,
every `MuxStaticG` field holds, and `mux_ok_gs` gives `mux_ok`'s whole
conclusion. At the y → x hand-over z_ack's fall and j0's rise reach uxa at
the same tick: z_ack at uxa is 1 at 68 and 0 at 69, j0 at uxa 0 at 68 and 1
at 69 (binary model: the equality is clean). -/
theorem passA5 :
    ¬ ((RA.run 5 uW).Wzx.hi + ((RA.run 5 uW).Lxa.hi + (RA.run 5 uW).wxah) ≤
        (uW.lo + 1 + 1 + 1) + (RA.run 5 uW).W0x.lo) ∧
    MuxStaticG (RA.run 5 uW) uW 1 1 1 1 1 1 1 ∧
    (RA.run 5 uW).Wzx.hi = (uW.lo + 1 + 1 + 1) + (RA.run 5 uW).W0x.lo ∧
    RA.zx 5 68 = true ∧ RA.zx 5 69 = false ∧ RA.j0x uW 68 = false ∧ RA.j0x uW 69 = true ∧
    RA.xak uW 5 30 = false ∧ RA.xak uW 5 40 = true ∧ RA.yak 55 = true ∧
    MuxConcl (RA.run 5 uW) RA.j0 RA.j1 RA.zr (RA.xak uW 5) RA.yak := by
  have S := (RA.staticW 5 0 (by omega)).toG
  refine ⟨by decide, S, rfl, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact mux_ok_gs (RA.gates 5 uW) (RA.env 5 uW) (RA.causal 5 (by omega)) (Nat.le_refl 1) S
    (RA.rstOK 5 (by omega))

/-- **`S_XA_SEQ` is necessary at the boundary.** With a 6-tick z_ack → uxa
wire every `MuxStaticW … 1 0` field holds (`S_XA_SEQ` weakened by one), the
unweakened `S_XA_SEQ` fails by exactly one (`6 = 5 + 1`), reset sequencing
holds, and the conclusion fails: z_ack's fall of the y token 1 reaches uxa
at 70, j0's rise of the x token 2 at 69; uxa sees both high at 69 and its
node rises at 70: x_ack is 1 at 71, in `[XA 2, XA 3) = [57, 72)` (y's
token), where `mux_ok` says it is 0. -/
theorem failSEQ6 :
    MuxStaticW (RA.run 6 uW) uW 1 1 1 1 1 1 1 1 0 ∧
    (RA.run 6 uW).Wzx.hi = (uW.lo + 1 + 1 + 1) + (RA.run 6 uW).W0x.lo + 1 ∧
    MuxRstG (RA.run 6 uW) 12 ∧
    (RA.run 6 uW).ZA0 3 = 70 ∧ (RA.run 6 uW).A0 4 = 69 ∧
    (RA.run 6 uW).XA 2 = 57 ∧ (RA.run 6 uW).XA 3 = 72 ∧
    RA.zx 6 69 = true ∧ RA.j0x uW 69 = true ∧ RA.xak uW 6 71 = true ∧
    ¬ Tok (RA.run 6 uW).Tx (RA.xak uW 6) (RA.run 6 uW).XA (fun k => !(RA.run 6 uW).sv k) ∧
    ¬ MuxConcl (RA.run 6 uW) RA.j0 RA.j1 RA.zr (RA.xak uW 6) RA.yak := by
  have hX2 : (RA.run 6 uW).XA 2 = 57 := by rw [RA.XA_eq]
  have hX3 : (RA.run 6 uW).XA 3 = 72 := by rw [RA.XA_eq]
  have v : RA.zx 6 69 = true ∧ RA.j0x uW 69 = true ∧ RA.xak uW 6 71 = true := by decide +kernel
  have nx : ¬ Tok (RA.run 6 uW).Tx (RA.xak uW 6) (RA.run 6 uW).XA (fun k => !(RA.run 6 uW).sv k) := by
    intro h
    have := h.hi 1 71 (by decide) (by rw [show 2 * 1 = 2 from rfl, hX2]; omega)
      (by rw [show 2 * 1 + 1 = 3 from rfl, hX3]; omega)
    rw [v.2.2] at this; exact absurd this (by decide)
  exact ⟨RA.staticW 6 1 (by omega), rfl, RA.rstOK 6 (by omega), by rw [RA.ZA0_eq],
    by rw [RA.A0_eq, RA.E_eq], hX2, hX3, v.1, v.2.1, v.2.2, nx, fun h => nx h.2.2.2.1⟩

/-- The counter-run meets every other hypothesis, so `ClaimSEQ 1` is false. -/
theorem claimSEQ1_false : ¬ ClaimSEQ 1 := by
  intro h
  exact failSEQ6.2.2.2.2.2.2.2.2.2.2.2
    (h (RA.run 6 uW) uW 1 1 1 1 1 1 1 12 RA.rst RA.x RA.y RA.ctl RA.za RA.xj RA.yj RA.cj RA.cj RA.sx
      RA.sx RA.j0 RA.q0 RA.j1 RA.q1 RA.e0 RA.e1 RA.ei RA.zr (RA.j0x uW) RA.j1y (RA.zx 6) RA.zy
      (RA.xa uW 6) (RA.qa uW 6) RA.ya RA.qb (RA.xak uW 6) RA.yak
      (RA.gates 6 uW) (RA.env 6 uW) (RA.causal 6 (by omega)) (Nat.le_refl 1) failSEQ6.1
      (RA.rstOK 6 (by omega)))

end Formal.Cells.Necessity7Mux
