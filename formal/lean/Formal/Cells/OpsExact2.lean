import Formal.Cells.OpsExact
open Formal.Core.LutList

/-!
# Shard B, probe Lt5: the remaining operator exactness items

Follows Lt4 (`OpsExact`, notes `B-ops-exact.md`). Contents:

1. `MuxRtz`: a mux run whose z_ack → uxa wire is a FIFO channel with a
   time-varying delay (8 ticks on z_ack's falls, 1 on its rises; `Rz`, not a
   shift). Every `MuxStatic` field holds except `S_XA_RTZ`, which fails by one
   tick, and every other hypothesis of `mux_ok_static` (gates on the REAL
   INITs, environment, causality, reset sequencing) holds. The conclusion
   fails: uxa's node re-fires inside the following y token, so x_ack is not a
   clean token trace (`cex_S_XA_RTZ`). **`S_XA_RTZ` is exact** (tight by one
   tick) once the z_ack wire's rise/fall spread exceeds the j0 → uxa wire's.
2. `MuxB`: the x/y mirror of Lt4's `MuxA` (y late at uj1, `Wc1 = 2`):
   `S_Z_S0` necessary on its own (`cex_S_Z_S0`, `S_Z_S1` holding) and `S_Z_Y`
   tight by one tick when y is the join's late input (`cex_S_Z_Y`).
3. `cel_run_g`: the gated C-element run with `H_DEP` asked only at real edges
   (the gated input's edges in its gate-off tokens are bookkeeping), and
   `merge_ok_g`: `merge_ok_noskew` with `MergeTimingG`, whose `H_DEP_XA` /
   `H_DEP_YA` have no instance at the other client's (bookkeeping) edges.
   Its static form `MergeStaticG` (`merge_timing_g_of_static`, `merge_ok_gs`)
   is node-launched and spread-free: `S_XA_N` (two forms) and `S_XA_SEQ` (the
   y → x fork, no loop term) replace `S_XA_FORK`, `S_XA_ZA`, `S_XA_R`; the old
   set implies it (`MergeStaticNS.g`). Each new field is tight by one tick in
   a counter-run: `MergeN` (`S_XA_N`, x_req form), `MergeR` (`S_XA_N`, z_ack
   form), `MergeS` (`S_XA_SEQ`).
-/

namespace Formal.Cells.OpsTimed
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace Vph)
open Formal.Cells.Bundling (StableOn Gate Transport transport_gate)
open Formal.Cells.ConstraintsMux (DmRel dm_settles DM_ODD dm_odd_rel usel_high)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B or2_spec c2_spec j0_spec j1_spec)

/-- First-arrival of an edge, from the read-time map: if the output reads at
or after `c` at `v` and before `c` at every earlier instant, the edge at `c`
arrives at `v`. -/
theorem Ret.fst_eq_of (r : Ret) {c v : Nat} (h1 : c ≤ r.σ v) (h2 : v = 0 ∨ r.σ (v - 1) < c) :
    r.fst c = v := by
  have a := r.fst_spec c
  rcases Nat.lt_trichotomy (r.fst c) v with h | h | h
  · rcases h2 with h2 | h2
    · omega
    · have := r.mono (r.fst c) (v - 1) (by omega); omega
  · exact h
  · have := r.fst_before (c := c) (t := v) h; omega

/-! ## 1. `S_XA_RTZ` is exact: a z_ack wire with more spread than the request wire

`MuxRtz.run`: every LUT and wire one tick, except `W0x = shift 6` (the
j0 → uxa wire) and `Wzx = Rz` (the z_ack → uxa wire): `Rz` holds the wire's
old value for 7 extra ticks after each z_ack FALL (delay 8) and passes rises
in 1 tick. `Lxa.hi + wxah = 2`, reset high on `[0, 8)`.

Control token `k` (even: x, odd: y) on base `20k`: ctl_req rises at `20k+10`
(ctl is the late input at its join), the join fires at `E(2k) = 20k+12`,
the server answers at `ζ(2k) = 20k+16` and drops at `ζ(2k+1) = 20k+28`; the
next control token is raised by the minimal causal chain from that fall, so
z_ack's next rise is at `20k+36`, exactly `8` ticks later. At uxa the fall
arrives at `20k+36` and the rise at `20k+37`: a one-tick low pulse, while
uxa's loop needs two. In an x token uxa's node is high when that pulse
arrives; the C-element LUT sees `C(0, 0, 1) = 0`, then `C(0, 1, 1) = 1` from
its stale feedback: the node re-fires inside the y token. -/
namespace MuxRtz
set_option maxRecDepth 100000

/-- The z_ack → uxa wire: delay `min e 7 + 1` on z_ack's falls (at `20k+28`),
1 otherwise. The counter-run uses `e = 7` (delay 8), the boundary run `e = 6`
(delay 7). -/
def Rz (e : Nat) : Ret where
  σ t := if 29 ≤ t ∧ (t - 29) % 20 < min e 7 then t - (t - 29) % 20 - 2 else t - 1
  lo := 1
  hi := min e 7 + 1
  mono a b h := by
    show (if 29 ≤ a ∧ (a - 29) % 20 < min e 7 then a - (a - 29) % 20 - 2 else a - 1) ≤
      (if 29 ≤ b ∧ (b - 29) % 20 < min e 7 then b - (b - 29) % 20 - 2 else b - 1)
    split <;> split <;> omega
  ge t := by
    show t - (min e 7 + 1) ≤ (if 29 ≤ t ∧ (t - 29) % 20 < min e 7 then t - (t - 29) % 20 - 2 else t - 1)
    split <;> omega
  le t := by
    show (if 29 ≤ t ∧ (t - 29) % 20 < min e 7 then t - (t - 29) % 20 - 2 else t - 1) ≤ t - 1
    split <;> omega

theorem Rz_σ (e t : Nat) : (Rz e).σ t =
    if 29 ≤ t ∧ (t - 29) % 20 < min e 7 then t - (t - 29) % 20 - 2 else t - 1 := rfl

def W6 : Ret := Ret.shift 6
def rst8 (t : Nat) : Bool := decide (t < 8)
theorem rst8_hi : ∀ t, t < 8 → rst8 t = true := fun t h => by simp [rst8, h]
theorem rst8_lo : ∀ t, 8 ≤ t → rst8 t = false := fun t h => by simp [rst8]; omega

def run (e : Nat) : MuxRun where
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
  W0x := W6
  W1y := uW
  Lor := uW
  Dz := uW
  Wzx := Rz e
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := 1
  wxah := 1
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ξ j := 40 * (j / 2) + 8 + 14 * (j % 2)
  η j := 40 * (j / 2) + 28 + 14 * (j % 2)
  γ j := 20 * (j / 2) + 10 + 8 * (j % 2)
  ζ j := 20 * (j / 2) + 16 + 12 * (j % 2)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

-- environment
def x (t : Nat) : Bool := decide (8 ≤ t ∧ (t - 8) % 40 < 14)
def y (t : Nat) : Bool := decide (28 ≤ t ∧ (t - 28) % 40 < 14)
def ctl (t : Nat) : Bool := decide (10 ≤ t ∧ (t - 10) % 20 < 8)
def za (t : Nat) : Bool := decide (16 ≤ t ∧ (t - 16) % 20 < 12)
def sx (t : Nat) : Bool := svW ((t - 4) / 20)
-- the cell
def xj (t : Nat) : Bool := x (t - 1)
def yj (t : Nat) : Bool := y (t - 1)
def cj (t : Nat) : Bool := ctl (t - 1)
def j0 : Nat → Bool
  | 0 => false
  | 1 => j0B (xj 0) (cj 0) (sx 0) false (rst8 0)
  | t + 2 => j0B (xj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j0 t) (rst8 (t + 1))
def q0 (t : Nat) : Bool := j0 (t - 1)
def j1 : Nat → Bool
  | 0 => false
  | 1 => j1B (yj 0) (cj 0) (sx 0) false (rst8 0)
  | t + 2 => j1B (yj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j1 t) (rst8 (t + 1))
def q1 (t : Nat) : Bool := j1 (t - 1)
def e0 (t : Nat) : Bool := j0 (t - 1)
def e1 (t : Nat) : Bool := j1 (t - 1)
def ei (t : Nat) : Bool := or2B (e0 (t - 1)) (e1 (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
def j0x (t : Nat) : Bool := j0 (t - 6)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (e : Nat) (t : Nat) : Bool := za ((Rz e).σ t)
def zy (t : Nat) : Bool := za (t - 1)
def xa (e : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x 0) (zx e 0) false (rst8 0)
  | t + 2 => c2B (j0x (t + 1)) (zx e (t + 1)) (xa e t) (rst8 (t + 1))
def qa (e : Nat) (t : Nat) : Bool := xa e (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zy 0) false (rst8 0)
  | t + 2 => c2B (j1y (t + 1)) (zy (t + 1)) (ya t) (rst8 (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (e : Nat) (t : Nat) : Bool := xa e (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates (e : Nat) : MuxGates (run e) rst8 x y ctl za xj yj cj cj sx sx j0 q0 j1 q1 e0 e1 ei zr j0x
    j1y (zx e) zy (xa e) (qa e) ya qb (xak e) yak where
  H_WX _ _ := rfl
  H_WY _ _ := rfl
  H_WC0 _ _ := rfl
  H_WC1 _ _ := rfl
  H_UJ0 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ0_FB := win11 (fun _ _ => rfl)
  H_UJ0_POS := by show 1 ≤ 1 + 1; omega
  H_UJ1 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ1_FB := win11 (fun _ _ => rfl)
  H_UJ1_POS := by show 1 ≤ 1 + 1; omega
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
  H_UXA_POS := by show 1 ≤ 1 + 1; omega
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by show 1 ≤ 1 + 1; omega
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem enum0 (e : Nat) : Enum (fun k => !(run e).sv k) (run e).κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 (e : Nat) : Enum (run e).sv (run e).κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

/-! Closed forms of the derived edges. -/
variable {e : Nat}

theorem f6 (c : Nat) (hc : 1 ≤ c) : W6.fst c = c + 6 := Ret.fst_shift 6 c hc

theorem Xp_eq (j : Nat) : (run e).Xp j = 40 * (j / 2) + 9 + 14 * (j % 2) := by
  show uW.fst (40 * (j / 2) + 8 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : (run e).Yp j = 40 * (j / 2) + 29 + 14 * (j % 2) := by
  show uW.fst (40 * (j / 2) + 28 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : (run e).C0 j = 20 * (j / 2) + 11 + 8 * (j % 2) := by
  show uW.fst (20 * (j / 2) + 10 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C1_eq (j : Nat) : (run e).C1 j = 20 * (j / 2) + 11 + 8 * (j % 2) := by
  show uW.fst (20 * (j / 2) + 10 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem D0_eq (j : Nat) : (run e).D0 j = 40 * (j / 2) + 11 + 8 * (j % 2) := by
  show (run e).C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [C0_eq]; omega
theorem D1_eq (j : Nat) : (run e).D1 j = 40 * (j / 2) + 31 + 8 * (j % 2) := by
  show (run e).C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C1_eq]; omega
theorem c0_eq (j : Nat) : (run e).c0 j = 40 * (j / 2) + 11 + 12 * (j % 2) := by
  show max ((run e).Xp j) ((run e).D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : (run e).c1 j = 40 * (j / 2) + 31 + 12 * (j % 2) := by
  show max ((run e).Yp j) ((run e).D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : (run e).τ0 j = 40 * (j / 2) + 12 + 12 * (j % 2) := by
  show uW.fst ((run e).c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : (run e).τ1 j = 40 * (j / 2) + 32 + 12 * (j % 2) := by
  show uW.fst ((run e).c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : (run e).E j = 20 * (j / 2) + 12 + 12 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : (run e).sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx (run e).κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum0 e) (j / 2 / 2)
      rw [show (run e).κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega
  · have hs : (run e).sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx (run e).κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum1 e) (j / 2 / 2)
      rw [show (run e).κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega

theorem env (e : Nat) : MuxEnv (run e) rst8 x y ctl za sx sx 8 where
  H_RST_HI := rst8_hi
  H_RST_LO := rst8_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 40 * (0 / 2) + 8 + 14 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 40 * (2 * k / 2) + 8 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 1) / 2) + 8 + 14 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 40 * ((2 * k + 1) / 2) + 8 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 2) / 2) + 8 + 14 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 40 * (0 / 2) + 28 + 14 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 40 * (2 * k / 2) + 28 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 1) / 2) + 28 + 14 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 40 * ((2 * k + 1) / 2) + 28 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 2) / 2) + 28 + 14 * ((2 * k + 2) % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 20 * (0 / 2) + 10 + 8 * (0 % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : 20 * (2 * k / 2) + 10 + 8 * (2 * k % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 1) / 2) + 10 + 8 * ((2 * k + 1) % 2) := h2
      simp only [ctl, decide_eq_true_eq]; omega
    · have h1 : 20 * ((2 * k + 1) / 2) + 10 + 8 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 2) / 2) + 10 + 8 * ((2 * k + 2) % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 20 * (0 / 2) + 16 + 12 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 20 * (2 * k / 2) + 16 + 12 * (2 * k % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 1) / 2) + 16 + 12 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 20 * ((2 * k + 1) / 2) + 16 + 12 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 2) / 2) + 16 + 12 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_ENUM0 := enum0 e
  H_ENUM1 := enum1 e
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq] at h1 h2
    show svW ((t - 4) / 20) = svW k
    rw [show (t - 4) / 20 = k by omega]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq] at h1 h2
    show svW ((t - 4) / 20) = svW k
    rw [show (t - 4) / 20 = k by omega]

theorem O0_eq (j : Nat) : (run e).O0 j = (run e).E j + 1 := by
  show uW.fst ((run e).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : (run e).O1 j = (run e).E j + 1 := by
  show uW.fst ((run e).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A0_eq (j : Nat) : (run e).A0 j = (run e).E j + 6 := by
  show W6.fst ((run e).E j) = _; rw [f6 _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : (run e).A1 j = (run e).E j + 1 := by
  show uW.fst ((run e).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]

/-- z_ack at uxa: rises one tick late, falls `min e 7 + 1` ticks late. -/
theorem ZA0_ev (k : Nat) : (run e).ZA0 (2 * k) = 20 * k + 17 := by
  show (Rz e).fst (20 * (2 * k / 2) + 16 + 12 * (2 * k % 2)) = _
  rw [show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
  apply Ret.fst_eq_of
  · rw [Rz_σ]; split <;> omega
  · right; rw [Rz_σ]; split <;> omega
theorem ZA0_od (he : 1 ≤ e) (k : Nat) : (run e).ZA0 (2 * k + 1) = 20 * k + 29 + min e 7 := by
  show (Rz e).fst (20 * ((2 * k + 1) / 2) + 16 + 12 * ((2 * k + 1) % 2)) = _
  rw [show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega]
  apply Ret.fst_eq_of
  · rw [Rz_σ]; split <;> omega
  · right; rw [Rz_σ]; split <;> omega
theorem ZA1_eq (j : Nat) : (run e).ZA1 j = 20 * (j / 2) + 17 + 12 * (j % 2) := by
  show uW.fst (20 * (j / 2) + 16 + 12 * (j % 2)) = _; rw [fuW _ (by omega)]; omega

theorem Z_eq (j : Nat) : (run e).Z j = (run e).E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show (run e).Lor = uW from rfl, show (run e).Dz = uW from rfl]
  have hE := E_eq (e := e) j
  split
  · rw [O0_eq, fuW ((run e).E j + 1) (by omega), fuW ((run e).E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW ((run e).E j + 1) (by omega), fuW ((run e).E j + 1 + 1) (by omega)]

theorem cx_ev (k : Nat) : (run e).cx (2 * k) = 20 * k + 18 := by
  show max ((run e).A0 (2 * k)) ((run e).ZA0 (2 * k)) = _; rw [A0_eq, ZA0_ev, E_eq]; omega
theorem cx_od (he : 1 ≤ e) (k : Nat) : (run e).cx (2 * k + 1) = 20 * k + 29 + min e 7 := by
  show max ((run e).A0 (2 * k + 1)) ((run e).ZA0 (2 * k + 1)) = _
  rw [A0_eq, ZA0_od he, E_eq]; omega
theorem cy_eq (j : Nat) : (run e).cy j = 20 * (j / 2) + 17 + 12 * (j % 2) := by
  show max ((run e).A1 j) ((run e).ZA1 j) = _; rw [A1_eq, ZA1_eq, E_eq]; omega
theorem XA_ev (k : Nat) : (run e).XA (2 * k) = 20 * k + 20 := by
  show uW.fst (uW.fst ((run e).cx (2 * k))) = _
  rw [cx_ev, fuW (20 * k + 18) (by omega), fuW (20 * k + 18 + 1) (by omega)]
theorem XA_od (he : 1 ≤ e) (k : Nat) : (run e).XA (2 * k + 1) = 20 * k + 31 + min e 7 := by
  show uW.fst (uW.fst ((run e).cx (2 * k + 1))) = _
  rw [cx_od he, fuW (20 * k + 29 + min e 7) (by omega), fuW (20 * k + 29 + min e 7 + 1) (by omega)]
  omega
theorem YA_eq (j : Nat) : (run e).YA j = 20 * (j / 2) + 19 + 12 * (j % 2) := by
  show uW.fst (uW.fst ((run e).cy j)) = _
  rw [cy_eq, fuW (20 * (j / 2) + 17 + 12 * (j % 2)) (by omega),
    fuW (20 * (j / 2) + 17 + 12 * (j % 2) + 1) (by omega)]; omega

theorem causal (he : 1 ≤ e) : MuxCausal (run e) uW 1 1 1 1 where
  H_XC_FALL m := by
    show (run e).XA (2 * (2 * m)) + 1 ≤ 40 * ((2 * m + 1) / 2) + 8 + 14 * ((2 * m + 1) % 2)
    rw [XA_ev]; omega
  H_XC_RISE m := by
    show (run e).XA (2 * (2 * m) + 1) + 1 ≤ 40 * ((2 * m + 2) / 2) + 8 + 14 * ((2 * m + 2) % 2)
    rw [XA_od he]; omega
  H_YC_FALL m := by
    rw [YA_eq]; show _ ≤ 40 * ((2 * m + 1) / 2) + 28 + 14 * ((2 * m + 1) % 2)
    show 20 * (2 * (2 * m + 1) / 2) + 19 + 12 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [YA_eq]; show _ ≤ 40 * ((2 * m + 2) / 2) + 28 + 14 * ((2 * m + 2) % 2)
    show 20 * ((2 * (2 * m + 1) + 1) / 2) + 19 + 12 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (20 * (j / 2) + 16 + 12 * (j % 2)) + 1 ≤ 20 * ((j + 1) / 2) + 10 + 8 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 20 * (j / 2) + 16 + 12 * (j % 2); omega
  H_POS j := by show 1 ≤ 20 * (j / 2) + 10 + 8 * (j % 2); omega

theorem hRL (he : e ≤ 7) : (run e).Wx.hi ≤ 8 ∧ (run e).Wy.hi ≤ 8 ∧ (run e).Wc0.hi ≤ 8 ∧
    (run e).Wc1.hi ≤ 8 ∧ (run e).Lj0.hi + (run e).wj0h ≤ 8 ∧ (run e).Lj1.hi + (run e).wj1h ≤ 8 ∧
    (run e).Lj0.hi + (run e).W0x.hi ≤ 8 ∧ (run e).Lj1.hi + (run e).W1y.hi ≤ 8 ∧
    (run e).Wzx.hi ≤ 8 ∧ (run e).Wzy.hi ≤ 8 ∧ (run e).Lxa.hi + (run e).wxah ≤ 8 ∧
    (run e).Lya.hi + (run e).wyah ≤ 8 := by
  simp only [run, uW, Ret.shift, W6, Rz]; omega

theorem hRE : 8 ≤ (run e).Xp 0 ∧ 8 ≤ (run e).D0 0 ∧ 8 ≤ (run e).Yp 0 ∧ 8 ≤ (run e).D1 0 ∧
    8 ≤ (run e).A0 0 ∧ 8 ≤ (run e).ZA0 0 ∧ 8 ≤ (run e).A1 0 ∧ 8 ≤ (run e).ZA1 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [A0_eq, E_eq]; omega
  · rw [show (0 : Nat) = 2 * 0 from rfl, ZA0_ev]; omega
  · rw [A1_eq, E_eq]; omega
  · rw [ZA1_eq]; omega

/-- **Boundary** (`e = 6`: z_ack falls reach uxa 7 ticks late). Every
`MuxStatic` field holds, `S_XA_RTZ` with equality (`9 ≤ 9`), and
`mux_ok_static` applies: x_ack and y_ack are clean token traces. -/
theorem static6 : MuxStatic (run 6) uW 1 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem bnd_S_XA_RTZ :
    (run 6).Wzx.hi + ((run 6).Lxa.hi + (run 6).wxah) =
      (run 6).Wzx.lo + (uW.lo + 1 + 1 + 1) + (1 + (run 6).Lor.lo + (run 6).Dz.lo + 1) ∧
    Tok (run 6).Tz zr (run 6).Z (fun _ => true) ∧
    Tok (run 6).Tx (xak 6) (run 6).XA (fun k => !(run 6).sv k) ∧
    Tok (run 6).Tx (xak 6) (rx (run 6).XA (run 6).κ0) (fun _ => true) ∧
    Tok (run 6).Ty yak (run 6).YA (run 6).sv :=
  let h := mux_ok_static (gates 6) (env 6) (causal (by decide)) static6 (hRL (by decide)) hRE
  ⟨by decide, h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- At `e = 7` (z_ack falls reach uxa 8 ticks late) every `MuxStatic` field
except `S_XA_RTZ` holds; `S_XA_FORK` with equality. -/
theorem static_but_rtz :
    (1 ≤ (run 7).Lj0.lo ∧ 1 ≤ (run 7).Lj1.lo) ∧ (1 ≤ (run 7).Wc0.lo ∧ 1 ≤ (run 7).Wc1.lo) ∧
    (1 ≤ (run 7).W0o.lo ∧ 1 ≤ (run 7).W1o.lo) ∧
    (run 7).Lj0.hi + (run 7).wj0h ≤
      (run 7).Lj0.lo + (run 7).W0x.lo + (run 7).Lxa.lo + (run 7).Wxa.lo + 1 + (run 7).Wx.lo ∧
    (run 7).Lj1.hi + (run 7).wj1h ≤
      (run 7).Lj1.lo + (run 7).W1y.lo + (run 7).Lya.lo + (run 7).Wya.lo + 1 + (run 7).Wy.lo ∧
    (run 7).Lj0.hi + (run 7).wj0h ≤
      (run 7).Lj0.lo + (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + uW.lo + 1 + (run 7).Wc0.lo ∧
    (run 7).Lj1.hi + (run 7).wj1h ≤
      (run 7).Lj1.lo + (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + uW.lo + 1 + (run 7).Wc1.lo ∧
    ((run 7).W0o.hi ≤ (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + (run 7).W1o.lo ∧
      (run 7).W1o.hi ≤ (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + (run 7).W0o.lo) ∧
    (run 7).Wzx.hi + ((run 7).Lxa.hi + (run 7).wxah) = (uW.lo + 1 + 1 + 1) + (run 7).W0x.lo ∧
    (run 7).Wzy.hi + ((run 7).Lya.hi + (run 7).wyah) ≤ (uW.lo + 1 + 1 + 1) + (run 7).W1y.lo ∧
    (run 7).Wzy.hi + ((run 7).Lya.hi + (run 7).wyah) ≤
      (run 7).Wzy.lo + (uW.lo + 1 + 1 + 1) + (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) ∧
    ((run 7).W0x.hi + ((run 7).Lxa.hi + (run 7).wxah) ≤
        (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + (run 7).W0x.lo ∧
      (run 7).W0x.hi + ((run 7).Lxa.hi + (run 7).wxah) ≤
        2 * (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + (run 7).Wzx.lo) ∧
    ((run 7).W1y.hi + ((run 7).Lya.hi + (run 7).wyah) ≤
        (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + (run 7).W1y.lo ∧
      (run 7).W1y.hi + ((run 7).Lya.hi + (run 7).wyah) ≤
        2 * (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + (run 7).Wzy.lo) := by
  decide

/-- `S_XA_RTZ` fails by one tick at `e = 7`: `10 > 9`. -/
theorem rtz_fails :
    (run 7).Wzx.hi + ((run 7).Lxa.hi + (run 7).wxah) =
      (run 7).Wzx.lo + (uW.lo + 1 + 1 + 1) + (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + 1 ∧
    ¬ MuxStatic (run 7) uW 1 1 1 1 1 1 1 := by
  refine ⟨by decide, fun S => ?_⟩
  have := S.S_XA_RTZ; revert this; decide

/-- The event form fails too: `H_DEP_XA` at `j = 1` against the next z_ack
edge (`38 > 37`); at `e = 6` it holds with equality. -/
theorem dep_values : (run 7).cx 1 + (run 7).Lxa.hi + (run 7).wxah = 38 ∧ (run 7).ZA0 2 = 37 ∧
    (run 6).cx 1 + (run 6).Lxa.hi + (run 6).wxah = 37 ∧ (run 6).ZA0 2 = 37 := by
  have a7 := cx_od (e := 7) (by decide) 0
  have a6 := cx_od (e := 6) (by decide) 0
  have z7 := ZA0_ev (e := 7) 1
  have z6 := ZA0_ev (e := 6) 1
  simp only [Nat.mul_zero, Nat.zero_add, Nat.mul_one] at a7 a6 z7 z6
  refine ⟨?_, z7, ?_, z6⟩
  · rw [a7]; decide
  · rw [a6]; decide

/-- The traces themselves at `e = 7`: x's token 0 is acknowledged normally
(x_ack high at `XA 0 = 20`, low again at `XA 1 = 38`); in y's token
(control token 1) uxa's node re-fires from its stale feedback: x_ack is high
at `39`, before `XA 2 = 40`, and again at `41`, inside y's slot. At `e = 6`
x_ack stays low there. -/
theorem glitch_values :
    (run 7).XA 0 = 20 ∧ (run 7).XA 1 = 38 ∧ (run 7).XA 2 = 40 ∧ (run 7).XA 3 = 58 ∧
    xak 7 20 = true ∧ xak 7 37 = true ∧ xak 7 38 = false ∧ xak 7 39 = true ∧ xak 7 41 = true ∧
    zx 7 36 = false ∧ zx 7 35 = true ∧ zx 7 37 = true ∧ j0x 36 = false ∧ (run 7).sv 1 = true ∧
    xak 6 39 = false ∧ xak 6 41 = false := by
  refine ⟨XA_ev 0, XA_od (by decide) 0, XA_ev 1, XA_od (by decide) 1, ?_⟩
  decide

/-- **`S_XA_RTZ` is exact.** At `e = 7` every hypothesis of `mux_ok_static`
except `S_XA_RTZ` holds (`gates`, `env`, `causal`, `static_but_rtz`, `hRL`,
`hRE`), `S_XA_RTZ` fails by one tick (`rtz_fails`), and `mux_ok_static`'s
conclusion is false: x_ack is not a clean token trace on its x-gated edges
(it is high at `t = 39`, after x's token ended at `XA 1 = 38` and before
`XA 2 = 40`), nor on x's own token sequence; the event form `MuxTiming`
fails. At `e = 6` everything holds (`bnd_S_XA_RTZ`). -/
theorem cex_S_XA_RTZ :
    ¬ Tok (run 7).Tx (xak 7) (run 7).XA (fun k => !(run 7).sv k) ∧
    ¬ Tok (run 7).Tx (xak 7) (rx (run 7).XA (run 7).κ0) (fun _ => true) ∧
    ¬ MuxTiming (run 7) 8 := by
  have g := glitch_values
  have d := dep_values
  refine ⟨fun h => ?_, fun h => ?_, fun TM => ?_⟩
  · have := h.lo 0 39 (by decide) (by rw [g.2.1]; omega) (by rw [g.2.2.1]; omega)
    rw [g.2.2.2.2.2.2.2.1] at this; exact absurd this (by decide)
  · -- x's own sequence: token 0 ends at XA 1 = 38, x's token 1 starts at XA (2 κ0 1) = XA 4 = 60
    have h4 : rx (run 7).XA (run 7).κ0 1 = 38 := by
      rw [show (1 : Nat) = 2 * 0 + 1 from rfl, rx_o]; exact XA_od (by decide) 0
    have h2 : rx (run 7).XA (run 7).κ0 2 = 60 := by
      rw [show (2 : Nat) = 2 * 0 + 2 from rfl, rx_e2]; exact XA_ev 2
    have := h.lo 0 39 (by decide) (by rw [h4]; omega) (by rw [h2]; omega)
    rw [g.2.2.2.2.2.2.2.1] at this; exact absurd this (by decide)
  · have h := (TM.H_DEP_XA 1).2
    rw [d.1, d.2.1] at h; omega

end MuxRtz

/-! ## 2. The x/y mirror of `MuxA`: y late at its join, `Wc1 = 2`

Lt4's `MuxA` with the two inputs' roles exchanged. Every LUT and wire one
tick, except the ctl_req wire to uj1 (`Wc1`), which is two. Control token `k`
(EVEN: y, odd: x) on base `20k`: ctl_req rises at `20k+8` (y tokens) or
`20k+10` (x tokens), falls at `20k+18`. y's request rises at `40m+10`, so it
reaches uj1 at `20k+11`, one tick AFTER ctl_req (`20k+10` through the 2-tick
wire): **y is the join's late input**. x's request rises at `40m+26`,
reaching uj0 4 ticks before ctl_req. The edges are MuxA's:
`E (2k) = 20k+12`, `Z (2k) = 20k+15`, `ζ (2k) = 20k+16`, `XA = YA = 20k+19`.

* `S_Z_S0` RHS `= Ls + 1 + 1 + 1 + 1 + 1 = 9`, `S_Z_S1` RHS `= 10`: at
  `shi = 10` only `S_Z_S0` fails, and the conclusion fails in an x token;
* `S_Z_Y` is TIGHT (y late): at `bhi = 6` it fails by one tick and the
  conclusion fails in a y token. -/
namespace MuxB
set_option maxRecDepth 100000

/-- Token `k` selects y when `k` is even. -/
def svB (k : Nat) : Bool := decide (k % 2 = 0)

def run : MuxRun where
  Wx := uW
  Wy := uW
  Wc0 := uW
  Wc1 := Ret.shift 2
  Lj0 := uW
  Lj1 := uW
  wj0l := 1
  wj0h := 1
  wj1l := 1
  wj1h := 1
  W0o := uW
  W1o := uW
  W0x := uW
  W1y := uW
  Lor := uW
  Dz := uW
  Wzx := uW
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := 1
  wxah := 1
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ξ j := 40 * (j / 2) + 26 + 14 * (j % 2)
  η j := 40 * (j / 2) + 10 + 10 * (j % 2)
  γ j := if j % 2 = 0 then 20 * (j / 2) + 8 + 2 * ((j / 2) % 2) else 20 * (j / 2) + 18
  ζ j := 20 * (j / 2) + 16 + 10 * (j % 2)
  sv := svB
  κ0 m := 2 * m + 1
  κ1 m := 2 * m

def sx (t : Nat) : Bool := svB (MuxA.sTok t)
-- environment
def x (t : Nat) : Bool := decide (26 ≤ t ∧ (t - 26) % 40 < 14)
def y (t : Nat) : Bool := decide (10 ≤ t ∧ (t - 10) % 40 < 10)
-- the cell
def xj (t : Nat) : Bool := x (t - 1)
def yj (t : Nat) : Bool := y (t - 1)
def cj0 (t : Nat) : Bool := MuxA.ctl (t - 1)
def cj1 (t : Nat) : Bool := MuxA.ctl (t - 2)
def j0 : Nat → Bool
  | 0 => false
  | 1 => j0B (xj 0) (cj0 0) (sx 0) false (rstW 0)
  | t + 2 => j0B (xj (t + 1)) (cj0 (t + 1)) (sx (t + 1)) (j0 t) (rstW (t + 1))
def q0 (t : Nat) : Bool := j0 (t - 1)
def j1 : Nat → Bool
  | 0 => false
  | 1 => j1B (yj 0) (cj1 0) (sx 0) false (rstW 0)
  | t + 2 => j1B (yj (t + 1)) (cj1 (t + 1)) (sx (t + 1)) (j1 t) (rstW (t + 1))
def q1 (t : Nat) : Bool := j1 (t - 1)
def e0 (t : Nat) : Bool := j0 (t - 1)
def e1 (t : Nat) : Bool := j1 (t - 1)
def ei (t : Nat) : Bool := or2B (e0 (t - 1)) (e1 (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
def j0x (t : Nat) : Bool := j0 (t - 1)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (t : Nat) : Bool := MuxA.za (t - 1)
def xa : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (j0x (t + 1)) (zx (t + 1)) (xa t) (rstW (t + 1))
def qa (t : Nat) : Bool := xa (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (j1y (t + 1)) (zx (t + 1)) (ya t) (rstW (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (t : Nat) : Bool := xa (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates : MuxGates run rstW x y MuxA.ctl MuxA.za xj yj cj0 cj1 sx sx j0 q0 j1 q1 e0 e1 ei zr
    j0x j1y zx zx xa qa ya qb xak yak where
  H_WX _ _ := rfl
  H_WY _ _ := rfl
  H_WC0 _ _ := rfl
  H_WC1 _ _ := rfl
  H_UJ0 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ0_FB := win11 (fun _ _ => rfl)
  H_UJ0_POS := by decide
  H_UJ1 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ1_FB := win11 (fun _ _ => rfl)
  H_UJ1_POS := by decide
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
  H_UXA_POS := by decide
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by decide
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem enum0 : Enum (fun k => !run.sv k) run.κ0 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show (!decide ((2 * m + 1) % 2 = 0)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 0)) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

theorem enum1 : Enum run.sv run.κ1 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show decide (2 * m % 2 = 0) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 0) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

/-! Closed forms of the derived edges. -/
theorem γ_eq (j : Nat) : run.γ j =
    if j % 2 = 0 then 20 * (j / 2) + 8 + 2 * ((j / 2) % 2) else 20 * (j / 2) + 18 := rfl
theorem Xp_eq (j : Nat) : run.Xp j = 40 * (j / 2) + 27 + 14 * (j % 2) := by
  show uW.fst (40 * (j / 2) + 26 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : run.Yp j = 40 * (j / 2) + 11 + 10 * (j % 2) := by
  show uW.fst (40 * (j / 2) + 10 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : run.C0 j = run.γ j + 1 := by
  show uW.fst (run.γ j) = _; rw [fuW _ (by rw [γ_eq]; split <;> omega)]
theorem C1_eq (j : Nat) : run.C1 j = run.γ j + 2 := by
  show (Ret.shift 2).fst (run.γ j) = _
  rw [Ret.fst_shift 2 _ (by rw [γ_eq]; split <;> omega)]
theorem D0_eq (j : Nat) : run.D0 j = 40 * (j / 2) + 31 + 8 * (j % 2) := by
  show run.C0 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C0_eq, γ_eq]; split <;> omega
theorem D1_eq (j : Nat) : run.D1 j = 40 * (j / 2) + 10 + 10 * (j % 2) := by
  show run.C1 (2 * (2 * (j / 2)) + j % 2) = _; rw [C1_eq, γ_eq]; split <;> omega
theorem c0_eq (j : Nat) : run.c0 j = 40 * (j / 2) + 31 + 10 * (j % 2) := by
  show max (run.Xp j) (run.D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : run.c1 j = 40 * (j / 2) + 11 + 10 * (j % 2) := by
  show max (run.Yp j) (run.D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : run.τ0 j = 40 * (j / 2) + 32 + 10 * (j % 2) := by
  show uW.fst (run.c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : run.τ1 j = 40 * (j / 2) + 12 + 10 * (j % 2) := by
  show uW.fst (run.c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : run.E j = 20 * (j / 2) + 12 + 10 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : run.sv (j / 2) = true := by show decide (j / 2 % 2 = 0) = true; simp; omega
    have hi : idx run.κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum1 (j / 2 / 2)
      rw [show run.κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega
  · have hs : run.sv (j / 2) = false := by show decide (j / 2 % 2 = 0) = false; simp; omega
    have hi : idx run.κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum0 (j / 2 / 2)
      rw [show run.κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega

theorem env : MuxEnv run rstW x y MuxA.ctl MuxA.za sx sx 4 where
  H_RST_HI := rstW_hi
  H_RST_LO := rstW_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 40 * (0 / 2) + 26 + 14 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 40 * (2 * k / 2) + 26 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 1) / 2) + 26 + 14 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 40 * ((2 * k + 1) / 2) + 26 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 2) / 2) + 26 + 14 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 40 * (0 / 2) + 10 + 10 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 40 * (2 * k / 2) + 10 + 10 * (2 * k % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 1) / 2) + 10 + 10 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 40 * ((2 * k + 1) / 2) + 10 + 10 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 2) / 2) + 10 + 10 * ((2 * k + 2) % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_CTL := MuxA.env.H_CTL
  H_ZA := MuxA.env.H_ZA
  H_ENUM0 := enum0
  H_ENUM1 := enum1
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq, γ_eq] at h1 h2
    show svB (MuxA.sTok t) = svB k
    rw [MuxA.sTok_eq k t (by unfold MuxA.sS; split at h1 <;> omega)
      (by unfold MuxA.sS; split at h2 <;> omega)]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq, γ_eq] at h1 h2
    show svB (MuxA.sTok t) = svB k
    rw [MuxA.sTok_eq k t (by unfold MuxA.sS; split at h1 <;> omega)
      (by unfold MuxA.sS; split at h2 <;> omega)]

theorem O0_eq (j : Nat) : run.O0 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : run.O1 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A0_eq (j : Nat) : run.A0 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : run.A1 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (j : Nat) : run.ZA0 j = 20 * (j / 2) + 17 + 10 * (j % 2) ∧
    run.ZA1 j = 20 * (j / 2) + 17 + 10 * (j % 2) := by
  constructor <;> (show uW.fst (20 * (j / 2) + 16 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega)

theorem Z_eq (j : Nat) : run.Z j = run.E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show run.Lor = uW from rfl, show run.Dz = uW from rfl]
  have hE := E_eq j
  split
  · rw [O0_eq, fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]

theorem XA_eq (j : Nat) : run.XA j = 20 * (j / 2) + 19 + 10 * (j % 2) ∧
    run.YA j = 20 * (j / 2) + 19 + 10 * (j % 2) := by
  have hm : max (run.E j + 1) (20 * (j / 2) + 17 + 10 * (j % 2)) = 20 * (j / 2) + 17 + 10 * (j % 2) := by
    rw [E_eq]; omega
  constructor
  · show uW.fst (uW.fst (max (run.A0 j) (run.ZA0 j))) = _
    rw [A0_eq, (ZA_eq j).1, hm, fuW (20 * (j / 2) + 17 + 10 * (j % 2)) (by omega),
      fuW (20 * (j / 2) + 17 + 10 * (j % 2) + 1) (by omega)]; omega
  · show uW.fst (uW.fst (max (run.A1 j) (run.ZA1 j))) = _
    rw [A1_eq, (ZA_eq j).2, hm, fuW (20 * (j / 2) + 17 + 10 * (j % 2)) (by omega),
      fuW (20 * (j / 2) + 17 + 10 * (j % 2) + 1) (by omega)]; omega

theorem causal : MuxCausal run uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [(XA_eq _).1]; show _ ≤ 40 * ((2 * m + 1) / 2) + 26 + 14 * ((2 * m + 1) % 2)
    show 20 * (2 * (2 * m + 1) / 2) + 19 + 10 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [(XA_eq _).1]; show _ ≤ 40 * ((2 * m + 2) / 2) + 26 + 14 * ((2 * m + 2) % 2)
    show 20 * ((2 * (2 * m + 1) + 1) / 2) + 19 + 10 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_YC_FALL m := by
    rw [(XA_eq _).2]; show _ ≤ 40 * ((2 * m + 1) / 2) + 10 + 10 * ((2 * m + 1) % 2)
    show 20 * (2 * (2 * m) / 2) + 19 + 10 * (2 * (2 * m) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [(XA_eq _).2]; show _ ≤ 40 * ((2 * m + 2) / 2) + 10 + 10 * ((2 * m + 2) % 2)
    show 20 * ((2 * (2 * m) + 1) / 2) + 19 + 10 * ((2 * (2 * m) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (20 * (j / 2) + 16 + 10 * (j % 2)) + 1 ≤ run.γ (j + 1)
    rw [fuW _ (by omega), γ_eq]; split <;> omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 20 * (j / 2) + 16 + 10 * (j % 2); omega
  H_POS j := by rw [γ_eq]; split <;> omega

theorem static : MuxStatic run uW 1 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem hRE : 4 ≤ run.Xp 0 ∧ 4 ≤ run.D0 0 ∧ 4 ≤ run.Yp 0 ∧ 4 ≤ run.D1 0 ∧ 4 ≤ run.A0 0 ∧
    4 ≤ run.ZA0 0 ∧ 4 ≤ run.A1 0 ∧ 4 ≤ run.ZA1 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [A0_eq, E_eq]; omega
  · rw [(ZA_eq 0).1]; omega
  · rw [A1_eq, E_eq]; omega
  · rw [(ZA_eq 0).2]; omega

/-- Non-vacuity of the control side (`mux_ok` through the static obligations). -/
theorem witness : Tok run.Tz zr run.Z (fun _ => true) ∧
    Tok run.Tx xak run.XA (fun k => !run.sv k) ∧ Tok run.Ty yak run.YA run.sv :=
  let h := mux_ok_static gates env causal static (by decide) hRE
  ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- The run is what it claims: y arrives at uj1 after ctl_req (y late),
x arrives at uj0 before ctl_req (ctl late); the server sees both kinds. -/
theorem witness_values :
    run.Yp 0 = 11 ∧ run.C1 0 = 10 ∧ run.Xp 0 = 27 ∧ run.C0 2 = 31 ∧
    yak 19 = true ∧ xak 19 = false ∧ yak 39 = false ∧ xak 39 = true ∧
    zr 15 = true ∧ zr 35 = true ∧ j1 11 = false ∧ j1 12 = true := by
  refine ⟨by rw [Yp_eq], by rw [C1_eq]; rfl, by rw [Xp_eq], by rw [C0_eq]; rfl, ?_⟩
  decide

-- data: x's `m`-th bit from its request rise `40m+26`, y's from `40m+10`
-- (values: x carries MuxCex.yvC, y carries MuxCex.xvC, i.e. MuxA's swapped)
def xdB (t : Nat) : Bool := MuxCex.yvC ((t - 26) / 40)
def ydB (t : Nat) : Bool := MuxCex.xvC ((t - 10) / 40)
def zB (ds da db : Nat) (t : Nat) : Bool := lutB DM_ODD [sx (t - ds), xdB (t - da), ydB (t - db)]

theorem z_rel (ds da db : Nat) : DmRel sx xdB ydB (zB ds da db) ds ds da da db db :=
  dm_odd_rel (transport_gate DM_ODD [(sx, ds, ds, ds), (xdB, da, da, da), (ydB, db, db, db)]
    (zB ds da db)
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MuxDataEnv run uW sx xdB ydB MuxA.sS (fun k => MuxA.sS (k + 1) - 1)
    (fun m => 40 * m + 26) (fun m => 40 * m + 65) (fun m => 40 * m + 10) (fun m => 40 * m + 49)
    MuxCex.yvC MuxCex.xvC 4 0 0 where
  H_S_DATA k t h1 h2 := by
    show svB (MuxA.sTok t) = svB k
    rw [MuxA.sTok_eq k t h1 (by unfold MuxA.sS at h2 ⊢; omega)]
  H_X_DATA m t h1 h2 := by
    show MuxCex.yvC ((t - 26) / 40) = MuxCex.yvC m; rw [show (t - 26) / 40 = m by omega]
  H_Y_DATA m t h1 h2 := by
    show MuxCex.xvC ((t - 10) / 40) = MuxCex.xvC m; rw [show (t - 10) / 40 = m by omega]
  H_S_LEAD k := by
    rw [γ_eq]; unfold MuxA.sS
    rw [show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega]; simp only [ite_true]; omega
  H_X_LEAD m := by show _ ≤ 40 * (2 * m / 2) + 26 + 14 * (2 * m % 2); omega
  H_Y_LEAD m := by show _ ≤ 40 * (2 * m / 2) + 10 + 10 * (2 * m % 2); omega
  H_S_HOLD k := by
    show uW.fst (20 * (2 * k / 2) + 16 + 10 * (2 * k % 2)) ≤ _
    rw [fuW _ (by omega)]; unfold MuxA.sS; omega
  H_X_HOLD m := by
    rw [(XA_eq _).1]
    show 20 * (2 * (2 * m + 1) / 2) + 19 + 10 * (2 * (2 * m + 1) % 2) ≤ _; omega
  H_Y_HOLD m := by
    rw [(XA_eq _).2]; show 20 * (2 * (2 * m) / 2) + 19 + 10 * (2 * (2 * m) % 2) ≤ _; omega
  H_POS j := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [γ_eq]; split <;> omega
    · show 1 ≤ 40 * (j / 2) + 26 + 14 * (j % 2); omega
    · show 1 ≤ 40 * (j / 2) + 10 + 10 * (j % 2); omega
    · show 1 ≤ 20 * (j / 2) + 16 + 10 * (j % 2); omega

/-- `mux_value_ok_static` (value half) on this run. -/
theorem apply_ok (ds da db : Nat) (SD : MuxDataStatic run 1 ds da db 0 4 0 0) :
    ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + run.holdM uW ds da db k →
      zB ds da db t = run.zv MuxCex.yvC MuxCex.xvC k :=
  (mux_value_ok_static gates env causal static (by decide) hRE
    (z_rel ds da db) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) data_env SD).2

theorem Z_ev (k : Nat) : run.Z (2 * k) = 20 * k + 15 := by rw [Z_eq, E_eq]; omega

/-- Boundary: `shi = 9` (S_Z_S0's; S_Z_S1 has 1 to spare), `ahi = bhi = 5`. -/
theorem bnd : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + run.holdM uW 9 5 5 k →
    zB 9 5 5 t = run.zv MuxCex.yvC MuxCex.xvC k :=
  apply_ok 9 5 5 (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **S_Z_S0 alone** (`shi = 10`): `S_Z_S1` holds (with equality), `S_Z_S0`
fails by one tick, `S_Z_X`/`S_Z_Y` hold; x's token 0 (control token 1)
still reads token 0's select (y): `z (Z 2) = xvC 0 = 1` (y's bit), expected
x's bit `yvC 0 = 0`. So `S_Z_S0` is necessary on its own. -/
theorem cex_S_Z_S0 :
    ¬ (10 + 0 ≤ 4 + run.Wc0.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (10 + 0 ≤ 4 + run.Wc1.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 ≤ run.W0o.lo ∧ 1 ≤ run.W1o.lo) ∧
    (1 + 0 ≤ 0 + run.Wx.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 0 + run.Wy.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    run.sv 1 = false ∧ run.Z (2 * 1) = 35 ∧ zB 10 1 1 35 = true ∧
      run.zv MuxCex.yvC MuxCex.xvC 1 = false ∧
    ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 10 1 1 k → zB 10 1 1 t = run.zv MuxCex.yvC MuxCex.xvC k) ∧
    ¬ MuxDataStatic run 1 10 1 1 0 4 0 0 := by
  have z1 := Z_ev 1
  have hv : run.zv MuxCex.yvC MuxCex.xvC 1 = false := by
    unfold MuxRun.zv
    rw [show run.sv 1 = false from rfl, show (1 : Nat) = run.κ0 0 from rfl, idx_κ enum0 0]; rfl
  have nc : ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 10 1 1 k → zB 10 1 1 t = run.zv MuxCex.yvC MuxCex.xvC k) := by
    intro h
    have := h 1 35 (by rw [z1]; omega) (by
      unfold MuxRun.holdM; rw [show run.sv 1 = false from rfl]; decide)
    rw [hv] at this; revert this; decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, z1, by decide, hv, nc, ?_⟩
  intro SD; exact nc (apply_ok 10 1 1 SD)

/-- **S_Z_Y is tight when y is the late input** (`bhi = 6`, one past its
boundary; S_Z_S0/S1 and S_Z_X hold): control token 2 (y's token 1) sees
y's previous bit: `z (Z 4) = xvC 0 = 1`, expected `xvC 1 = 0`. -/
theorem cex_S_Z_Y :
    ¬ (6 + 0 ≤ 0 + run.Wy.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 4 + run.Wc0.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 4 + run.Wc1.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 0 + run.Wx.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    run.sv 2 = true ∧ run.Z (2 * 2) = 55 ∧ zB 1 1 6 55 = true ∧
      run.zv MuxCex.yvC MuxCex.xvC 2 = false ∧
    ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 1 1 6 k → zB 1 1 6 t = run.zv MuxCex.yvC MuxCex.xvC k) ∧
    ¬ MuxDataStatic run 1 1 1 6 0 4 0 0 := by
  have z2 := Z_ev 2
  have hv : run.zv MuxCex.yvC MuxCex.xvC 2 = false := by
    unfold MuxRun.zv
    rw [show run.sv 2 = true from rfl, show (2 : Nat) = run.κ1 1 from rfl, idx_κ enum1 1]; rfl
  have nc : ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 1 1 6 k → zB 1 1 6 t = run.zv MuxCex.yvC MuxCex.xvC k) := by
    intro h
    have := h 2 55 (by rw [z2]; omega) (by
      unfold MuxRun.holdM; rw [show run.sv 2 = true from rfl]; decide)
    rw [hv] at this; revert this; decide
  refine ⟨by decide, by decide, by decide, by decide, rfl, z2, by decide, hv, nc, ?_⟩
  intro SD; exact nc (apply_ok 1 1 6 SD)

end MuxB

/-! ## 3. `H_DEP` only at real edges: `cel_run_g` and `merge_ok_g`

`cel_run` asks the C-element's env latency (`H_DEP`) at EVERY edge of both
inputs. When one input `a` is gated (low across its gate-off tokens: x_req at
the merge's uxa in y's tokens, j0 at the mux's uxa) its edges in those tokens
are bookkeeping: the wire does not move there. In such a token the excitation
target is 0, `a` is low and the loop has settled low since the last real fall,
so the other input `b` (z_ack, which does pulse) cannot move the C-element.
`cel_run_g` asks `H_DEP` only in gate-on tokens, plus two plain ORDERING facts
(no loop latency): b's edges are ordered (`hbm`), and after a gate-off token
b's last fall reaches the C-element no later than a's next real rise (`hab`).
The conclusion is still stated on the bookkeeping phase starts
`max (ea j) (eb j)`, which needs them ordered (`hcm`) and unbounded edges. -/

-- Retiming bookkeeping edges is Lt3's `Tok.retime` (OpsCounter): a clean token
-- trace on unbounded edges is one on any nondecreasing sequence agreeing on
-- the gate-on tokens.

/-- a's edges with its gate-off tokens moved onto b's edges. -/
def rtA (ga : Nat → Bool) (ea eb : Nat → Nat) (j : Nat) : Nat := if ga (j / 2) then ea j else eb j

section celg
variable {a b rst O qp ex : Trace} {L : Ret} {wl wh : Nat}

theorem vph_odd' (k : Nat) : Vph (2 * k + 1) = false := by
  show decide ((2 * k + 1) % 2 = 0) = false; simp

/-- **`cel_run_g`: the gated C-element run with `H_DEP` only at real
edges.** Input `a` is gated by `ga`, input `b` pulses in every token. The
hypotheses beyond reset sequencing:
* `hdep` (H_DEP, real edges only): in a gate-on token, each phase start
  plus the loop precedes b's next edge, and a's next edge if that edge is real;
* `hbm`: b's edges are ordered at the C-element (no latency);
* `hab` (ordering, no latency): after a gate-off token, b's fall reaches the
  C-element no later than a's next real rise;
* `hcm`, `hua`, `hub`: the bookkeeping phase starts are ordered, and the
  edge sequences are unbounded (they only shape the statement).
Unlike `cel_run`, a's first edge need not follow reset release (reset holds
the excitation low until b's first edge, which must).
Conclusion: `cel_run`'s, the excitation is the token trace on
`max (ea j) (eb j)` with gate `ga`. -/
theorem cel_run_g (C : CEl a b rst O qp ex L wl wh) {T R : Nat} {ea eb : Nat → Nat}
    {ga : Nat → Bool} (ha : Tok T a ea ga) (hb : Tok T b eb (fun _ => true))
    (hrh : ∀ t, t < R → rst t = true) (hrl : ∀ t, R ≤ t → rst t = false)
    (hT : T ≤ R) (hR : L.hi + wh ≤ R) (hRb : R ≤ eb 0)
    (hdep : ∀ j, ga (j / 2) = true → max (ea j) (eb j) + L.hi + wh ≤ eb (j + 1) ∧
      (ga ((j + 1) / 2) = true → max (ea j) (eb j) + L.hi + wh ≤ ea (j + 1)))
    (hbm : ∀ j, eb j ≤ eb (j + 1))
    (hab : ∀ k, ga k = false → ga (k + 1) = true → eb (2 * k + 1) ≤ ea (2 * k + 2))
    (hcm : ∀ j, max (ea j) (eb j) ≤ max (ea (j + 1)) (eb (j + 1)))
    (hua : ∀ t, ∃ n, t < ea n) (hub : ∀ t, ∃ n, t < eb n) :
    Tok 0 ex (fun j => max (ea j) (eb j)) ga := by
  obtain ⟨A, hA⟩ : ∃ A : Nat → Nat, A = rtA ga ea eb := ⟨_, rfl⟩
  have eT : ∀ j, ga (j / 2) = true → A j = ea j := fun j h => by
    rw [hA]; unfold rtA; rw [h]; rfl
  have eF : ∀ j, ga (j / 2) = false → A j = eb j := fun j h => by
    rw [hA]; unfold rtA; rw [h]; rfl
  -- ordering of the retimed phase starts (no latency)
  have Ord : ∀ j, max (A j) (eb j) ≤ A (j + 1) ∧ max (A j) (eb j) ≤ eb (j + 1) := by
    intro j
    cases hg : ga (j / 2)
    · have h1 := eF j hg
      have hb1 := hbm j
      refine ⟨?_, by rw [h1]; omega⟩
      cases hg1 : ga ((j + 1) / 2)
      · rw [eF (j + 1) hg1, h1]; omega
      · have hj : j % 2 = 1 := by
          apply Classical.byContradiction; intro hn
          rw [show (j + 1) / 2 = j / 2 by omega, hg] at hg1; exact absurd hg1 (by simp)
        obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
        rw [eT _ hg1, h1]
        have := hab k (by rw [show (2 * k + 1) / 2 = k by omega] at hg; exact hg)
          (by rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega] at hg1; exact hg1)
        rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega]; omega
    · have h1 := eT j hg
      obtain ⟨d1, d2⟩ := hdep j hg
      refine ⟨?_, by rw [h1]; omega⟩
      cases hg1 : ga ((j + 1) / 2)
      · rw [eF (j + 1) hg1, h1]; omega
      · rw [eT (j + 1) hg1, h1]; have := d2 hg1; omega
  -- the loop latency in gate-on phases
  have Dep : ∀ j, ga (j / 2) = true →
      max (A j) (eb j) + L.hi + wh ≤ A (j + 1) ∧ max (A j) (eb j) + L.hi + wh ≤ eb (j + 1) := by
    intro j hg
    have h1 := eT j hg
    obtain ⟨d1, d2⟩ := hdep j hg
    refine ⟨?_, by rw [h1]; omega⟩
    cases hg1 : ga ((j + 1) / 2)
    · rw [eF (j + 1) hg1, h1]; omega
    · rw [eT (j + 1) hg1, h1]; have := d2 hg1; omega
  have Am : ∀ j, A j ≤ A (j + 1) := fun j => by have := (Ord j).1; omega
  have haR : Tok T a A ga := ha.retime hua (mono_of_step A Am) (fun k hk =>
    ⟨eT _ (by rw [show 2 * k / 2 = k by omega]; exact hk),
     eT _ (by rw [show (2 * k + 1) / 2 = k by omega]; exact hk)⟩)
  have cR : ∀ j, R ≤ max (A j) (eb j) := by
    intro j
    induction j with
    | zero => omega
    | succ j ih => have := Ord j; omega
  have hpre : ∀ s, 0 ≤ s → s < max (A 0) (eb 0) → ex s = false :=
    exc_hold C false 0 R (max (A 0) (eb 0))
      (fun s _ h => by rw [C.H_EX, hrh s h]; rfl)
      (fun s h1 h2 => ⟨hrl s h1, Or.inr ⟨by
        by_cases h3 : s < A 0
        · exact Or.inl (haR.pre s (by omega) h3)
        · exact Or.inr (hb.pre s (by omega) (by omega)), by omega⟩⟩)
  -- input values across a phase
  have va : ∀ j s, max (A j) (eb j) ≤ s → s < max (A (j + 1)) (eb (j + 1)) →
      (s < A (j + 1) → a s = (Vph j && ga (j / 2))) ∧
      (A (j + 1) ≤ s → a s = (Vph (j + 1) && ga ((j + 1) / 2))) := fun j s h1 h2 =>
    ⟨fun h3 => haR.at_phase j s (by have := cR j; omega) (by omega) h3,
      fun h3 => haR.at_phase (j + 1) s (by have := cR j; omega) h3
        (by have := Ord (j + 1); omega)⟩
  have vb : ∀ j s, max (A j) (eb j) ≤ s → s < max (A (j + 1)) (eb (j + 1)) →
      (s < eb (j + 1) → b s = (Vph j && true)) := fun j s h1 h2 h3 =>
    hb.at_phase j s (by have := cR j; omega) (by omega) h3
  -- one phase, given the settled-low invariant before a gate-off phase
  have step : ∀ j, (ga (j / 2) = false → ∃ l, l + L.hi + wh ≤ eb j ∧
        ∀ s, l ≤ s → s < max (A j) (eb j) → ex s = false) →
      (∀ s, max (A j) (eb j) ≤ s → s < max (A (j + 1)) (eb (j + 1)) →
        ex s = (Vph j && ga (j / 2))) ∧
      ((Vph j && ga (j / 2)) = false → ∃ l, l + L.hi + wh ≤ eb (j + 1) ∧
        ∀ s, l ≤ s → s < max (A (j + 1)) (eb (j + 1)) → ex s = false) := by
    intro j hprev
    cases hg : ga (j / 2)
    · -- gate off: a stays low, the loop has settled low since `l`
      obtain ⟨l, hl, hlow⟩ := hprev hg
      have hb1 := hbm j
      have hold := exc_hold C false l (max (A j) (eb j)) (max (A (j + 1)) (eb (j + 1)))
        (fun s h1 h2 => hlow s h1 h2)
        (fun s h1 h2 => ⟨hrl s (by have := cR j; omega), Or.inr ⟨by
          by_cases e1 : s < A (j + 1)
          · left; rw [(va j s h1 h2).1 e1, hg]; simp
          · have e2 : s < eb (j + 1) := by omega
            rcases Nat.mod_two_eq_zero_or_one j with hj | hj
            · left
              rw [(va j s h1 h2).2 (by omega), show (j + 1) / 2 = j / 2 by omega, hg]; simp
            · right
              rw [vb j s h1 h2 e2]
              obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
              rw [vph_odd']; rfl, by omega⟩⟩)
      refine ⟨fun s h1 h2 => by rw [Bool.and_false]; exact hold s (by omega) h2,
        fun _ => ⟨l, by omega, hold⟩⟩
    · -- gate on: an ordinary phase, both inputs move to the target
      obtain ⟨d1, d2⟩ := Dep j hg
      have v : ∀ s, max (A j) (eb j) ≤ s → s < max (A (j + 1)) (eb (j + 1)) → ex s = Vph j :=
        exc_hold C (Vph j) (max (A j) (eb j)) (max (A j) (eb j)) _ (fun s h1 h2 => by omega)
          (fun s h1 h2 => ⟨hrl s (by have := cR j; omega), by
            have ea1 : s < A (j + 1) → a s = Vph j := fun e1 => by
              rw [(va j s h1 h2).1 e1, hg]; simp
            have eb1 : s < eb (j + 1) → b s = Vph j := fun e2 => by
              rw [vb j s h1 h2 e2]; simp
            by_cases e1 : s < A (j + 1)
            · by_cases e2 : s < eb (j + 1)
              · exact Or.inl ⟨ea1 e1, eb1 e2⟩
              · exact Or.inr ⟨Or.inl (ea1 e1), by omega⟩
            · exact Or.inr ⟨Or.inr (eb1 (by omega)), by omega⟩⟩)
      refine ⟨fun s h1 h2 => by rw [Bool.and_true]; exact v s h1 h2, fun hv => ?_⟩
      rw [Bool.and_true] at hv
      exact ⟨max (A j) (eb j), d2, fun s h1 h2 => by rw [← hv]; exact v s h1 h2⟩
  have phase : ∀ j, (∀ s, max (A j) (eb j) ≤ s → s < max (A (j + 1)) (eb (j + 1)) →
        ex s = (Vph j && ga (j / 2))) ∧
      ((Vph j && ga (j / 2)) = false → ∃ l, l + L.hi + wh ≤ eb (j + 1) ∧
        ∀ s, l ≤ s → s < max (A (j + 1)) (eb (j + 1)) → ex s = false) := by
    intro j
    induction j with
    | zero => exact step 0 (fun _ => ⟨0, by omega, hpre⟩)
    | succ j ih =>
      apply step (j + 1)
      intro hg
      apply ih.2
      cases hg0 : ga (j / 2)
      · simp
      · have hj : j % 2 = 1 := by
          apply Classical.byContradiction; intro hn
          rw [show (j + 1) / 2 = j / 2 by omega, hg0] at hg; exact absurd hg (by simp)
        obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
        rw [vph_odd']; rfl
  have tok : Tok 0 ex (fun j => max (A j) (eb j)) ga := by
    refine ⟨fun t _ h2 => hpre t (by omega) h2, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · rw [(phase (2 * k)).1 t h1 h2, show 2 * k / 2 = k by omega]
      have : Vph (2 * k) = true := by show decide (2 * k % 2 = 0) = true; simp
      rw [this]; rfl
    · rw [(phase (2 * k + 1)).1 t h1 h2, vph_odd']; rfl
  refine tok.retime (fun t => ?_) (mono_of_step _ hcm) (fun k hk => ?_)
  · obtain ⟨n, hn⟩ := hub t; exact ⟨n, by omega⟩
  · rw [eT _ (by rw [show 2 * k / 2 = k by omega]; exact hk),
      eT _ (by rw [show (2 * k + 1) / 2 = k by omega]; exact hk)]
    exact ⟨rfl, rfl⟩

end celg

/-! ### `merge_ok` with `H_DEP` only at real edges -/

/-- **`merge_ok`'s timing obligations, real edges only.** Like
`MergeTimingNoSkew`, but uxa's `H_DEP_XA` is asked only in x's tokens (and
against x_req's next edge only when that edge is x's), uya's only in y's;
in their place two ORDERING facts without loop latency: when an x token
follows a y token, the y token's z_ack fall reaches uxa no later than x's
request does (`H_SEQ_XA`), and symmetrically. -/
structure MergeTimingG (P : MergeRun) (R : Nat) : Prop where
  H_RST_LONG : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
    P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R
  /-- Only z_ack's first edge must follow reset release; the requests may
  reach uxa/uya earlier (reset holds the C-elements low). -/
  H_RST_EARLY : R ≤ P.ZA0 0 ∧ R ≤ P.ZA1 0
  H_DEP_XA : ∀ j, P.sv (j / 2) = false → P.cx j + P.Lxa.hi + P.wxah ≤ P.ZA0 (j + 1) ∧
    (P.sv ((j + 1) / 2) = false → P.cx j + P.Lxa.hi + P.wxah ≤ P.AX (j + 1))
  H_DEP_YA : ∀ j, P.sv (j / 2) = true → P.cy j + P.Lya.hi + P.wyah ≤ P.ZA1 (j + 1) ∧
    (P.sv ((j + 1) / 2) = true → P.cy j + P.Lya.hi + P.wyah ≤ P.AY (j + 1))
  H_SEQ_XA : ∀ k, P.sv k = true → P.sv (k + 1) = false → P.ZA0 (2 * k + 1) ≤ P.AX (2 * k + 2)
  H_SEQ_YA : ∀ k, P.sv k = false → P.sv (k + 1) = true → P.ZA1 (2 * k + 1) ≤ P.AY (2 * k + 2)

/-- The old event-form obligations imply the new ones (strictly fewer). -/
theorem MergeTimingNoSkew.g {P : MergeRun} {R : Nat} (TM : MergeTimingNoSkew P R) : MergeTimingG P R := by
  refine ⟨TM.H_RST_LONG, ⟨TM.H_RST_EARLY.2.1, TM.H_RST_EARLY.2.2.2⟩, fun j _ => ⟨(TM.H_DEP_XA j).2, fun _ => (TM.H_DEP_XA j).1⟩,
    fun j _ => ⟨(TM.H_DEP_YA j).2, fun _ => (TM.H_DEP_YA j).1⟩, fun k _ _ => ?_, fun k _ _ => ?_⟩
  · have := (TM.H_DEP_XA (2 * k + 1)).1
    unfold MergeRun.cx at this; rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at this; omega
  · have := (TM.H_DEP_YA (2 * k + 1)).1
    unfold MergeRun.cy at this; rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at this; omega

section mergeg
variable {P : MergeRun} {Eo Es : Nat}

/-- z_ack's edges are ordered (port-level causality only). -/
theorem merge_ζ_step (Cs : MergeCausal P Eo Es) (j : Nat) : P.ζ j ≤ P.ζ (j + 1) := by
  have h2 := Cs.H_OWN j
  have hx : P.ζ j ≤ P.XA j := by
    have := P.Wzx.fst_ge (P.ζ j); have := P.Lxa.fst_ge (P.cx j); have := P.Wxa.fst_ge (P.Lxa.fst (P.cx j))
    unfold MergeRun.XA MergeRun.cx MergeRun.ZA0 at *; omega
  have hy : P.ζ j ≤ P.YA j := by
    have := P.Wzy.fst_ge (P.ζ j); have := P.Lya.fst_ge (P.cy j); have := P.Wya.fst_ge (P.Lya.fst (P.cy j))
    unfold MergeRun.YA MergeRun.cy MergeRun.ZA1 at *; omega
  have h3 := merge_ρ_le_S (P := P) (j + 1)
  have := P.Lor.fst_ge (orEdges (fun k => !P.sv k) P.XO P.YO (j + 1))
  have := P.Dz.fst_ge (P.Lor.fst (orEdges (fun k => !P.sv k) P.XO P.YO (j + 1)))
  have h4 := Cs.H_SRV (j + 1)
  unfold MergeRun.Z at h4
  split at h2 <;> omega

/-- **`merge_ok_g`: `merge_ok_noskew` with `H_DEP` only at real edges**
(`MergeTimingG`). Same conclusion. -/
theorem merge_ok_g {R : Nat} {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak : Trace}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (TM : MergeTimingG P R)
    (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es) :
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Ty yak P.YA P.sv ∧
    (∀ j, P.ρ j ≤ P.Z j ∧ P.ζ j ≤ P.XA j ∧ P.ζ j ≤ P.YA j) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := TM.H_RST_LONG
  obtain ⟨u2, u4⟩ := TM.H_RST_EARLY
  -- the z_req half and the ordering facts are those of `merge_ok_noskew`
  have st := merge_or_step Cs hEs
  have Su : ∀ j, j ≤ orEdges (fun k => !P.sv k) P.XO P.YO j := by
    intro j; induction j with
    | zero => omega
    | succ j ih => have := st j; omega
  have ρu : ∀ n, n < P.ρ (n + 1) := fun n => by have := Su n; have := merge_S_lt_ρ Cs hEs n; omega
  have ρm := merge_ρ_mono' Cs hEs
  have ζm : ∀ j, P.ζ j ≤ P.ζ (j + 1) := merge_ζ_step Cs
  have ρζ : ∀ j, P.ρ j ≤ P.ζ j := fun j => by
    have := merge_ρ_le_S (P := P) j
    have := P.Lor.fst_ge (orEdges (fun k => !P.sv k) P.XO P.YO j)
    have := P.Dz.fst_ge (P.Lor.fst (orEdges (fun k => !P.sv k) P.XO P.YO j))
    have := Cs.H_SRV j; unfold MergeRun.Z at *; omega
  have AXm : ∀ j, P.AX j ≤ P.AX (j + 1) := fun j => fst_mono _ (ρm j (j + 1) (by omega))
  have AYm : ∀ j, P.AY j ≤ P.AY (j + 1) := fun j => fst_mono _ (ρm j (j + 1) (by omega))
  have Z0m : ∀ j, P.ZA0 j ≤ P.ZA0 (j + 1) := fun j => fst_mono _ (ζm j)
  have Z1m : ∀ j, P.ZA1 j ≤ P.ZA1 (j + 1) := fun j => fst_mono _ (ζm j)
  have AXu : ∀ t, ∃ n, t < P.AX n := fun t =>
    ⟨t + 1, by have := ρu t; have := P.Wxc.fst_ge (P.ρ (t + 1)); unfold MergeRun.AX; omega⟩
  have AYu : ∀ t, ∃ n, t < P.AY n := fun t =>
    ⟨t + 1, by have := ρu t; have := P.Wyc.fst_ge (P.ρ (t + 1)); unfold MergeRun.AY; omega⟩
  have Z0u : ∀ t, ∃ n, t < P.ZA0 n := fun t =>
    ⟨t + 1, by have := ρu t; have := ρζ (t + 1); have := P.Wzx.fst_ge (P.ζ (t + 1)); unfold MergeRun.ZA0; omega⟩
  have Z1u : ∀ t, ∃ n, t < P.ZA1 n := fun t =>
    ⟨t + 1, by have := ρu t; have := ρζ (t + 1); have := P.Wzy.fst_ge (P.ζ (t + 1)); unfold MergeRun.ZA1; omega⟩
  have Sm := mono_of_step (orEdges (fun k => !P.sv k) P.XO P.YO) (fun j => Nat.le_of_lt (st j))
  have p0 : Tok (P.Wxo.hi + P.Wyo.hi) xo P.XO (fun k => !P.sv k) :=
    (V.H_X.fifo P.Wxo G.H_WXO).mono (by omega)
  have p1 : Tok (P.Wxo.hi + P.Wyo.hi) yo P.YO (fun k => !(!P.sv k)) :=
    ((V.H_Y.fifo P.Wyo G.H_WYO).mono (by omega)).gcongr (fun k => by simp)
  have o := or_tok_mono p0 p1
    (fun t => ⟨t + 1, by have := ρu t; have := P.Wxo.fst_ge (P.ρ (t + 1)); unfold MergeRun.XO; omega⟩)
    (fun t => ⟨t + 1, by have := ρu t; have := P.Wyo.fst_ge (P.ρ (t + 1)); unfold MergeRun.YO; omega⟩)
    Sm
  have zt := (o.fifo P.Lor (y := ei) (fun t ht => by rw [G.H_UOR t ht, or2_spec])).fifo P.Dz G.H_DZ
  -- uxa: x_req gated by x's tokens, z_ack in every token
  have ax : Tok R xc P.AX (fun k => !P.sv k) := (V.H_X.fifo P.Wxc G.H_WXC).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl xc zx rst xa qa (fun t => c2B (xc t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run_g CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u2
    (fun j hj => by
      have h := TM.H_DEP_XA j (by simpa using hj)
      exact ⟨h.1, fun h2 => h.2 (by simpa using h2)⟩)
    Z0m (fun k h1 h2 => TM.H_SEQ_XA k (by simpa using h1) (by simpa using h2))
    (fun j => by have := AXm j; have := Z0m j; omega) AXu Z0u)
  -- uya
  have ay : Tok R yc P.AY P.sv := (V.H_Y.fifo P.Wyc G.H_WYC).mono (by omega)
  have zy' : Tok R zy P.ZA1 (fun _ => true) := (V.H_ZA.fifo P.Wzy G.H_WZY).mono (by omega)
  have CY : CEl yc zy rst ya qb (fun t => c2B (yc t) (zy t) (qb t) (rst t)) P.Lya P.wyal P.wyah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UYA, G.H_UYA_FB, G.H_UYA_POS⟩
  have ny := cel_node CY (cel_run_g CY ay zy' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u4
    TM.H_DEP_YA Z1m TM.H_SEQ_YA (fun j => by have := AYm j; have := Z1m j; omega) AYu Z1u)
  refine ⟨zt.congr (fun j => rfl), nx.fifo P.Wxa G.H_WXA, ny.fifo P.Wya G.H_WYA, fun j => ⟨?_, ?_, ?_⟩⟩
  · have := merge_ρ_le_S (P := P) j
    have := P.Lor.fst_ge (orEdges (fun k => !P.sv k) P.XO P.YO j)
    have := P.Dz.fst_ge (P.Lor.fst (orEdges (fun k => !P.sv k) P.XO P.YO j))
    unfold MergeRun.Z; omega
  · unfold MergeRun.XA MergeRun.cx MergeRun.ZA0
    have := P.Wzx.fst_ge (P.ζ j)
    have := P.Lxa.fst_ge (max (P.AX j) (P.Wzx.fst (P.ζ j)))
    have := P.Wxa.fst_ge (P.Lxa.fst (max (P.AX j) (P.Wzx.fst (P.ζ j))))
    omega
  · unfold MergeRun.YA MergeRun.cy MergeRun.ZA1
    have := P.Wzy.fst_ge (P.ζ j)
    have := P.Lya.fst_ge (max (P.AY j) (P.Wzy.fst (P.ζ j)))
    have := P.Wya.fst_ge (P.Lya.fst (max (P.AY j) (P.Wzy.fst (P.ζ j))))
    omega

/-- `merge_ok_g` generalises `merge_ok_noskew` (its hypothesis is implied by
the old one, `MergeTimingNoSkew.g`), and is not vacuous: Lt's unit merge run. -/
theorem MergeWit.g_witness :
    Tok MergeWit.run.Tx MergeWit.xak MergeWit.run.XA (fun k => !MergeWit.run.sv k) :=
  (merge_ok_g MergeWit.gates MergeWit.env
    (merge_timing_ns_of_static MergeWit.causal MergeWit.static.ns (by decide) MergeCex.hRE).g
    MergeWit.causal (Nat.le_refl 1)).2.1

end mergeg

/-! ### The static form: node-launched, spread-free

With `H_DEP` asked only in the owner's tokens, every instance is launched by
a REAL edge of uxa's node: in an x token the next x_req edge and the next
z_ack edge are both causally after x_ack, i.e. after the node. So each loop
bound is node-launched (`S_XA_N`) and carries no wire-spread term, and the
fork condition of a y → x hand-over needs no loop term (`S_XA_SEQ`). -/

/-- **Static per-arc obligations of the merge, real edges only.** -/
structure MergeStaticG (P : MergeRun) (Eo Es wo wz la wa : Nat) : Prop where
  H_WO : wo ≤ P.Wxo.lo ∧ wo ≤ P.Wyo.lo
  H_WZ : wz ≤ P.Wzx.lo ∧ wz ≤ P.Wzy.lo
  H_LA : la ≤ P.Lxa.lo ∧ la ≤ P.Lya.lo
  H_WA : wa ≤ P.Wxa.lo ∧ wa ≤ P.Wya.lo
  /-- **S_XA_SEQ** (`z_ack -> {uxa, uya}` fork at a y → x hand-over, no
  loop term): y's token's z_ack fall reaches uxa no later than x's next
  request, which waits for y_ack's fall. -/
  S_XA_SEQ : P.Wzx.hi ≤ (wz + la + wa + Eo) + P.Wxc.lo
  S_YA_SEQ : P.Wzy.hi ≤ (wz + la + wa + Eo) + P.Wyc.lo
  /-- **S_XA_N** (uxa's loop, node-launched): after uxa's node moves in an x
  token, x_ack moves at the client (`Lxa.lo + Wxa.lo`), the client reacts
  (`Eo`), and the next x_req edge reaches uxa (`Wxc.lo`), or the next request
  runs through the server and z_ack reaches uxa (`Kz + Wzx.lo`). The loop
  must settle first. -/
  S_XA_N : P.Lxa.hi + P.wxah ≤ P.Lxa.lo + P.Wxa.lo + Eo + P.Wxc.lo ∧
    P.Lxa.hi + P.wxah ≤ P.Lxa.lo + P.Wxa.lo + Eo + (wo + P.Lor.lo + P.Dz.lo + Es) + P.Wzx.lo
  S_YA_N : P.Lya.hi + P.wyah ≤ P.Lya.lo + P.Wya.lo + Eo + P.Wyc.lo ∧
    P.Lya.hi + P.wyah ≤ P.Lya.lo + P.Wya.lo + Eo + (wo + P.Lor.lo + P.Dz.lo + Es) + P.Wzy.lo

/-- The old static set implies the new one (`S_XA_FORK ⇒ S_XA_SEQ`, and
`S_XA_FORK`, `S_XA_ZA` ⇒ `S_XA_N`); `S_XA_R` is no longer needed. -/
theorem MergeStaticNS.g {P : MergeRun} {Eo Es wo wz la wa : Nat} (S : MergeStaticNS P Eo Es wo wz la wa) :
    MergeStaticG P Eo Es wo wz la wa := by
  have := S.H_WZ; have := S.H_LA; have := S.H_WA; have := S.S_XA_FORK; have := S.S_YA_FORK
  have := S.S_XA_ZA; have := S.S_YA_ZA
  have := P.Wzx.lo_le_hi; have := P.Wzy.lo_le_hi
  exact ⟨S.H_WO, S.H_WZ, S.H_LA, S.H_WA, by omega, by omega, ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

section mergegs
variable {P : MergeRun} {Eo Es wo wz la wa : Nat}

theorem merge_RZ_g (Cs : MergeCausal P Eo Es) (S : MergeStaticG P Eo Es wo wz la wa)
    (j : Nat) : P.ρ j + (wo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
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

/-- **The real-edge event obligations from causality and `MergeStaticG`.** -/
theorem merge_timing_g_of_static {R : Nat} (Cs : MergeCausal P Eo Es) (S : MergeStaticG P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.ZA0 0 ∧ R ≤ P.ZA1 0) : MergeTimingG P R := by
  have RZ := merge_RZ_g Cs S
  have hWZ := S.H_WZ; have hLA := S.H_LA; have hWA := S.H_WA
  have pz : ∀ j, 1 ≤ P.ζ j := fun j => by have := RZ j; have := Cs.H_POS j; omega
  -- after uxa's node edge in an x token: x_ack, the client, the next request
  have NX : ∀ j, P.sv (j / 2) = false → P.cx j + P.Lxa.lo + P.Wxa.lo + Eo ≤ P.ρ (j + 1) := by
    intro j hs
    have ho := Cs.H_OWN j; rw [hs] at ho; simp only [Bool.false_eq_true, ite_false] at ho
    have hc : 1 ≤ P.cx j := by
      have := fl P.Wzx (pz j); have := pz j; unfold MergeRun.cx MergeRun.ZA0; omega
    have b := fl P.Lxa hc
    have c := fl P.Wxa (c := P.Lxa.fst (P.cx j)) (by omega)
    have : P.XA j = P.Wxa.fst (P.Lxa.fst (P.cx j)) := rfl
    omega
  have NY : ∀ j, P.sv (j / 2) = true → P.cy j + P.Lya.lo + P.Wya.lo + Eo ≤ P.ρ (j + 1) := by
    intro j hs
    have ho := Cs.H_OWN j; rw [hs] at ho; simp only [ite_true] at ho
    have hc : 1 ≤ P.cy j := by
      have := fl P.Wzy (pz j); have := pz j; unfold MergeRun.cy MergeRun.ZA1; omega
    have b := fl P.Lya hc
    have c := fl P.Wya (c := P.Lya.fst (P.cy j)) (by omega)
    have : P.YA j = P.Wya.fst (P.Lya.fst (P.cy j)) := rfl
    omega
  refine ⟨hRL, hRE, fun j hs => ⟨?_, fun _ => ?_⟩, fun j hs => ⟨?_, fun _ => ?_⟩,
    fun k h1 h2 => ?_, fun k h1 h2 => ?_⟩
  · have := NX j hs; have := RZ (j + 1); have := fl P.Wzx (pz (j + 1)); have := S.S_XA_N
    unfold MergeRun.ZA0; omega
  · have := NX j hs; have := fl P.Wxc (Cs.H_POS (j + 1)); have := S.S_XA_N
    unfold MergeRun.AX; omega
  · have := NY j hs; have := RZ (j + 1); have := fl P.Wzy (pz (j + 1)); have := S.S_YA_N
    unfold MergeRun.ZA1; omega
  · have := NY j hs; have := fl P.Wyc (Cs.H_POS (j + 1)); have := S.S_YA_N
    unfold MergeRun.AY; omega
  · -- y's token k, then x's: y_ack fell after z_ack's fall, then x requested
    have ho := Cs.H_OWN (2 * k + 1)
    rw [show (2 * k + 1) / 2 = k by omega, h1] at ho; simp only [ite_true] at ho
    have := merge_ζ_le_YA (P := P) (2 * k + 1) (pz _)
    have := P.Wzx.fst_le (P.ζ (2 * k + 1)); have := fl P.Wxc (Cs.H_POS (2 * k + 1 + 1))
    have := S.S_XA_SEQ
    unfold MergeRun.ZA0 MergeRun.AX; rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega]; omega
  · have ho := Cs.H_OWN (2 * k + 1)
    rw [show (2 * k + 1) / 2 = k by omega, h1] at ho; simp only [Bool.false_eq_true, ite_false] at ho
    have := merge_ζ_le_XA (P := P) (2 * k + 1) (pz _)
    have := P.Wzy.fst_le (P.ζ (2 * k + 1)); have := fl P.Wyc (Cs.H_POS (2 * k + 1 + 1))
    have := S.S_YA_SEQ
    unfold MergeRun.ZA1 MergeRun.AY; rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega]; omega

/-- **`merge_ok_gs`**: `merge_ok`'s conclusion from causal partners, reset
sequencing and `MergeStaticG` (no `S_OR`, no `S_XA_R`, no spread terms). -/
theorem merge_ok_gs {R : Nat} {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak : Trace}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es)
    (S : MergeStaticG P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.ZA0 0 ∧ R ≤ P.ZA1 0) :
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Ty yak P.YA P.sv ∧
    (∀ j, P.ρ j ≤ P.Z j ∧ P.ζ j ≤ P.XA j ∧ P.ζ j ≤ P.YA j) :=
  merge_ok_g G V (merge_timing_g_of_static Cs S hRL hRE) Cs hEs

end mergegs

/-! ### `S_XA_N` is tight: a long uxa feedback wire

`MergeN.run w`: Lt's unit-delay merge run (`MergeWit.run`) with uxa's
feedback wire a `w`-tick transport delay (window `[w, w]`) and reset high on
`[0, 8)` (x_req reaches uxa at `5`, during reset, which `MergeTimingG`
allows). uxa's derived edges do not depend on `w`. In x's token 0 the node
rises at `10`, x_ack at `11`; x drops its request at `12`, which reaches uxa
at `13`, while z_ack is still high there (until `17`). `S_XA_N`'s first form
reads `1 + w ≤ 1 + 1 + 1 + 1`: at `w = 3` it holds with equality and
`merge_ok_gs` applies; at `w = 4` it fails by one tick, and the LUT, still
reading its own pre-rise output through the long feedback wire, computes
`C(0, 1, 0) = 0`: x_ack drops at `15`, inside x's token. -/
namespace MergeN
set_option maxRecDepth 100000

def run (w : Nat) : MergeRun := { MergeWit.run with wxal := w, wxah := w }

def rst8 (t : Nat) : Bool := decide (t < 8)

/-- uxa with a `w`-tick feedback wire: `xaH w n` is the trace up to time `n`. -/
def xaH (w : Nat) : Nat → Nat → Bool
  | 0 => fun _ => false
  | n + 1 => fun s => if s ≤ n then xaH w n s
      else c2B (MergeWit.xo n) (MergeWit.zx n) (xaH w n (n - w)) (rst8 n)
def xa (w : Nat) (t : Nat) : Bool := xaH w t t
def qa (w : Nat) (t : Nat) : Bool := xa w (t - w)
def xak (w : Nat) (t : Nat) : Bool := xa w (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (MergeWit.yo 0) (MergeWit.zx 0) false (rst8 0)
  | t + 2 => c2B (MergeWit.yo (t + 1)) (MergeWit.zx (t + 1)) (ya t) (rst8 (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem xaH_stable (w : Nat) : ∀ n s, s ≤ n → xaH w n s = xa w s := by
  intro n
  induction n with
  | zero => intro s hs; have : s = 0 := by omega
            subst this; rfl
  | succ n ih =>
    intro s hs
    by_cases h : s ≤ n
    · show (if s ≤ n then xaH w n s else _) = _; rw [ite_eq_left_iff.mpr (fun hn => absurd h hn)]; exact ih s h
    · have : s = n + 1 := by omega
      subst this; rfl

theorem gates (w : Nat) : MergeGates (run w) rst8 MergeWit.x MergeWit.y MergeWit.za MergeWit.xo MergeWit.yo
    MergeWit.ei MergeWit.zr MergeWit.xo MergeWit.yo MergeWit.zx MergeWit.zx (xa w) (qa w) ya qb
    (xak w) yak where
  H_WXO _ _ := rfl
  H_WYO _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_WXC _ _ := rfl
  H_WYC _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by have : 1 ≤ t := ht; omega⟩
    show xaH w (n + 1) (n + 1) = c2B (MergeWit.xo (n + 1 - 1)) (MergeWit.zx (n + 1 - 1))
      (xa w (n + 1 - 1 - w)) (rst8 (n + 1 - 1))
    rw [show n + 1 - 1 = n by omega, ← xaH_stable w n (n - w) (by omega)]
    show (if n + 1 ≤ n then _ else _) = _
    split
    · omega
    · rfl
  H_UXA_FB t ht := by
    have : w ≤ t := ht
    show ∃ s, t ≤ s + w ∧ s + w ≤ t ∧ qa w t = xa w s
    exact ⟨t - w, by omega, by omega, rfl⟩
  H_UXA_POS := by show 1 ≤ 1 + w; omega
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by show 1 ≤ 1 + 1; omega
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem env (w : Nat) : MergeEnv (run w) rst8 MergeWit.x MergeWit.y MergeWit.za 8 where
  H_RST_HI t h := by simp [rst8, h]
  H_RST_LO t h := by simp [rst8]; omega
  H_X := MergeWit.env.H_X
  H_Y := MergeWit.env.H_Y
  H_ZA := MergeWit.env.H_ZA

theorem causal (w : Nat) : MergeCausal (run w) 1 1 :=
  ⟨MergeWit.causal.H_OWN, MergeWit.causal.H_SRV, MergeWit.causal.H_POS⟩

theorem hRL (w : Nat) (hw : w ≤ 7) : (run w).Wxc.hi ≤ 8 ∧ (run w).Wyc.hi ≤ 8 ∧ (run w).Wzx.hi ≤ 8 ∧
    (run w).Wzy.hi ≤ 8 ∧ (run w).Lxa.hi + (run w).wxah ≤ 8 ∧ (run w).Lya.hi + (run w).wyah ≤ 8 := by
  show 1 ≤ 8 ∧ 1 ≤ 8 ∧ 1 ≤ 8 ∧ 1 ≤ 8 ∧ 1 + w ≤ 8 ∧ 1 + 1 ≤ 8; omega

theorem hRE (w : Nat) : 8 ≤ (run w).ZA0 0 ∧ 8 ≤ (run w).ZA1 0 := by
  refine ⟨?_, ?_⟩
  · show 8 ≤ uW.fst (8 * 0 + 8); rw [fuW _ (by omega)]; omega
  · show 8 ≤ uW.fst (8 * 0 + 8); rw [fuW _ (by omega)]; omega

/-- Boundary `w = 3`: `MergeStaticG` holds, `S_XA_N` with equality, and
`merge_ok_gs` gives clean acknowledges. -/
theorem static3 : MergeStaticG (run 3) 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem bnd_S_XA_N :
    (run 3).Lxa.hi + (run 3).wxah = (run 3).Lxa.lo + (run 3).Wxa.lo + 1 + (run 3).Wxc.lo ∧
    Tok (run 3).Tx (xak 3) (run 3).XA (fun k => !(run 3).sv k) ∧
    Tok (run 3).Ty yak (run 3).YA (run 3).sv :=
  let h := merge_ok_gs (gates 3) (env 3) (causal 3) (Nat.le_refl 1) static3 (hRL 3 (by decide)) (hRE 3)
  ⟨by decide, h.2.1, h.2.2.1⟩

/-- At `w = 4`, every `MergeStaticG` field holds except `S_XA_N`'s first form,
which fails by one tick (`5 > 4`). -/
theorem static_but_N4 :
    (1 ≤ (run 4).Wxo.lo ∧ 1 ≤ (run 4).Wyo.lo) ∧ (1 ≤ (run 4).Wzx.lo ∧ 1 ≤ (run 4).Wzy.lo) ∧
    (1 ≤ (run 4).Lxa.lo ∧ 1 ≤ (run 4).Lya.lo) ∧ (1 ≤ (run 4).Wxa.lo ∧ 1 ≤ (run 4).Wya.lo) ∧
    (run 4).Wzx.hi ≤ (1 + 1 + 1 + 1) + (run 4).Wxc.lo ∧
    (run 4).Wzy.hi ≤ (1 + 1 + 1 + 1) + (run 4).Wyc.lo ∧
    (run 4).Lxa.hi + (run 4).wxah ≤
      (run 4).Lxa.lo + (run 4).Wxa.lo + 1 + (1 + (run 4).Lor.lo + (run 4).Dz.lo + 1) + (run 4).Wzx.lo ∧
    (run 4).Lya.hi + (run 4).wyah ≤ (run 4).Lya.lo + (run 4).Wya.lo + 1 + (run 4).Wyc.lo ∧
    (run 4).Lya.hi + (run 4).wyah ≤
      (run 4).Lya.lo + (run 4).Wya.lo + 1 + (1 + (run 4).Lor.lo + (run 4).Dz.lo + 1) + (run 4).Wzy.lo ∧
    (run 4).Lxa.hi + (run 4).wxah = (run 4).Lxa.lo + (run 4).Wxa.lo + 1 + (run 4).Wxc.lo + 1 := by
  decide

theorem glitch_values :
    (run 4).XA 0 = 11 ∧ (run 4).XA 1 = 19 ∧ (run 4).sv 0 = false ∧
    xak 4 11 = true ∧ xak 4 14 = true ∧ xak 4 15 = false ∧ xak 4 16 = true ∧
    xak 3 15 = true ∧ xak 3 18 = true ∧ xak 3 19 = false := by
  refine ⟨(MergeWit.XA_eq 0).1, (MergeWit.XA_eq 1).1, rfl, ?_⟩
  decide

/-- **`S_XA_N` is exact (its x_req form, tight by one tick).** At `w = 4`
every hypothesis of `merge_ok_gs` except that field holds (`gates`, `env`,
`causal`, `static_but_N4`, `hRL`, `hRE`), and x_ack is not a clean token
trace: it is low at `15`, inside x's token 0 (`[XA 0, XA 1) = [11, 19)`).
The event form fails at `H_DEP_XA 0` against x_req's next edge. -/
theorem cex_S_XA_N :
    ¬ Tok (run 4).Tx (xak 4) (run 4).XA (fun k => !(run 4).sv k) ∧
    ¬ MergeStaticG (run 4) 1 1 1 1 1 1 ∧ ¬ MergeTimingG (run 4) 8 := by
  have g := glitch_values
  refine ⟨fun h => ?_, fun S => ?_, fun TM => ?_⟩
  · have := h.hi 0 15 (by decide) (by rw [g.1]; omega) (by rw [g.2.1]; omega)
    rw [g.2.2.2.2.2.1, g.2.2.1] at this; exact absurd this (by decide)
  · have := S.S_XA_N.1; revert this; decide
  · have h := (TM.H_DEP_XA 0 rfl).2 rfl
    have e1 : (run 4).cx 0 = 9 := by
      show max (uW.fst (8 * 0 + 4)) (uW.fst (8 * 0 + 8)) = 9
      rw [fuW (8 * 0 + 4) (by omega), fuW (8 * 0 + 8) (by omega)]; omega
    have e2 : (run 4).AX (0 + 1) = 13 := by
      show uW.fst (8 * 1 + 4) = 13; rw [fuW _ (by omega)]
    rw [e1, e2] at h; revert h; decide

end MergeN

/-! ### `S_XA_SEQ` is tight: a slow z_ack → uxa wire at a y → x hand-over

`MergeS.run d`: every LUT and wire one tick except the z_ack → uxa wire,
a `d`-tick transport delay; reset high on `[0, 8)`. Merged tokens alternate
x (even) and y (odd), period `42` per pair, every partner reacting as early
as `MergeCausal _ 1 1` allows at the y → x hand-over: y's token `2m+1`
requests at `42m+30`, z_ack falls at `42m+42`, y_ack falls at `42m+45` and x
requests at `42m+46`, reaching uxa at `42m+47`; z_ack's fall reaches uxa at
`42m+42+d`. `S_XA_SEQ` reads `d ≤ 1 + 1 + 1 + 1 + 1`: at `d = 5` every field
of `MergeStaticG` holds and `merge_ok_gs` applies; at `d = 6` only
`S_XA_SEQ` fails (by one tick) and uxa sees x_req high while the stale z_ack
pulse of y's token is still high: `C(1, 1, 0) = 1`, x_ack rises inside y's
slot, before the server has answered x's request. -/
namespace MergeS
set_option maxRecDepth 100000

def ρS (d j : Nat) : Nat :=
  42 * (j / 4) + 4 + 26 * ((j / 2) % 2) + (if j % 2 = 0 then 0 else if (j / 2) % 2 = 0 then 7 + d else 8)

def run (d : Nat) : MergeRun where
  Wxo := uW
  Wyo := uW
  Lor := uW
  Dz := uW
  Wxc := uW
  Wyc := uW
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
  ρ j := ρS d j
  ζ j := ρS d j + 4
  sv := svW

def rst8 (t : Nat) : Bool := decide (t < 8)
def x (d t : Nat) : Bool := decide (4 ≤ t ∧ (t - 4) % 42 < 7 + d)
def y (t : Nat) : Bool := decide (30 ≤ t ∧ (t - 30) % 42 < 8)
def za (d t : Nat) : Bool := decide (8 ≤ t ∧ ((t - 8) % 42 < 7 + d ∨ (26 ≤ (t - 8) % 42 ∧ (t - 8) % 42 < 34)))
def xo (d t : Nat) : Bool := x d (t - 1)
def yo (t : Nat) : Bool := y (t - 1)
def ei (d t : Nat) : Bool := or2B (xo d (t - 1)) (yo (t - 1))
def zr (d t : Nat) : Bool := ei d (t - 1)
def zx (d t : Nat) : Bool := za d (t - d)
def zy (d t : Nat) : Bool := za d (t - 1)
def xa (d : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (xo d 0) (zx d 0) false (rst8 0)
  | t + 2 => c2B (xo d (t + 1)) (zx d (t + 1)) (xa d t) (rst8 (t + 1))
def qa (d t : Nat) : Bool := xa d (t - 1)
def ya (d : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (yo 0) (zy d 0) false (rst8 0)
  | t + 2 => c2B (yo (t + 1)) (zy d (t + 1)) (ya d t) (rst8 (t + 1))
def qb (d t : Nat) : Bool := ya d (t - 1)
def xak (d t : Nat) : Bool := xa d (t - 1)
def yak (d t : Nat) : Bool := ya d (t - 1)

theorem gates (d : Nat) : MergeGates (run d) rst8 (x d) y (za d) (xo d) yo (ei d) (zr d) (xo d) yo
    (zx d) (zy d) (xa d) (qa d) (ya d) (qb d) (xak d) (yak d) where
  H_WXO _ _ := rfl
  H_WYO _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_WXC _ _ := rfl
  H_WYC _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UXA_FB := win11 (fun _ _ => rfl)
  H_UXA_POS := by show 1 ≤ 1 + 1; omega
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by show 1 ≤ 1 + 1; omega
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

/-- The request edges of merged token `k`: rise `ρS (2k)`, fall `ρS (2k+1)`. -/
theorem ρ_e (d k : Nat) : ρS d (2 * k) = 42 * (k / 2) + 4 + 26 * (k % 2) := by
  unfold ρS; rw [show 2 * k / 4 = k / 2 by omega, show 2 * k / 2 = k by omega]; simp
theorem ρ_o (d k : Nat) : ρS d (2 * k + 1) =
    42 * (k / 2) + 4 + 26 * (k % 2) + (if k % 2 = 0 then 7 + d else 8) := by
  unfold ρS
  rw [show (2 * k + 1) / 4 = k / 2 by omega, show (2 * k + 1) / 2 = k by omega,
    show (2 * k + 1) % 2 = 1 by omega]
  simp

theorem sv_eq (d k : Nat) : (run d).sv k = decide (k % 2 = 1) := rfl

theorem env (d : Nat) (hd : d ≤ 6) : MergeEnv (run d) rst8 (x d) y (za d) 8 where
  H_RST_HI t h := by simp [rst8, h]
  H_RST_LO t h := by simp [rst8]; omega
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < ρS d (2 * 0) := h2
      rw [ρ_e] at h2; simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : ρS d (2 * k) ≤ t := h1
      have h2 : t < ρS d (2 * k + 1) := h2
      rw [ρ_e] at h1; rw [ρ_o] at h2
      rw [sv_eq]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hk] at h1 h2; simp only [ite_true] at h2
        simp only [x, hk]; simp; omega
      · rw [hk] at h1 h2; simp only [show (1 : Nat) ≠ 0 from by omega, ite_false] at h2
        simp only [x, hk]; simp; omega
    · have h1 : ρS d (2 * k + 1) ≤ t := h1
      have h2 : t < ρS d (2 * (k + 1)) := h2
      rw [ρ_o] at h1; rw [ρ_e] at h2
      simp only [x, decide_eq_false_iff_not]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hk] at h1; simp only [ite_true] at h1; omega
      · rw [hk] at h1; simp only [show (1 : Nat) ≠ 0 from by omega, ite_false] at h1; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < ρS d (2 * 0) := h2
      rw [ρ_e] at h2; simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : ρS d (2 * k) ≤ t := h1
      have h2 : t < ρS d (2 * k + 1) := h2
      rw [ρ_e] at h1; rw [ρ_o] at h2
      rw [sv_eq]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hk] at h1 h2; simp only [ite_true] at h2
        simp only [y, hk]; simp; omega
      · rw [hk] at h1 h2; simp only [show (1 : Nat) ≠ 0 from by omega, ite_false] at h2
        simp only [y, hk]; simp; omega
    · have h1 : ρS d (2 * k + 1) ≤ t := h1
      have h2 : t < ρS d (2 * (k + 1)) := h2
      rw [ρ_o] at h1; rw [ρ_e] at h2
      simp only [y, decide_eq_false_iff_not]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hk] at h1; simp only [ite_true] at h1; omega
      · rw [hk] at h1; simp only [show (1 : Nat) ≠ 0 from by omega, ite_false] at h1; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < ρS d (2 * 0) + 4 := h2
      rw [ρ_e] at h2; simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : ρS d (2 * k) + 4 ≤ t := h1
      have h2 : t < ρS d (2 * k + 1) + 4 := h2
      rw [ρ_e] at h1; rw [ρ_o] at h2
      simp only [za, decide_eq_true_eq]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hk] at h1 h2; simp only [ite_true] at h2; omega
      · rw [hk] at h1 h2; simp only [show (1 : Nat) ≠ 0 from by omega, ite_false] at h2; omega
    · have h1 : ρS d (2 * k + 1) + 4 ≤ t := h1
      have h2 : t < ρS d (2 * (k + 1)) + 4 := h2
      rw [ρ_o] at h1; rw [ρ_e] at h2
      simp only [za, decide_eq_false_iff_not]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk
      · rw [hk] at h1; simp only [ite_true] at h1; omega
      · rw [hk] at h1; simp only [show (1 : Nat) ≠ 0 from by omega, ite_false] at h1; omega

theorem ρpos (d j : Nat) : 4 ≤ ρS d j := by unfold ρS; omega

theorem AX_eq (d j : Nat) : (run d).AX j = ρS d j + 1 := by
  show uW.fst (ρS d j) = _; rw [fuW _ (by have := ρpos d j; omega)]
theorem AY_eq (d j : Nat) : (run d).AY j = ρS d j + 1 := by
  show uW.fst (ρS d j) = _; rw [fuW _ (by have := ρpos d j; omega)]
theorem ZA0_eq (d j : Nat) : (run d).ZA0 j = ρS d j + 4 + d := by
  show (Ret.shift d).fst (ρS d j + 4) = _; rw [Ret.fst_shift d _ (by omega)]
theorem ZA1_eq (d j : Nat) : (run d).ZA1 j = ρS d j + 5 := by
  show uW.fst (ρS d j + 4) = _; rw [fuW _ (by omega)]
theorem XA_eq (d j : Nat) : (run d).XA j = ρS d j + 6 + d := by
  show uW.fst (uW.fst (max ((run d).AX j) ((run d).ZA0 j))) = _
  rw [AX_eq, ZA0_eq, show max (ρS d j + 1) (ρS d j + 4 + d) = ρS d j + 4 + d by omega,
    fuW (ρS d j + 4 + d) (by omega), fuW (ρS d j + 4 + d + 1) (by omega)]; omega
theorem YA_eq (d j : Nat) : (run d).YA j = ρS d j + 7 := by
  show uW.fst (uW.fst (max ((run d).AY j) ((run d).ZA1 j))) = _
  rw [AY_eq, ZA1_eq, show max (ρS d j + 1) (ρS d j + 5) = ρS d j + 5 by omega,
    fuW (ρS d j + 5) (by omega), fuW (ρS d j + 5 + 1) (by omega)]
theorem Z_eq (d j : Nat) : (run d).Z j = ρS d j + 3 := by
  unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO
  rw [show (run d).ρ j = ρS d j from rfl, show (run d).Lor = uW from rfl, show (run d).Dz = uW from rfl,
    show (run d).Wxo = uW from rfl, show (run d).Wyo = uW from rfl]
  have := ρpos d j
  split
  · rw [fuW (ρS d j) (by omega), fuW (ρS d j + 1) (by omega), fuW (ρS d j + 1 + 1) (by omega)]
  · rw [fuW (ρS d j) (by omega), fuW (ρS d j + 1) (by omega), fuW (ρS d j + 1 + 1) (by omega)]

theorem causal (d : Nat) (hd : d ≤ 6) : MergeCausal (run d) 1 1 where
  H_OWN j := by
    show (if (run d).sv (j / 2) then (run d).YA j else (run d).XA j) + 1 ≤ ρS d (j + 1)
    rw [sv_eq, XA_eq, YA_eq]
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
      rw [ρ_e, ρ_o, show 2 * k / 2 = k by omega]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk] <;> omega
    · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
      rw [ρ_o, show 2 * k + 1 + 1 = 2 * (k + 1) by omega, ρ_e, show (2 * k + 1) / 2 = k by omega]
      rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> simp [hk] <;> omega
  H_SRV j := by rw [Z_eq]; show _ ≤ ρS d j + 4; omega
  H_POS j := by have := ρpos d j; show 1 ≤ ρS d j; omega

theorem hRL (d : Nat) (hd : d ≤ 8) : (run d).Wxc.hi ≤ 8 ∧ (run d).Wyc.hi ≤ 8 ∧ (run d).Wzx.hi ≤ 8 ∧
    (run d).Wzy.hi ≤ 8 ∧ (run d).Lxa.hi + (run d).wxah ≤ 8 ∧ (run d).Lya.hi + (run d).wyah ≤ 8 := by
  show 1 ≤ 8 ∧ 1 ≤ 8 ∧ d ≤ 8 ∧ 1 ≤ 8 ∧ 1 + 1 ≤ 8 ∧ 1 + 1 ≤ 8; omega

theorem hRE (d : Nat) : 8 ≤ (run d).ZA0 0 ∧ 8 ≤ (run d).ZA1 0 := by
  rw [ZA0_eq, ZA1_eq]; have := ρpos d 0; omega

/-- Boundary `d = 5`: `MergeStaticG` holds (`S_XA_SEQ` with equality) and
`merge_ok_gs` gives clean acknowledges. -/
theorem static5 : MergeStaticG (run 5) 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem bnd_S_XA_SEQ :
    (run 5).Wzx.hi = (1 + 1 + 1 + 1) + (run 5).Wxc.lo ∧
    Tok (run 5).Tx (xak 5) (run 5).XA (fun k => !(run 5).sv k) ∧
    Tok (run 5).Ty (yak 5) (run 5).YA (run 5).sv :=
  let h := merge_ok_gs (gates 5) (env 5 (by decide)) (causal 5 (by decide)) (Nat.le_refl 1) static5
    (hRL 5 (by decide)) (hRE 5)
  ⟨by decide, h.2.1, h.2.2.1⟩

/-- At `d = 6` only `S_XA_SEQ` fails (by one tick). -/
theorem static_but_seq6 :
    (1 ≤ (run 6).Wxo.lo ∧ 1 ≤ (run 6).Wyo.lo) ∧ (1 ≤ (run 6).Wzx.lo ∧ 1 ≤ (run 6).Wzy.lo) ∧
    (1 ≤ (run 6).Lxa.lo ∧ 1 ≤ (run 6).Lya.lo) ∧ (1 ≤ (run 6).Wxa.lo ∧ 1 ≤ (run 6).Wya.lo) ∧
    (run 6).Wzx.hi = (1 + 1 + 1 + 1) + (run 6).Wxc.lo + 1 ∧
    (run 6).Wzy.hi ≤ (1 + 1 + 1 + 1) + (run 6).Wyc.lo ∧
    ((run 6).Lxa.hi + (run 6).wxah ≤ (run 6).Lxa.lo + (run 6).Wxa.lo + 1 + (run 6).Wxc.lo ∧
      (run 6).Lxa.hi + (run 6).wxah ≤
        (run 6).Lxa.lo + (run 6).Wxa.lo + 1 + (1 + (run 6).Lor.lo + (run 6).Dz.lo + 1) + (run 6).Wzx.lo) ∧
    ((run 6).Lya.hi + (run 6).wyah ≤ (run 6).Lya.lo + (run 6).Wya.lo + 1 + (run 6).Wyc.lo ∧
      (run 6).Lya.hi + (run 6).wyah ≤
        (run 6).Lya.lo + (run 6).Wya.lo + 1 + (1 + (run 6).Lor.lo + (run 6).Dz.lo + 1) + (run 6).Wzy.lo) := by
  decide

/-- The traces at the first y → x hand-over (`m = 0`): y's token 1 runs on
`[30, 38)`, z_ack is high on `[34, 42)` and reaches uxa `d` ticks later; x's
token 2 requests at `46`, reaching uxa at `47`. -/
theorem glitch_values :
    (run 6).XA 2 = 42 ∧ (run 6).XA 3 = 50 ∧ (run 6).sv 1 = true ∧
    xak 6 49 = true ∧ xak 6 48 = false ∧ xak 5 48 = false ∧ xak 5 49 = false ∧
    zx 6 47 = true ∧ zx 6 48 = false ∧ x 6 46 = true ∧ zr 6 48 = false ∧ zr 6 49 = true ∧
    (run 6).ZA0 4 = 56 := by
  refine ⟨?_, ?_, rfl, ?_⟩
  · rw [XA_eq]; decide
  · rw [XA_eq]; decide
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **`S_XA_SEQ` is exact (tight by one tick).** At `d = 6` every
hypothesis of `merge_ok_gs` except `S_XA_SEQ` holds, and x_ack is high at
`49`, inside y's token 1 (its slot `[XA 2, XA 3) = [42, 50)`, gate off): the
same tick x's z_req reaches the server, 7 ticks before the server's z_ack
rise for x reaches uxa (`ZA0 4 = 56`). -/
theorem cex_S_XA_SEQ :
    ¬ Tok (run 6).Tx (xak 6) (run 6).XA (fun k => !(run 6).sv k) ∧
    ¬ MergeStaticG (run 6) 1 1 1 1 1 1 ∧ ¬ MergeTimingG (run 6) 8 := by
  have g := glitch_values
  refine ⟨fun h => ?_, fun S => ?_, fun TM => ?_⟩
  · have := h.hi 1 49 (by decide) (by rw [g.1]; omega) (by rw [g.2.1]; omega)
    rw [g.2.2.2.1, g.2.2.1] at this; exact absurd this (by decide)
  · have := S.S_XA_SEQ; revert this; decide
  · have h := TM.H_SEQ_XA 1 rfl rfl
    rw [ZA0_eq, AX_eq] at h; revert h; decide

end MergeS

/-! ### `S_XA_N`'s z_ack form is tight too: a long x_req → uxa wire

`MergeR.run w`: every merged token is x's (y never requests); every LUT and
wire one tick except the x_req → uxa wire (`Wxc = shift 6`) and uxa's
feedback wire (`w` ticks); reset high on `[0, 10)`. With the long request
wire x_req is uxa's late input and z_ack's next edge (through x_ack, the
client, uor, the delay line, the server: `Lxa.lo + Wxa.lo + Eo + Kz + Wzx.lo
= 8` after the node) comes before x_req's (`Lxa.lo + Wxa.lo + Eo + Wxc.lo =
9`). `S_XA_N`'s second form reads `1 + w ≤ 8`: at `w = 7` everything holds;
at `w = 8` only that form fails (the first holds with equality), z_ack's
fall reaches uxa while its LUT still reads its pre-rise output, and x_ack
drops inside x's token. -/
namespace MergeR
set_option maxRecDepth 100000

def run (w : Nat) : MergeRun where
  Wxo := uW
  Wyo := uW
  Lor := uW
  Dz := uW
  Wxc := Ret.shift 6
  Wyc := uW
  Wzx := uW
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := w
  wxah := w
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ρ j := 18 * (j / 2) + 6 + 9 * (j % 2)
  ζ j := 18 * (j / 2) + 10 + 9 * (j % 2)
  sv _ := false

def rst10 (t : Nat) : Bool := decide (t < 10)
def x (t : Nat) : Bool := decide (6 ≤ t ∧ (t - 6) % 18 < 9)
def y (_ : Nat) : Bool := false
def za (t : Nat) : Bool := decide (10 ≤ t ∧ (t - 10) % 18 < 9)
def xo (t : Nat) : Bool := x (t - 1)
def yo (t : Nat) : Bool := y (t - 1)
def ei (t : Nat) : Bool := or2B (xo (t - 1)) (yo (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
def xc (t : Nat) : Bool := x (t - 6)
def zx (t : Nat) : Bool := za (t - 1)

def xaH (w : Nat) : Nat → Nat → Bool
  | 0 => fun _ => false
  | n + 1 => fun s => if s ≤ n then xaH w n s else c2B (xc n) (zx n) (xaH w n (n - w)) (rst10 n)
def xa (w : Nat) (t : Nat) : Bool := xaH w t t
def qa (w : Nat) (t : Nat) : Bool := xa w (t - w)
def xak (w : Nat) (t : Nat) : Bool := xa w (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (yo 0) (zx 0) false (rst10 0)
  | t + 2 => c2B (yo (t + 1)) (zx (t + 1)) (ya t) (rst10 (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem xaH_stable (w : Nat) : ∀ n s, s ≤ n → xaH w n s = xa w s := by
  intro n
  induction n with
  | zero => intro s hs; have : s = 0 := by omega
            subst this; rfl
  | succ n ih =>
    intro s hs
    by_cases h : s ≤ n
    · show (if s ≤ n then xaH w n s else _) = _
      split
      · exact ih s h
      · omega
    · have : s = n + 1 := by omega
      subst this; rfl

theorem gates (w : Nat) : MergeGates (run w) rst10 x y za xo yo ei zr xc yo zx zx (xa w) (qa w) ya qb
    (xak w) yak where
  H_WXO _ _ := rfl
  H_WYO _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_WXC _ _ := rfl
  H_WYC _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    obtain ⟨n, rfl⟩ : ∃ n, t = n + 1 := ⟨t - 1, by have : 1 ≤ t := ht; omega⟩
    show xaH w (n + 1) (n + 1) = c2B (xc (n + 1 - 1)) (zx (n + 1 - 1))
      (xa w (n + 1 - 1 - w)) (rst10 (n + 1 - 1))
    rw [show n + 1 - 1 = n by omega, ← xaH_stable w n (n - w) (by omega)]
    show (if n + 1 ≤ n then _ else _) = _
    split
    · omega
    · rfl
  H_UXA_FB t ht := by
    have : w ≤ t := ht
    show ∃ s, t ≤ s + w ∧ s + w ≤ t ∧ qa w t = xa w s
    exact ⟨t - w, by omega, by omega, rfl⟩
  H_UXA_POS := by show 1 ≤ 1 + w; omega
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by show 1 ≤ 1 + 1; omega
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem env (w : Nat) : MergeEnv (run w) rst10 x y za 10 where
  H_RST_HI t h := by simp [rst10, h]
  H_RST_LO t h := by simp [rst10]; omega
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 18 * (0 / 2) + 6 + 9 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 18 * (2 * k / 2) + 6 + 9 * (2 * k % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 1) / 2) + 6 + 9 * ((2 * k + 1) % 2) := h2
      show x t = !false; simp only [x, Bool.not_false, decide_eq_true_eq]; omega
    · have h1 : 18 * ((2 * k + 1) / 2) + 6 + 9 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 2) / 2) + 6 + 9 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := ⟨fun _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 18 * (0 / 2) + 10 + 9 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 18 * (2 * k / 2) + 10 + 9 * (2 * k % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 1) / 2) + 10 + 9 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 18 * ((2 * k + 1) / 2) + 10 + 9 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 2) / 2) + 10 + 9 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega

theorem AX_eq (w j : Nat) : (run w).AX j = 18 * (j / 2) + 12 + 9 * (j % 2) := by
  show (Ret.shift 6).fst (18 * (j / 2) + 6 + 9 * (j % 2)) = _; rw [Ret.fst_shift 6 _ (by omega)]; omega
theorem ZA0_eq (w j : Nat) : (run w).ZA0 j = 18 * (j / 2) + 11 + 9 * (j % 2) := by
  show uW.fst (18 * (j / 2) + 10 + 9 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem XA_eq (w j : Nat) : (run w).XA j = 18 * (j / 2) + 14 + 9 * (j % 2) := by
  show uW.fst (uW.fst (max ((run w).AX j) ((run w).ZA0 j))) = _
  rw [AX_eq, ZA0_eq, show max (18 * (j / 2) + 12 + 9 * (j % 2)) (18 * (j / 2) + 11 + 9 * (j % 2)) =
    18 * (j / 2) + 12 + 9 * (j % 2) by omega,
    fuW (18 * (j / 2) + 12 + 9 * (j % 2)) (by omega), fuW (18 * (j / 2) + 12 + 9 * (j % 2) + 1) (by omega)]
  omega
theorem Z_eq (w j : Nat) : (run w).Z j = 18 * (j / 2) + 9 + 9 * (j % 2) := by
  unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO
  rw [show (run w).Lor = uW from rfl, show (run w).Dz = uW from rfl,
    show (run w).Wxo = uW from rfl, show (run w).Wyo = uW from rfl]
  rw [ite_self]
  show uW.fst (uW.fst (uW.fst (18 * (j / 2) + 6 + 9 * (j % 2)))) = _
  rw [fuW (18 * (j / 2) + 6 + 9 * (j % 2)) (by omega), fuW (18 * (j / 2) + 6 + 9 * (j % 2) + 1) (by omega),
    fuW (18 * (j / 2) + 6 + 9 * (j % 2) + 1 + 1) (by omega)]; omega

theorem causal (w : Nat) : MergeCausal (run w) 1 1 where
  H_OWN j := by
    show (if false = true then _ else (run w).XA j) + 1 ≤ 18 * ((j + 1) / 2) + 6 + 9 * ((j + 1) % 2)
    simp only [Bool.false_eq_true, ite_false]; rw [XA_eq]; omega
  H_SRV j := by rw [Z_eq]; show _ ≤ 18 * (j / 2) + 10 + 9 * (j % 2); omega
  H_POS j := by show 1 ≤ 18 * (j / 2) + 6 + 9 * (j % 2); omega

theorem hRL (w : Nat) (hw : w ≤ 9) : (run w).Wxc.hi ≤ 10 ∧ (run w).Wyc.hi ≤ 10 ∧ (run w).Wzx.hi ≤ 10 ∧
    (run w).Wzy.hi ≤ 10 ∧ (run w).Lxa.hi + (run w).wxah ≤ 10 ∧ (run w).Lya.hi + (run w).wyah ≤ 10 := by
  show 6 ≤ 10 ∧ 1 ≤ 10 ∧ 1 ≤ 10 ∧ 1 ≤ 10 ∧ 1 + w ≤ 10 ∧ 1 + 1 ≤ 10; omega

theorem hRE (w : Nat) : 10 ≤ (run w).ZA0 0 ∧ 10 ≤ (run w).ZA1 0 := by
  refine ⟨by rw [ZA0_eq]; omega, ?_⟩
  show 10 ≤ uW.fst (18 * (0 / 2) + 10 + 9 * (0 % 2)); rw [fuW _ (by omega)]; omega

theorem static7 : MergeStaticG (run 7) 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- Boundary `w = 7`: `MergeStaticG` holds, `S_XA_N`'s z_ack form with
equality, and `merge_ok_gs` applies. -/
theorem bnd_S_XA_N2 :
    (run 7).Lxa.hi + (run 7).wxah =
      (run 7).Lxa.lo + (run 7).Wxa.lo + 1 + (1 + (run 7).Lor.lo + (run 7).Dz.lo + 1) + (run 7).Wzx.lo ∧
    Tok (run 7).Tx (xak 7) (run 7).XA (fun k => !(run 7).sv k) :=
  ⟨by decide, (merge_ok_gs (gates 7) (env 7) (causal 7) (Nat.le_refl 1) static7 (hRL 7 (by decide))
    (hRE 7)).2.1⟩

/-- At `w = 8` every `MergeStaticG` field holds except `S_XA_N`'s z_ack
form (`9 > 8`); its x_req form holds with equality. -/
theorem static_but_N2 :
    (run 8).Wzx.hi ≤ (1 + 1 + 1 + 1) + (run 8).Wxc.lo ∧
    (run 8).Wzy.hi ≤ (1 + 1 + 1 + 1) + (run 8).Wyc.lo ∧
    (run 8).Lxa.hi + (run 8).wxah = (run 8).Lxa.lo + (run 8).Wxa.lo + 1 + (run 8).Wxc.lo ∧
    (run 8).Lxa.hi + (run 8).wxah =
      (run 8).Lxa.lo + (run 8).Wxa.lo + 1 + (1 + (run 8).Lor.lo + (run 8).Dz.lo + 1) + (run 8).Wzx.lo + 1 ∧
    ((run 8).Lya.hi + (run 8).wyah ≤ (run 8).Lya.lo + (run 8).Wya.lo + 1 + (run 8).Wyc.lo ∧
      (run 8).Lya.hi + (run 8).wyah ≤
        (run 8).Lya.lo + (run 8).Wya.lo + 1 + (1 + (run 8).Lor.lo + (run 8).Dz.lo + 1) + (run 8).Wzy.lo) ∧
    (1 ≤ (run 8).Wxo.lo ∧ 1 ≤ (run 8).Wyo.lo) ∧ (1 ≤ (run 8).Wzx.lo ∧ 1 ≤ (run 8).Wzy.lo) ∧
    (1 ≤ (run 8).Lxa.lo ∧ 1 ≤ (run 8).Lya.lo) ∧ (1 ≤ (run 8).Wxa.lo ∧ 1 ≤ (run 8).Wya.lo) := by
  decide

theorem glitch_values :
    (run 8).XA 0 = 14 ∧ (run 8).XA 1 = 23 ∧ (run 8).sv 0 = false ∧
    xak 8 14 = true ∧ xak 8 21 = true ∧ xak 8 22 = false ∧ xak 7 22 = true ∧ xak 7 23 = false := by
  refine ⟨by rw [XA_eq], by rw [XA_eq], rfl, ?_⟩
  decide

/-- **`S_XA_N`'s z_ack form is exact (tight by one tick).** At `w = 8`
every hypothesis of `merge_ok_gs` except that form holds; z_ack's fall
reaches uxa at `20`, x_req's at `21`, uxa's LUT still reads its pre-rise
output and x_ack drops at `22`, inside x's token 0 (`[XA 0, XA 1) = [14, 23)`). -/
theorem cex_S_XA_N2 :
    ¬ Tok (run 8).Tx (xak 8) (run 8).XA (fun k => !(run 8).sv k) ∧
    ¬ MergeStaticG (run 8) 1 1 1 1 1 1 ∧ ¬ MergeTimingG (run 8) 10 := by
  have g := glitch_values
  refine ⟨fun h => ?_, fun S => ?_, fun TM => ?_⟩
  · have := h.hi 0 22 (by decide) (by rw [g.1]; omega) (by rw [g.2.1]; omega)
    rw [g.2.2.2.2.2.1, g.2.2.1] at this; exact absurd this (by decide)
  · have := S.S_XA_N.2; revert this; decide
  · have h := (TM.H_DEP_XA 0 rfl).1
    have e1 : (run 8).cx 0 = 12 := by
      show max ((run 8).AX 0) ((run 8).ZA0 0) = 12; rw [AX_eq, ZA0_eq]; omega
    rw [e1, ZA0_eq] at h; revert h; decide

end MergeR

end Formal.Cells.OpsTimed
