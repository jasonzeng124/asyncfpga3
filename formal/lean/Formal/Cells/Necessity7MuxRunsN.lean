import Formal.Cells.Necessity7MuxRuns

/-!
# Necessity7MuxRunsN: the client-loop boundary (`S_XA_R`) and `S_XA_J.1`

Probe Bnx7 (shard B), second runs file (see `Necessity7MuxRuns` for the
model, the weakened claims and family `RA`).

* `RN.run w`: unit LUTs and wires, uxa's feedback net `w` ticks, both
  clients tight (`Ex = Ey = 1`: each drops its request one tick after
  seeing its ack), the control sender tight (`Ec = 1`), reset on `[0, 12)`,
  period 23 per control token, x / y alternating.
  - `passN5`: `S_XA_FORK` fails (`1 + 6 ≤ 5`), `S_XA_N` holds with equality
    (`6 ≤ 6`): passes (`mux_ok_gs`).
  - `failR6`, `claimR1_false`: `S_XA_R` off by exactly one (`S_XA_N`:
    `7 = 6 + 1`; the fork disjunct fails too, by 3), every other field holds;
    x_req's fall (client, one tick after x_ack) reaches uxa as j0's fall at
    33, before uxa's 6-tick feedback shows x_ack's rise of 28: uxa reads
    `C(0, 1, 0) = 0` and x_ack is 0 at 35, inside `[XA 0, XA 1) = [29, 44)`.
* `RB.run`: family `RA`'s schedule with `Wzx = uW` and the j0 → uxa wire
  `Rx` (1 tick on j0's rises, 8 on its falls: `Rx.lo = 1`, `Rx.hi = 8`).
  `passB`: `S_XA_J.1` fails (`8 + 2 ≤ 4 + 4 + 1` is false), every
  `MuxStaticG` field holds: passes.

## Assumed / proved / NOT covered

As `Necessity7MuxRuns`. NOT covered: the uya mirrors; an iff; the `+1`.
-/

namespace Formal.Cells.Necessity7Mux
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B)
open Formal.Cells.Necessity4Mux (MuxConcl)

namespace RN

def run (w : Nat) : MuxRun where
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
  W0x := uW
  W1y := uW
  Lor := uW
  Dz := uW
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
  ξ j := 46 * (j / 2) + 17 + 13 * (j % 2)
  η j := 46 * (j / 2) + 40 + 13 * (j % 2)
  γ j := 23 * (j / 2) + 20 + 8 * (j % 2)
  ζ j := 23 * (j / 2) + 26 + 15 * (j % 2)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

def rst (t : Nat) : Bool := decide (t < 12)
theorem rst_hi : ∀ t, t < 12 → rst t = true := fun t h => by simp [rst, h]
theorem rst_lo : ∀ t, 12 ≤ t → rst t = false := fun t h => by simp [rst]; omega

-- environment
def x (t : Nat) : Bool := decide (17 ≤ t ∧ (t - 17) % 46 < 13)
def y (t : Nat) : Bool := decide (40 ≤ t ∧ (t - 40) % 46 < 13)
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
def j0x (t : Nat) : Bool := j0 (t - 1)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
def zy (t : Nat) : Bool := za (t - 1)
/-- uxa's gate relation through a `w`-tick feedback net. -/
def XaEq (w : Nat) (X : Trace) : Prop :=
  ∀ t, 1 ≤ t → X t = c2B (j0x (t - 1)) (zx (t - 1)) (X (t - 1 - w)) (rst (t - 1))
/-- uxa with a 5-tick feedback net (loop 6). -/
def xa5 : Nat → Bool
  | t + 6 => c2B (j0x (t + 5)) (zx (t + 5)) (xa5 t) (rst (t + 5))
  | _ => false
/-- uxa with a 6-tick feedback net (loop 7). -/
def xa6 : Nat → Bool
  | t + 7 => c2B (j0x (t + 6)) (zx (t + 6)) (xa6 t) (rst (t + 6))
  | _ => false
theorem xa5_eq : XaEq 5 xa5 := by
  intro t ht
  match t, ht with
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | t + 6, _ => rfl
theorem xa6_eq : XaEq 6 xa6 := by
  intro t ht
  match t, ht with
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | t + 7, _ => rfl
def qa (w : Nat) (X : Trace) (t : Nat) : Bool := X (t - w)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zy 0) false (rst 0)
  | t + 2 => c2B (j1y (t + 1)) (zy (t + 1)) (ya t) (rst (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (X : Trace) (t : Nat) : Bool := X (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates (w : Nat) (X : Trace) (hX : XaEq w X) :
    MuxGates (run w) rst x y ctl za xj yj cj cj sx sx j0 q0 j1 q1 e0 e1 ei zr
      j0x j1y zx zy X (qa w X) ya qb (xak X) yak where
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
  H_UXA t ht := hX t ht
  H_UXA_FB := fun t ht => by
    have h : w ≤ t := ht
    exact ⟨t - w, by show t ≤ t - w + w; omega, by show t - w + w ≤ t; omega, rfl⟩
  H_UXA_POS := by show 1 ≤ 1 + w; omega
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := Nat.le_of_ble_eq_true rfl
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

section closed
variable (w : Nat)

theorem enum0 : Enum (fun k => !(run w).sv k) (run w).κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum (run w).sv (run w).κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

theorem Xp_eq (j : Nat) : (run w).Xp j = 46 * (j / 2) + 18 + 13 * (j % 2) := by
  show uW.fst (46 * (j / 2) + 17 + 13 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : (run w).Yp j = 46 * (j / 2) + 41 + 13 * (j % 2) := by
  show uW.fst (46 * (j / 2) + 40 + 13 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : (run w).C0 j = 23 * (j / 2) + 21 + 8 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 20 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C1_eq (j : Nat) : (run w).C1 j = 23 * (j / 2) + 21 + 8 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 20 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem D0_eq (j : Nat) : (run w).D0 j = 46 * (j / 2) + 21 + 8 * (j % 2) := by
  show (run w).C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [C0_eq]; omega
theorem D1_eq (j : Nat) : (run w).D1 j = 46 * (j / 2) + 44 + 8 * (j % 2) := by
  show (run w).C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C1_eq]; omega
theorem c0_eq (j : Nat) : (run w).c0 j = 46 * (j / 2) + 21 + 10 * (j % 2) := by
  show max ((run w).Xp j) ((run w).D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : (run w).c1 j = 46 * (j / 2) + 44 + 10 * (j % 2) := by
  show max ((run w).Yp j) ((run w).D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : (run w).τ0 j = 46 * (j / 2) + 22 + 10 * (j % 2) := by
  show uW.fst ((run w).c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : (run w).τ1 j = 46 * (j / 2) + 45 + 10 * (j % 2) := by
  show uW.fst ((run w).c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : (run w).E j = 23 * (j / 2) + 22 + 10 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : (run w).sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx (run w).κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum0 w) (j / 2 / 2)
      rw [show (run w).κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega
  · have hs : (run w).sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx (run w).κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum1 w) (j / 2 / 2)
      rw [show (run w).κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega

theorem O0_eq (j : Nat) : (run w).O0 j = (run w).E j + 1 := by
  show uW.fst ((run w).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : (run w).O1 j = (run w).E j + 1 := by
  show uW.fst ((run w).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : (run w).A1 j = (run w).E j + 1 := by
  show uW.fst ((run w).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA0_eq (j : Nat) : (run w).ZA0 j = 23 * (j / 2) + 27 + 15 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 26 + 15 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem ZA1_eq (j : Nat) : (run w).ZA1 j = 23 * (j / 2) + 27 + 15 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 26 + 15 * (j % 2)) = _; rw [fuW _ (by omega)]; omega

theorem Z_eq (j : Nat) : (run w).Z j = (run w).E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show (run w).Lor = uW from rfl, show (run w).Dz = uW from rfl]
  have hE := E_eq w j
  split
  · rw [O0_eq, fuW ((run w).E j + 1) (by omega), fuW ((run w).E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW ((run w).E j + 1) (by omega), fuW ((run w).E j + 1 + 1) (by omega)]

theorem YA_eq (j : Nat) : (run w).YA j = 23 * (j / 2) + 29 + 15 * (j % 2) := by
  show uW.fst (uW.fst (max ((run w).A1 j) ((run w).ZA1 j))) = _
  rw [A1_eq, ZA1_eq, E_eq, show max (23 * (j / 2) + 22 + 10 * (j % 2) + 1) (23 * (j / 2) + 27 + 15 * (j % 2))
    = 23 * (j / 2) + 27 + 15 * (j % 2) by omega, fuW (23 * (j / 2) + 27 + 15 * (j % 2)) (by omega),
    fuW (23 * (j / 2) + 27 + 15 * (j % 2) + 1) (by omega)]; omega

theorem env : MuxEnv (run w) rst x y ctl za sx sx 12 where
  H_RST_HI := rst_hi
  H_RST_LO := rst_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 46 * (0 / 2) + 17 + 13 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 46 * (2 * k / 2) + 17 + 13 * (2 * k % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 1) / 2) + 17 + 13 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 46 * ((2 * k + 1) / 2) + 17 + 13 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 2) / 2) + 17 + 13 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 46 * (0 / 2) + 40 + 13 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 46 * (2 * k / 2) + 40 + 13 * (2 * k % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 1) / 2) + 40 + 13 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 46 * ((2 * k + 1) / 2) + 40 + 13 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 2) / 2) + 40 + 13 * ((2 * k + 2) % 2) := h2
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
  H_ENUM0 := enum0 w
  H_ENUM1 := enum1 w
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq] at h1 h2
    show svW ((t - 20) / 23) = svW k
    rw [show (t - 20) / 23 = k by omega]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq] at h1 h2
    show svW ((t - 20) / 23) = svW k
    rw [show (t - 20) / 23 = k by omega]

end closed

section uw2
variable (w : Nat)

theorem A0_eq (j : Nat) : (run w).A0 j = (run w).E j + 1 := by
  show uW.fst ((run w).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]

theorem XA_eq (j : Nat) : (run w).XA j = 23 * (j / 2) + 29 + 15 * (j % 2) := by
  show uW.fst (uW.fst (max ((run w).A0 j) ((run w).ZA0 j))) = _
  rw [A0_eq, ZA0_eq, E_eq, show max (23 * (j / 2) + 22 + 10 * (j % 2) + 1)
    (23 * (j / 2) + 27 + 15 * (j % 2)) = 23 * (j / 2) + 27 + 15 * (j % 2) by omega,
    fuW (23 * (j / 2) + 27 + 15 * (j % 2)) (by omega),
    fuW (23 * (j / 2) + 27 + 15 * (j % 2) + 1) (by omega)]; omega

/-- The partners are causal; both clients, the control sender and the
server's rise are tight. -/
theorem causal : MuxCausal (run w) uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [XA_eq]; show _ ≤ 46 * ((2 * m + 1) / 2) + 17 + 13 * ((2 * m + 1) % 2)
    show 23 * (2 * (2 * m) / 2) + 29 + 15 * (2 * (2 * m) % 2) + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [XA_eq]; show _ ≤ 46 * ((2 * m + 2) / 2) + 17 + 13 * ((2 * m + 2) % 2)
    show 23 * ((2 * (2 * m) + 1) / 2) + 29 + 15 * ((2 * (2 * m) + 1) % 2) + 1 ≤ _; omega
  H_YC_FALL m := by
    rw [YA_eq]; show _ ≤ 46 * ((2 * m + 1) / 2) + 40 + 13 * ((2 * m + 1) % 2)
    show 23 * (2 * (2 * m + 1) / 2) + 29 + 15 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [YA_eq]; show _ ≤ 46 * ((2 * m + 2) / 2) + 40 + 13 * ((2 * m + 2) % 2)
    show 23 * ((2 * (2 * m + 1) + 1) / 2) + 29 + 15 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (23 * (j / 2) + 26 + 15 * (j % 2)) + 1 ≤ 23 * ((j + 1) / 2) + 20 + 8 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 23 * (j / 2) + 26 + 15 * (j % 2); omega
  H_POS j := by show 1 ≤ 23 * (j / 2) + 20 + 8 * (j % 2); omega

theorem rstOK (hw : w ≤ 11) : MuxRstG (run w) 12 := by
  have b : ∀ {a c : Nat}, Nat.ble a c = true → a ≤ c := fun h => Nat.le_of_ble_eq_true h
  refine ⟨⟨b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl,
    b rfl, by show 1 + w ≤ 12; omega, b rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [ZA0_eq]; omega
  · rw [ZA1_eq]; omega

/-- Every field holds; `S_XA_R` (through its left disjunct `S_XA_N`) needs
`w ≤ 5 + sr`. -/
theorem staticW (sr : Nat) (h1 : w ≤ 5 + sr) (h2 : w ≤ 7) :
    MuxStaticW (run w) uW 1 1 1 1 1 1 1 0 sr where
  H_LJ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WC := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WO := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_J0_X := Nat.le_of_ble_eq_true rfl
  S_J1_Y := Nat.le_of_ble_eq_true rfl
  S_J0_C := Nat.le_of_ble_eq_true rfl
  S_J1_C := Nat.le_of_ble_eq_true rfl
  S_XA_RTZ := by show 1 + (1 + w) ≤ 1 + (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1); omega
  S_YA_RTZ := Nat.le_of_ble_eq_true rfl
  S_XA_J2 := by show 1 + (1 + w) ≤ 2 * (1 + 1 + 1 + 1) + (1 + 1 + 1 + 1) + 1; omega
  S_YA_J2 := Nat.le_of_ble_eq_true rfl
  S_XA_R := Or.inl (by show 1 + w ≤ 1 + 1 + 1 + 1 + 1 + 1 + sr; omega)
  S_YA_R := Or.inl (Nat.le_of_ble_eq_true rfl)
  S_XA_SEQ := Nat.le_of_ble_eq_true rfl
  S_YA_SEQ := Nat.le_of_ble_eq_true rfl

end uw2
end RN

/-- **`S_XA_FORK` is not necessary, second witness.** With a 5-tick uxa
feedback net the shipped `S_XA_FORK` fails (`1 + 6 ≤ 4 + 1` is false), the
client loop `S_XA_N` holds with equality, every `MuxStaticG` field holds:
`mux_ok_gs` gives `mux_ok`'s whole conclusion. The race is live: x_ack rises
at 28 (node), its feedback shows it at 33, j0's fall reaches uxa at 33. -/
theorem passN5 :
    ¬ ((RN.run 5).Wzx.hi + ((RN.run 5).Lxa.hi + (RN.run 5).wxah) ≤
        (uW.lo + 1 + 1 + 1) + (RN.run 5).W0x.lo) ∧
    (RN.run 5).Lxa.hi + (RN.run 5).wxah = (RN.run 5).Lxa.lo + (RN.run 5).Wxa.lo + 1 +
      (RN.run 5).Wx.lo + (RN.run 5).Lj0.lo + (RN.run 5).W0x.lo ∧
    MuxStaticG (RN.run 5) uW 1 1 1 1 1 1 1 ∧
    RN.xa5 28 = true ∧ RN.xa5 27 = false ∧ RN.j0x 32 = true ∧ RN.j0x 33 = false ∧
    RN.xak RN.xa5 40 = true ∧
    MuxConcl (RN.run 5) RN.j0 RN.j1 RN.zr (RN.xak RN.xa5) RN.yak := by
  have S := (RN.staticW 5 0 (by omega) (by omega)).toG
  refine ⟨by decide, rfl, S, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, ?_⟩
  exact mux_ok_gs (RN.gates 5 RN.xa5 RN.xa5_eq) (RN.env 5) (RN.causal 5) (Nat.le_refl 1) S
    (RN.rstOK 5 (by omega))

/-- **`S_XA_R` is necessary at the boundary (its client-loop disjunct).**
With a 6-tick uxa feedback net every `MuxStaticW … 0 1` field holds
(`S_XA_R` weakened by one), the unweakened `S_XA_R` is false (`S_XA_N` by
exactly one, `7 = 6 + 1`; `S_XA_FORK` by 3), reset sequencing holds, and the
conclusion fails: x_ack is 0 at 35, inside `[XA 0, XA 1) = [29, 44)`, where
`mux_ok` says it is 1. -/
theorem failR6 :
    MuxStaticW (RN.run 6) uW 1 1 1 1 1 1 1 0 1 ∧
    (RN.run 6).Lxa.hi + (RN.run 6).wxah = (RN.run 6).Lxa.lo + (RN.run 6).Wxa.lo + 1 +
      (RN.run 6).Wx.lo + (RN.run 6).Lj0.lo + (RN.run 6).W0x.lo + 1 ∧
    ¬ ((RN.run 6).Lxa.hi + (RN.run 6).wxah ≤ (RN.run 6).Lxa.lo + (RN.run 6).Wxa.lo + 1 +
        (RN.run 6).Wx.lo + (RN.run 6).Lj0.lo + (RN.run 6).W0x.lo ∨
      ((RN.run 6).Wzx.hi + ((RN.run 6).Lxa.hi + (RN.run 6).wxah) ≤ (uW.lo + 1 + 1 + 1) + (RN.run 6).W0x.lo ∧
       (RN.run 6).W0x.hi + ((RN.run 6).Lxa.hi + (RN.run 6).wxah) ≤
         (1 + (RN.run 6).Lor.lo + (RN.run 6).Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + (RN.run 6).W0x.lo)) ∧
    MuxRstG (RN.run 6) 12 ∧
    (RN.run 6).XA 0 = 29 ∧ (RN.run 6).XA 1 = 44 ∧ (RN.run 6).A0 1 = 33 ∧
    RN.xa6 28 = true ∧ RN.j0x 33 = false ∧ RN.zx 33 = true ∧ RN.xak RN.xa6 35 = false ∧
    ¬ Tok (RN.run 6).Tx (RN.xak RN.xa6) (RN.run 6).XA (fun k => !(RN.run 6).sv k) ∧
    ¬ MuxConcl (RN.run 6) RN.j0 RN.j1 RN.zr (RN.xak RN.xa6) RN.yak := by
  have hX0 : (RN.run 6).XA 0 = 29 := by rw [RN.XA_eq]
  have hX1 : (RN.run 6).XA 1 = 44 := by rw [RN.XA_eq]
  have v : RN.xa6 28 = true ∧ RN.j0x 33 = false ∧ RN.zx 33 = true ∧ RN.xak RN.xa6 35 = false := by
    decide +kernel
  have nx : ¬ Tok (RN.run 6).Tx (RN.xak RN.xa6) (RN.run 6).XA (fun k => !(RN.run 6).sv k) := by
    intro h
    have := h.hi 0 35 (by decide) (by rw [show 2 * 0 = 0 from rfl, hX0]; omega)
      (by rw [show 2 * 0 + 1 = 1 from rfl, hX1]; omega)
    rw [v.2.2.2] at this; exact absurd this (by decide)
  exact ⟨RN.staticW 6 1 (by omega) (by omega), rfl, by decide, RN.rstOK 6 (by omega), hX0, hX1,
    by rw [RN.A0_eq, RN.E_eq], v.1, v.2.1, v.2.2.1, v.2.2.2, nx, fun h => nx h.2.2.2.1⟩

/-- The counter-run meets every other hypothesis, so `ClaimR 1` is false. -/
theorem claimR1_false : ¬ ClaimR 1 := by
  intro h
  exact failR6.2.2.2.2.2.2.2.2.2.2.2.2
    (h (RN.run 6) uW 1 1 1 1 1 1 1 12 RN.rst RN.x RN.y RN.ctl RN.za RN.xj RN.yj RN.cj RN.cj RN.sx
      RN.sx RN.j0 RN.q0 RN.j1 RN.q1 RN.e0 RN.e1 RN.ei RN.zr RN.j0x RN.j1y RN.zx RN.zy
      RN.xa6 (RN.qa 6 RN.xa6) RN.ya RN.qb (RN.xak RN.xa6) RN.yak
      (RN.gates 6 RN.xa6 RN.xa6_eq) (RN.env 6) (RN.causal 6) (Nat.le_refl 1) failR6.1
      (RN.rstOK 6 (by omega)))

/-! ## Family `RB`: a j0 → uxa wire with rise / fall spread -/
namespace RB

/-- The j0 → uxa wire: 1 tick, except that it holds its old value for 7
extra ticks after each control token's join fall (at `23 k + 37`). -/
def Rx : Ret where
  σ t := if 38 ≤ t ∧ (t - 38) % 23 < 7 then t - (t - 38) % 23 - 2 else t - 1
  lo := 1
  hi := 8
  mono a b h := by
    show (if 38 ≤ a ∧ (a - 38) % 23 < 7 then a - (a - 38) % 23 - 2 else a - 1) ≤
      (if 38 ≤ b ∧ (b - 38) % 23 < 7 then b - (b - 38) % 23 - 2 else b - 1)
    split <;> split <;> omega
  ge t := by
    show t - 8 ≤ (if 38 ≤ t ∧ (t - 38) % 23 < 7 then t - (t - 38) % 23 - 2 else t - 1)
    split <;> omega
  le t := by
    show (if 38 ≤ t ∧ (t - 38) % 23 < 7 then t - (t - 38) % 23 - 2 else t - 1) ≤ t - 1
    split <;> omega

theorem Rx_σ (t : Nat) :
    Rx.σ t = if 38 ≤ t ∧ (t - 38) % 23 < 7 then t - (t - 38) % 23 - 2 else t - 1 := rfl

abbrev run : MuxRun := RA.run 1 Rx

theorem A0_e (k : Nat) : run.A0 (2 * k) = 23 * k + 23 := by
  show Rx.fst (run.E (2 * k)) = _
  rw [RA.E_eq, show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega]
  apply Ret.fst_eq_of
  · rw [Rx_σ]; split <;> omega
  · right; rw [Rx_σ]; split <;> omega

theorem A0_o (k : Nat) : run.A0 (2 * k + 1) = 23 * k + 45 := by
  show Rx.fst (run.E (2 * k + 1)) = _
  rw [RA.E_eq, show (2 * k + 1) / 2 = k by omega, show (2 * k + 1) % 2 = 1 by omega]
  apply Ret.fst_eq_of
  · rw [Rx_σ]; split <;> omega
  · right; rw [Rx_σ]; split <;> omega

theorem A0_eq (j : Nat) : run.A0 j = 23 * (j / 2) + 23 + 22 * (j % 2) := by
  rcases Nat.mod_two_eq_zero_or_one j with h | h
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    rw [A0_e]; omega
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    rw [A0_o]; omega

theorem XA_eq (j : Nat) : run.XA j = 23 * (j / 2) + 29 + 18 * (j % 2) := by
  show uW.fst (uW.fst (max (run.A0 j) (run.ZA0 j))) = _
  rw [A0_eq, RA.ZA0_eq, show max (23 * (j / 2) + 23 + 22 * (j % 2)) (23 * (j / 2) + 26 + 15 * (j % 2) + 1)
    = 23 * (j / 2) + 27 + 18 * (j % 2) by omega,
    fuW (23 * (j / 2) + 27 + 18 * (j % 2)) (by omega),
    fuW (23 * (j / 2) + 27 + 18 * (j % 2) + 1) (by omega)]; omega

theorem causal : MuxCausal run uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [XA_eq]; show _ ≤ 46 * ((2 * m + 1) / 2) + 17 + 18 * ((2 * m + 1) % 2)
    show 23 * (2 * (2 * m) / 2) + 29 + 18 * (2 * (2 * m) % 2) + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [XA_eq]; show _ ≤ 46 * ((2 * m + 2) / 2) + 17 + 18 * ((2 * m + 2) % 2)
    show 23 * ((2 * (2 * m) + 1) / 2) + 29 + 18 * ((2 * (2 * m) + 1) % 2) + 1 ≤ _; omega
  H_YC_FALL m := (RA.causal 1 (by omega)).H_YC_FALL m
  H_YC_RISE m := (RA.causal 1 (by omega)).H_YC_RISE m
  H_CTL_C j := (RA.causal 1 (by omega)).H_CTL_C j
  H_SRV j := (RA.causal 1 (by omega)).H_SRV j
  H_POS j := (RA.causal 1 (by omega)).H_POS j

theorem rstOK : MuxRstG run 12 := by
  have b : ∀ {a c : Nat}, Nat.ble a c = true → a ≤ c := fun h => Nat.le_of_ble_eq_true h
  refine ⟨⟨b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [RA.Xp_eq]; omega
  · rw [RA.D0_eq]; omega
  · rw [RA.Yp_eq]; omega
  · rw [RA.D1_eq]; omega
  · rw [RA.ZA0_eq]; omega
  · rw [RA.ZA1_eq]; omega

theorem static : MuxStaticG run uW 1 1 1 1 1 1 1 where
  H_LJ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WC := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WO := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_J0_X := Nat.le_of_ble_eq_true rfl
  S_J1_Y := Nat.le_of_ble_eq_true rfl
  S_J0_C := Nat.le_of_ble_eq_true rfl
  S_J1_C := Nat.le_of_ble_eq_true rfl
  S_XA_RTZ := Nat.le_of_ble_eq_true rfl
  S_YA_RTZ := Nat.le_of_ble_eq_true rfl
  S_XA_J2 := Nat.le_of_ble_eq_true rfl
  S_YA_J2 := Nat.le_of_ble_eq_true rfl
  S_XA_R := Or.inl (Nat.le_of_ble_eq_true rfl)
  S_YA_R := Or.inl (Nat.le_of_ble_eq_true rfl)
  S_XA_SEQ := Nat.le_of_ble_eq_true rfl
  S_YA_SEQ := Nat.le_of_ble_eq_true rfl

end RB

/-- **`S_XA_J.1` is not necessary** (first conjunct of row
`bd_mux.uxa_join_latency`). With a j0 → uxa wire of 1 tick on rises and 8
on falls, the shipped `S_XA_J.1` fails (`8 + 2 ≤ 4 + 4 + 1` is false), every
`MuxStaticG` field holds (`S_XA_N` with 4 ticks of slack, `S_XA_J.2`
`10 ≤ 13`), and `mux_ok_gs` gives `mux_ok`'s whole conclusion. The slow
j0 fall is live: j0 falls at 37, it reaches uxa at 45, and x_ack (node)
falls at 46. -/
theorem passB :
    ¬ (RB.run.W0x.hi + (RB.run.Lxa.hi + RB.run.wxah) ≤
        (1 + RB.run.Lor.lo + RB.run.Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + RB.run.W0x.lo) ∧
    MuxStaticG RB.run uW 1 1 1 1 1 1 1 ∧
    RA.j0 36 = true ∧ RA.j0 37 = false ∧ RA.j0x RB.Rx 44 = true ∧ RA.j0x RB.Rx 45 = false ∧
    RA.xa RB.Rx 1 45 = true ∧ RA.xa RB.Rx 1 46 = false ∧
    MuxConcl RB.run RA.j0 RA.j1 RA.zr (RA.xak RB.Rx 1) RA.yak := by
  refine ⟨by decide, RB.static, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  exact mux_ok_gs (RA.gates 1 RB.Rx) (RA.env 1 RB.Rx) RB.causal (Nat.le_refl 1) RB.static RB.rstOK

end Formal.Cells.Necessity7Mux
