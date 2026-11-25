import Formal.Cells.Necessity4Mux

/-!
# Necessity4MuxC: `bd_mux.uj_env_latency_ctl` (S_J0_C) is necessary at the boundary

Probe Bnx4 (shard B). The row `bd_mux.uj_env_latency_ctl` is the shipped
`MuxStatic` field pair `S_J0_C` / `S_J1_C` (`OpsTimedMux`):

    S_J0_C : Lj0.hi + wj0h ≤ Lj0.lo + (wo + Lor.lo + Dz.lo + Es) + Wzc.lo + Ec + Wc0.lo

Unlike `S_J0_X` (Necessity4Mux), its return path (join → uor → line →
server → z_ack → control sender → ctl_req → join) is the only one: the
control sender waits for nothing else. So no max form is needed.

## Result

* `MuxStaticC … s` is the shipped `MuxStatic` with `S_J0_C` weakened by
  `s` ticks, every other field word for word; `ClaimC s` is the shipped
  `mux_ok_static` with that structure. `claimC0 : ClaimC 0` is the shipped
  theorem.
* `claimC1_false : ¬ ClaimC 1`. A concrete run (`N5.run 8`, real INITs, all
  gate relations for all `t`): every LUT and wire 1 tick except the two ack
  wires `Wxa`, `Wya` (6 ticks, so the client return is long) and uj0's
  feedback net (8 ticks); the control sender answers in 1. Every shipped
  `MuxStatic` field holds (`S_J0_X` too: `9 ≤ 11`) except `S_J0_C`, which
  fails by exactly 1 (`9 = 8 + 1`); reset sequencing holds; and z_req is 0 at
  33 inside its token-0 window `[25, 40)`: ctl_req's fall reaches uj0 at 29
  (decode 0 at the LUT from 30) while x_req is still high and the 8-tick
  feedback shows j0's rise (at 22) only from 30, so j0 is 0 at 30 (a runt).
* `pass7`: the same family with a 7-tick net meets every shipped field and
  the shipped theorem applies (non-vacuity next to the boundary).

So the row is **sufficient + necessary_at_boundary** (x branch, uj0; the uj1
form is the symmetric statement, its counter-run not built). Binary `≤`
form; the strict (+1) JSON form is 2 ticks from the refuted point (audit P8
item 1 caveat), backed only by CElemStrict's generic X-window result.

Assumed / NOT covered: as Necessity4Mux (lumped LUT arcs, FIFO line,
port-level causal partners). One parameter point; not an iff.
-/

namespace Formal.Cells.Necessity4Mux
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B)

/-- The shipped `MuxStatic` with `S_J0_C` weakened by `s`. -/
structure MuxStaticC (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo s : Nat) : Prop where
  H_LJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo
  H_WC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo
  H_WO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo
  S_J0_X : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + P.W0x.lo + P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo
  S_J1_Y : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + P.W1y.lo + P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo
  S_J0_C : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc0.lo + s
  S_J1_C : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc1.lo
  S_OR : P.W0o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1o.lo ∧
    P.W1o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0o.lo
  S_XA_FORK : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo
  S_YA_FORK : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo
  S_XA_RTZ : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_RTZ : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_XA_J : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0x.lo ∧
    P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzx.lo
  S_YA_J : P.W1y.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1y.lo ∧
    P.W1y.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzy.lo

theorem MuxStaticC.toStatic {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}
    (S : MuxStaticC P Wzc Ex Ey Ec Es lj wc wo 0) : MuxStatic P Wzc Ex Ey Ec Es lj wc wo :=
  ⟨S.H_LJ, S.H_WC, S.H_WO, S.S_J0_X, S.S_J1_Y, S.S_J0_C, S.S_J1_C, S.S_OR, S.S_XA_FORK, S.S_YA_FORK,
    S.S_XA_RTZ, S.S_YA_RTZ, S.S_XA_J, S.S_YA_J⟩

/-- The shipped `mux_ok_static` with `S_J0_C` weakened by `s`; its conclusion
(z_req and both acks). -/
def ClaimC (s : Nat) : Prop :=
  ∀ (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo R : Nat)
    (rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak : Trace),
    MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak →
    MuxEnv P rst x y ctl za sx0 sx1 R → MuxCausal P Wzc Ex Ey Ec Es →
    MuxStaticC P Wzc Ex Ey Ec Es lj wc wo s → MuxRst P R →
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Tx xak (rx P.XA P.κ0) (fun _ => true) ∧
    Tok P.Ty yak P.YA P.sv ∧ Tok P.Ty yak (rx P.YA P.κ1) (fun _ => true)

theorem claimC0 : ClaimC 0 := by
  intro P Wzc Ex Ey Ec Es lj wc wo R rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x
    j1y zx zy xa qa ya qb xak yak G V Cs S hR
  exact mux_ok_static G V Cs S.toStatic hR.1 hR.2

/-! ## The run family

Every LUT, wire and line one tick, except `Wxa = Wya = shift 6` and uj0's
feedback net (`W` ticks). Reset high on `[0, 12)`. Tokens alternate x, y
(period 23 per token, base `b = 23 k + 20`); each client raises its request
4 ticks before ctl_req; x client, control sender and server answer in one
tick (all tight). Derived edges of token `k`: join node `b + 2`, z_ack at the
server `b + 6`, ctl_req's fall at the join `b + 9`, x_ack `b + 14`, x_req's
fall at the join `b + 16`. -/
namespace N5

def w6 : Ret := Ret.shift 6
theorem fw6 (c : Nat) (hc : 1 ≤ c) : w6.fst c = c + 6 := Ret.fst_shift 6 c hc

def run (W : Nat) : MuxRun where
  Wx := uW
  Wy := uW
  Wc0 := uW
  Wc1 := uW
  Lj0 := uW
  Lj1 := uW
  wj0l := W
  wj0h := W
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
  Wxa := w6
  Wya := w6
  ξ j := 46 * (j / 2) + 16 + 19 * (j % 2)
  η j := 46 * (j / 2) + 39 + 19 * (j % 2)
  γ j := 23 * (j / 2) + 20 + 8 * (j % 2)
  ζ j := 23 * (j / 2) + 26 + 15 * (j % 2)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

def x (t : Nat) : Bool := decide (16 ≤ t ∧ (t - 16) % 46 < 19)
def y (t : Nat) : Bool := decide (39 ≤ t ∧ (t - 39) % 46 < 19)
def ctl (t : Nat) : Bool := decide (20 ≤ t ∧ (t - 20) % 23 < 8)
def za (t : Nat) : Bool := decide (26 ≤ t ∧ (t - 26) % 23 < 15)
def sx (t : Nat) : Bool := svW ((t - 20) / 23)
def xj (t : Nat) : Bool := x (t - 1)
def yj (t : Nat) : Bool := y (t - 1)
def cj (t : Nat) : Bool := ctl (t - 1)
def j1 : Nat → Bool
  | 0 => false
  | 1 => j1B (yj 0) (cj 0) (sx 0) false (N4.rst 0)
  | t + 2 => j1B (yj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j1 t) (N4.rst (t + 1))
def q1 (t : Nat) : Bool := j1 (t - 1)
def e1 (t : Nat) : Bool := j1 (t - 1)
def ei (J : Trace) (t : Nat) : Bool := or2B (N4.e0 J (t - 1)) (e1 (t - 1))
def zr (J : Trace) (t : Nat) : Bool := ei J (t - 1)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
def xa (J : Trace) : Nat → Bool
  | 0 => false
  | 1 => c2B (N4.j0x J 0) (zx 0) false (N4.rst 0)
  | t + 2 => c2B (N4.j0x J (t + 1)) (zx (t + 1)) (xa J t) (N4.rst (t + 1))
def qa (J : Trace) (t : Nat) : Bool := xa J (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zx 0) false (N4.rst 0)
  | t + 2 => c2B (j1y (t + 1)) (zx (t + 1)) (ya t) (N4.rst (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (J : Trace) (t : Nat) : Bool := xa J (t - 6)
def yak (t : Nat) : Bool := ya (t - 6)

def JoinEq (W : Nat) (J : Trace) : Prop :=
  ∀ t, 1 ≤ t → J t = j0B (xj (t - 1)) (cj (t - 1)) (sx (t - 1)) (J (t - 1 - W)) (N4.rst (t - 1))

/-- uj0 with a 7-tick feedback net (loop 8). -/
def j0p : Nat → Bool
  | t + 8 => j0B (xj (t + 7)) (cj (t + 7)) (sx (t + 7)) (j0p t) (N4.rst (t + 7))
  | _ => false
/-- uj0 with an 8-tick feedback net (loop 9). -/
def j0f : Nat → Bool
  | t + 9 => j0B (xj (t + 8)) (cj (t + 8)) (sx (t + 8)) (j0f t) (N4.rst (t + 8))
  | _ => false

theorem j0p_eq : JoinEq 7 j0p := by
  intro t ht
  match t, ht with
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | t + 8, _ => rfl

theorem j0f_eq : JoinEq 8 j0f := by
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
  | t + 9, _ => rfl

theorem gates (W : Nat) (J : Trace) (hJ : JoinEq W J) :
    MuxGates (run W) N4.rst x y ctl za xj yj cj cj sx sx J (N4.q0 W J) j1 q1 (N4.e0 J) e1 (ei J) (zr J)
      (N4.j0x J) j1y zx zx (xa J) (qa J) ya qb (xak J) yak where
  H_WX _ _ := rfl
  H_WY _ _ := rfl
  H_WC0 _ _ := rfl
  H_WC1 _ _ := rfl
  H_UJ0 t ht := hJ t ht
  H_UJ0_FB := fun t ht => by
    have h : W ≤ t := ht
    exact ⟨t - W, by show t ≤ t - W + W; omega, by show t - W + W ≤ t; omega, rfl⟩
  H_UJ0_POS := by show 1 ≤ 1 + W; omega
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
variable (W : Nat)

theorem enum0 : Enum (fun k => !(run W).sv k) (run W).κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum (run W).sv (run W).κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

theorem Xp_eq (j : Nat) : (run W).Xp j = 46 * (j / 2) + 17 + 19 * (j % 2) := by
  show uW.fst (46 * (j / 2) + 16 + 19 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : (run W).Yp j = 46 * (j / 2) + 40 + 19 * (j % 2) := by
  show uW.fst (46 * (j / 2) + 39 + 19 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : (run W).C0 j = 23 * (j / 2) + 21 + 8 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 20 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C1_eq (j : Nat) : (run W).C1 j = 23 * (j / 2) + 21 + 8 * (j % 2) := by
  show uW.fst (23 * (j / 2) + 20 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem D0_eq (j : Nat) : (run W).D0 j = 46 * (j / 2) + 21 + 8 * (j % 2) := by
  show (run W).C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [C0_eq]; omega
theorem D1_eq (j : Nat) : (run W).D1 j = 46 * (j / 2) + 44 + 8 * (j % 2) := by
  show (run W).C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C1_eq]; omega
theorem c0_eq (j : Nat) : (run W).c0 j = 46 * (j / 2) + 21 + 15 * (j % 2) := by
  show max ((run W).Xp j) ((run W).D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : (run W).c1 j = 46 * (j / 2) + 44 + 15 * (j % 2) := by
  show max ((run W).Yp j) ((run W).D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : (run W).τ0 j = 46 * (j / 2) + 22 + 15 * (j % 2) := by
  show uW.fst ((run W).c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : (run W).τ1 j = 46 * (j / 2) + 45 + 15 * (j % 2) := by
  show uW.fst ((run W).c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : (run W).E j = 23 * (j / 2) + 22 + 15 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : (run W).sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx (run W).κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum0 W) (j / 2 / 2)
      rw [show (run W).κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega
  · have hs : (run W).sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx (run W).κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum1 W) (j / 2 / 2)
      rw [show (run W).κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega

theorem O0_eq (j : Nat) : (run W).O0 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : (run W).O1 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A0_eq (j : Nat) : (run W).A0 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : (run W).A1 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (j : Nat) : (run W).ZA0 j = 23 * (j / 2) + 27 + 15 * (j % 2) ∧
    (run W).ZA1 j = 23 * (j / 2) + 27 + 15 * (j % 2) := by
  constructor <;> (show uW.fst (23 * (j / 2) + 26 + 15 * (j % 2)) = _; rw [fuW _ (by omega)]; omega)

theorem Z_eq (j : Nat) : (run W).Z j = (run W).E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show (run W).Lor = uW from rfl, show (run W).Dz = uW from rfl]
  have hE := E_eq W j
  split
  · rw [O0_eq, fuW ((run W).E j + 1) (by omega), fuW ((run W).E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW ((run W).E j + 1) (by omega), fuW ((run W).E j + 1 + 1) (by omega)]

theorem XA_eq (j : Nat) : (run W).XA j = 23 * (j / 2) + 34 + 15 * (j % 2) ∧
    (run W).YA j = 23 * (j / 2) + 34 + 15 * (j % 2) := by
  have hm : max ((run W).E j + 1) (23 * (j / 2) + 27 + 15 * (j % 2)) = 23 * (j / 2) + 27 + 15 * (j % 2) := by
    rw [E_eq]; omega
  constructor
  · show w6.fst (uW.fst (max ((run W).A0 j) ((run W).ZA0 j))) = _
    rw [A0_eq, (ZA_eq W j).1, hm, fuW (23 * (j / 2) + 27 + 15 * (j % 2)) (by omega),
      fw6 (23 * (j / 2) + 27 + 15 * (j % 2) + 1) (by omega)]; omega
  · show w6.fst (uW.fst (max ((run W).A1 j) ((run W).ZA1 j))) = _
    rw [A1_eq, (ZA_eq W j).2, hm, fuW (23 * (j / 2) + 27 + 15 * (j % 2)) (by omega),
      fw6 (23 * (j / 2) + 27 + 15 * (j % 2) + 1) (by omega)]; omega

theorem env : MuxEnv (run W) N4.rst x y ctl za sx sx 12 where
  H_RST_HI := N4.rst_hi
  H_RST_LO := N4.rst_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 46 * (0 / 2) + 16 + 19 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 46 * (2 * k / 2) + 16 + 19 * (2 * k % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 1) / 2) + 16 + 19 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 46 * ((2 * k + 1) / 2) + 16 + 19 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 2) / 2) + 16 + 19 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 46 * (0 / 2) + 39 + 19 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 46 * (2 * k / 2) + 39 + 19 * (2 * k % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 1) / 2) + 39 + 19 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 46 * ((2 * k + 1) / 2) + 39 + 19 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 46 * ((2 * k + 2) / 2) + 39 + 19 * ((2 * k + 2) % 2) := h2
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
  H_ENUM0 := enum0 W
  H_ENUM1 := enum1 W
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq] at h1 h2
    show svW ((t - 20) / 23) = svW k
    rw [show (t - 20) / 23 = k by omega]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq] at h1 h2
    show svW ((t - 20) / 23) = svW k
    rw [show (t - 20) / 23 = k by omega]

/-- The partners are causal; client, control sender and server all tight. -/
theorem causal : MuxCausal (run W) uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [(XA_eq W _).1]; show _ ≤ 46 * ((2 * m + 1) / 2) + 16 + 19 * ((2 * m + 1) % 2)
    show 23 * (2 * (2 * m) / 2) + 34 + 15 * (2 * (2 * m) % 2) + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [(XA_eq W _).1]; show _ ≤ 46 * ((2 * m + 2) / 2) + 16 + 19 * ((2 * m + 2) % 2)
    show 23 * ((2 * (2 * m) + 1) / 2) + 34 + 15 * ((2 * (2 * m) + 1) % 2) + 1 ≤ _; omega
  H_YC_FALL m := by
    rw [(XA_eq W _).2]; show _ ≤ 46 * ((2 * m + 1) / 2) + 39 + 19 * ((2 * m + 1) % 2)
    show 23 * (2 * (2 * m + 1) / 2) + 34 + 15 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [(XA_eq W _).2]; show _ ≤ 46 * ((2 * m + 2) / 2) + 39 + 19 * ((2 * m + 2) % 2)
    show 23 * ((2 * (2 * m + 1) + 1) / 2) + 34 + 15 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (23 * (j / 2) + 26 + 15 * (j % 2)) + 1 ≤ 23 * ((j + 1) / 2) + 20 + 8 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 23 * (j / 2) + 26 + 15 * (j % 2); omega
  H_POS j := by show 1 ≤ 23 * (j / 2) + 20 + 8 * (j % 2); omega

theorem rstOK (hW : W ≤ 11) : MuxRst (run W) 12 := by
  have b : ∀ {a c : Nat}, Nat.ble a c = true → a ≤ c := fun h => Nat.le_of_ble_eq_true h
  refine ⟨⟨b rfl, b rfl, b rfl, b rfl, by show 1 + W ≤ 12; omega, b rfl,
    b rfl, b rfl, b rfl, b rfl, b rfl, b rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [A0_eq, E_eq]; omega
  · rw [(ZA_eq W 0).1]; omega
  · rw [A1_eq, E_eq]; omega
  · rw [(ZA_eq W 0).2]; omega

/-- Every shipped static obligation, `S_J0_C` at slack `s`, holds as long as
`1 + W ≤ 8 + s` (and `W ≤ 10` for `S_J0_X`). -/
theorem staticC (s : Nat) (h1 : 1 + W ≤ 8 + s) (h2 : W ≤ 10) :
    MuxStaticC (run W) uW 1 1 1 1 1 1 1 s where
  H_LJ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WC := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WO := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_J0_X := by show 1 + W ≤ 1 + 1 + 1 + 6 + 1 + 1; omega
  S_J1_Y := Nat.le_of_ble_eq_true rfl
  S_J0_C := by show 1 + W ≤ 1 + (1 + 1 + 1 + 1) + 1 + 1 + 1 + s; omega
  S_J1_C := Nat.le_of_ble_eq_true rfl
  S_OR := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_XA_FORK := Nat.le_of_ble_eq_true rfl
  S_YA_FORK := Nat.le_of_ble_eq_true rfl
  S_XA_RTZ := Nat.le_of_ble_eq_true rfl
  S_YA_RTZ := Nat.le_of_ble_eq_true rfl
  S_XA_J := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_YA_J := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

end closed
end N5

open N5

/-- Next to the boundary (7-tick net) every shipped field holds and the
shipped `mux_ok_static` applies. -/
theorem pass7 :
    MuxStatic (run 7) uW 1 1 1 1 1 1 1 ∧
    Tok (run 7).Tz (zr j0p) (run 7).Z (fun _ => true) ∧
    Tok (run 7).Tx (xak j0p) (run 7).XA (fun k => !(run 7).sv k) ∧
    zr j0p 33 = true ∧ xak j0p 37 = true ∧ yak 37 = false := by
  have S := (staticC 7 0 (by omega) (by omega)).toStatic
  have h := mux_ok_static (gates 7 j0p j0p_eq) (env 7) (causal 7) S (rstOK 7 (by omega)).1
    (rstOK 7 (by omega)).2
  exact ⟨S, h.1, h.2.1, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **The counter-run at slack 1.** With an 8-tick uj0 feedback net every
shipped `MuxStatic` field holds except `S_J0_C`, which holds only weakened by
one tick and fails by exactly one; reset sequencing holds; z_req is 0 at 33
inside its token-0 window `[Z 0, Z 1) = [25, 40)`. -/
theorem failC8 :
    MuxStaticC (run 8) uW 1 1 1 1 1 1 1 1 ∧
    (run 8).Lj0.hi + (run 8).wj0h = (run 8).Lj0.lo + (1 + (run 8).Lor.lo + (run 8).Dz.lo + 1) +
      uW.lo + 1 + (run 8).Wc0.lo + 1 ∧
    MuxRst (run 8) 12 ∧
    (run 8).Z 0 = 25 ∧ (run 8).Z 1 = 40 ∧ (run 8).E 0 = 22 ∧ (run 8).E 1 = 37 ∧
    j0f 30 = false ∧ zr j0f 33 = false ∧
    ¬ Tok (run 8).Tz (zr j0f) (run 8).Z (fun _ => true) := by
  have hZ0 : (run 8).Z 0 = 25 := by rw [Z_eq, E_eq]
  have hZ1 : (run 8).Z 1 = 40 := by rw [Z_eq, E_eq]
  have v1 : j0f 30 = false := by decide +kernel
  have v2 : zr j0f 33 = false := by decide +kernel
  have nz : ¬ Tok (run 8).Tz (zr j0f) (run 8).Z (fun _ => true) := by
    intro h
    have := h.hi 0 33 (by decide) (by rw [show 2 * 0 = 0 from rfl, hZ0]; omega)
      (by rw [show 2 * 0 + 1 = 1 from rfl, hZ1]; omega)
    rw [v2] at this; exact absurd this (by decide)
  exact ⟨staticC 8 1 (by omega) (by omega), by decide, rstOK 8 (by omega), hZ0, hZ1,
    by rw [E_eq], by rw [E_eq], v1, v2, nz⟩

/-- **`S_J0_C` cannot be weakened by one tick**: the shipped theorem with
`S_J0_C + 1` is false (counter-run `failC8`, every other hypothesis met). -/
theorem claimC1_false : ¬ ClaimC 1 := by
  intro h
  exact failC8.2.2.2.2.2.2.2.2.2
    (h (run 8) uW 1 1 1 1 1 1 1 12 N4.rst x y ctl za xj yj cj cj sx sx j0f (N4.q0 8 j0f) j1 q1
      (N4.e0 j0f) e1 (ei j0f) (zr j0f) (N4.j0x j0f) j1y zx zx (xa j0f) (qa j0f) ya qb (xak j0f) yak
      (gates 8 j0f j0f_eq) (env 8) (causal 8) failC8.1 (rstOK 8 (by omega))).1

end Formal.Cells.Necessity4Mux
