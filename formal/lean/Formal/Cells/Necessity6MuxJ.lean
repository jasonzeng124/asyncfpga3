import Formal.Cells.Necessity4Mux

/-!
# Necessity6MuxJ: `bd_mux.uxa_join_latency`, its z_ack half (`S_XA_J.2`)

Probe Bnx6 (shard B). The row `bd_mux.uxa_join_latency` is the `MuxStatic`
field pair `S_XA_J` / `S_YA_J` (`OpsTimedMux`), each a conjunction:

    S_XA_J.1 : W0x.hi + (Lxa.hi + wxah) ≤ Kz + Kc + W0x.lo        (next j0 edge at uxa)
    S_XA_J.2 : W0x.hi + (Lxa.hi + wxah) ≤ 2 Kz + Kc + Wzx.lo      (next z_ack edge at uxa)

with `Kz = wo + Lor.lo + Dz.lo + Es` (join node → z_ack at the server) and
`Kc = Wzc.lo + Ec + wc + lj` (z_ack → next join node through the control
sender). `S_XA_J.2` is a real race: j0's fall (end of an x token) travels
the j0 → uxa wire, while the same fall runs through uor, the line, the
server, the control sender, the NEXT token's join (a y token), uor, the line
and the server again, and comes back as z_ack's next rise at uxa. If the
rise arrives before uxa's loop has settled after j0's fall, uxa holds
x_ack high in a y token.

## Result

* `ClaimJ s`: `mux_ok` (whole conclusion) from `MuxGates + MuxEnv +
  MuxCausal +` reset sequencing `+ MuxStatic` with `S_XA_J.2` weakened by `s`
  (`MuxStaticJ`), every other field word for word. `claimJ0 : ClaimJ 0` is
  the shipped `mux_timing_of_static` + `mux_ok`.
* `J.run`: unit LUTs and wires except a **12-tick j0 → uxa wire** (`W0x`),
  tokens alternating x / y, every partner tight (`Ex = Ey = Ec = Es = 1`),
  reset held to 14. Real INITs, every gate relation for all `t`, open-loop
  periodic environment (period 43 per x / y pair: an x token lasts 25 ticks
  because x_ack waits for the slow j0 branch, a y token 18).
* `failJ`, `claimJ1_false : ¬ ClaimJ 1`: every `MuxStaticJ … 1` field holds,
  `S_XA_J.2` fails by exactly one (`12 + 2 = 13 + 1`), `S_XA_J.1` and the
  uya pair hold, reset sequencing holds, and the conclusion fails: j0's fall
  of token 0 reaches uxa at 57 while z_ack's rise of token 1 (a y token)
  reaches uxa at 58, one tick before uxa's feedback has shown x_ack's fall;
  x_ack then oscillates (period 2) through the y transaction: x_ack is 1 at
  60, inside `[XA 1, XA 2) = [59, 67)` where it must be 0.

So `S_XA_J.2` (the second conjunct of the row, uxa side) is **necessary at
the boundary** (one point, binary `≤`; the JSON's strict `+1` is 2 ticks
from the refuted point). The uya side is the mirror statement, not built.

## NOT covered (the first conjunct)

`S_XA_J.1` (against the next j0 edge) and `S_XA_FORK` (`bd_mux.
isochronic_forks`) look NOT necessary: in a token selecting x, the next j0
edge at uxa is causally after x_ack's edge (through the x client), and in a
token not selecting x, j0 does not move: the "next j0 edge" that `cel_run`
charges there is a bookkeeping edge of a gated-off token (`Tok` with gate
false). Showing non-necessity needs a `cel_run` whose `H_DEP` is required
only at real edges (gate on), or a retiming of the gated-off tokens'
bookkeeping edges; not attempted here. See B-necessity6.md.

## Assumed / proved / NOT covered

Assumed: OpsTimedMux's model (lumped FIFO LUT arcs `H_LUT_FIFO`, window
wires, FIFO line, port-level causal partners), real INITs of
uj0 / uj1 / uor / bd_c2.
Proved: as above. NOT covered: an iff over the box; the uya mirror run;
`S_XA_J.1`; per-pin arcs; the Kleene X `+1`.
-/

namespace Formal.Cells.Necessity6MuxJ
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B)
open Formal.Cells.Necessity4Mux (MuxConcl MuxRst)

/-- `MuxStatic` with the second conjunct of `S_XA_J` weakened by `s`. -/
structure MuxStaticJ (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo s : Nat) : Prop where
  H_LJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo
  H_WC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo
  H_WO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo
  S_J0_X : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + P.W0x.lo + P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo
  S_J1_Y : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + P.W1y.lo + P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo
  S_J0_C : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc0.lo
  S_J1_C : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc1.lo
  S_OR : P.W0o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1o.lo ∧
    P.W1o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0o.lo
  S_XA_FORK : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo
  S_YA_FORK : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo
  S_XA_RTZ : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_RTZ : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_XA_J1 : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0x.lo
  /-- **S_XA_J.2**, weakened by `s`. -/
  S_XA_J2 : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤
    2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzx.lo + s
  S_YA_J : P.W1y.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1y.lo ∧
    P.W1y.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzy.lo

theorem static_of {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}
    (S : MuxStaticJ P Wzc Ex Ey Ec Es lj wc wo 0) : MuxStatic P Wzc Ex Ey Ec Es lj wc wo :=
  ⟨S.H_LJ, S.H_WC, S.H_WO, S.S_J0_X, S.S_J1_Y, S.S_J0_C, S.S_J1_C, S.S_OR, S.S_XA_FORK, S.S_YA_FORK,
    S.S_XA_RTZ, S.S_YA_RTZ, ⟨S.S_XA_J1, by have := S.S_XA_J2; omega⟩, S.S_YA_J⟩

def ClaimJ (s : Nat) : Prop :=
  ∀ (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo R : Nat)
    (rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak : Trace),
    MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak →
    MuxEnv P rst x y ctl za sx0 sx1 R → MuxCausal P Wzc Ex Ey Ec Es →
    MuxStaticJ P Wzc Ex Ey Ec Es lj wc wo s → MuxRst P R → MuxConcl P j0 j1 zr xak yak

theorem claimJ0 : ClaimJ 0 := by
  intro P Wzc Ex Ey Ec Es lj wc wo R rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x
    j1y zx zy xa qa ya qb xak yak G V Cs S hR
  exact mux_ok G V (mux_timing_of_static V.H_ENUM0 V.H_ENUM1 Cs (static_of S) hR.1 hR.2)

/-! ## The run: a 12-tick j0 → uxa wire -/
namespace J

def run : MuxRun where
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
  W0x := Ret.shift 12
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
  ξ j := 43 * (j / 2) + 18 + 25 * (j % 2)
  η j := 43 * (j / 2) + 45 + 16 * (j % 2)
  γ j := 43 * (j / 4) + 26 + 8 * (j % 2) + 25 * (j / 2 % 2)
  ζ j := 43 * (j / 4) + 32 + 17 * (j % 2) + 25 * (j / 2 % 2) - 7 * (j % 4 / 3)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

def rst (t : Nat) : Bool := decide (t < 14)
-- environment
def x (t : Nat) : Bool := decide (18 ≤ t ∧ (t - 18) % 43 < 25)
def y (t : Nat) : Bool := decide (45 ≤ t ∧ (t - 45) % 43 < 16)
def ctl (t : Nat) : Bool :=
  decide (26 ≤ t ∧ ((t - 26) % 43 < 8 ∨ (25 ≤ (t - 26) % 43 ∧ (t - 26) % 43 < 33)))
def za (t : Nat) : Bool :=
  decide (32 ≤ t ∧ ((t - 32) % 43 < 17 ∨ (25 ≤ (t - 32) % 43 ∧ (t - 32) % 43 < 35)))
def sx (t : Nat) : Bool := decide (27 ≤ t ∧ 25 ≤ (t - 27) % 43)
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
/-- j0 at uxa, through the 12-tick wire. -/
def j0x (t : Nat) : Bool := j0 (t - 12)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
def xa : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x 0) (zx 0) false (rst 0)
  | t + 2 => c2B (j0x (t + 1)) (zx (t + 1)) (xa t) (rst (t + 1))
def qa (t : Nat) : Bool := xa (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zx 0) false (rst 0)
  | t + 2 => c2B (j1y (t + 1)) (zx (t + 1)) (ya t) (rst (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (t : Nat) : Bool := xa (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates : MuxGates run rst x y ctl za xj yj cj cj sx sx j0 q0 j1 q1 e0 e1 ei zr
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

theorem enum0 : Enum (fun k => !run.sv k) run.κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum run.sv run.κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

theorem f12 (c : Nat) (hc : 1 ≤ c) : (Ret.shift 12).fst c = c + 12 := Ret.fst_shift 12 c hc

/-! Closed forms. -/
theorem γ_eq (j : Nat) : run.γ j = 43 * (j / 4) + 26 + 8 * (j % 2) + 25 * (j / 2 % 2) := rfl
theorem Xp_eq (j : Nat) : run.Xp j = 43 * (j / 2) + 19 + 25 * (j % 2) := by
  show uW.fst (43 * (j / 2) + 18 + 25 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : run.Yp j = 43 * (j / 2) + 46 + 16 * (j % 2) := by
  show uW.fst (43 * (j / 2) + 45 + 16 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C_eq (j : Nat) : run.C0 j = run.γ j + 1 ∧ run.C1 j = run.γ j + 1 := by
  constructor <;> (show uW.fst (run.γ j) = _; rw [fuW _ (by rw [γ_eq]; omega)])
theorem D0_eq (j : Nat) : run.D0 j = 43 * (j / 2) + 27 + 8 * (j % 2) := by
  show run.C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [(C_eq _).1, γ_eq]; omega
theorem D1_eq (j : Nat) : run.D1 j = 43 * (j / 2) + 52 + 8 * (j % 2) := by
  show run.C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [(C_eq _).2, γ_eq]; omega
theorem τ0_eq (j : Nat) : run.τ0 j = 43 * (j / 2) + 28 + 17 * (j % 2) := by
  show uW.fst (max (run.Xp j) (run.D0 j)) = _
  rw [Xp_eq, D0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : run.τ1 j = 43 * (j / 2) + 53 + 10 * (j % 2) := by
  show uW.fst (max (run.Yp j) (run.D1 j)) = _
  rw [Yp_eq, D1_eq, fuW _ (by omega)]; omega

theorem dec4 (j : Nat) : ∃ m r, j = 4 * m + r ∧ (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) :=
  ⟨j / 4, j % 4, by omega, by omega⟩

theorem E_eq (j : Nat) :
    run.E j = 43 * (j / 4) + 28 + 17 * (j % 2) + 25 * (j / 2 % 2) - 7 * (j % 4 / 3) := by
  have hq := dec4 j
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : run.sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx run.κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum0 (j / 2 / 2)
      rw [show run.κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    have e : run.E j = run.τ0 (2 * idx run.κ0 (j / 2) + j % 2) := by
      unfold MuxRun.E; rw [hs]; rfl
    rw [e, hi, τ0_eq]
    obtain ⟨m, r, rfl, hr⟩ := hq
    rcases hr with rfl | rfl | rfl | rfl <;> omega
  · have hs : run.sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx run.κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum1 (j / 2 / 2)
      rw [show run.κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    have e : run.E j = run.τ1 (2 * idx run.κ1 (j / 2) + j % 2) := by
      unfold MuxRun.E; rw [hs]; rfl
    rw [e, hi, τ1_eq]
    obtain ⟨m, r, rfl, hr⟩ := hq
    rcases hr with rfl | rfl | rfl | rfl <;> omega

theorem E_pos (j : Nat) : 28 ≤ run.E j := by
  rw [E_eq]; obtain ⟨m, r, rfl, hr⟩ := dec4 j
  rcases hr with rfl | rfl | rfl | rfl <;> omega

theorem ζ_eq (j : Nat) : run.ζ j = run.E j + 4 := by
  rw [E_eq]; show 43 * (j / 4) + 32 + 17 * (j % 2) + 25 * (j / 2 % 2) - 7 * (j % 4 / 3) = _; omega

theorem E4 (m : Nat) : run.E (4 * m) = 43 * m + 28 ∧ run.E (4 * m + 1) = 43 * m + 45 ∧
    run.E (4 * m + 2) = 43 * m + 53 ∧ run.E (4 * m + 3) = 43 * m + 63 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [E_eq] <;> omega
theorem γ4 (m : Nat) : run.γ (4 * m) = 43 * m + 26 ∧ run.γ (4 * m + 1) = 43 * m + 34 ∧
    run.γ (4 * m + 2) = 43 * m + 51 ∧ run.γ (4 * m + 3) = 43 * m + 59 ∧ run.γ (4 * m + 4) = 43 * m + 69 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [γ_eq] <;> omega
/-- `(t - c) mod 43` inside one period. -/
theorem m43 (m t a b c : Nat) (h1 : 43 * m + a ≤ t) (h2 : t < 43 * m + b) (hca : c ≤ a)
    (hb : b ≤ c + 43) : (t - c) % 43 = t - c - 43 * m := by
  have e : t - c = (t - c - 43 * m) + 43 * m := by omega
  calc (t - c) % 43 = ((t - c - 43 * m) + 43 * m) % 43 := by rw [← e]
    _ = t - c - 43 * m := by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
/-- The edges of control token `k`, by parity. -/
theorem γk (k : Nat) : ∃ m, (k = 2 * m ∧ run.γ (2 * k) = 43 * m + 26 ∧ run.γ (2 * k + 1) = 43 * m + 34 ∧
      run.γ (2 * k + 2) = 43 * m + 51 ∧ run.ζ (2 * k) = 43 * m + 32 ∧ run.ζ (2 * k + 1) = 43 * m + 49 ∧
      run.ζ (2 * k + 2) = 43 * m + 57) ∨
    (k = 2 * m + 1 ∧ run.γ (2 * k) = 43 * m + 51 ∧ run.γ (2 * k + 1) = 43 * m + 59 ∧
      run.γ (2 * k + 2) = 43 * m + 69 ∧ run.ζ (2 * k) = 43 * m + 57 ∧ run.ζ (2 * k + 1) = 43 * m + 67 ∧
      run.ζ (2 * k + 2) = 43 * m + 75) := by
  refine ⟨k / 2, ?_⟩
  rcases Nat.mod_two_eq_zero_or_one k with h | h
  · left
    have e1 : 2 * k = 4 * (k / 2) := by omega
    have e2 : 2 * k + 1 = 4 * (k / 2) + 1 := by omega
    have e3 : 2 * k + 2 = 4 * (k / 2) + 2 := by omega
    have g := γ4 (k / 2); have E := E4 (k / 2)
    refine ⟨by omega, by rw [e1]; exact g.1, by rw [e2]; exact g.2.1, by rw [e3]; exact g.2.2.1, ?_, ?_, ?_⟩
    · rw [ζ_eq, e1, E.1]
    · rw [ζ_eq, e2, E.2.1]
    · rw [ζ_eq, e3, E.2.2.1]
  · right
    have e1 : 2 * k = 4 * (k / 2) + 2 := by omega
    have e2 : 2 * k + 1 = 4 * (k / 2) + 3 := by omega
    have e3 : 2 * k + 2 = 4 * (k / 2 + 1) := by omega
    have g := γ4 (k / 2); have E := E4 (k / 2); have E' := E4 (k / 2 + 1)
    refine ⟨by omega, by rw [e1]; exact g.2.2.1, by rw [e2]; exact g.2.2.2.1,
      by rw [show 2 * k + 2 = 4 * (k / 2) + 4 by omega]; exact g.2.2.2.2, ?_, ?_, ?_⟩
    · rw [ζ_eq, e1, E.2.2.1]
    · rw [ζ_eq, e2, E.2.2.2]
    · rw [ζ_eq, e3, E'.1]; omega
theorem Z_eq (j : Nat) : run.Z j = run.E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show run.Lor = uW from rfl, show run.Dz = uW from rfl]
  have hE := E_pos j
  split
  · show uW.fst (uW.fst (uW.fst (run.E j))) = _
    rw [fuW (run.E j) (by omega), fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]
  · show uW.fst (uW.fst (uW.fst (run.E j))) = _
    rw [fuW (run.E j) (by omega), fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]
theorem A0_eq (j : Nat) : run.A0 j = run.E j + 12 := by
  show (Ret.shift 12).fst (run.E j) = _; rw [f12 _ (by have := E_pos j; omega)]
theorem A1_eq (j : Nat) : run.A1 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by have := E_pos j; omega)]
theorem ZA_eq (j : Nat) : run.ZA0 j = run.E j + 5 ∧ run.ZA1 j = run.E j + 5 := by
  constructor <;> (show uW.fst (run.ζ j) = _; rw [ζ_eq, fuW _ (by omega)])
theorem XA_eq (j : Nat) : run.XA j = run.E j + 14 := by
  show uW.fst (uW.fst (max (run.A0 j) (run.ZA0 j))) = _
  have := E_pos j
  rw [A0_eq, (ZA_eq j).1, show max (run.E j + 12) (run.E j + 5) = run.E j + 12 by omega,
    fuW (run.E j + 12) (by omega), fuW (run.E j + 12 + 1) (by omega)]
theorem YA_eq (j : Nat) : run.YA j = run.E j + 7 := by
  show uW.fst (uW.fst (max (run.A1 j) (run.ZA1 j))) = _
  have := E_pos j
  rw [A1_eq, (ZA_eq j).2, show max (run.E j + 1) (run.E j + 5) = run.E j + 5 by omega,
    fuW (run.E j + 5) (by omega), fuW (run.E j + 5 + 1) (by omega)]

theorem env : MuxEnv run rst x y ctl za sx sx 14 where
  H_RST_HI t h := by simp [rst, h]
  H_RST_LO t h := by simp [rst]; omega
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 43 * (0 / 2) + 18 + 25 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 43 * (2 * k / 2) + 18 + 25 * (2 * k % 2) ≤ t := h1
      have h2 : t < 43 * ((2 * k + 1) / 2) + 18 + 25 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 43 * ((2 * k + 1) / 2) + 18 + 25 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 43 * ((2 * k + 2) / 2) + 18 + 25 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 43 * (0 / 2) + 45 + 16 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 43 * (2 * k / 2) + 45 + 16 * (2 * k % 2) ≤ t := h1
      have h2 : t < 43 * ((2 * k + 1) / 2) + 45 + 16 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 43 * ((2 * k + 1) / 2) + 45 + 16 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 43 * ((2 * k + 2) / 2) + 45 + 16 * ((2 * k + 2) % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < run.γ 0 := h2; rw [γ_eq] at h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : run.γ (2 * k) ≤ t := h1; have h2 : t < run.γ (2 * k + 1) := h2
      simp only [ctl, decide_eq_true_eq]
      obtain ⟨m, ⟨_, g1, g2, _⟩ | ⟨_, g1, g2, _⟩⟩ := γk k
      · rw [g1] at h1; rw [g2] at h2; have := m43 m t 26 34 26 h1 h2 (by omega) (by omega); omega
      · rw [g1] at h1; rw [g2] at h2; have := m43 m t 51 59 26 h1 h2 (by omega) (by omega); omega
    · have h1 : run.γ (2 * k + 1) ≤ t := h1; have h2 : t < run.γ (2 * k + 2) := h2
      simp only [ctl, decide_eq_false_iff_not]
      obtain ⟨m, ⟨_, _, g2, g3, _⟩ | ⟨_, _, g2, g3, _⟩⟩ := γk k
      · rw [g2] at h1; rw [g3] at h2; have := m43 m t 34 51 26 h1 h2 (by omega) (by omega); omega
      · rw [g2] at h1; rw [g3] at h2
        by_cases ht : t < 43 * m + 26 + 43
        · have := m43 m t 59 69 26 h1 ht (by omega) (by omega); omega
        · have := m43 (m + 1) t 26 26 26 (by omega) (by omega) (by omega) (by omega); omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < run.ζ 0 := h2; rw [ζ_eq, (E4 0).1] at h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : run.ζ (2 * k) ≤ t := h1; have h2 : t < run.ζ (2 * k + 1) := h2
      simp only [za, decide_eq_true_eq]
      obtain ⟨m, ⟨_, _, _, _, g1, g2, _⟩ | ⟨_, _, _, _, g1, g2, _⟩⟩ := γk k
      · rw [g1] at h1; rw [g2] at h2; have := m43 m t 32 49 32 h1 h2 (by omega) (by omega); omega
      · rw [g1] at h1; rw [g2] at h2; have := m43 m t 57 67 32 h1 h2 (by omega) (by omega); omega
    · have h1 : run.ζ (2 * k + 1) ≤ t := h1; have h2 : t < run.ζ (2 * k + 2) := h2
      simp only [za, decide_eq_false_iff_not]
      obtain ⟨m, ⟨_, _, _, _, _, g2, g3⟩ | ⟨_, _, _, _, _, g2, g3⟩⟩ := γk k
      · rw [g2] at h1; rw [g3] at h2; have := m43 m t 49 57 32 h1 h2 (by omega) (by omega); omega
      · rw [g2] at h1; rw [g3] at h2; have := m43 m t 67 75 32 h1 h2 (by omega) (by omega); omega
  H_ENUM0 := enum0
  H_ENUM1 := enum1
  H_S_PIN0 k t h1 h2 := by
    rw [(C_eq _).1] at h1 h2
    show decide (27 ≤ t ∧ 25 ≤ (t - 27) % 43) = decide (k % 2 = 1)
    obtain ⟨m, ⟨hk, g1, g2, _⟩ | ⟨hk, g1, g2, _⟩⟩ := γk k
    · rw [g1] at h1; rw [g2] at h2; have := m43 m t 27 35 27 h1 h2 (by omega) (by omega)
      exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · rw [g1] at h1; rw [g2] at h2; have := m43 m t 52 60 27 h1 h2 (by omega) (by omega)
      exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
  H_S_PIN1 k t h1 h2 := by
    rw [(C_eq _).2] at h1 h2
    show decide (27 ≤ t ∧ 25 ≤ (t - 27) % 43) = decide (k % 2 = 1)
    obtain ⟨m, ⟨hk, g1, g2, _⟩ | ⟨hk, g1, g2, _⟩⟩ := γk k
    · rw [g1] at h1; rw [g2] at h2; have := m43 m t 27 35 27 h1 h2 (by omega) (by omega)
      exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩
    · rw [g1] at h1; rw [g2] at h2; have := m43 m t 52 60 27 h1 h2 (by omega) (by omega)
      exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

/-- The partners are causal; every one is tight somewhere. -/
theorem causal : MuxCausal run uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [XA_eq, show 2 * run.κ0 m = 4 * m by show 2 * (2 * m) = 4 * m; omega, (E4 m).1]
    show _ ≤ 43 * ((2 * m + 1) / 2) + 18 + 25 * ((2 * m + 1) % 2); omega
  H_XC_RISE m := by
    rw [XA_eq, show 2 * run.κ0 m + 1 = 4 * m + 1 by show 2 * (2 * m) + 1 = 4 * m + 1; omega, (E4 m).2.1]
    show _ ≤ 43 * ((2 * m + 2) / 2) + 18 + 25 * ((2 * m + 2) % 2); omega
  H_YC_FALL m := by
    rw [YA_eq, show 2 * run.κ1 m = 4 * m + 2 by show 2 * (2 * m + 1) = 4 * m + 2; omega, (E4 m).2.2.1]
    show _ ≤ 43 * ((2 * m + 1) / 2) + 45 + 16 * ((2 * m + 1) % 2); omega
  H_YC_RISE m := by
    rw [YA_eq, show 2 * run.κ1 m + 1 = 4 * m + 3 by show 2 * (2 * m + 1) + 1 = 4 * m + 3; omega,
      (E4 m).2.2.2]
    show _ ≤ 43 * ((2 * m + 2) / 2) + 45 + 16 * ((2 * m + 2) % 2); omega
  H_CTL_C j := by
    show uW.fst (run.ζ j) + 1 ≤ run.γ (j + 1)
    rw [ζ_eq, fuW _ (by omega)]
    obtain ⟨m, r, rfl, hr⟩ := dec4 j
    have E := E4 m; have g := γ4 m
    rcases hr with rfl | rfl | rfl | rfl
    · rw [show 4 * m + 0 = 4 * m by omega, E.1, show 4 * m + 1 = 4 * m + 1 from rfl, g.2.1]; omega
    · rw [E.2.1, show 4 * m + 1 + 1 = 4 * m + 2 by omega, g.2.2.1]; omega
    · rw [E.2.2.1, show 4 * m + 2 + 1 = 4 * m + 3 by omega, g.2.2.2.1]; omega
    · rw [E.2.2.2, show 4 * m + 3 + 1 = 4 * m + 4 by omega, g.2.2.2.2]; omega
  H_SRV j := by rw [Z_eq, ζ_eq]; omega
  H_POS j := by rw [γ_eq]; omega

theorem rstOK : MuxRst run 14 := by
  have b : ∀ {a c : Nat}, Nat.ble a c = true → a ≤ c := fun h => Nat.le_of_ble_eq_true h
  refine ⟨⟨b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl, b rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [A0_eq]; have := E_pos 0; omega
  · rw [(ZA_eq 0).1]; have := E_pos 0; omega
  · rw [A1_eq]; have := E_pos 0; omega
  · rw [(ZA_eq 0).2]; have := E_pos 0; omega

/-- Every field holds, `S_XA_J.2` only when weakened by one tick. -/
theorem staticJ1 : MuxStaticJ run uW 1 1 1 1 1 1 1 1 where
  H_LJ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WC := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WO := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_J0_X := Nat.le_of_ble_eq_true rfl
  S_J1_Y := Nat.le_of_ble_eq_true rfl
  S_J0_C := Nat.le_of_ble_eq_true rfl
  S_J1_C := Nat.le_of_ble_eq_true rfl
  S_OR := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_XA_FORK := Nat.le_of_ble_eq_true rfl
  S_YA_FORK := Nat.le_of_ble_eq_true rfl
  S_XA_RTZ := Nat.le_of_ble_eq_true rfl
  S_YA_RTZ := Nat.le_of_ble_eq_true rfl
  S_XA_J1 := Nat.le_of_ble_eq_true rfl
  S_XA_J2 := Nat.le_of_ble_eq_true rfl
  S_YA_J := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

end J

/-- **`S_XA_J.2` is necessary at the boundary.** In `J.run` every
`MuxStaticJ … 1` field holds, `S_XA_J.2` fails by exactly one, reset
sequencing holds, and x_ack is 1 at 60, inside `[XA 1, XA 2) = [59, 67)`
(a y transaction), where `mux_ok` says it is 0: j0's fall reaches uxa at
57, z_ack's next rise at 58, and uxa's loop (2 ticks) has not settled. -/
theorem failJ :
    MuxStaticJ J.run uW 1 1 1 1 1 1 1 1 ∧
    J.run.W0x.hi + (J.run.Lxa.hi + J.run.wxah) =
      2 * (1 + J.run.Lor.lo + J.run.Dz.lo + 1) + (uW.lo + 1 + 1 + 1) + J.run.Wzx.lo + 1 ∧
    MuxRst J.run 14 ∧
    J.run.E 1 = 45 ∧ J.run.A0 1 = 57 ∧ J.run.ZA0 2 = 58 ∧ J.run.XA 1 = 59 ∧ J.run.XA 2 = 67 ∧
    J.j0x 56 = true ∧ J.j0x 57 = false ∧ J.zx 57 = false ∧ J.zx 58 = true ∧
    J.xak 59 = false ∧ J.xak 60 = true ∧ J.xak 61 = false ∧ J.xak 62 = true ∧
    ¬ Tok J.run.Tx J.xak J.run.XA (fun k => !J.run.sv k) ∧
    ¬ MuxConcl J.run J.j0 J.j1 J.zr J.xak J.yak := by
  have hE1 : J.run.E 1 = 45 := by rw [J.E_eq]
  have hXA1 : J.run.XA 1 = 59 := by rw [J.XA_eq, J.E_eq]
  have hXA2 : J.run.XA 2 = 67 := by rw [J.XA_eq, J.E_eq]
  have v : J.j0x 56 = true ∧ J.j0x 57 = false ∧ J.zx 57 = false ∧ J.zx 58 = true ∧
      J.xak 59 = false ∧ J.xak 60 = true ∧ J.xak 61 = false ∧ J.xak 62 = true := by decide +kernel
  have nx : ¬ Tok J.run.Tx J.xak J.run.XA (fun k => !J.run.sv k) := by
    intro h
    have := h.lo 0 60 (by decide) (by rw [show 2 * 0 + 1 = 1 from rfl, hXA1]; omega)
      (by rw [show 2 * 0 + 2 = 2 from rfl, hXA2]; omega)
    rw [v.2.2.2.2.2.1] at this; exact absurd this (by decide)
  exact ⟨J.staticJ1, rfl, J.rstOK, hE1, by rw [J.A0_eq, hE1], by rw [(J.ZA_eq 2).1, J.E_eq],
    hXA1, hXA2, v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2.1, v.2.2.2.2.2.2.1,
    v.2.2.2.2.2.2.2, nx, fun h => nx h.2.2.2.1⟩

/-- The counter-run meets every other hypothesis, so `ClaimJ 1` is false. -/
theorem claimJ1_false : ¬ ClaimJ 1 := by
  intro h
  exact failJ.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    (h J.run uW 1 1 1 1 1 1 1 14 J.rst J.x J.y J.ctl J.za J.xj J.yj J.cj J.cj J.sx J.sx J.j0 J.q0 J.j1
      J.q1 J.e0 J.e1 J.ei J.zr J.j0x J.j1y J.zx J.zx J.xa J.qa J.ya J.qb J.xak J.yak
      J.gates J.env J.causal J.staticJ1 J.rstOK)

end Formal.Cells.Necessity6MuxJ
