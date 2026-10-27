import Formal.Cells.OpsTimed2

/-!
# Shard B, probe Lt3: are the operator cells' obligations NECESSARY?

Probes Lt / Lt2 (`OpsTimed`, `OpsTimedMux`, `OpsTimedWit`, `OpsTimed2`) proved
the timed contracts of `bd_steer`, `bd_mux`, `bd_merge` under named per-arc
obligations, and showed by proof-level negative controls that the proofs
USE them. Here, for each obligation, we look for a concrete transport-delay
run on the REAL INITs that satisfies every other hypothesis of the theorem,
violates exactly that obligation (by the smallest amount we can), and in which
the theorem's conclusion is FALSE (kernel-evaluated: a wrong bit delivered at
an instant inside the theorem's window). Where the conclusion survives a
violation we say so and prove the survival.

The control side of every run is probe Lt's unit-delay witness
(`MuxWit.run`, `MergeWit.run`: every LUT/wire one tick, causal partners, all
`MuxStatic`/`MergeStatic` obligations proved there), reused unchanged. Only
the data side is varied: the data and select traces and the transport delay
of each datamux/usel pin. So every counter-run below satisfies the control
hypotheses of `mux_value_ok_static` / `merge_data_ok` by the SAME proof terms
as the non-vacuity witnesses.

For each obligation `O` there are (where meaningful) two theorems:
* `bnd_O`: the obligation holds with EQUALITY (boundary), and the theorem's
  conclusion holds (by applying the theorem);
* `cex_O`: one tick (or the stated amount) past the boundary, every other
  hypothesis still holds, `O` fails, and the conclusion fails at an explicit
  token and instant (with the delivered bit and the expected bit both shown).

Data values are chosen per the house rule (never degenerate): in every failing
instant the bit delivered differs from the expected bit, and the expected bit
is not a constant of the run (it takes both values over the tokens).
-/

namespace Formal.Cells.OpsTimed
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.Bundling (StableOn Gate Transport transport_gate)
open Formal.Cells.ConstraintsMux (DmRel dm_settles DM_ODD dm_odd_rel)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B or2_spec c2_spec j0_spec j1_spec)

/-! ## 1. bd_merge: data-path obligations (`MergeDataStatic`)

Control side: `MergeWit.run` (`ρ j = 8j+4`, `Z j = 8j+7`, `ζ j = 8j+8`,
`XA j = 8j+11`; even merged tokens are x's, odd y's). Data: x drives
`xvC k` during slot `[16k, 16k+15]`, y drives `yvC k`; both settle 4 ticks
before the owner's request (`Lx = Ly = 4`), hold until after the ack. The
values are chosen so that each kind of failure is visible:
`xvC = 1,1,0,0,…` (x's value changes between x tokens 0 and 2),
`yvC = 0,0,0,1,…` (y's value changes between y tokens 1 and 3), and
x ≠ y in token 0 (an x token) and in token 1 (a y token). -/
namespace MergeCex

set_option maxRecDepth 100000

def xvC (k : Nat) : Bool := decide (k % 4 < 2)
def yvC (k : Nat) : Bool := decide (k % 4 = 3)
def xdC (t : Nat) : Bool := xvC (t / 16)
def ydC (t : Nat) : Bool := yvC (t / 16)

/-- `usel` (REAL INIT `4'hE`) with transport delay `dr` on `I0 = x_req` and
`dq` on `I1 = x_ack` (the uxa node). -/
def selD (dr dq : Nat) (t : Nat) : Bool := lutB 0xE [MergeWit.x (t - dr), MergeWit.xa (t - dq)]
/-- `udat` odd bit (REAL INIT `8'hE4`, `.a(y_data) .b(x_data) .s(sel)`) with
transport delays `ds` (select), `dy`, `dx`. -/
def zD (dr dq ds dy dx : Nat) (t : Nat) : Bool :=
  lutB DM_ODD [selD dr dq (t - ds), ydC (t - dy), xdC (t - dx)]

theorem sel_gate (dr dq : Nat) : Gate 0xE [(MergeWit.x, dr, dr), (MergeWit.xa, dq, dq)] (selD dr dq) :=
  transport_gate 0xE [(MergeWit.x, dr, dr, dr), (MergeWit.xa, dq, dq, dq)] (selD dr dq)
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl)

theorem z_rel (dr dq ds dy dx : Nat) :
    DmRel (selD dr dq) ydC xdC (zD dr dq ds dy dx) ds ds dy dy dx dx :=
  dm_odd_rel (transport_gate DM_ODD [(selD dr dq, ds, ds, ds), (ydC, dy, dy, dy), (xdC, dx, dx, dx)]
    (zD dr dq ds dy dx)
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MergeDataEnv MergeWit.run xdC ydC (fun k => 16 * k) (fun k => 16 * k + 15)
    (fun k => 16 * k) (fun k => 16 * k + 15) xvC yvC 4 4 where
  H_X_DATA k _ t h1 h2 := by show xvC (t / 16) = xvC k; rw [show t / 16 = k by omega]
  H_Y_DATA k _ t h1 h2 := by show yvC (t / 16) = yvC k; rw [show t / 16 = k by omega]
  H_X_LEAD k _ := by show _ ≤ 8 * (2 * k) + 4; omega
  H_Y_LEAD k _ := by show _ ≤ 8 * (2 * k) + 4; omega
  H_X_HOLD k _ := by rw [(MergeWit.XA_eq _).1]; show _ ≤ 16 * k + 15; omega
  H_Y_HOLD k _ := by rw [(MergeWit.XA_eq _).2]; show _ ≤ 16 * k + 15; omega

theorem hRE : 4 ≤ MergeWit.run.AX 0 ∧ 4 ≤ MergeWit.run.ZA0 0 ∧ 4 ≤ MergeWit.run.AY 0 ∧
    4 ≤ MergeWit.run.ZA1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
  · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega
  · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
  · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega

/-- `merge_data_ok` on `MergeWit.run` with this file's data and the given pin
delays (windows `[d, d]`), `Eo = Es = wo = wz = la = wa = 1`, `Mz = 0`,
`Hm = 2`, `Lx = Ly = 4`. -/
theorem apply_ok (dr dq ds dy dx : Nat)
    (SD : MergeDataStatic MergeWit.run 1 1 1 1 1 1 dr dr dq dq ds ds dx dx dy dy 0 2 4 4) :
    ∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
      zD dr dq ds dy dx t = (if MergeWit.run.sv k then yvC k else xvC k) :=
  merge_data_ok MergeWit.gates MergeWit.env MergeWit.causal MergeWit.static (by decide) hRE
    (sel_gate dr dq) (Nat.le_refl _) (Nat.le_refl _) (z_rel dr dq ds dy dx)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) data_env SD

/-! Shorthands for `MergeWit.run`'s lumped arcs (all unit): `Kz = wo + Lor.lo +
Dz.lo + Es = 4`, `Ka = wz + la + wa + Eo = 4`, request path `Wxo.lo + Lor.lo +
Dz.lo = Wyo.lo + Lor.lo + Dz.lo = 3`. The `MergeDataStatic` fields are
restated literally in each counter-theorem (with the run's numbers), so the
reader can see which one fails. -/

/-! ### S_ZM_SEL_X (`bd_merge.bundled_z`): `hr + sh + Mz ≤ Wxo.lo + Lor.lo + Dz.lo` -/

/-- Boundary: `hr = 2, sh = 1`: `2 + 1 + 0 = 3`. The theorem applies. -/
theorem bnd_S_ZM_SEL_X : ∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
    zD 2 1 1 1 1 t = (if MergeWit.run.sv k then yvC k else xvC k) :=
  apply_ok 2 1 1 1 1 (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **Counter-run for S_ZM_SEL_X.** usel's `x_req` pin 3 ticks (`hr = 3`,
one past the boundary); every other hypothesis of `merge_data_ok` holds
(control side: Lt's witness; data env; every other `MergeDataStatic` field).
In x's token 0 the select is still low when z_req reaches the server, so the
server samples y's bit: `z (Z 0) = 0`, expected x's bit `1`. -/
theorem cex_S_ZM_SEL_X :
    -- the failing obligation
    ¬ (3 + 1 + 0 ≤ MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    -- every other field of `MergeDataStatic … 3 3 1 1 1 1 1 1 1 1 0 2 4 4`
    (1 + 0 ≤ 4 + MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (1 + 0 ≤ 4 + MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (3 + 1 + 0 ≤ (1 + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo + 1) + (1 + 1 + 1 + 1) +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    (MergeWit.run.Wzx.hi + MergeWit.run.Lxa.hi + 1 + 1 + 0 ≤ (1 + 1 + 1 + 1) +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    (MergeWit.run.Wxc.hi + MergeWit.run.Lxa.hi + 1 + 1 + 0 ≤
      (1 + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo + 1) + (1 + 1 + 1 + 1) +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    (2 + 1 ≤ MergeWit.run.Wzx.lo + MergeWit.run.Lxa.lo + MergeWit.run.Wxa.lo + 1 + 3 + 1) ∧
    (2 + 1 ≤ MergeWit.run.Wzy.lo + MergeWit.run.Lya.lo + MergeWit.run.Wya.lo + 1 + min 3 1 + 1) ∧
    (2 ≤ MergeWit.run.Wzx.lo + MergeWit.run.Lxa.lo + MergeWit.run.Wxa.lo + 1) ∧
    (2 ≤ MergeWit.run.Wzy.lo + MergeWit.run.Lya.lo + MergeWit.run.Wya.lo + 1) ∧
    (max 3 (MergeWit.run.Lxa.hi + 1) + 1 + 0 ≤ MergeWit.run.ρ 0 +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    -- the conclusion of `merge_data_ok` fails at token 0, instant `Z 0`
    MergeWit.run.sv 0 = false ∧ MergeWit.run.Z (2 * 0) = 7 ∧ MergeWit.run.ζ (2 * 0) = 8 ∧
    zD 3 1 1 1 1 7 = false ∧ xvC 0 = true ∧ xvC 2 = false ∧
    ¬ (∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
      zD 3 1 1 1 1 t = (if MergeWit.run.sv k then yvC k else xvC k)) := by
  have hz : MergeWit.run.Z (2 * 0) = 7 := MergeWit.Z_eq 0
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, rfl, hz, rfl, by decide, by decide, by decide, ?_⟩
  intro h
  have := h 0 7 (by rw [hz]; omega) (by decide)
  revert this; decide

/-- The same run as a hypothesis-level statement: everything `merge_data_ok`
needs except `MergeDataStatic` holds, and no `MergeDataStatic` instance with
these windows exists (it would make the conclusion true). -/
theorem cex_S_ZM_SEL_X_static :
    ¬ MergeDataStatic MergeWit.run 1 1 1 1 1 1 3 3 1 1 1 1 1 1 1 1 0 2 4 4 := by
  intro SD
  have := apply_ok 3 1 1 1 1 SD 0 7 (by rw [MergeWit.Z_eq 0]; omega) (by decide)
  revert this; decide

/-! ### S_ZM_X / S_ZM_Y (`bd_merge.bundled_z_data`): `xh + Mz ≤ Lx + Wxo.lo + Lor.lo + Dz.lo` -/

theorem bnd_S_ZM_XY : ∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
    zD 1 1 1 7 7 t = (if MergeWit.run.sv k then yvC k else xvC k) :=
  apply_ok 1 1 1 7 7 (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **Counter-run for S_ZM_X**: x_data's pin 8 ticks (`xh = 8 = Lx + 3 + 1`).
x's token 2: the server sees x's PREVIOUS value (`xvC 1 = 1`) instead of
`xvC 2 = 0`. Every other `MergeDataStatic` field holds (in particular
`S_ZM_Y` with `yh = 7`). -/
theorem cex_S_ZM_X :
    ¬ (8 + 0 ≤ 4 + MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (7 + 0 ≤ 4 + MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (1 + 1 + 0 ≤ MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (2 ≤ MergeWit.run.Wzx.lo + MergeWit.run.Lxa.lo + MergeWit.run.Wxa.lo + 8) ∧
    MergeWit.run.sv 2 = false ∧ MergeWit.run.Z (2 * 2) = 39 ∧ MergeWit.run.ζ (2 * 2) = 40 ∧
    zD 1 1 1 7 8 39 = true ∧ xvC 2 = false ∧
    ¬ (∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
      zD 1 1 1 7 8 t = (if MergeWit.run.sv k then yvC k else xvC k)) := by
  have hz : MergeWit.run.Z (2 * 2) = 39 := MergeWit.Z_eq 4
  refine ⟨by decide, by decide, by decide, by decide, rfl, hz, rfl, by decide, by decide, ?_⟩
  intro h
  have := h 2 39 (by rw [hz]; omega) (by decide)
  revert this; decide

theorem cex_S_ZM_X_static :
    ¬ MergeDataStatic MergeWit.run 1 1 1 1 1 1 1 1 1 1 1 1 8 8 7 7 0 2 4 4 := by
  intro SD
  have := apply_ok 1 1 1 7 8 SD 2 39 (by rw [MergeWit.Z_eq 4]; omega) (by decide)
  revert this; decide

/-- **Counter-run for S_ZM_Y**: y_data's pin 8 ticks. y's token 3: the
server sees `yvC 2 = 0` instead of `yvC 3 = 1`. -/
theorem cex_S_ZM_Y :
    ¬ (8 + 0 ≤ 4 + MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (7 + 0 ≤ 4 + MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    MergeWit.run.sv 3 = true ∧ MergeWit.run.Z (2 * 3) = 55 ∧ MergeWit.run.ζ (2 * 3) = 56 ∧
    zD 1 1 1 8 7 55 = false ∧ yvC 3 = true ∧
    ¬ (∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
      zD 1 1 1 8 7 t = (if MergeWit.run.sv k then yvC k else xvC k)) := by
  have hz : MergeWit.run.Z (2 * 3) = 55 := MergeWit.Z_eq 6
  refine ⟨by decide, by decide, rfl, hz, rfl, by decide, by decide, ?_⟩
  intro h
  have := h 3 55 (by rw [hz]; omega) (by decide)
  revert this; decide

theorem cex_S_ZM_Y_static :
    ¬ MergeDataStatic MergeWit.run 1 1 1 1 1 1 1 1 1 1 1 1 7 7 8 8 0 2 4 4 := by
  intro SD
  have := apply_ok 1 1 1 8 7 SD 3 55 (by rw [MergeWit.Z_eq 6]; omega) (by decide)
  revert this; decide

/-! ### S_SEL_XA_Z (`bd_merge.isochronic_forks`, x_ack branch, z_ack form):
`Wzx.hi + Lxa.hi + hq + sh + Mz ≤ Ka + Wyo.lo + Lor.lo + Dz.lo` -/

/-- Boundary: `hq = 4`: `1 + 1 + 4 + 1 + 0 = 7 = 4 + 3`. -/
theorem bnd_S_SEL_XA_Z : ∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
    zD 1 4 1 1 1 t = (if MergeWit.run.sv k then yvC k else xvC k) :=
  apply_ok 1 4 1 1 1 (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **Counter-run for S_SEL_XA_Z**: usel's `x_ack` pin 5 ticks (`hq = 5`, one
past the boundary). x's previous token's x_ack (the uxa node) is still seen
high by usel when y's token 1 z_req reaches the server, so the datamux still
selects x: `z (Z 2) = xvC 1 = 1`, expected `yvC 1 = 0`. Every other field
holds, including the request form `S_SEL_XA_R` and `H_SEL_START`. -/
theorem cex_S_SEL_XA_Z :
    ¬ (MergeWit.run.Wzx.hi + MergeWit.run.Lxa.hi + 5 + 1 + 0 ≤ (1 + 1 + 1 + 1) +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    (MergeWit.run.Wxc.hi + MergeWit.run.Lxa.hi + 5 + 1 + 0 ≤
      (1 + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo + 1) + (1 + 1 + 1 + 1) +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    (max 1 (MergeWit.run.Lxa.hi + 5) + 1 + 0 ≤ MergeWit.run.ρ 0 +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    (2 + 1 ≤ MergeWit.run.Wzy.lo + MergeWit.run.Lya.lo + MergeWit.run.Wya.lo + 1 + min 1 5 + 1) ∧
    (1 + 1 + 0 ≤ MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    MergeWit.run.sv 1 = true ∧ MergeWit.run.Z (2 * 1) = 23 ∧ MergeWit.run.ζ (2 * 1) = 24 ∧
    zD 1 5 1 1 1 23 = true ∧ yvC 1 = false ∧ MergeWit.xa 17 = true ∧ MergeWit.xa 18 = false ∧
    ¬ (∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
      zD 1 5 1 1 1 t = (if MergeWit.run.sv k then yvC k else xvC k)) := by
  have hz : MergeWit.run.Z (2 * 1) = 23 := MergeWit.Z_eq 2
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, hz, rfl, by decide, by decide,
    by decide, by decide, ?_⟩
  intro h
  have := h 1 23 (by rw [hz]; omega) (by decide)
  revert this; decide

theorem cex_S_SEL_XA_Z_static :
    ¬ MergeDataStatic MergeWit.run 1 1 1 1 1 1 1 1 5 5 1 1 1 1 1 1 0 2 4 4 := by
  intro SD
  have := apply_ok 1 5 1 1 1 SD 1 23 (by rw [MergeWit.Z_eq 2]; omega) (by decide)
  revert this; decide

end MergeCex

/-! ## 2. bd_mux: data-path obligations (`MuxDataStatic`)

Control side: `MuxWit.run` (control tokens alternate x, y; `Z (2k) = 18k+13`,
`ζ (2k) = 18k+14`; x's request rises at `36m+4` and reaches uj0 at `36m+5`,
ctl_req reaches it at `36m+9`: in this run the CONTROL request is the late
input of each join, by 4 ticks). Select: Lt's `MuxWit.sx` (settled 4 ticks
before ctl_req, `Ls = 4`). Data: x's `m`-th token `xvC m = 1,0,1,0,…` settles
exactly when x_req rises (`Lx = 0`, slot `[36m+4, 36m+39]`), y's
`yvC m = 0,0,1,1,…` exactly when y_req rises (`Ly = 0`, slot
`[36m+22, 36m+57]`). -/
namespace MuxCex

set_option maxRecDepth 100000

def xvC (m : Nat) : Bool := decide (m % 2 = 0)
def yvC (m : Nat) : Bool := decide (m % 4 ≥ 2)
def xdC (t : Nat) : Bool := xvC ((t - 4) / 36)
def ydC (t : Nat) : Bool := yvC ((t - 22) / 36)

/-- `udat` odd bit, REAL INIT `8'hE4` (`.a(x_data) .b(y_data) .s(s)`), transport
delays `ds`, `da`, `db` on its three pins. -/
def zM (ds da db : Nat) (t : Nat) : Bool := lutB DM_ODD [MuxWit.sx (t - ds), xdC (t - da), ydC (t - db)]

theorem z_rel (ds da db : Nat) : DmRel MuxWit.sx xdC ydC (zM ds da db) ds ds da da db db :=
  dm_odd_rel (transport_gate DM_ODD [(MuxWit.sx, ds, ds, ds), (xdC, da, da, da), (ydC, db, db, db)]
    (zM ds da db)
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MuxDataEnv MuxWit.run uW MuxWit.sx xdC ydC (fun k => 18 * k + 4)
    (fun k => 18 * k + 21) (fun m => 36 * m + 4) (fun m => 36 * m + 39) (fun m => 36 * m + 22)
    (fun m => 36 * m + 57) xvC yvC 4 0 0 where
  H_S_DATA k t h1 h2 := by
    show svW ((t - 4) / 18) = svW k; rw [show (t - 4) / 18 = k by omega]
  H_X_DATA m t h1 h2 := by show xvC ((t - 4) / 36) = xvC m; rw [show (t - 4) / 36 = m by omega]
  H_Y_DATA m t h1 h2 := by show yvC ((t - 22) / 36) = yvC m; rw [show (t - 22) / 36 = m by omega]
  H_S_LEAD k := by show _ ≤ 18 * (2 * k / 2) + 8 + 8 * (2 * k % 2); omega
  H_X_LEAD m := by show _ ≤ 36 * (2 * m / 2) + 4 + 14 * (2 * m % 2); omega
  H_Y_LEAD m := by show _ ≤ 36 * (2 * m / 2) + 22 + 14 * (2 * m % 2); omega
  H_S_HOLD k := by
    show uW.fst (18 * (2 * k / 2) + 14 + 10 * (2 * k % 2)) ≤ _
    rw [fuW _ (by omega)]; omega
  H_X_HOLD m := by
    rw [(MuxWit.XA_eq _).1]; show 18 * (2 * (2 * m) / 2) + 17 + 10 * (2 * (2 * m) % 2) ≤ _; omega
  H_Y_HOLD m := by
    rw [(MuxWit.XA_eq _).2]
    show 18 * (2 * (2 * m + 1) / 2) + 17 + 10 * (2 * (2 * m + 1) % 2) ≤ _; omega
  H_POS j := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 1 ≤ 18 * (j / 2) + 8 + 8 * (j % 2); omega
    · show 1 ≤ 36 * (j / 2) + 4 + 14 * (j % 2); omega
    · show 1 ≤ 36 * (j / 2) + 22 + 14 * (j % 2); omega
    · show 1 ≤ 18 * (j / 2) + 14 + 10 * (j % 2); omega

theorem hRE : 4 ≤ MuxWit.run.Xp 0 ∧ 4 ≤ MuxWit.run.D0 0 ∧ 4 ≤ MuxWit.run.Yp 0 ∧
    4 ≤ MuxWit.run.D1 0 ∧ 4 ≤ MuxWit.run.A0 0 ∧ 4 ≤ MuxWit.run.ZA0 0 ∧ 4 ≤ MuxWit.run.A1 0 ∧
    4 ≤ MuxWit.run.ZA1 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MuxWit.Xp_eq]; omega
  · rw [MuxWit.D0_eq]; omega
  · rw [MuxWit.Yp_eq]; omega
  · rw [MuxWit.D1_eq]; omega
  · rw [MuxWit.A0_eq, MuxWit.E_eq]; omega
  · rw [(MuxWit.ZA_eq 0).1]; omega
  · rw [MuxWit.A1_eq, MuxWit.E_eq]; omega
  · rw [(MuxWit.ZA_eq 0).2]; omega

/-- `mux_value_ok_static` on `MuxWit.run` with this file's data, pin delays
`ds, da, db` (windows `[d, d]`), `wo = 1`, `Mz = 0`, `Ls = 4`, `Lx = Ly = 0`. -/
theorem apply_ok (ds da db : Nat) (SD : MuxDataStatic MuxWit.run 1 ds da db 0 4 0 0) :
    ∀ k t, MuxWit.run.Z (2 * k) ≤ t + 0 → t ≤ MuxWit.run.ζ (2 * k) + MuxWit.run.holdM uW ds da db k →
      zM ds da db t = MuxWit.run.zv xvC yvC k :=
  (mux_value_ok_static MuxWit.gates MuxWit.env MuxWit.causal MuxWit.static (by decide) hRE
    (z_rel ds da db) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) data_env SD).2

theorem Z_ev (k : Nat) : MuxWit.run.Z (2 * k) = 18 * k + 13 := by
  rw [MuxWit.Z_eq, MuxWit.E_eq]; omega

/-- Boundary of all four mux data obligations at once: `shi = 9 = Ls + 5`,
`ahi = bhi = 5 = 0 + 5` (the request path `Wc/Wx + Lj + wo + Lor + Dz = 5`). -/
theorem bnd_S_Z : ∀ k t, MuxWit.run.Z (2 * k) ≤ t + 0 →
    t ≤ MuxWit.run.ζ (2 * k) + MuxWit.run.holdM uW 9 5 5 k → zM 9 5 5 t = MuxWit.run.zv xvC yvC k :=
  apply_ok 9 5 5 (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-! ### S_Z_S0 / S_Z_S1 (`bd_mux.bundled_z_s`): `shi + Mz ≤ Ls + Wc?.lo + Lj?.lo + wo + Lor.lo + Dz.lo`

The two share the select pin's window `shi` and, in this run, have equal
right-hand sides (`Wc0 = Wc1`, `Lj0 = Lj1`), so no run of THIS family
violates one without the other; the counter-run fails in an x token (S0's
case) AND in a y token (S1's case). -/

/-- **Counter-run for S_Z_S0 / S_Z_S1**: `shi = 10` (one past the boundary).
In y's token (control token 1) the stale select still picks x: `z (Z 2) =
xvC 0 = 1`, expected `yvC 0 = 0`; in control token 4 (an x token) it picks
y: `z (Z 8) = yvC 1 = 0`, expected `xvC 2 = 1`. `S_Z_X`, `S_Z_Y` hold. -/
theorem cex_S_Z_S :
    ¬ (10 + 0 ≤ 4 + MuxWit.run.Wc0.lo + MuxWit.run.Lj0.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    ¬ (10 + 0 ≤ 4 + MuxWit.run.Wc1.lo + MuxWit.run.Lj1.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 ≤ MuxWit.run.W0o.lo ∧ 1 ≤ MuxWit.run.W1o.lo) ∧
    (1 + 0 ≤ 0 + MuxWit.run.Wx.lo + MuxWit.run.Lj0.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 0 + MuxWit.run.Wy.lo + MuxWit.run.Lj1.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    MuxWit.run.sv 1 = true ∧ MuxWit.run.Z (2 * 1) = 31 ∧ zM 10 1 1 31 = true ∧
      MuxWit.run.zv xvC yvC 1 = false ∧
    MuxWit.run.sv 4 = false ∧ MuxWit.run.Z (2 * 4) = 85 ∧ zM 10 1 1 85 = false ∧
      MuxWit.run.zv xvC yvC 4 = true ∧
    ¬ (∀ k t, MuxWit.run.Z (2 * k) ≤ t + 0 →
      t ≤ MuxWit.run.ζ (2 * k) + MuxWit.run.holdM uW 10 1 1 k → zM 10 1 1 t = MuxWit.run.zv xvC yvC k) := by
  have z1 := Z_ev 1; have z4 := Z_ev 4
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, z1, by decide, by decide,
    rfl, z4, by decide, by decide, ?_⟩
  intro h
  have := h 1 31 (by rw [z1]; omega) (by decide)
  revert this; decide

/-! ### S_Z_X / S_Z_Y (`bd_mux.bundled_z_data`): `ahi + Mz ≤ Lx + Wx.lo + Lj0.lo + wo + Lor.lo + Dz.lo`

Here the obligation is NOT tight in this run: the static form bounds `Z(2k)`
below through x's OWN request path, but the join waits for the later of x_req
and ctl_req, and in `MuxWit.run` ctl_req is later by 4 ticks. So a violation
by up to 4 ticks is harmless (`surv_S_Z_X`, proved for every token and
instant), and 5 ticks fails (`cex_S_Z_X`). The exact condition is
`ahi + Mz ≤ Lx + (Z(2k) − ξ(2m))` per token; the static form is its
instance when x's request is the join's late input and every request-path
arc is at its minimum. -/

theorem idx0 (m : Nat) : idx MuxWit.run.κ0 (2 * m) = m := idx_κ MuxWit.enum0 m
theorem idx1 (m : Nat) : idx MuxWit.run.κ1 (2 * m + 1) = m := idx_κ MuxWit.enum1 m
theorem sv_e (m : Nat) : MuxWit.run.sv (2 * m) = false := by
  show decide (2 * m % 2 = 1) = false; simp
theorem sv_o (m : Nat) : MuxWit.run.sv (2 * m + 1) = true := by
  show decide ((2 * m + 1) % 2 = 1) = true; simp
theorem ζ_ev (k : Nat) : MuxWit.run.ζ (2 * k) = 18 * k + 14 := by
  show 18 * (2 * k / 2) + 14 + 10 * (2 * k % 2) = _; omega

/-- **Survival**: `ahi = 9` violates S_Z_X by 4 (`9 + 0 > 0 + 5`), every
other hypothesis holds, and the conclusion of `mux_value_ok_static`'s value
half STILL holds for every control token and instant. -/
theorem surv_S_Z_X :
    ¬ (9 + 0 ≤ 0 + MuxWit.run.Wx.lo + MuxWit.run.Lj0.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 4 + MuxWit.run.Wc0.lo + MuxWit.run.Lj0.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 4 + MuxWit.run.Wc1.lo + MuxWit.run.Lj1.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 0 + MuxWit.run.Wy.lo + MuxWit.run.Lj1.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (∀ k t, MuxWit.run.Z (2 * k) ≤ t + 0 →
      t ≤ MuxWit.run.ζ (2 * k) + MuxWit.run.holdM uW 1 9 1 k → zM 1 9 1 t = MuxWit.run.zv xvC yvC k) := by
  refine ⟨by decide, by decide, by decide, by decide, ?_⟩
  intro k t h1 h2
  have hR := z_rel 1 9 1
  rw [Z_ev] at h1
  rw [ζ_ev] at h2
  obtain ⟨m, hm⟩ : ∃ m, k = 2 * m ∨ k = 2 * m + 1 := ⟨k / 2, by omega⟩
  rcases hm with rfl | rfl
  · have hS := data_env.H_S_DATA (2 * m)
    rw [sv_e] at hS
    have hv : MuxWit.run.zv xvC yvC (2 * m) = xvC m := by
      unfold MuxRun.zv; rw [sv_e, idx0]; rfl
    have hh : MuxWit.run.holdM uW 1 9 1 (2 * m) = 2 := by
      unfold MuxRun.holdM; rw [sv_e]; rfl
    rw [hh] at h2
    have st := dm_settles hR (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) false (xvC m) _ _ _ _
      hS (data_env.H_X_DATA m)
    rw [hv]
    exact st t (by simp only [Bool.false_eq_true, ite_false]; omega)
      (by simp only [Bool.false_eq_true, ite_false]; omega)
  · have hS := data_env.H_S_DATA (2 * m + 1)
    rw [sv_o] at hS
    have hv : MuxWit.run.zv xvC yvC (2 * m + 1) = yvC m := by
      unfold MuxRun.zv; rw [sv_o, idx1]; rfl
    have hh : MuxWit.run.holdM uW 1 9 1 (2 * m + 1) = 2 := by
      unfold MuxRun.holdM; rw [sv_o]; rfl
    rw [hh] at h2
    have st := dm_settles hR (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) true (yvC m) _ _ _ _
      hS (data_env.H_Y_DATA m)
    rw [hv]
    exact st t (by simp only [ite_true]; omega) (by simp only [ite_true]; omega)

/-- **Counter-run for S_Z_X**: `ahi = 10` (S_Z_X violated by 5; S_Z_S0/S1,
S_Z_Y hold). Control token 2 (x's token 1): the server sees x's previous
bit `xvC 0 = 1`, expected `xvC 1 = 0`. -/
theorem cex_S_Z_X :
    ¬ (10 + 0 ≤ 0 + MuxWit.run.Wx.lo + MuxWit.run.Lj0.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 4 + MuxWit.run.Wc0.lo + MuxWit.run.Lj0.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 4 + MuxWit.run.Wc1.lo + MuxWit.run.Lj1.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 0 + MuxWit.run.Wy.lo + MuxWit.run.Lj1.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    MuxWit.run.sv 2 = false ∧ MuxWit.run.Z (2 * 2) = 49 ∧ zM 1 10 1 49 = true ∧
      MuxWit.run.zv xvC yvC 2 = false ∧
    ¬ (∀ k t, MuxWit.run.Z (2 * k) ≤ t + 0 →
      t ≤ MuxWit.run.ζ (2 * k) + MuxWit.run.holdM uW 1 10 1 k → zM 1 10 1 t = MuxWit.run.zv xvC yvC k) := by
  have z2 := Z_ev 2
  refine ⟨by decide, by decide, by decide, by decide, rfl, z2, by decide, by decide, ?_⟩
  intro h
  have := h 2 49 (by rw [z2]; omega) (by decide)
  revert this; decide

/-- **Counter-run for S_Z_Y**: `bhi = 10`. Control token 5 (y's token 2):
the server sees `yvC 1 = 0`, expected `yvC 2 = 1`. -/
theorem cex_S_Z_Y :
    ¬ (10 + 0 ≤ 0 + MuxWit.run.Wy.lo + MuxWit.run.Lj1.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    (1 + 0 ≤ 0 + MuxWit.run.Wx.lo + MuxWit.run.Lj0.lo + 1 + MuxWit.run.Lor.lo + MuxWit.run.Dz.lo) ∧
    MuxWit.run.sv 5 = true ∧ MuxWit.run.Z (2 * 5) = 103 ∧ zM 1 1 10 103 = false ∧
      MuxWit.run.zv xvC yvC 5 = true ∧
    ¬ (∀ k t, MuxWit.run.Z (2 * k) ≤ t + 0 →
      t ≤ MuxWit.run.ζ (2 * k) + MuxWit.run.holdM uW 1 1 10 k → zM 1 1 10 t = MuxWit.run.zv xvC yvC k) := by
  have z5 := Z_ev 5
  refine ⟨by decide, by decide, rfl, z5, by decide, by decide, ?_⟩
  intro h
  have := h 5 103 (by rw [z5]; omega) (by decide)
  revert this; decide

end MuxCex

/-! ## 3. H_OR_SKEW (and its static form S_OR) is NOT necessary

`or_tok` (the OR of two exclusively gated token traces) asks that EVERY edge
of each pin's sequence precede the other pin's next edge, including the
edges of tokens the pin does not carry (a gate-off slot's edges are only
bookkeeping: the pin is low across them). Those fictitious edges are what
`H_OR_SKEW` (`O0 j ≤ O1 (j+1) ∧ O1 j ≤ O0 (j+1)` for ALL `j`) constrains,
and what `S_OR` bounds by a wire-skew inequality. Below:

* `Tok.retime`: a token trace may be re-timed onto any monotone sequence that
  agrees with its own on its gate-on slots (the pin is low across every run
  of gate-off slots);
* `or_tok_mono`: hence the OR is a clean four-phase trace on the selected
  edges as soon as THAT sequence is monotone (no skew condition at all);
* `mux_or_mono`: for the mux, that sequence (`orEdges … O0 O1`) is strictly
  increasing by port-level causality alone (`MuxCausal`, `1 ≤ Es`): each
  selected edge reaches uor before the server sees z_req move, before z_ack
  moves, before the control sender moves, before the next join edge;
* `mux_ok_noskew`: `mux_ok`'s whole conclusion without `H_OR_SKEW`.

So `H_OR_SKEW` / `S_OR` are proof artefacts: no run can be a counter-example.
(In `mux_timing_of_static`, `S_OR` is used for nothing but `H_OR_SKEW`.) -/

namespace Tok
variable {T : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool}

theorem slot_of :
    ∀ n t, e 0 ≤ t → t < e n → ∃ i, e i ≤ t ∧ t < e (i + 1) := by
  intro n
  induction n with
  | zero => intro t h1 h2; omega
  | succ n ih =>
    intro t h1 h2
    by_cases h : t < e n
    · exact ih t h1 h
    · exact ⟨n, by omega, h2⟩

/-- **Re-timing a token trace.** If `S` is monotone and equals `e` on every
gate-on slot, the trace is also a token trace on `S` (with `e` unbounded,
every instant outside the gate-on slots is low; `e` need not be monotone). -/
theorem retime (h : Tok T x e g) (eunb : ∀ t, ∃ n, t < e n)
    {S : Nat → Nat} (smono : ∀ a b, a ≤ b → S a ≤ S b)
    (hS : ∀ k, g k = true → S (2 * k) = e (2 * k) ∧ S (2 * k + 1) = e (2 * k + 1)) :
    Tok T x S g := by
  -- an instant inside a gate-on slot of `e` lies in the same slot of `S`
  have on : ∀ t, T ≤ t → x t = true → ∃ k, g k = true ∧ S (2 * k) ≤ t ∧ t < S (2 * k + 1) := by
    intro t hT hx
    by_cases h0 : t < e 0
    · rw [h.pre t hT h0] at hx; exact absurd hx (by simp)
    · obtain ⟨n, hn⟩ := eunb t
      obtain ⟨i, hi1, hi2⟩ := slot_of (e := e) n t (by omega) hn
      by_cases hl : SlotLow g i
      · rw [h.low_slot i t hl hT hi1 hi2] at hx; exact absurd hx (by simp)
      · have hi : i % 2 = 0 ∧ g (i / 2) = true := by
          unfold SlotLow at hl; constructor
          · omega
          · cases hg : g (i / 2)
            · exact absurd (Or.inr hg) hl
            · rfl
        obtain ⟨k, rfl⟩ : ∃ k, i = 2 * k := ⟨i / 2, by omega⟩
        rw [show 2 * k / 2 = k by omega] at hi
        have e1 := hS k hi.2
        exact ⟨k, hi.2, by omega, by omega⟩
  -- so any instant in a low slot of `S` (or before `S 0`) is low
  have low : ∀ t, T ≤ t → (t < S 0 ∨ ∃ j, SlotLow g j ∧ S j ≤ t ∧ t < S (j + 1)) → x t = false := by
    intro t hT hc
    cases hx : x t
    · rfl
    · obtain ⟨k, hk, h1, h2⟩ := on t hT hx
      exfalso
      rcases hc with hc | ⟨j, hj, h3, h4⟩
      · have := smono 0 (2 * k) (Nat.zero_le _); omega
      · rcases Nat.lt_trichotomy j (2 * k) with c | c | c
        · have := smono (j + 1) (2 * k) (by omega); omega
        · subst c
          unfold SlotLow at hj
          rcases hj with hj | hj
          · omega
          · rw [show 2 * k / 2 = k by omega, hk] at hj; exact absurd hj (by simp)
        · have := smono (2 * k + 1) j (by omega); omega
  refine ⟨fun t hT h2 => low t hT (Or.inl h2), fun k t hT h1 h2 => ?_,
    fun k t hT h1 h2 => low t hT (Or.inr ⟨2 * k + 1, Or.inl (by omega), h1, h2⟩)⟩
  cases hg : g k
  · exact low t hT (Or.inr ⟨2 * k, Tok.slotLow_even hg, h1, h2⟩)
  · have e1 := hS k hg
    rw [h.hi k t hT (by omega) (by omega), hg]

end Tok

/-- **OR without a skew condition.** Each pin a token trace on its own
unbounded edges, exclusive gates; if the SELECTED edge sequence is
monotone, the OR is one clean four-phase transaction per token on it. -/
theorem or_tok_mono {T : Nat} {x y : Trace} {e e' : Nat → Nat} {g : Nat → Bool}
    (hx : Tok T x e g) (hy : Tok T y e' (fun k => !g k))
    (eu : ∀ t, ∃ n, t < e n) (eu' : ∀ t, ∃ n, t < e' n)
    (sm : ∀ a b, a ≤ b → orEdges g e e' a ≤ orEdges g e e' b) :
    Tok T (fun t => x t || y t) (orEdges g e e') (fun _ => true) := by
  have dk : ∀ k, 2 * k / 2 = k := fun k => by omega
  have dk1 : ∀ k, (2 * k + 1) / 2 = k := fun k => by omega
  have x' := hx.retime eu sm (fun k hk => by
    unfold orEdges; rw [dk, dk1, hk]; exact ⟨rfl, rfl⟩)
  have y' := hy.retime eu' sm (fun k hk => by
    have hk' : g k = false := by simpa using hk
    unfold orEdges; rw [dk, dk1, hk']; exact ⟨rfl, rfl⟩)
  have o := or_tok x' y' (fun j => sm j (j + 1) (by omega)) (fun j => sm j (j + 1) (by omega))
  exact o.congr (fun j => by unfold orEdges; split <;> rfl)

section noskew
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es : Nat}

/-- The OR's selected edge at uor. -/
def MuxRun.Sor (P : MuxRun) (j : Nat) : Nat := orEdges (fun k => !P.sv k) P.O0 P.O1 j

/-- **The mux's selected-edge sequence at uor is strictly increasing, from
port-level causality alone** (no static inequality): `E j ≤ Sor j ≤ Z j <
ζ j ≤ E (j+1) ≤ Sor (j+1)`. -/
theorem mux_or_step (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hEs : 1 ≤ Es) (j : Nat) :
    P.E j ≤ P.Sor j ∧ P.Sor j < P.E (j + 1) := by
  have hES : P.E j ≤ P.Sor j := by
    unfold MuxRun.Sor orEdges MuxRun.O0 MuxRun.O1
    split
    · exact P.W0o.fst_ge _
    · exact P.W1o.fst_ge _
  refine ⟨hES, ?_⟩
  have hSZ : P.Sor j ≤ P.Z j := by
    have := P.Lor.fst_ge (P.Sor j); have := P.Dz.fst_ge (P.Lor.fst (P.Sor j))
    unfold MuxRun.Z; unfold MuxRun.Sor at *; omega
  have h1 := Cs.H_SRV j
  have h2 := Cs.H_CTL_C j
  have h3 := Wzc.fst_ge (P.ζ j)
  have hC := C_le_E hE0 hE1 Cs.H_POS (j + 1)
  have hg0 := P.Wc0.fst_ge (P.γ (j + 1)); have hg1 := P.Wc1.fst_ge (P.γ (j + 1))
  cases hs : P.sv ((j + 1) / 2)
  · have := (hC.2 hs).1; unfold MuxRun.C0 at *; omega
  · have := (hC.1 hs).1; unfold MuxRun.C1 at *; omega

/-- `mux_ok`'s timing obligations without `H_OR_SKEW` (and without
`H_CTL_SEQ`, which is only used for the monotonicity of the join edges,
here derived from causality). -/
structure MuxTimingNoSkew (P : MuxRun) (R : Nat) : Prop where
  H_RST_LONG : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
    P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
    P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
    P.Lya.hi + P.wyah ≤ R
  H_RST_EARLY : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
    R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0
  H_DEP_J0 : ∀ j, P.c0 j + P.Lj0.hi + P.wj0h ≤ P.Xp (j + 1) ∧ P.c0 j + P.Lj0.hi + P.wj0h ≤ P.D0 (j + 1)
  H_DEP_J1 : ∀ j, P.c1 j + P.Lj1.hi + P.wj1h ≤ P.Yp (j + 1) ∧ P.c1 j + P.Lj1.hi + P.wj1h ≤ P.D1 (j + 1)
  H_DEP_XA : ∀ j, P.cx j + P.Lxa.hi + P.wxah ≤ P.A0 (j + 1) ∧ P.cx j + P.Lxa.hi + P.wxah ≤ P.ZA0 (j + 1)
  H_DEP_YA : ∀ j, P.cy j + P.Lya.hi + P.wyah ≤ P.A1 (j + 1) ∧ P.cy j + P.Lya.hi + P.wyah ≤ P.ZA1 (j + 1)

/-- **`mux_ok_noskew`: `mux_ok`'s conclusions without `H_OR_SKEW`**, with the
partners' port-level causality (`MuxCausal`, a server taking at least one
tick) in place of the skew condition and of `H_CTL_SEQ`. -/
theorem mux_ok_noskew {R : Nat} {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y
      zx zy xa qa ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (TM : MuxTimingNoSkew P R)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hEs : 1 ≤ Es) :
    Tok P.Lj0.hi j0 P.E (fun k => !P.sv k) ∧ Tok P.Lj1.hi j1 P.E P.sv ∧
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Tx xak (rx P.XA P.κ0) (fun _ => true) ∧
    Tok P.Ty yak P.YA P.sv ∧ Tok P.Ty yak (rx P.YA P.κ1) (fun _ => true) := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, u3, u4, u5, u6, u7, u8⟩ := TM.H_RST_EARLY
  have st := mux_or_step V.H_ENUM0 V.H_ENUM1 Cs hEs
  have Em : ∀ a b, a ≤ b → P.E a ≤ P.E b :=
    mono_of_step P.E (fun j => by have := st j; omega)
  have Eu : ∀ j, j ≤ P.E j := by
    intro j; induction j with
    | zero => omega
    | succ j ih => have := st j; omega
  have Sm : ∀ a b, a ≤ b → P.Sor a ≤ P.Sor b :=
    mono_of_step P.Sor (fun j => by have := st j; have := st (j + 1); omega)
  -- joins (as in `mux_ok`)
  have hxj : Tok R xj P.Xp (fun _ => true) := ((V.H_X.fifo P.Wx G.H_WX).mono (by omega))
  have hdec0 : Tok R (fun t => cj0 t && !sx0 t) P.D0 (fun _ => true) :=
    (((V.H_CTL.fifo P.Wc0 G.H_WC0).gate (fun a b => a && !b) (fun _ => rfl) (s := sx0) (sv := P.sv)
      (fun k t _ h1 h2 => V.H_S_PIN0 k t h1 h2)).reindex V.H_ENUM0).mono (by omega)
  have C0 : CEl xj (fun t => cj0 t && !sx0 t) rst j0 q0
      (fun t => j0B (xj t) (cj0 t) (sx0 t) (q0 t) (rst t)) P.Lj0 P.wj0l P.wj0h :=
    ⟨fun t => j0_spec _ _ _ _ _, G.H_UJ0, G.H_UJ0_FB, G.H_UJ0_POS⟩
  have n0 := cel_node C0 (cel_run C0 hxj hdec0 V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u1 u2 TM.H_DEP_J0)
  have j0E : Tok P.Lj0.hi j0 P.E (fun k => !P.sv k) :=
    ((n0.congr (fun j => (E_rx0 V.H_ENUM0 j).symm)).lift V.H_ENUM0 (fun j => Em j (j + 1) (by omega)))
  have hyj : Tok R yj P.Yp (fun _ => true) := ((V.H_Y.fifo P.Wy G.H_WY).mono (by omega))
  have hdec1 : Tok R (fun t => cj1 t && sx1 t) P.D1 (fun _ => true) :=
    (((V.H_CTL.fifo P.Wc1 G.H_WC1).gate (fun a b => a && b) (fun _ => rfl) (s := sx1) (sv := P.sv)
      (fun k t _ h1 h2 => V.H_S_PIN1 k t h1 h2)).reindex V.H_ENUM1).mono (by omega)
  have C1 : CEl yj (fun t => cj1 t && sx1 t) rst j1 q1
      (fun t => j1B (yj t) (cj1 t) (sx1 t) (q1 t) (rst t)) P.Lj1 P.wj1l P.wj1h :=
    ⟨fun t => j1_spec _ _ _ _ _, G.H_UJ1, G.H_UJ1_FB, G.H_UJ1_POS⟩
  have n1 := cel_node C1 (cel_run C1 hyj hdec1 V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u3 u4 TM.H_DEP_J1)
  have j1E : Tok P.Lj1.hi j1 P.E P.sv :=
    ((n1.congr (fun j => (E_rx1 V.H_ENUM1 j).symm)).lift V.H_ENUM1 (fun j => Em j (j + 1) (by omega)))
  -- uor WITHOUT the skew condition
  have p0 : Tok (P.Lj0.hi + P.W0o.hi + (P.Lj1.hi + P.W1o.hi)) e0 P.O0 (fun k => !P.sv k) :=
    (j0E.fifo P.W0o G.H_W0O).mono (by omega)
  have p1 : Tok (P.Lj0.hi + P.W0o.hi + (P.Lj1.hi + P.W1o.hi)) e1 P.O1 (fun k => !(!P.sv k)) :=
    ((j1E.fifo P.W1o G.H_W1O).mono (by omega)).gcongr (fun k => by simp)
  have o := or_tok_mono p0 p1
    (fun t => ⟨t + 1, by
      have := Eu (t + 1); have := P.W0o.fst_ge (P.E (t + 1)); unfold MuxRun.O0; omega⟩)
    (fun t => ⟨t + 1, by
      have := Eu (t + 1); have := P.W1o.fst_ge (P.E (t + 1)); unfold MuxRun.O1; omega⟩)
    Sm
  have zt := (o.fifo P.Lor (y := ei) (fun t ht => by rw [G.H_UOR t ht, or2_spec])).fifo P.Dz G.H_DZ
  -- the acknowledge C-elements (as in `mux_ok`)
  have ax : Tok R j0x P.A0 (fun k => !P.sv k) := (j0E.fifo P.W0x G.H_W0X).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl j0x zx rst xa qa (fun t => c2B (j0x t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r11 u5 u6 TM.H_DEP_XA)
  have xk : Tok P.Tx xak P.XA (fun k => !P.sv k) :=
    ((nx.fifo P.Wxa G.H_WXA).gcongr (fun k => by simp))
  have ay : Tok R j1y P.A1 P.sv := (j1E.fifo P.W1y G.H_W1Y).mono (by omega)
  have zy' : Tok R zy P.ZA1 (fun _ => true) := (V.H_ZA.fifo P.Wzy G.H_WZY).mono (by omega)
  have CY : CEl j1y zy rst ya qb (fun t => c2B (j1y t) (zy t) (qb t) (rst t)) P.Lya P.wyal P.wyah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UYA, G.H_UYA_FB, G.H_UYA_POS⟩
  have ny := cel_node CY (cel_run CY ay zy' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r12 u7 u8 TM.H_DEP_YA)
  have yk : Tok P.Ty yak P.YA P.sv :=
    ((ny.fifo P.Wya G.H_WYA).gcongr (fun k => by simp))
  exact ⟨j0E, j1E, zt.congr (fun j => rfl), xk, xk.reindex V.H_ENUM0, yk, yk.reindex V.H_ENUM1⟩

end noskew

/-- Non-vacuity of `mux_ok_noskew` on Lt's unit-delay mux run. -/
theorem MuxWit.noskew_witness :
    Tok MuxWit.run.Tz MuxWit.zr MuxWit.run.Z (fun _ => true) :=
  (mux_ok_noskew MuxWit.gates MuxWit.env
    ⟨MuxWit.timing.H_RST_LONG, MuxWit.timing.H_RST_EARLY, MuxWit.timing.H_DEP_J0,
      MuxWit.timing.H_DEP_J1, MuxWit.timing.H_DEP_XA, MuxWit.timing.H_DEP_YA⟩
    MuxWit.causal (Nat.le_refl 1)).2.2.1

/-! ## 4. S_XA_PW / S_YA_PW are NOT necessary for the real acknowledge pulses

`mux_pulses` (Lt2) proves `∀ j, XA j < XA (j+1)` over the CONTROL-indexed
edges, i.e. including the bookkeeping edges of tokens that select y (x_ack
does not move in them), and needs **S_XA_PW** (spread of `z_ack → uxa →
client` below a round trip) for that. The physically meaningful statement is
that every x token's acknowledge is a non-empty pulse at the client: x-indexed
strictness. That follows from the client's own causality: x drops its
request only after SEEING x_ack rise (`H_XC_FALL`), and uxa's node can fall
only after x_req's fall crossed the join, so x_ack's fall reaches the client
after its rise did, through the SAME FIFO wire: a pulse whose end is caused
by its own observation cannot be swallowed by the wire that delivered it.
Likewise for the gap (`H_XC_RISE`). No spread condition is involved; only
`1 ≤ Ex` (the client takes at least one tick). -/

section noPW
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es : Nat}

theorem mux_E_x (hE0 : Enum (fun k => !P.sv k) P.κ0) (m r : Nat) (hr : r < 2) :
    P.E (2 * P.κ0 m + r) = P.τ0 (2 * m + r) := by
  have hs : P.sv (P.κ0 m) = false := by have := hE0.hit m; simpa using this
  unfold MuxRun.E
  rw [show (2 * P.κ0 m + r) / 2 = P.κ0 m by omega, show (2 * P.κ0 m + r) % 2 = r by omega, hs,
    idx_κ hE0 m]
  rfl

theorem mux_E_y (hE1 : Enum P.sv P.κ1) (m r : Nat) (hr : r < 2) :
    P.E (2 * P.κ1 m + r) = P.τ1 (2 * m + r) := by
  have hs : P.sv (P.κ1 m) = true := hE1.hit m
  unfold MuxRun.E
  rw [show (2 * P.κ1 m + r) / 2 = P.κ1 m by omega, show (2 * P.κ1 m + r) % 2 = r by omega, hs,
    idx_κ hE1 m]
  rfl

/-- x's request edge `ξ i` (x-indexed) is before x_ack's edge at the client
for the control token that consumes it (same parity). -/
theorem mux_ξ_le_XA (hE0 : Enum (fun k => !P.sv k) P.κ0) (m r : Nat) (hr : r < 2) :
    P.ξ (2 * m + r) ≤ P.XA (2 * P.κ0 m + r) := by
  have hE := mux_E_x hE0 m r hr
  have a1 := P.Wx.fst_ge (P.ξ (2 * m + r))
  have a2 := P.Lj0.fst_ge (P.c0 (2 * m + r))
  have a3 := P.W0x.fst_ge (P.E (2 * P.κ0 m + r))
  have a4 := P.Lxa.fst_ge (P.cx (2 * P.κ0 m + r))
  have a5 := P.Wxa.fst_ge (P.Lxa.fst (P.cx (2 * P.κ0 m + r)))
  unfold MuxRun.XA MuxRun.cx MuxRun.A0 MuxRun.τ0 MuxRun.c0 MuxRun.Xp at *
  omega

theorem mux_η_le_YA (hE1 : Enum P.sv P.κ1) (m r : Nat) (hr : r < 2) :
    P.η (2 * m + r) ≤ P.YA (2 * P.κ1 m + r) := by
  have hE := mux_E_y hE1 m r hr
  have a1 := P.Wy.fst_ge (P.η (2 * m + r))
  have a2 := P.Lj1.fst_ge (P.c1 (2 * m + r))
  have a3 := P.W1y.fst_ge (P.E (2 * P.κ1 m + r))
  have a4 := P.Lya.fst_ge (P.cy (2 * P.κ1 m + r))
  have a5 := P.Wya.fst_ge (P.Lya.fst (P.cy (2 * P.κ1 m + r)))
  unfold MuxRun.YA MuxRun.cy MuxRun.A1 MuxRun.τ1 MuxRun.c1 MuxRun.Yp at *
  omega

/-- **x_ack's pulses and gaps at the client are non-empty, x-indexed, from
causality alone** (no S_XA_PW, no static inequality). -/
theorem mux_XA_real_step (hE0 : Enum (fun k => !P.sv k) P.κ0) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (hEx : 1 ≤ Ex) (m : Nat) :
    P.XA (2 * P.κ0 m) < P.XA (2 * P.κ0 m + 1) ∧ P.XA (2 * P.κ0 m + 1) < P.XA (2 * P.κ0 (m + 1)) := by
  have f := Cs.H_XC_FALL m; have r := Cs.H_XC_RISE m
  have l1 := mux_ξ_le_XA hE0 m 1 (by omega)
  have l2 := mux_ξ_le_XA hE0 (m + 1) 0 (by omega)
  simp only [Nat.add_zero] at l2
  rw [show 2 * (m + 1) = 2 * m + 2 by omega] at l2
  constructor <;> omega

theorem mux_YA_real_step (hE1 : Enum P.sv P.κ1) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (hEy : 1 ≤ Ey) (m : Nat) :
    P.YA (2 * P.κ1 m) < P.YA (2 * P.κ1 m + 1) ∧ P.YA (2 * P.κ1 m + 1) < P.YA (2 * P.κ1 (m + 1)) := by
  have f := Cs.H_YC_FALL m; have r := Cs.H_YC_RISE m
  have l1 := mux_η_le_YA hE1 m 1 (by omega)
  have l2 := mux_η_le_YA hE1 (m + 1) 0 (by omega)
  simp only [Nat.add_zero] at l2
  rw [show 2 * (m + 1) = 2 * m + 2 by omega] at l2
  constructor <;> omega

/-- **`mux_ack_pulses_noPW`**: `mux_pulses`' acknowledge conclusions for the
real pulses (x_ack high at the start of every x token's acknowledge and low
at its end, at the client; y likewise), under all of `mux_pulses`'
hypotheses EXCEPT `S_XA_PW`, `S_YA_PW` (and `1 ≤ Es`, `H_START` in its
control-indexed form), with `1 ≤ Ex`, `1 ≤ Ey` and the start-up condition at
the first real edge instead. -/
theorem mux_ack_pulses_noPW {R lj wc wo : Nat} {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr
      j0x j1y zx zy xa qa ya qb xak yak : Trace}
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
    (hEx : 1 ≤ Ex) (hEy : 1 ≤ Ey)
    (H_START_XY : P.Tx ≤ P.XA (2 * P.κ0 0) ∧ P.Ty ≤ P.YA (2 * P.κ1 0)) :
    (∀ m, xak (P.XA (2 * P.κ0 m)) = true ∧ xak (P.XA (2 * P.κ0 m + 1)) = false) ∧
    (∀ m, yak (P.YA (2 * P.κ1 m)) = true ∧ yak (P.YA (2 * P.κ1 m + 1)) = false) := by
  have hE0 := V.H_ENUM0; have hE1 := V.H_ENUM1
  obtain ⟨_, _, xr, _, yr⟩ := mux_ok_static G V Cs S hRL hRE
  have Xs := mux_XA_real_step hE0 Cs hEx
  have Ys := mux_YA_real_step hE1 Cs hEy
  have Xm : ∀ m, P.XA (2 * P.κ0 0) ≤ P.XA (2 * P.κ0 m) := by
    intro m; induction m with
    | zero => omega
    | succ m ih => have := Xs m; omega
  have Ym : ∀ m, P.YA (2 * P.κ1 0) ≤ P.YA (2 * P.κ1 m) := by
    intro m; induction m with
    | zero => omega
    | succ m ih => have := Ys m; omega
  refine ⟨fun m => ⟨?_, ?_⟩, fun m => ⟨?_, ?_⟩⟩
  · have h := (xr.at_edge m (by rw [rx_e]; have := Xm m; omega)
      (by rw [rx_e, rx_o]; exact (Xs m).1)).1
    rw [rx_e] at h; exact h
  · have h := xr.at_gap m (by rw [rx_o]; have := Xm m; have := (Xs m).1; omega)
      (by rw [rx_o, rx_e2]; exact (Xs m).2)
    rw [rx_o] at h; exact h
  · have h := (yr.at_edge m (by rw [rx_e]; have := Ym m; omega)
      (by rw [rx_e, rx_o]; exact (Ys m).1)).1
    rw [rx_e] at h; exact h
  · have h := yr.at_gap m (by rw [rx_o]; have := Ym m; have := (Ys m).1; omega)
      (by rw [rx_o, rx_e2]; exact (Ys m).2)
    rw [rx_o] at h; exact h

end noPW

/-! The merge, same argument: the owner drops its request only after seeing
its ack rise (`H_OWN`), and uxa's node falls only after that request fall
crossed it. -/
section noPWmerge
variable {P : MergeRun} {Eo Es : Nat}

theorem merge_XA_real_step (Cs : MergeCausal P Eo Es) (hEo : 1 ≤ Eo) (k : Nat) (hk : P.sv k = false) :
    P.XA (2 * k) < P.XA (2 * k + 1) := by
  have h := Cs.H_OWN (2 * k)
  rw [show 2 * k / 2 = k by omega, hk] at h
  simp only [Bool.false_eq_true, ite_false] at h
  have a1 := P.Wxc.fst_ge (P.ρ (2 * k + 1))
  have a4 := P.Lxa.fst_ge (P.cx (2 * k + 1))
  have a5 := P.Wxa.fst_ge (P.Lxa.fst (P.cx (2 * k + 1)))
  unfold MergeRun.XA MergeRun.cx MergeRun.AX at *
  omega

theorem merge_YA_real_step (Cs : MergeCausal P Eo Es) (hEo : 1 ≤ Eo) (k : Nat) (hk : P.sv k = true) :
    P.YA (2 * k) < P.YA (2 * k + 1) := by
  have h := Cs.H_OWN (2 * k)
  rw [show 2 * k / 2 = k by omega, hk] at h
  simp only [ite_true] at h
  have a1 := P.Wyc.fst_ge (P.ρ (2 * k + 1))
  have a4 := P.Lya.fst_ge (P.cy (2 * k + 1))
  have a5 := P.Wya.fst_ge (P.Lya.fst (P.cy (2 * k + 1)))
  unfold MergeRun.YA MergeRun.cy MergeRun.AY at *
  omega

end noPWmerge

/-- Non-vacuity of `mux_ack_pulses_noPW` on Lt's unit-delay mux run. -/
theorem MuxWit.ack_pulses_noPW_witness :
    (∀ m, MuxWit.xak (MuxWit.run.XA (2 * MuxWit.run.κ0 m)) = true ∧
      MuxWit.xak (MuxWit.run.XA (2 * MuxWit.run.κ0 m + 1)) = false) ∧
    (∀ m, MuxWit.yak (MuxWit.run.YA (2 * MuxWit.run.κ1 m)) = true ∧
      MuxWit.yak (MuxWit.run.YA (2 * MuxWit.run.κ1 m + 1)) = false) :=
  mux_ack_pulses_noPW MuxWit.gates MuxWit.env MuxWit.causal MuxWit.static (by decide)
    MuxCex.hRE (Nat.le_refl 1) (Nat.le_refl 1) (by
      constructor
      · rw [(MuxWit.XA_eq _).1]; show 1 + 1 ≤ 18 * (2 * (2 * 0) / 2) + 17 + 10 * (2 * (2 * 0) % 2); omega
      · rw [(MuxWit.XA_eq _).2]; show 1 + 1 ≤ 18 * (2 * (2 * 0 + 1) / 2) + 17 + 10 * (2 * (2 * 0 + 1) % 2)
        omega)

/-! ## 5. bd_steer's H_ACK_SKEW is NOT necessary either

`steer_back` ORs the two branches' acknowledges at `uack` with `or_tok` under
**H_ACK_SKEW** (every edge of each pin before the other pin's next edge,
bookkeeping edges included). With `or_tok_mono` the only thing needed is that
the selected acknowledge edges at uack (`au`) increase, which is the
sender/receiver causality (`H_RCV`, `H_SND`, `1 ≤ Es`): `au j ≤ K j <
ρ (j+1) ≤ Rsel (j+1) ≤ A (j+1) ≤ au (j+1)`. -/
theorem steer_back_noskew {P : SteerRun} {req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack : Trace}
    {Ta Er Es : Nat}
    (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (h0 : Tok Ta a0 P.A (fun k => !P.sv k)) (h1 : Tok Ta a1 P.A P.sv)
    (H_RCV : ∀ j, P.Rsel j + Er ≤ P.A j) (H_SND : ∀ j, P.K j + Es ≤ P.ρ (j + 1)) (hEs : 1 ≤ Es) :
    Tok (P.T2 Ta) ack P.K (fun _ => true) := by
  have hAau : ∀ j, P.A j ≤ P.au j := fun j => by
    unfold SteerRun.au orEdges; split
    · exact P.Wa0.fst_ge _
    · exact P.Wa1.fst_ge _
  have hρR : ∀ j, P.ρ j ≤ P.Rsel j := fun j => by
    have a := P.Wq.fst_ge (P.ρ j)
    have b5 := P.L5.fst_ge (P.Wq.fst (P.ρ j)); have b6 := P.L6.fst_ge (P.Wq.fst (P.ρ j))
    have c0 := P.W0.fst_ge (P.L5.fst (P.Wq.fst (P.ρ j)))
    have c1 := P.W1.fst_ge (P.L6.fst (P.Wq.fst (P.ρ j)))
    unfold SteerRun.Rsel SteerRun.R0 SteerRun.R1 SteerRun.qr; split <;> omega
  have hauK : ∀ j, P.au j ≤ P.K j := fun j => by
    have := P.La.fst_ge (P.au j); have := P.Wk.fst_ge (P.La.fst (P.au j))
    unfold SteerRun.K; omega
  have step : ∀ j, P.au j < P.au (j + 1) := fun j => by
    have := hauK j; have := H_SND j; have := hρR (j + 1); have := H_RCV (j + 1); have := hAau (j + 1)
    omega
  have Au : ∀ j, j ≤ P.au j := by
    intro j; induction j with
    | zero => omega
    | succ j ih => have := step j; omega
  have Ku : ∀ j, P.au j < P.A (j + 1) := fun j => by
    have := hauK j; have := H_SND j; have := hρR (j + 1); have := H_RCV (j + 1); omega
  have p0 := (h0.fifo P.Wa0 G.H_WA0).mono (T' := Ta + (P.Wa0.hi + P.Wa1.hi)) (by omega)
  have p1 := (h1.fifo P.Wa1 G.H_WA1).mono (T' := Ta + (P.Wa0.hi + P.Wa1.hi)) (by omega)
  have p1' : Tok (Ta + (P.Wa0.hi + P.Wa1.hi)) a1u (fun j => P.Wa1.fst (P.A j))
      (fun k => !(!P.sv k)) := by simpa using p1
  have o := or_tok_mono p0 p1'
    (fun t => ⟨t + 1, by have := Au t; have := Ku t; have := P.Wa0.fst_ge (P.A (t + 1)); omega⟩)
    (fun t => ⟨t + 1, by have := Au t; have := Ku t; have := P.Wa1.fst_ge (P.A (t + 1)); omega⟩)
    (mono_of_step P.au (fun j => Nat.le_of_lt (step j)))
  have ot := o.fifo P.La (y := ao) (fun t ht => by rw [G.H_UA t ht, or2_spec])
  exact (ot.fifo P.Wk G.H_WK).congr (fun j => rfl)

/-- The merge's selected edge sequence at uor (`orEdges … XO YO`) is strictly
increasing from `MergeCausal` alone (with `1 ≤ Es`): so `or_tok_mono`
replaces `MergeTiming.H_OR_SKEW` / `MergeStatic.S_OR` exactly as for the mux
(the `merge_ok` re-plumbing, a copy of `mux_ok_noskew`'s, is not written). -/
theorem merge_or_step {P : MergeRun} {Eo Es : Nat} (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es) (j : Nat) :
    orEdges (fun k => !P.sv k) P.XO P.YO j < orEdges (fun k => !P.sv k) P.XO P.YO (j + 1) := by
  have hρS : ∀ j, P.ρ j ≤ orEdges (fun k => !P.sv k) P.XO P.YO j := fun j => by
    unfold orEdges MergeRun.XO MergeRun.YO; split
    · exact P.Wxo.fst_ge _
    · exact P.Wyo.fst_ge _
  have hSZ : orEdges (fun k => !P.sv k) P.XO P.YO j ≤ P.Z j := by
    have := P.Lor.fst_ge (orEdges (fun k => !P.sv k) P.XO P.YO j)
    have := P.Dz.fst_ge (P.Lor.fst (orEdges (fun k => !P.sv k) P.XO P.YO j))
    unfold MergeRun.Z; omega
  have h1 := Cs.H_SRV j
  have h2 := Cs.H_OWN j
  have hx : P.ζ j ≤ P.XA j := by
    have := P.Wzx.fst_ge (P.ζ j); have := P.Lxa.fst_ge (P.cx j); have := P.Wxa.fst_ge (P.Lxa.fst (P.cx j))
    unfold MergeRun.XA MergeRun.cx MergeRun.ZA0 at *; omega
  have hy : P.ζ j ≤ P.YA j := by
    have := P.Wzy.fst_ge (P.ζ j); have := P.Lya.fst_ge (P.cy j); have := P.Wya.fst_ge (P.Lya.fst (P.cy j))
    unfold MergeRun.YA MergeRun.cy MergeRun.ZA1 at *; omega
  have := hρS (j + 1)
  split at h2 <;> omega

end Formal.Cells.OpsTimed
