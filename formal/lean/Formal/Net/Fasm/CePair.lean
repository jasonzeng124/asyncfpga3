import Formal.Net.Fasm.CePairS1
import Formal.Net.Fasm.CePairS2
import Formal.Net.Fasm.CePairS3
import Formal.Net.Fasm.CePairS4

/-!
# Track 11b: the ROUTED bd_c2 -> bd_c2n pair, read from the FASM, is the logical pair

Design: `formal/tools/fasm2lean/ce_pair.v` (`q1 = bd_c2(a, b, rst)`,
`q2 = bd_c2n(q1, c, rst)`, cells verbatim from `cells/rtl/bd_ce.v`), routed by
`formal/tools/fasm2lean/route.sh SEED` (toolchain.sh ok, nextpnr sha256
9c732bc6303458df, `--freq 100 --ignore-loops --seed SEED`), seeds 1..4. Each
seed places the two LUTs on different sites with a different physical pin
permutation (see the generated `CePairS<n>.lean`).

The Lean data in `CePairS<n>` is extracted from the FASM alone (plus
prjxray-db); nextpnr's routed JSON, its SDF and the yosys netlist are not
inputs. The logical side is shard B's `exc INIT a b q rst` with the INITs
copied verbatim from the RTL (`Formal.Cells.CElemTiming`).

## Proved here (all by `decide` / term proofs; no unproved goals, no added axioms, no native code)

* `next_state_s1` .. `next_state_s4`: for every value of the input ports
  and of the two outputs, the LUT the BITSTREAM wires to port `q1` is driven
  to `bd_c2(a, b, q1, rst)` and the one wired to `q2` to `bd_c2n(q1, c, q2, rst)`.
  The statement only mentions port names, so it is the same for every seed;
  LUT order, sites and pin order come from the FASM.
* `perm_matters_s1`: the negative control. The logical INIT on the physical
  pins (i.e. ignoring the placer's permutation, the family of the August
  lut-pinmap bug) is NOT the cell: the check can fail.
* `q1_loop_s1`: from the physical gate relations (`Behaves`) of seed 1, the
  routed q1 LUT and its routed feedback pin satisfy shard B's `Loop INIT_c2`,
  so `q1_follow_hold_s1` (B's `c2_follow_hold`) holds for the ROUTED cell, with
  the feedback-wire bounds now those of the real route (`dw 1 0`).
* `q1_follow_hold_s1_ps`: the same with the numbers: LUT `[45, 124]` ps
  (prjxray LUT6 arc), feedback `[213, 709]` ps (the generated route bound).
* `q1_kleene_s1`: the same equality in shard B's Kleene semantics `lutK`
  (X inputs included): permuting pins does not change the closure semantics.
-/

namespace Formal.Net.Fasm.CePair
open Formal.Net.Fasm Formal.Cells Formal.Cells.CElemTiming

/-- Name -> value environment over the design's ports. -/
def env (a b c r q1 q2 : Bool) : List (String × Bool) :=
  [("a", a), ("b", b), ("c", c), ("rst", r), ("q1", q1), ("q2", q2)]

/-- The seed-independent claim about a physical net `N` with input ports `ps`. -/
def Spec (N : PNet) (ps : List String) : Prop :=
  ∀ a b c r q1 q2 : Bool,
    N.outNext "q1" (portVals ps (env a b c r q1 q2)) (outState N (env a b c r q1 q2))
      = exc INIT_c2 a b q1 r ∧
    N.outNext "q2" (portVals ps (env a b c r q1 q2)) (outState N (env a b c r q1 q2))
      = exc INIT_c2n q1 c q2 r

instance (N : PNet) (ps : List String) : Decidable (Spec N ps) := by
  unfold Spec; exact inferInstance

theorem next_state_s1 : Spec CePairS1.net CePairS1.ports := by decide
theorem next_state_s2 : Spec CePairS2.net CePairS2.ports := by decide
theorem next_state_s3 : Spec CePairS3.net CePairS3.ports := by decide
theorem next_state_s4 : Spec CePairS4.net CePairS4.ports := by decide

/-- The two cells really are a C-element and a C(a,~b) (B's lemmas, restated). -/
theorem next_state_s1_bool (a b c r q1 q2 : Bool) :
    CePairS1.net.outNext "q1" (portVals CePairS1.ports (env a b c r q1 q2))
        (outState CePairS1.net (env a b c r q1 q2))
      = (!r && ((a && b) || (a && q1) || (b && q1))) := by
  rw [(next_state_s1 a b c r q1 q2).1, c2_eq]

/-! ## Negative controls: the check can fail -/

/-- The physical LUT of seed 1 with the LOGICAL INIT (no pin re-encoding). -/
def s1_unpermuted : PNet :=
  ⟨[{ CePairS1.lut0 with init := INIT_c2n }, { CePairS1.lut1 with init := INIT_c2 }],
   CePairS1.net.outs⟩

theorem perm_matters_s1 : ¬ Spec s1_unpermuted CePairS1.ports := by decide

/-- Seed 1 with the routes of physical pins B2 (rst) and B3 (b) of the q1 LUT
swapped: a one-pip-pair routing defect the netlist would never show. -/
def s1_swapped : PNet :=
  ⟨[CePairS1.lut0, { CePairS1.lut1 with pins := [.lut 1 .o6, .port 1, .port 3, .port 0, .const false, .const false] }],
   CePairS1.net.outs⟩

theorem swap_caught_s1 : ¬ Spec s1_swapped CePairS1.ports := by decide

/-! ## Bridge to shard B's timing theorems, through the physical gate relations -/

/-- The q1 LUT of seed 1 on its physical pins `[B1..B6] = [q1 fb, rst, b, a, 0, 0]`
is `exc INIT_c2 a b q rst`. -/
theorem s1_lut1_fn (x0 x1 x2 x3 : Bool) :
    CePairS1.lut1.fn .o6 [x0, x1, x2, x3, false, false] = exc INIT_c2 x3 x2 x0 x1 := by
  revert x0 x1 x2 x3; decide

theorem s1_lut1_pins : CePairS1.lut1.pins =
    [.lut 1 .o6, .port 3, .port 1, .port 0, .const false, .const false] := rfl

/-- **The routed q1 cell is shard B's `Loop`.** Given the physical net's gate
relations (`Behaves`, every field a named hypothesis) and B's positivity
hypothesis on the loop, the q1 LUT with its ROUTED feedback pin B1 satisfies
`Loop INIT_c2` with `a, b, rst` = the traces at physical pins B4, B3, B2. -/
theorem q1_loop_s1 {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
    {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}
    (h : Behaves CePairS1.net ins out pin dl dw)
    (H_LOOP_POS : 0 < (dl 1).1 + (dw 1 0).1) :
    Loop INIT_c2 (pin 1 3) (pin 1 2) (pin 1 1) (out 1 .o6) (pin 1 0)
      (dl 1).1 (dl 1).2 (dw 1 0).1 (dw 1 0).2 where
  H_LUT := by
    have hl := h.H_LUT 1 CePairS1.lut1 .o6 rfl
    have h4 := h.H_TIE 1 CePairS1.lut1 4 false rfl rfl
    have h5 := h.H_TIE 1 CePairS1.lut1 5 false rfl rfl
    have e : (fun t => CePairS1.lut1.fn .o6 ((List.range 6).map (fun k => pin 1 k t)))
        = (fun t => exc INIT_c2 (pin 1 3 t) (pin 1 2 t) (pin 1 0 t) (pin 1 1 t)) := by
      funext t
      show CePairS1.lut1.fn .o6 [pin 1 0 t, pin 1 1 t, pin 1 2 t, pin 1 3 t, pin 1 4 t, pin 1 5 t] = _
      rw [h4 t, h5 t, s1_lut1_fn]
    rw [e] at hl; exact hl
  H_FB := h.H_ROUTE 1 CePairS1.lut1 0 (.lut 1 .o6) rfl rfl (by intro v hv; cases hv)
  H_LOOP_POS := H_LOOP_POS

/-- B's follow-and-hold theorem, for the cell as the bitstream wires it. -/
theorem q1_follow_hold_s1 {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
    {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}
    (h : Behaves CePairS1.net ins out pin dl dw)
    (H_LOOP_POS : 0 < (dl 1).1 + (dw 1 0).1)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + ((dl 1).2 + (dw 1 0).2) →
      pin 1 3 s = v ∧ pin 1 2 s = v ∧ pin 1 1 s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → pin 1 1 s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → pin 1 3 s = v ∨ pin 1 2 s = v) :
    ∀ t, t0 + (dl 1).2 ≤ t → t ≤ t2 + (dl 1).1 → out 1 .o6 t = v :=
  (c2_follow_hold (q1_loop_s1 h H_LOOP_POS) v t0 t2 H_PULSE H_NORST H_NOT_BOTH).1

/-- The feedback route of the seed-1 q1 cell, as the generator computed it from
the bits + prjxray-db: B1 <- CLBLM_IMUX15 <- LOGIC_OUTS21 <- CLBLM_M_BMUX. -/
theorem s1_fb_delay : CePairS1.pinDelay[1]![0]! = (213, 709) := rfl

/-- **With the numbers.** LUT core `I -> O6` in `[45, 124]` ps (prjxray-db
`timings/CLBLM_R.sdf`, LUT6 fast_min / slow_max; hypothesis `H_DL`) and the
feedback route in the generated `[213, 709]` ps (`H_DW`, candidate bound, see
`pinDelay`): `a = b = v` (and `rst = 0`) at the physical pins for 833 ps sets
the ROUTED q1 cell to `v` from 124 ps on, and it holds while `a, b` are not
both `!v`. -/
theorem q1_follow_hold_s1_ps {ins : Nat → Trace} {out : Nat → LOut → Trace} {pin : Nat → Nat → Trace}
    {dl : Nat → Nat × Nat} {dw : Nat → Nat → Nat × Nat}
    (h : Behaves CePairS1.net ins out pin dl dw)
    (H_DL : dl 1 = (45, 124)) (H_DW : dw 1 0 = CePairS1.pinDelay[1]![0]!)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + 833 → pin 1 3 s = v ∧ pin 1 2 s = v ∧ pin 1 1 s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → pin 1 1 s = false)
    (H_NOT_BOTH : ∀ s, t0 ≤ s → s ≤ t2 → pin 1 3 s = v ∨ pin 1 2 s = v) :
    ∀ t, t0 + 124 ≤ t → t ≤ t2 + 45 → out 1 .o6 t = v := by
  rw [s1_fb_delay] at H_DW
  have hp : 0 < (dl 1).1 + (dw 1 0).1 := by rw [H_DL, H_DW]; decide
  have := q1_follow_hold_s1 h hp v t0 t2 (by rw [H_DL, H_DW]; exact H_PULSE) H_NORST H_NOT_BOTH
  rw [H_DL] at this; exact this

/-! ## Kleene (H_KLEENE_LUT, shard B) -/

/-- With X allowed on every live pin, the physical q1 LUT and the logical
`bd_c2` LUT give the same Kleene value (81 cases). -/
theorem q1_kleene_s1 (x0 x1 x2 x3 : K3) :
    lutK CePairS1.lut1.init [x0, x1, x2, x3, .f, .f] = lutK INIT_c2 [x3, x2, x0, x1, .f, .f] := by
  cases x0 <;> cases x1 <;> cases x2 <;> cases x3 <;> decide

end Formal.Net.Fasm.CePair
