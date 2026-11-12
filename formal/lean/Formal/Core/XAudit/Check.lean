import Formal.Core.XAudit.Design

/-!
# Formal.Core.XAudit.Check — a kernel cross-check of one `xaudit` verdict

The design and stimulus below are what `xaudit --emit-lean` printed for the
REAL yosys netlist `formal/tools/import/json/bd_c2.json` (shard C's import of
`cells/rtl/bd_ce.v`, yosys 0.62: the `bd_c2` LUT6 with IBUF/OBUF pads), the
stimulus `formal/tools-A/xaudit/designs/bd_c2_kcheck.stim.json` and the bands
`designs/kcheck.bands.json` (1 step = 50 ps; LUT [45,124] ps -> [1,3] steps,
every routed arc [100,300] ps -> [2,6] steps, pads [1,1] step).
Wires: 2 `a`, 3 `b`, 4 `rst` (ports), 5/6/9 pad outputs, 10..13 the routed
pins I0..I3 of `u`, 7 the LUT output `q` (storage node), 8 the `q` pad output.

The executable printed (`results/bd_c2_kcheck.txt`):

    STORAGE u/O (wire 7 '$iopadmap$q'): final 0, 0 flagged
      X [0, 450] ps: power-up, resolved at 500 ps
      X [1700, 1950] ps: transition 0 -> 1
      X [2200, 2950] ps: transition 1 -> 0

Here the kernel (`decide +kernel`: kernel evaluation, no `native_decide`, no
compiled code) recomputes the same function `audit` and checks the two
X-free windows and the values, and `noX_sound`/`audit_binary` turn them into
statements about every behaviour. Expected values are derived from the cell
(`bd_c2` = maj(a,b,q) under rst = 0), not pasted: q = 0 from reset until b
rises (a alone cannot set it), q = 1 once a and b are both 1.
-/

namespace Formal.Core.XAudit.Check

open Formal.Core K3
open Formal.Core.XAudit
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig)

def design : Design := ⟨13, [
    ⟨"$iopadmap$bd_c2.a/O", 1, 2, [2], 5, 1, 1⟩,
    ⟨"$iopadmap$bd_c2.b/O", 1, 2, [3], 6, 1, 1⟩,
    ⟨"$iopadmap$bd_c2.q/O", 1, 2, [7], 8, 1, 1⟩,
    ⟨"$iopadmap$bd_c2.rst/O", 1, 2, [4], 9, 1, 1⟩,
    ⟨"u/I0", 1, 2, [5], 10, 2, 6⟩,
    ⟨"u/I1", 1, 2, [6], 11, 2, 6⟩,
    ⟨"u/I2", 1, 2, [7], 12, 2, 6⟩,
    ⟨"u/I3", 1, 2, [9], 13, 2, 6⟩,
    ⟨"u/O", 6, 65303191044489448, [10, 11, 12, 13, 0, 0], 7, 1, 3⟩]⟩

def stim : Stim := ⟨[(0, .zero), (1, .one), (2, .zero), (3, .zero), (4, .one)],
  [(10, 4, .zero), (20, 2, .one), (30, 3, .one), (40, 2, .zero), (50, 3, .zero)]⟩

def horizon : Nat := 60

/-- The INIT is `bd_c2`'s `64'h00E8_00E8_00E8_00E8` (bd_ce.v). -/
theorem init_is_bd_c2 : (65303191044489448 : Nat) = 0x00E800E800E800E8 := by decide

theorem design_wf : design.WF := by decide +kernel

/-- The kernel's verdicts: `q` (wire 7) has no X on [10, 33] (500..1650 ps)
and on [40, 43] (2000..2150 ps); it is 0 at step 20 and 1 at step 40. -/
theorem verdicts :
    noX (audit design stim.u horizon) horizon 7 10 33 = true ∧
    noX (audit design stim.u horizon) horizon 7 40 43 = true ∧
    valAt (audit design stim.u horizon) horizon 20 7 = zero ∧
    valAt (audit design stim.u horizon) horizon 40 7 = one := by
  decide +kernel

/-- The X-window on [34, 38] is real output of the audit too (not an X-free
claim): the kernel agrees that step 36 is `X`. -/
theorem q_X_at_36 : valAt (audit design stim.u horizon) horizon 36 7 = X := by
  decide +kernel

/-- **For every behaviour** of the parsed `bd_c2` netlist (every pad, route and
LUT delay inside its band as monotone warps, any power-up state) driven by the
stimulus: `q` is 0 at every step of [10, 33] and 1 at every step of [40, 43]. -/
theorem q_concrete (x : Fin design.n → Sig) (hsat : Circuit.Sat (toCircuit (build design)) x)
    (hin : InputsCovered design stim.u x) :
    (∀ s, 10 ≤ s → s ≤ 33 → x 7 s = false) ∧ (∀ s, 40 ≤ s → s ≤ 43 → x 7 s = true) := by
  obtain ⟨h1, h2, -, -⟩ := verdicts
  refine ⟨fun s a b => ?_, fun s a b => ?_⟩
  · have e := noX_sound design design_wf stim.u horizon 7 10 33 (by decide) h1 x hsat hin s a b
    -- the printed value there is 0: every step of the window, by the kernel
    have hv : ∀ s, 10 ≤ s → s ≤ 33 → valAt (audit design stim.u horizon) horizon s 7 = zero := by
      have : (List.range' 10 24).all
          (fun s => valAt (audit design stim.u horizon) horizon s 7 == zero) = true := by
        decide +kernel
      simp only [List.all_eq_true, List.mem_range'_1, beq_iff_eq] at this
      exact fun s a b => this s ⟨a, by omega⟩
    rw [e]
    show (valAt (audit design stim.u horizon) horizon s 7).pick = false
    rw [hv s a b]; rfl
  · have e := noX_sound design design_wf stim.u horizon 7 40 43 (by decide) h2 x hsat hin s a b
    have hv : ∀ s, 40 ≤ s → s ≤ 43 → valAt (audit design stim.u horizon) horizon s 7 = one := by
      have : (List.range' 40 4).all
          (fun s => valAt (audit design stim.u horizon) horizon s 7 == one) = true := by
        decide +kernel
      simp only [List.all_eq_true, List.mem_range'_1, beq_iff_eq] at this
      exact fun s a b => this s ⟨a, by omega⟩
    rw [e]
    show (valAt (audit design stim.u horizon) horizon s 7).pick = true
    rw [hv s a b]; rfl

end Formal.Core.XAudit.Check
