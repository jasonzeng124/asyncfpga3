import Formal.Timing.Checker

/-!
# `win_exact` is exact only when the cell functions are free (audit answer, probe C-aud)

Audit C.md rows 1 and 4 (REPORT: "interval STA checker sound and per-node exact",
OVERSTATED). `win_early_attained` / `win_late_attained` (and through them `win_exact`
and `check_exact_disjoint`) build the attaining run with node functions the WITNESS
chooses (OR in `earlyRun`, AND-of-reachable-inputs in `lateRun`). So the windows are
the exact hull over the class of ALL local cell functions, i.e. given only the arc
topology and delays. For a netlist whose cell functions are fixed (real LUT INITs), the
soundness half (`changes_in_window`, `check_sound`) still holds, but the window is only
an UPPER bound on when the node can switch.

Counterexample (the auditor's `xor_never_switches`, `audit/lean/C/AuditTiming.lean`):
two parallel `[5,5]` arcs `0 → 1`, node 1 an XOR of its two pins. `win` reports
`(5, 5)`; in every fixed-delay run with that function node 1 never switches; a fixed
run with that function exists (so the statement is not vacuous); and with the OR
function the window IS attained (`win_exact`), so the gap is due to the function.

Assumed: Semantics.lean's `FixedRun` (one delay per arc, H_LAUNCH, H_LOCAL,
H_ZERO_DELAY_FN). Not covered: which real LUT functions attain their windows; the
per-event `Run` semantics (where a pulse could pass) -- the counterexample is stated for
fixed delays, the physically intended reading.
-/

namespace Formal.Timing.FixedFn
open Formal.Net Formal.Timing

/-- Two parallel equal-delay arcs into node 1 (a reconvergent fanout in one hop). -/
def xorNet : Netlist where arcs := [⟨0, 1, 5, 5⟩, ⟨0, 1, 5, 5⟩]

/-- The fixed cell function of node 1: XOR of its two pins. -/
def xorFn : (Nat → Bool) → Bool := fun x => x 0 != x 1

theorem xorNet_wf : xorNet.WF := by decide

theorem xorNet_win : win xorNet 1 = some (5, 5) := by decide

/-- **Fixed functions: the window is not attained.** In every fixed-delay run whose
node 1 computes XOR, node 1 never switches, although `win` says `(5, 5)`. -/
theorem xor_never_switches {sig : Nat → Trace} (r : FixedRun xorNet sig)
    (hg : r.g 1 = xorFn) : ∀ t, ¬ changes (sig 1) t := by
  have h0 : r.d 0 = 5 := by have := r.range 0 _ rfl; simp only at this; omega
  have h1 : r.d 1 = 5 := by have := r.range 1 _ rfl; simp only at this; omega
  have hc : ∀ t, sig 1 t = false := by
    intro t
    rw [r.node 1 (by decide) t, hg]
    simp [xorFn, fixedPin, xorNet, h0, h1]
  intro t h; exact h ((hc t).trans (hc (t + 1)).symm)

/-- A launch step at time 0. -/
def stepSig : Trace := fun t => decide (1 ≤ t)

def xorSig : Nat → Trace
  | 0 => stepSig
  | _ => fun _ => false

/-- Non-vacuity: a fixed-delay run of `xorNet` with node 1 = XOR exists, and the launch
really switches in it. -/
def xorRun : FixedRun xorNet xorSig where
  d := fun _ => 5
  g := fun v => match v with
    | 1 => xorFn
    | _ => fun _ => false
  launch := by
    intro t ht
    apply Classical.byContradiction; intro h0; apply ht
    simp only [xorSig, stepSig, decide_eq_decide]; omega
  range := by
    intro k a hk
    match k, hk with
    | 0, hk => simp [xorNet] at hk; subst hk; decide
    | 1, hk => simp [xorNet] at hk; subst hk; decide
    | k + 2, hk => simp [xorNet] at hk
  local_ := by
    intro v x y hxy
    match v with
    | 1 => simp only [xorFn]; rw [hxy 0 _ rfl rfl, hxy 1 _ rfl rfl]
    | 0 => rfl
    | v + 2 => rfl
  node := by
    intro v hv t
    match v with
    | 0 => exact absurd rfl hv
    | 1 => simp [xorSig, xorFn, fixedPin, xorNet]
    | v + 2 => rfl

theorem xorRun_g : xorRun.g 1 = xorFn := rfl

theorem xor_launch_switches : changes (xorSig 0) 0 := by
  unfold changes xorSig stepSig; decide

/-- **`win_exact` with fixed cell functions is only an upper bound.** There is a
well-formed netlist and a fixed function for node 1 such that `win` reports `(5, 5)`,
fixed-delay runs with that function exist, and in none of them does node 1 ever switch
(so neither end of the window is attained); yet with the witness-chosen function the
window is attained (`win_exact`). -/
theorem win_exact_needs_free_fn :
    ∃ (net : Netlist) (f : (Nat → Bool) → Bool),
      net.WF ∧ win net 1 = some (5, 5) ∧
      (∃ sig, ∃ r : FixedRun net sig, r.g 1 = f) ∧
      (∀ sig (r : FixedRun net sig), r.g 1 = f → ∀ t, ¬ changes (sig 1) t) ∧
      (∃ sig, Nonempty (FixedRun net sig) ∧ changes (sig 1) 5) :=
  ⟨xorNet, xorFn, xorNet_wf, xorNet_win, ⟨xorSig, xorRun, xorRun_g⟩,
    fun _ r hg => xor_never_switches r hg,
    ((win_exact xorNet_wf 1).2 5 5 xorNet_win).2.1⟩

end Formal.Timing.FixedFn
