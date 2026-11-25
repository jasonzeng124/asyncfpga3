import Formal.Timing.WinArray

/-!
# The verdict `tcheck` prints, and why a PASS means something (probe C-10e)

One obligation = one race netlist (10a's `Netlist`, built by the untrusted
front end `extract.py` from a routed design and per-arc delay intervals), a
request node, the data nodes, and a setup margin.  The executable computes
exactly `verdict` below on the parsed instance; `verdict_sound` is 10a's
`check_sound` (through 10d's `checkArr_sound`) restated for it.

What the theorem covers: the arithmetic of the windows and the check, for every
run of 10a's semantics (`Run`: H_LAUNCH, H_BOUNDED_DELAY per arc, H_QUIESCENT,
H_LOCAL, H_ZERO_DELAY_FN).  What it does not cover (stated in the notes): that
the netlist the front end emitted is the right one for the routed circuit, the
parser, and the Lean compiler (`lake exe` runs compiled code, not the kernel).
-/

namespace Tcheck
open Formal.Timing Formal.Net

/-- One obligation instance. -/
structure Inst where
  net : Netlist
  req : Nat
  data : List Nat
  setup : Nat

/-- What `tcheck` prints as PASS: the netlist is well formed (a DAG in index
order, `lo ≤ hi`), decided at run time, and 10d's one-pass check holds. -/
def verdict (i : Inst) : Bool := decide i.net.WF && checkArr i.net i.req i.data i.setup

/-- The margin `tcheck` prints: earliest request minus latest data minus setup. -/
def margin (i : Inst) : Option Int := slackArr i.net i.req i.data i.setup

/-- **Soundness of a printed PASS.** In every run of the instance's netlist, every
data change precedes every request change by at least `setup`. -/
theorem verdict_sound (i : Inst) (h : verdict i = true) {sig : Nat → Trace}
    (r : Run i.net sig) : ∀ d ∈ i.data, ∀ s t, changes (sig d) s → changes (sig i.req) t →
      s + i.setup ≤ t := by
  simp only [verdict, Bool.and_eq_true, decide_eq_true_eq] at h
  exact checkArr_sound h.1 h.2 r

/-- The same for the stricter one-delay-per-arc reading (`FixedRun`). -/
theorem verdict_sound_fixed (i : Inst) (h : verdict i = true) {sig : Nat → Trace}
    (r : FixedRun i.net sig) : ∀ d ∈ i.data, ∀ s t, changes (sig d) s → changes (sig i.req) t →
      s + i.setup ≤ t :=
  verdict_sound i h r.toRun

/-- The printed margin is 10a's `slack` (for well-formed netlists). -/
theorem margin_eq (i : Inst) (hwf : i.net.WF) : margin i = slack i.net i.req i.data i.setup :=
  slackArr_eq i.net hwf i.req i.data i.setup

/-- The printed windows are 10a's `win` (for well-formed netlists), hence sound
(`changes_in_window`) and attained (`win_exact`). -/
theorem window_eq (i : Inst) (hwf : i.net.WF) (v : Nat) : winArr i.net v = win i.net v :=
  winArr_eq i.net hwf v

end Tcheck
