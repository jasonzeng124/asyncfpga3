import Formal.Net.CapstoneLiveWit
import Formal.Net.CapstoneLiveWitCex

/-! C-8z2 negative controls: each checker must REJECT a mutated input (each claim below proves
that the checker returns `false`). -/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd Formal.Net.CapNet.Wit

/-- Fork op 0's first output (channel 3) rises one tick late: still a legal `Cell` move, but
the step property (H_BOUNDED_DELAY' 1) fails. -/
def cdM (c : Fin NC) : CD := if c.val = 3 then ⟨[2, 100], [2, 101], 0, [], []⟩ else cdW c

example : opStep cdM 0 = false := by decide +kernel
example : opStep cdW 0 = true := by decide +kernel

/-- `start`'s own LUT does NOT have the step property on the witness run (it is excited to
offer again after its token closes, and never does): the exemption is used. -/
example : opStep cdW (prodOf start) = false := by decide +kernel

/-- A certificate entry naming a gate that is not excited at that tick is rejected. -/
example : ndChk cdW 0 ((187, 0, false) :: certL.drop 1) = false := by decide +kernel
/-- A certificate naming `start`'s own LUT is rejected. -/
example : ndOne cdW 0 (189, 0, true) = false := by decide +kernel
/-- The counterexample run fails the H_NO_DEADLOCK' certificate check at its last tick: no
gate but start's LUT is excited there (every entry of operators 0..366 is rejected). -/
example : (List.range NO).all (fun p => (List.range 8).all (fun j =>
    !ndOne cdX 130 (p, j, true) && !ndOne cdX 130 (p, j, false))) = true := by decide +kernel

end Formal.Net.CapNet.LiveWit
