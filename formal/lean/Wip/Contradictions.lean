import Formal.Core.XAudit.Events2Strict
import Formal.Core.EnvFast.DataHyp

/-!
# Wip/Contradictions — open statements left by the X1/X2/X6 resolution (shard A)

NOT BUILT, NOT CLAIMED. Every `sorry` below is an open statement. Notes:
`formal/notes/A-contradictions.md`.

1. `xevents2_pin` (X2): the executable has one band per LUT, so the strict
   verdict covers a feedback-pin skew of at most one step (`PinSkew 1`). The
   real gate is `BackPin` on per-pin arcs (prjxray gives I0..I5 → O
   separately). Shape of the theorem a per-pin `xevents2` would print:
   `Recog2` with per-pin bands + `BackPin` ⇒ every `Circuit.Sat` behaviour of
   a netlist whose LUTs are per-pin FIFO is a `BehP`. It needs a per-pin
   `toCircuit` (the current one has one channel per LUT) — about 1 day.

2. `soundD_refines` (X1): the timed reading of `SoundD` (`InWin`, the
   hypothesis H_SOUNDD_TRACE of `DataHyp.window_data`). Env has no timed
   semantics; the statement needs one (a timed run of a `Model` whose element
   delays are `Win` channels, with H_SETTLE as a delay inequality). Shape
   only; the `Model`-to-trace map `runOf` does not exist.
-/

namespace Formal.Wip.Contradictions

open Formal.Core.XAudit.Events2 Formal.Core.XAudit.Events2Strict

/-- (1) Per-pin xevents2, schematic: a per-pin behaviour of a recognised
netlist is safe under `BackPin`. The proved part is `BehP.safe`; the open
part is producing the `BehP` from the netlist. -/
theorem xevents2_pin {N : Nat} {net : CNet N} {b : Bands net} {pb : PinBands net}
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)}
    (hB : BackPin b pb back)
    (hbeh : True /- OPEN: every Circuit.Sat behaviour of the per-pin netlist yields a BehP -/) :
    ∀ x : BehP net b pb, ∀ t j, x.c j t = Formal.Core.XAudit.Events.ph (net.v j) (x.M t j) := by
  intro x; exact x.safe hB  -- the proved half; the netlist half is `hbeh`, open

/-- (2) Timed refinement of `SoundD` (shape only). -/
theorem soundD_refines : True := by
  sorry -- OPEN: needs a timed semantics of `Env.Model`

end Formal.Wip.Contradictions
