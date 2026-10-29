# A-xinert: an inertial option for xaudit (probe XInert, shard A)

STATUS: in progress (09:05 UTC). Code written (Parse/Main additive, SoundInertial.lean); checking; runs pending.

## Plan
1. Band format: optional `inertial` object (global ρ per gate kind, per cell, per arc; the value
   `"delay"` = Verilog default reject = the delay). CLI `--inertial check|widen` (default: off,
   old behaviour byte-identical). check: refuse unless ρ ≤ (hi+1-lo)·u for every gate.
   widen: hi := max(⌈H/u⌉, lo - 1 + ⌈ρ/u⌉) (minimal hi meeting the side condition).
2. Lean: `Formal/Core/XAudit/SoundInertial.lean`: the parser's new step mapping meets the
   side conditions of `XSimChanReal.boundedInertial_chanCells`; per-gate ps-level hypothesis
   (transport or inertial with ρ' ≤ ρ in the ps band) ⇒ `SoundPhys.SatPhys` ⇒ verdicts.
3. Reruns pipe3 / ring3 / gcd_hw (seed d) with ρ = 0, ρ = delay, ρ = 15, 50 ps.
4. Correct A-xaudit.md's fidelity row.
