# A-e8arb (probe E8Arb, shard A): H_ARB (HARB7) from "uncontested" + B's cell conditions

STATUS (2026-10-29, start): in progress. Nothing claimed yet.

Plan
1. Read HARB7's virtual core (Events7Beh `ND7`, events4/model.py vctl/arb:g/arb:R0) and the
   real bd_arbiter INITs (ustate FFF0_FFB2_ACAC_ACAC, ugrant 0C0C_0C0C_A0A0_A0A0).
2. Find B's race window W (ArbBinary / ArbCorners / OnGcdArb*, cell_constraints.json) and C's
   gcd_hw_arbiters_uncontended' (Formal/Net, read-only).
3. Define `Uncontested` on A's per-pin trace model (SatPin warps) for one arbiter.
4. Lean (Formal/Core/XAudit/Events8Arb.lean): an uncontested real bd_arbiter under the per-pin
   model is a behaviour of the virtual core (ND7 equations of ctl / grants / R0).
5. Discharge route for gcd_hw (C map / A certificate / counterexample), and the design_verdict8
   variant with H_ARB replaced.
