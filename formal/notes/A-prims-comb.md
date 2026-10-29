# A-prims-comb: digital semantics of the combinational primitives (LUT6_2, MUXF7/F8, CARRY4, OUTMUX hops)

Probe PrimsComb, shard A, session 2026-10-29. North-star goal 1.

STATUS: in progress (started 2026-10-29; census next, then port the lost drafts
Wip/_snapA/Formal/Core/Prims/{Muxf,Xray}.lean into Formal/Core/Prims/).

## Plan
1. Census: which of LUT6_2 / MUXF7 / MUXF8 / CARRY4 the routed gcd_hw, collatz, ipow, xorshift use.
2. Xray.lean: prjxray-db bands (fast/slow corners, not rise/fall), quoted from the SDF.
3. Muxf.lean: MUXF7/F8 Kleene mux, monotone, X containment, hazard results, timed model.
4. Lut62.lean: LUT6_2 O5/O6 sharing one mux tree.
5. Carry.lean: CARRY4 MUXCY/XORCY chain.
6. GenCheck.lean: equality with shard C's Formal.Gen.Netlist primitive models, or mismatches.
