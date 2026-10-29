# A-prims-dsp: digital semantics of DSP48E1 as ipow uses it

Probe PrimsDSP, shard A, session 2026-10-29. North-star goal 1 ("DSP48E1 ... if a design uses them").

STATUS: in progress (census done; Lean being written in Formal/Core/Prims/Dsp.lean).

## Plan
1. Census: exactly which DSP48E1 configuration ipow's routed design uses (from a routed JSON).
2. `Formal/Core/Prims/Dsp.lean` (Lean core only): the configuration as data, the UG479 function of
   that mode, the 3-DSP cascade = C's 32-bit multiply (algebra), bit-level Kleene X models with
   soundness, prjxray-db DSP arcs (fast/slow corners), a lumped bounded-delay channel, the
   bundled-data theorem (sample after the settle bound = product), glitch/tightness witnesses.
3. This note: problem statements, what is NOT modelled.
