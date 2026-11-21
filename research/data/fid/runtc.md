# A narrow request pulse into a C-element (formal C19, 2026-11-16)

Formal's C19: its failures from "steer cones" are 20-41 ps pulses reaching a link controller's request pin while the
other request is already high; in its transport model the pulse then circulates in the controller's feedback loop. Asked:
what does research's GLS do with such a pulse? `cells/gls/fid/f3/tb_f3_runtc.v`: the bd_c2n state LUT exactly as in
tb_f3_meta (q = C(r1, ~r2), feedback through an ICBUF, loop = FB + 124 ps), r2 = 0 throughout (the request already
asserted), r1 high for P ps; 200 trials per cell; q's edges counted for 8 ns after the pulse, then its settled value.

Models: **fid** = the gate's model (GLS_FID: transport pins + the state-node resolver, cells/gls/fid_core.vh);
**fid, resolver off** = +META_OFF=1, pure transport (formal's semantics without its 20 ps filter); **default** = the
old inertial prims.v model. Cell = settled 0 / settled 1 / most edges in one trial (2 = the pulse passes out of q once
and the node stays 0; 3 = a runt, then a resolved rise to 1; more = oscillation). X = 0 everywhere.

Reading:
- In the gate's model a pulse of 1-40 ps (formal's 20-41 ps) into a C-element with its other input high **never
  oscillates and never sets the node**: 200 / 200 settle at 0 for every P up to TLOOP - WIN/2 - noise (P <= 40 at
  loop 224, P <= 200 at loop 424). The pulse itself still leaves q once (2 edges): the output LUT is transport, so a
  narrow pulse continues downstream. Wider pulses resolve to 0 or 1 by the noise law, once (3 edges), never X.
- With the resolver off (pure transport, formal's semantics) **every** pulse below the loop delay circulates for the
  whole 8 ns (38-73 edges): formal's C19 oscillation is reproduced exactly when our resolver is removed. Our resolver
  is an assumption too (TAU = WIN = 150 ps, unsourced; f3_model.md); neither model is calibrated on a LUT loop.
- The old default (inertial) model swallows pulses < ~150 ps, but on the 424 ps loop it oscillates for P = 150-300.
- What settles it is silicon: BOARD-QUEUE item 2 (H_RUNT, research/board/runt/) measures a C-element's response to
  short pulses. Until then: formal's C19 rows depend on the absence of a resolver, and our gate's passes on such pulses
  depend on its presence. Rule E at the steer is the check that keeps the pulse from forming at all (the condition
  settles before the request, so a glitch on it is masked by the steer); its known-bad builds are in
  research/data/selneg/README.md.
