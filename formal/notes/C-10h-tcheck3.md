# C-10h: tcheck phase 3. Closing the trust gaps (in progress)

Shard C, probe 10h, 2026-10-27. Notes kept current while working.

## Status
- (b) H_EXTRACT_MIN: DONE. `Formal/Timing/Unroll.lean` (`pin_cause`, `pot_sound`,
  `potOK_sound`) and `formal/tools/tcheck/Tcheck/Cert.lean` (`lateOK_eq`, `cverdict_sound`)
  compile, no sorry/axiom/native_decide; axiom audit = propext, Classical.choice, Quot.sound.
  tcheck parses cert instances; `test/toycert.tc` self-test (pass / fail / CERTBAD) passes.
  certs.py emits Hc, Fc, Rc. Seed d first run: sdf rows identical to the 10g chains;
  293 of 948 prjxray H variant-rows had a SHORTER disturbance than 10g's SDF-chosen chain
  (H_EXTRACT_MIN was violated, by up to 942 ps), no verdict flipped.
- (a) fallback: CARRY4 cell arcs, CARRY4 S/DI site hops, F7/F8 select nets (AX/CX/BX),
  driver-side site hops (a5lut->amux etc., previously omitted = optimistic) added.
  LV/LVB long lines: diagnosed, not fixed.
- (c) four-seed rerun (run4.sh): running.
- A/F sdf-margin traces: F seed 2 uselect1 explained (H_CONTROLLING side-tap bound vs
  tighten's min(ripple, side): tighten t_flush 1617, tcheck 1758, t_reuse equal 5923).
  A: guard-pairing hypothesis being checked (traceA.py).
