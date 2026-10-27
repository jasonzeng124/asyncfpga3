# C-10h: tcheck phase 3. Closing the trust gaps (in progress)

Shard C, probe 10h, 2026-10-27. Notes kept current while working.

## Status
- (b) H_EXTRACT_MIN: Lean side DONE. `Formal/Timing/Unroll.lean` (`pot_sound`,
  `potOK_sound`) and `formal/tools/tcheck/Tcheck/Cert.lean` (`cverdict_sound`) compile,
  no sorry/axiom/native_decide; axiom audit = propext, Classical.choice, Quot.sound.
  tcheck parses cert instances; `test/toycert.tc` self-test (pass/fail/CERTBAD) passes.
- Python front end for cert instances: in progress.
- (a) fallback arcs: not started.
- (c) reruns: not started.
