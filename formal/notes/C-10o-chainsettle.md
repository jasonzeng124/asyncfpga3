# C-10o: H_CHAIN_SETTLED, exactly, and on the routes (track 10)

Shard C, probe 10o, 2026-10-29. Core Lean only, no sorry/axiom/native_decide.
(Draft in progress; results below are filled as they come.)

## Files

| file | contents |
|---|---|
| `Formal/Timing/ChainSettle.lean` | exact forced-low calculus for single-source AND/OR networks under per-arc BoundedDelay (Semantics' model): `pin_low`, `ext_bd`, `cert_sound`, `Lc`, `low_iff`, `Settled`, `settled_iff`, `runt_of_gap`, OR duals, interval lemmas |
| `Formal/Timing/ChainSettleChain.lean` | `pulse`, N = 2 closed form `chain2_settled_iff`, `runt_example`, `settled_example` |
| `formal/tools/chainck/` | row generator (exact rows + tcheck `Fu` rows for bd_link `uack`), run script |
