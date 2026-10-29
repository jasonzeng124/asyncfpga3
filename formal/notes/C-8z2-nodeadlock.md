# C-8z2: H_NO_DEADLOCK' is false as stated (counterexample); repaired theorem; joint witnesses

Shard C, probe 8z2, 2026-10-29. Core Lean only (no Mathlib), no sorry/axiom/native_decide.

**Status: PARTIAL (draft; numbers filled in when the kernel checks land).**

## Verdict

1. **8z's open obligation H_NO_DEADLOCK' is not a network property: it is false on a run that
   meets all six other hypotheses of `gcd_hw_live_final`** (`nd_counterexample`, kernel-checked).
   - The run: the unit-delay run of the concrete 465-channel network on a = 12, b = 18 in which
     `start`'s `bd_src` LUT, after its one offer, never releases its request.
   - 8z exempted that LUT from every delay bound once it has offered (H_BOUNDED_DELAY' skips it;
     H_START_ENV only covers the time before the first offer). So holding the request for ever
     is allowed.
   - Then the start token is never released, the return-to-zero wave that out0's close needs
     never starts, the network comes to rest after 126 ticks, and out0's acknowledge never falls.
   - So no proof of H_NO_DEADLOCK' from the network structure can exist. It hid an environment
     assumption: "the start token is released".
2. **Repair: `gcd_hw_live_final2`** (`CapstoneLiveNd2`). Same conclusion, with
   - **H_START_REL `H`** (new, environment): while `start`'s request and acknowledge are both
     high on a window of `H + 1` ticks, the request falls in it;
   - **H_NO_DEADLOCK''** in place of H_NO_DEADLOCK': quiescence also requires that `start`'s LUT
     is not excited to release. It is weaker than H_NO_DEADLOCK' (`nd2_of_nd'`), and the
     counterexample run violates H_START_REL (`x_not_rel`).
   - H_NO_DEADLOCK'' is still **OPEN** for general runs.
3. **Non-vacuity: one run satisfies ALL hypotheses of both theorems together**
   (`gcd_hw_live_joint_witness`, `gcd_hw_live2_joint_witness`, kernel-checked).
   - a = 12, b = 18, `H = 1`, free-running a/b sources, `start` offered once and released.
   - It meets H_CELLS (internal traces explicit), H_BUNDLE, H_START_ONCE, H_BOUNDED_DELAY' 1,
     H_START_ENV 1, H_START_REL 1, H_ARB_UNCONTESTED_BOUNDED 1 and H_NO_DEADLOCK' (hence
     H_NO_DEADLOCK'').
   - Its out0 token closes at tick 473 carrying 6 = gcd 12 18. Applying both theorems to it
     gives the same value (`gcd_hw_live_witness_consistent`, `gcd_hw_live2_witness_consistent`).
4. **H_NO_DEADLOCK'' in general: evidence only** (random bounded-delay runs, see below).
