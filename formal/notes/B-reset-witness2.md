# B-reset-witness2: a moving, varied-delay witness for gcd_hw's reset theorems

Probe Bwit (shard B), 2026-10-29. It answers self-audit 4 (`B-self-audit4.md`,
`SelfAuditB7.wv_frozen`). That audit found two gaps:
- `ResetCapstoneWit.nonvac_net2` (D = 40, W = 1) is frozen: power-up is the reset state and
  every gate holds until E.
- Bsa3's moving witnesses have D = W = 0.

So no reset witness had both moving state and nonzero delays. The run here has both.

No board, no route. `gNet` is Rst2's RTL-level control netlist (3322 nodes, real INITs).
Every time is a model step.

## Files and check

- `formal/lean/Formal/Cells/ResetWitness2Data.lean`: generated data. It holds `P0`, the
  power-up bitmask, and `lateL`, the wave-node states for steps 92..158. It is untrusted and
  has no imports.
- `formal/lean/Formal/Cells/ResetWitness2.lean`: the run, its proofs and the checks. It
  imports `ResetCapstone`, read-only.
- Generator, untrusted: `/tmp/claude-0/probes/Bwit/{net,sim,gen,emit}.py`. These are a
  Python re-implementation of `stepF` on `gNet`, parsed from `ResetGcdNet.lean`.
- `formal/lean/Wip/Bwit/M1.lean`: a mutant, not built. It flips one bit of `lateL[19]`
  (node 74 at step 111) and FAILS at `sa1` and at `delays_vary`.
- `formal/lean/Wip/Bwit/Ax.lean`: the `#print axioms` printout. It ends in a deliberately
  failing `example`, so the checker prints its output.

Check: `/tmp/claude-0/btools/bcheck.py Formal/Cells/ResetWitness2.lean` prints OK in about
35 s, with no warnings. `formal/scan.py` is clean on both files. Every computation is kernel
`decide +kernel`; there is no `native_decide`.

Axioms:
- `wRun`, `wBounded`: propext and Quot.sound.
- `pw_wrong`: propext.
- `late_at`, `nonvac_net3`, `reset_capstone_nonvac2`, `w_steer_hold`, `w_steer_tight`,
  `link_moves`, `delays_vary`, `nondegenerate`: propext, Classical.choice and Quot.sound.

## The run

Parameters: `D = 2`, `W = 1`, `F = 93` and `E = 158`. `F = 23·4 + 1`, so H_HOLD_LONG is
tight.

- **Power-up** `v0 = P0` is seeded pseudo-random. 1593 of the 3257 non-rst control nodes are
  wrong at step 0 (`pw_wrong`).
- **Inputs.**
  - rst is 0 at power-up, 1 on `(0, 93]`, and 0 after.
  - Each data net `i` is `(k/4 + i) % 3 == 0`: every data net toggles throughout.
- **Gates.** Gate `j` takes its current LUT value exactly at the steps `k` with
  `k % per j = 0`, where `per j = 1 + j % 3 ∈ {1, 2, 3}`. At all other steps it holds.
- **Wires.** Pin `q` of gate `j` reads its source `lag j q = (j + q) % 2 ∈ {0, 1}` steps
  late.
- **Definition.** `hist` gives (state k, state k-1) by structural recursion over all
  steps, and `wv k = (hist k).1`.

`wRun` (GMW `Run`) and `wBounded` (`Bounded gNet wv wRun 2 1`) are proved for every step,
with no computation:
- `rd = k - lag`.
- `fire_in`: every gate samples at least once in any 3 consecutive steps. So a gate whose LUT
  value is `b` on `[k, k+2]` shows `b` by `k + 3`.

**How the values are computed in the kernel.**
- **Early steps**: `wv 0..2` at single nodes, straight from the recursion. The cones are
  small.
- **Late segment `[F-1, E]`**: `late_aux` is an induction over the 65 steps. Each step
  checks only the 108 wave nodes and the 6 steers (`stepAt`, decided in 6 chunks).
- **Base** (steps 92 and 93): Rst2's `gcd_reset_binary`, with `base_ok` (decided) for the
  data.
- **Step** `k → k+1`: H_STEER_HOLD up to `k` comes from the induction hypothesis (the
  steers are non-wave, reset value 0). At `k + 1` it comes from the steer half of `stepAt`.
  Rst3's `gcd_wave_only`, run with `E := k + 1`, then puts every non-wave control node at
  its reset value. The wave nodes come from the wave half of `stepAt`. Data and rst come
  from the waveform.
- The other 3143 control nodes are never simulated. Their values come from the ternary wave
  theorem, which is why the whole file checks in about 35 s.

## Headline theorems

- **`nonvac_net3`**: one run meets every hypothesis of Bfw's `gcd_reset_vec_net` /
  `cellRunW_clean` and of Rst3's `gcd_clean_release`:
  - `Bounded 2 1`;
  - H_RST_CLEAN on `(0, 93]`;
  - H_HOLD_LONG `23·4 + 1 ≤ 93`, tight;
  - H_RST_LOW on `(93, 158]`;
  - H_STEER_HOLD on `(127, 158]`, a 31-step window. `w_steer_hold` proves it on all of
    `(93, 158]`.

  Both theorems are applied to the run in an `example`.
- **`w_steer_tight`**: `wv 159 100 = true`. Steer `ucond_br9.O5` rises at `E + 1`, so
  `E = 158` is the largest end for which H_STEER_HOLD holds in this run.
- **`reset_capstone_nonvac2`**: every hypothesis of `ResetCapstone.gcd_hw_safe_after_reset`
  holds jointly, with this run (`D = 2`, `W = 1`, rst held to 93, `T0 = T0of 2 1 = 92`).
  - H_MAP_T0 is discharged by `gcd_reset_binary` at `T0`. It is no longer a frozen-state
    unfolding.
  - The C side is the shipped one: `frzC chW` and `μW`.
- **Non-degeneracy.**
  - `link_moves`: the link controller `ulink_n68__1.ctl` (node 2439, `bd_c2n`, reset
    value 0) behaves as follows:
    - it is 1 at steps 0 and 1;
    - it falls to 0 at step 2, with rst held;
    - it is 0 on `[92, 94]`;
    - it rises at step 95, after release (it is on Rst2's frontier).
  - `delays_vary`: after release, in the matched delay `ucmpi0.udly`:
    - `g[1]` (node 69) follows its LUT value after 1 step (k = 101);
    - `g[3]` (node 71) after 2 steps (k = 104);
    - `g[6]` (node 74) after 3 = D + 1 steps (k = 109).

    The predicate `Resp j k d b` says: on `[k, k+d)` the gate sees `exc = b` while showing
    `!b`, and at `k+d` it shows `b`.
  - `nondegenerate` bundles these:
    - `D > 0` and `W > 0`;
    - a control node that is wrong at power-up and moves at a step `t > 0` (2439, `t = 1`)
      onto its reset value;
    - two gates with different observed delays.

    `per_vary` and `lag_vary` are the structural facts.

## Not covered (open)

- The C side of the joint witness is unchanged. C's family is frozen from `T0`, and `μW` is
  the degenerate map (`SelfAuditB7.μW_not_wiring`). B's run and C's family are still
  different models, joined only by H_MAP at `T0`. The conclusion of
  `gcd_hw_safe_after_reset` is still vacuous on the joint witness.
- The delay model is one family: periodic sampling per gate with a constant lag per pin.
  That is not every GMW run (no data-dependent or glitching schedules), though every run of
  the family is a GMW run.
- There is nothing about the board.
- The run after `E` is defined (the same recursion), but nothing is claimed about it.

## Proposed JOURNAL-B paragraph

Bwit (ResetWitness2, ResetWitness2Data) closes Bsa4's "frozen D = 40 witness" finding.
- `wv` is a GMW run of the real `gNet` with D = 2 and W = 1. It starts from a pseudo-random
  power-up (1593 control nodes wrong).
- Gate `j` samples every `1 + j % 3` steps, and pin lags are `(j+q) % 2`. Run and Bounded
  are proved for all steps, with no computation.
- Values on `[92, 158]` come from a 65-step induction. Only the 108 wave nodes and 6 steers
  are checked per step; Rst3's `gcd_wave_only` carries the other 3143 nodes. The file checks
  in about 35 s.
- `nonvac_net3`: H_RST_CLEAN, H_HOLD_LONG (tight, F = 93), H_RST_LOW, and H_STEER_HOLD on
  `(127, 158]`.
- `w_steer_tight`: a steer rises at 159.
- `reset_capstone_nonvac2`: all headline hypotheses jointly. The C side is still `frzC chW`
  and `μW`.
- Non-degeneracy:
  - `link_moves`: ulink_n68__1.ctl is 1, 1, 0 at steps 0..2, and rises again at 95;
  - `delays_vary`: observed gate delays 1, 2 and 3.
- Mutant M1 (one data bit) fails.
