# B-rig-src-witness: joint non-vacuity of `gcd_rig_first_env`, with lagged reads (probe Bjw)

Files:
- `formal/lean/Formal/Cells/RigSrcWitness.lean` (proofs);
- `formal/lean/Formal/Cells/RigSrcWitnessData.lean` (the generated run, event lists).

Both are core-only. They import `RigSrc` and C's `CapstoneWitnessLib`, and edit nothing.

Check:

    /tmp/claude-0/btools/bcheck.py Formal/Cells/RigSrcWitnessData.lean Formal/Cells/RigSrcWitness.lean
    -> OK, OK   (about 1 min once the closure is built)

- No `sorry`, `admit`, `axiom` or `native_decide`. Every check on the run is kernel `decide +kernel`.
- Axioms:
  - `gcd_rig_first_env_joint`, `gcd_rig_witness_consistent`: `propext`, `Classical.choice`, `Quot.sound`;
  - `w_nondegenerate`: `propext`;
  - `cell_sh1`: `propext`, `Quot.sound`.

Generator (untrusted, not committed): `/tmp/claude-0/probes/Bjw/gen/{rigsim2.py,gen.py}`. It
imports C's `formal/tools/capwit/sim.py` for the net and the kernel gate semantics. The kernel
re-checks everything it produces.

## Relation to Bsa3

Probe Bsa3's `SelfAuditB6.rig_env_feeds` already applies the theorem to a run with these settings:
- every read map `id`;
- urdly 0;
- latch at tick 474.

This probe gives a witness with **lagged reads everywhere the theorem lets a read lag**, as the lead asked. It also gives
the reusable shift lemma `cell_sh1`.

## Results

| theorem | statement |
|---|---|
| `cell_sh1` | C-convention run (all `req`/`ack` low at tick 0), non-source op `k`: `Cell ch sv k → Cell (rtC (shf 1) ∘ ch) sv k`, reset fields included |
| `w_ker`, `w_held`, `w_fork_wire`, `w_dat`, `w_rel`, `w_rel0`, `w_uenv1_b`, `w_c3`, `w_m1`, `w_m0` | each binder of `gcd_rig_first_env`, on the run `chR` with the maps below |
| `gcd_rig_first_env_joint` | ∃ one run, env traces `e k q` and maps `β φ1 φ0 γ` satisfying ALL binders jointly (stated verbatim, in binder order). Every map strictly lags from tick 5. `out0` is offered at 438 and latches at 489 (ack falls), carrying 6 |
| `w_nondegenerate` | the holds below, decided on the run |
| `gcd_rig_witness_consistent` | the theorem applied to the run: every first offer/latch carries 6 |

### The run (a = 12, b = 18)

The network is C's gcd_hw network: 465 channels, 367 operators. Kernel gates follow C's
generator semantics: delay 1, C-elements hold while their inputs disagree, and an arbiter grants
x on a tie.

The environment:

| part | model | reads |
|---|---|---|
| `env_c = e` | drives the three source requests through bd_fork's wires; `e(0) = 1` | — |
| c3 (`in_ack = k`) | `C3` | the `a`, `b`, `start` acks, 2, 3 and 5 ticks late (`γ z t = t - 2/3/5`) |
| uenv1 | `e = C(q, ¬k)` | `k` 3 ticks late (`β t = t - 3`), `q` 5 ticks late (`φ1 t = t - 5`) |
| uenv0 (`out0.ack = q`) | `q = C(res_req, ¬e)` | `res_req = out0.req` delayed by urdly = 7; `e` 4 ticks late (`φ0 t = t - 4`) |

- Every env gate fires 1 tick after its reads.
- urdly is not a read map of the theorem. It sits inside C's `Sink.wire` for out0, which H_KER
  checks: the ack moves to `out0.req` of the previous tick. This holds because `out0.req` is
  stable across the 7-tick lag.
- After uenv1's second rise (tick 453, lap 2 offered) the env holds. That is an inertial hold,
  and every env hypothesis is a guarded step form. The kernel then runs to quiescence (558 ticks).
- out0's ack can fall only after `e` has re-risen (M0 with a monotone `φ0`). So any witness
  with a latch must offer lap 2: a run of one lap only cannot witness TokAt.

### Non-degeneracy (`w_nondegenerate`, rig ticks)

- **c3:**
  - At 50, `a.ack = b.ack = 1`, `start.ack = 0`, and `k` holds 0.
  - From 98 to 103 all three acks are high but `k` is still 0 (its start pin is read 5 ticks late).
  - `k` rises at 104.
- **uenv1:**
  - It holds `e = 1` at 104..107 while excited (`k = 1`, `q = 0`, read stale). `e` falls at 108.
  - It holds `e = 0` at 300 with `q = 0`, `k = 0`. This is the hold H_ENV rests on.
  - It holds `e = 0` at 447..452 with `q = 1` already (read 5 ticks late). `e` re-rises at 453.
- **uenv0:** `out0.req` is high from 439, but `q` stays 0 until 447 (urdly).
- **start:** offered twice by 489 (the reset level, then lap 2).

### Method

C's event lists (`CD`, `bv`) start low, but the rig's source requests are HIGH at release.

1. Generate the run in C's convention: tick 0 idle, rig tick `t` = C tick `t + 1`.
2. Check every op with C's `kChk` (sources skipped).
3. Shift back with `cell_sh1`. Its reset fields at the new tick 0 follow from the guards at old step 0, because all
   tick-0 values are low.

`Held` survives the shift (`held_rt`). The env binders are checked at the listed toggle steps
(`sh_step`).

## NOT covered / open

- Other inputs and other schedules: one schedule, fixed lags, all kernel gate delays 1.
- Per-pin skew inside kernel cells: C's cell models have no read maps.
- Time-varying lags: each lag is a constant (`t - d`). The theorem allows any monotone causal map.
- Fidelity to the silicon: the theorem's hypotheses are not shown to hold of the board.
- H_SINK_SI for uenv0 + urdly (B-rig-src): this run satisfies it, because `out0.req` is stable.
  That is not proved in general.
- No binder of `gcd_rig_first_env` was found jointly unsatisfiable. So there is no contradiction
  to report.
