# B-rig-laps: gcd_rig's laps, H_SINK_SI, and the per-lap cut (probe Blap)

File: `formal/lean/Formal/Cells/RigLaps.lean`. Core Lean, no Mathlib. It imports B's
`RigSrc`, which brings in `RigToken` and C's `CapstoneRig` / `CapstoneRigTime`. No other file
was edited, and nothing of shard C was touched.

Check (2026-10-29):

    /tmp/claude-0/btools/bcheck.py Formal/Cells/RigLaps.lean
    -> == Formal/Cells/RigLaps.lean: OK

- No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern`, `unsafe` or
  `maxHeartbeats` appears in the file.
- `#print axioms` was run on the 13 headline theorems, using a temporary
  `#guard_msgs` tail that has since been removed. Every one shows at most
  `[propext, Classical.choice, Quot.sound]`; `pend_fast_nonvacuous` shows none.

Traces, in rig time:
- `e` = `env_c` = `start.req` (the `bd_fork` request outputs are wires);
- `q` = `env_c0` = `out0.ack`;
- `o` = `out0.req`;
- `rr` = `res_req` = `urdly(out0_req)`.

Laps are numbered as in C's `gcd_rig_window`: the reset level is offer 0, and lap `k ≥ 1` is
start's `k`-th rise after release.

## 1. Lap contract (task 1)

The hypotheses are `Ring e q T0 Tq φ1 φ0`, which is RigToken's `ring_alternation` set:
- quiet release state `e = 1`, `q = 0` on `[Tq, T0]`;
- `M1`: uenv1's `a` half;
- `M0`: uenv0's `b` half;
- both read through monotone causal maps.

`RigToken.set_move` / `c2n_move` derive `M1` / `M0` from the real INITs under the named
timing hypotheses H_LUT_FIFO, H_FB_FIRST (the RT_FB race), H_RST_ONE_FALL and H_WIRE_FIFO.
The kernel (`in_ack`, `res_req`) is arbitrary.

| theorem | proved (for every `k ≥ 1`) |
|---|---|
| `lap_offer` | At start's `k`-th re-offer (step `r`): `out0.ack` has risen exactly `k` times (results `0..k-1` consumed), still `k` at `r+1`. It has fallen `k-1` times, and it is HIGH at `r` and `r+1`. So lap `k` is offered while result `k-1`'s handshake is still open. Counts: `N e: 2k-1 → 2k`, `N q = 2k-1`. |
| `lap_close` | At `out0.ack`'s `k`-th fall (step `s`, result `k-1` closes): `env_c = 1` at `s` and `s+1`, and `env_c0 = 0` at `s+1`. Counts: `N e = N q = 2k`, so the env is **exactly in its release state**. Lap `k`'s offer `r < s` already happened (`out0.ack` was high there), and `start.req` stayed high on `[r+1, s+1]`. |
| `lap_result` | Result `k` is consumed (the `(k+1)`-th rise of `out0.ack`) only after lap `k`'s offer. |

So the order inside every lap is fixed:

    consume(k-1) < offer(k) < close(k-1) < consume(k)

"Offer `k` only after result `k-1` was consumed" holds. "The env token state is reset" holds
at the close, not at the offer.

**Index state.** No new theorem is needed. `RigIdx.idx_setup_suff` (2) already gives
operands equal to the window's vector on the whole window `[e n0 + vhi, e(n0+65536) + vlo)`.
`SetupOK` quantifies over every enable-high instant of the window, which covers every lap.
`H_TOKEN_STATIC` is not needed for any lap: `idx_fire` needs the token only until F's first
rise.

## 2. H_SINK_SI (task 2): it HOLDS, with a FIFO read; the counter-run is without one

C's `Sink.wire` says the ack moves only to `req` of the previous tick. For the rig, this is a
claim about `uenv0` behind `urdly` (`K.sink 416`) and about `upsnk = bd_delay #2`
(`K.sink 3`).

| theorem | assumed | proved |
|---|---|---|
| `sink_si_upto` / `sink_si` | ack moves only to `req (ρ t)`, with `ρ` monotone, causal and `≥ T0`; the channel is idle at `T0`; the sender moves `req` only to `¬ack` (send rule, at steps `< T` in the causal form) | `Sink.wire` at every step `≤ T` |
| `out0_sink_si` | uenv0's `a` half (`H_UENV0_A`); `H_URDLY_FIFO: rr s = o (δ s)` with `δ` monotone; composed read inside `[T0, t]`; send rule | `out0.ack` moves only to `out0.req` of the previous tick |
| `out0_sink_si_cells` | the same, with `H_UENV0_A` from uenv0's real `bd_c2n` INIT (`c2n_move`: H_LUT_FIFO, H_RST_ONE_FALL, H_FB_FIRST) | the same |
| `pend_sink_si` | `H_UPSNK_FIFO` (at least one tick, monotone); send rule | the same for `p_end` |
| `sink_C_of_wire` | the wire from `T0`; ack low at `T ≥ T0` | C's `Ops.Gcd.Sink (rtC (shf T) c)` |
| `rig_out0_sink` | `CellR` for every operator other than `K.sink 416`; H_BUNDLE; uenv0/urdly's read-map move; `out0.ack` low at release | C's `Sink (ch out0)`. The producer's send rule is not assumed: it is read off C's `gcd_hw_protocol` on the run frozen at each step (strong induction, as in `RigSrc.rig_cellR`) |
| `CXS.nonfifo_breaks_sink` | every hypothesis of `sink_si` except monotonicity of `ρ` (`ρ 3 = 3 > ρ 4 = 2`: the line shows an older `out0_req = 1` after the newer `0`) | the sink acknowledges at step 4→5 while `out0_req` is low, so `Sink.wire` fails, and with it C's receive rule |

Proof idea:
- Count with RigToken's `cell_count`: `N req ≤ N ack + 1` (send rule) and `N ack ≤ N req∘ρ`
  (the sink).
- At a move these force `N req t = N ack (t+1)`.
- Parity then gives `ack (t+1) = req t`.

The stale read is harmless only because the sender cannot move `req` again until the ack has
moved.

Fidelity:
- H_URDLY_FIFO / H_UPSNK_FIFO model `bd_delay` as an order-preserving delay (inertial
  swallowing is allowed: a monotone map can skip a pulse).
- A chain that reorders edges (rise and fall transport arcs differ by more than a pulse width)
  violates it. That is the counter-run.

## 3. Per-lap invariant for C (task 3), and why it is not yet enough

**`LapInv a b ch T := ∀ o, CellR (shiftRun T ch) (srcV a b) (opAt o)`.** This is exactly the
hypothesis of C's `gcd_rig_first`, for the run seen from `T`.

The cuts are:
- `T = 0`, the release;
- `T = e + 1` after every `out0` close `e`, where `lap_close` puts the env in its release
  state: `start.req = 1` is the lap's offer level, as at release, and `Src.iz` is not needed.

| theorem | assumed | proved |
|---|---|---|
| `gcd_rig_lap` | `LapInv` at `T`, H_BUNDLE, H_ENV | the `out0` offer numbered `cnt (riseB out0.req) T` (the first after `T`) carries `gcd a b` |
| **`gcd_rig_every`** | `LapInv` at 0 and after every close, H_BUNDLE, H_ENV, `a, b < 2^31` | **every** `out0` offer and **every** latched `out0` value is `gcd a b` |
| `lapinv_of_parts`, `lapinv_at_close` | sources' `SrcR` on the whole run (`RigSrc.rig_cellR`); H_SINK_SI; `H_KER_REARM` | `LapInv` at the close. The env, sources and `out0` sink are discharged. **Only the kernel residual `H_KER_REARM` stays open**: every other operator's cell model holds from `e+1`, reset fields included. |
| `lapinv_pend_idle` | `LapInv T` | `p_end.ack T = 0` (`Sink.init` of `K.sink 3`) |
| `lapinv_fails_pend_fast` | `start.req` high on `[r+1, T]`; fixed delays `H_FORK_DLY` (`p_end_req` = `start_req` `dF` earlier; the RTL makes it a wire) and `H_UPSNK_DLY` (`dP`); **H_PEND_FAST** `r+1+dF+dP ≤ T` | `¬ LapInv T` |
| `lap_cut_fails` | `Ring` on the rig's channels, the same delays, and H_PEND_FAST for lap `k` | `¬ LapInv` at result `k-1`'s close |
| `pend_fast_nonvacuous` | — | the hypotheses of `lapinv_fails_pend_fast` are jointly satisfiable |

**Verdict.** The out0-close cut is the right *environment* cut: the env is exactly reset
there. But it is not a cut for the *kernel*. Lap `k` has been offered since `r < s`, and
`p_end_req` is `start_req` through a wire. So whenever the 2-LUT `p_end` loop is faster than
`out0`'s return after the re-offer, `p_end_ack` is high at the close and `LapInv` fails. In
the rig that return includes `urdly`, CMPD = 16 elements, about 4.4 ns. Whether H_PEND_FAST
holds is a kernel timing question that is NOT proved here, but the expected sign is that it
holds, so this cut fails on silicon.

C's `rearm_fails_at_reoffer` shows that the re-offer cut fails too (`out0.ack` high). So
**`gcd_rig_every` is sound, but its hypothesis is expected false for the real rig.**

"Every result" needs a re-entrant cut: a window theorem whose start state lets `p_end`, `start`
and `out0` be mid-handshake (the return phase), with the kernel's other channels idle. That is
C-side work. B can supply the env/sink facts for it (`lap_offer` gives the state at the
re-offer: `start` rising, `out0.ack = 1`, all counts fixed by `k`).

## 4. Non-vacuity and exactness

- **`W.laps_nonvacuous`**: a 6-tick periodic env run with every read map `id`.
  - It meets `Ring` and every hypothesis of `sink_si` on `out0`.
  - Re-offers are at 5, 11 and 17; closes are at 6, 12 and 18, so 3 laps by tick 20.
  - The premises of `lap_offer` (step 11) and `lap_close` (step 12) hold with `k = 2`.
  - `sink_si`'s conclusion holds on it.
- **`CXS.nonfifo_breaks_sink`**: the counter-run for H_SINK_SI's only non-structural
  hypothesis.
- `pend_fast_nonvacuous`.
- **NOT done: a witness for `gcd_rig_every` / `LapInv`.** It would need a gcd_hw run with 2 or
  more invocations whose kernel is idle at each `out0` close. That is a C-side run like 8t,
  and by §3 it is only possible when the `p_end` loop is slower than `out0`'s return.

## NOT covered

- `H_KER_REARM`, and any re-entrant cut.
- Merging `rig_out0_sink` with `RigSrc.rig_cellR` into one induction (both sources and both
  sinks at once). `rig_out0_sink` takes the sources' `CellR` as given, and `rig_cellR` takes
  the sink as part of H_KER. Merging them is mechanical: the same freeze argument, one
  conjunction.
- `p_end`'s sink inside C's network (`pend_sink_si` is the trace form; its `SendStep` comes
  from the fork's model).
- Routed numbers for `dF`, `dP` and the out0 return. H_PEND_FAST is not checked on a route.
- RT_FB at uenv0/uenv1 (H_FB_FIRST behind `M0` / `M1`). It fails on seeds 2 and 4
  (B-rig-token §5).

## For C

1. Use `gcd_rig_every` as the iteration skeleton. It needs exactly `LapInv` at each close.
   `lapinv_at_close` reduces that to `H_KER_REARM`.
2. Expect `H_KER_REARM` to be false on silicon (`lap_cut_fails`). To prove every result, a
   window theorem from a re-entrant start state is needed.
3. In C's hypothesis table, `K.sink 416` (H_SINK_SI) is now **proved** from uenv0's INIT,
   H_URDLY_FIFO and the other cells (`rig_out0_sink`, `out0_sink_si_cells`). `K.sink 3` is
   proved in trace form (`pend_sink_si`).

Effort: about 2.5 h.
