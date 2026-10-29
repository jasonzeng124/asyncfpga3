# B-ring-phys (probe Bring): the `_set` stage and live physical rings

Lean, core only (no Mathlib in the closure). Each file checked OK with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/<file>` (autoImplicit=false, no warnings):

| file | contents |
|---|---|
| `formal/lean/Formal/Cells/RingPhysStage.lean` | the `bd_c2n_set` stage (`SetStage`), INIT duality, `link_segK'`, `set_segK`, `set_phases`, `set_reset_hold`; `StageB`/`WireB` (either polarity); frozen rings: `ring_frozen`, `ring_frozen_D`, `ring2_dead`, `ring_dead'`, `ring2_witness` |
| `formal/lean/Formal/Cells/RingPhys.lean` | the ring network (`RingData`, `PRing`, `PRingT`), the assume-guarantee closure (`ring_cell`, `ring_env`, `ring_nodes`), liveness (`ring_toggles`, `ring_inf`), necessity (`ring_cond`, `ring_k_tokens`, `ring_reset_live`), refinement onto C's `Ring` (`ring_tick`, `fire_set`, `ring_reach`, `ring_tokens`, `ring_live_C`) |
| `formal/lean/Formal/Cells/RingPhysWit.lean` | witness N = 3, one `_set` stage (C's `resetState 1`); `ring2_no_run` |
| `formal/lean/Formal/Cells/RingPhysWit2.lean` | witness N = 5, two `_set` stages (C's `kState 2`, two tokens); `two_tokens_four_frozen` |

C's definitions are imported, not restated: `Formal.Net.Ring` (`prv`, `nxt`, `tok`, `ctl`,
`excited`, `Reach`, `fire`, `D`, `resetState`, `kState`, `persistent`, `live_iff`, `D_reach`,
`dead_of_le_two`, `D_reset`, `D_kState`).

No sorry, axiom or native_decide. `#print axioms` on 33 headline theorems (temporary companion
file, deleted): 26 `[propext, Classical.choice, Quot.sound]`, 3 `[propext, Quot.sound]`,
1 `[propext]`, 3 none.

## Verdict

- **The `_set` stage is a reset-0 stage of the complemented traces.**
  `!c2n_set(a,b,q,r) = c2n(!a,!b,!q,r)`, by `decide` on the verbatim INITs (`exS_dual`).
  Every B lemma about `bd_c2n` therefore transfers to `bd_c2n_set` by complementing its
  pins and node (`setStage_norm`). Its per-segment contract `set_segK` has the form of
  `link_segK`. The node shows `!vW k` on segment `k`: it is high up to its first edge,
  which is a fall. `set_reset_hold`: the node is 1 on `[hi, R + lo)` whatever its pins do,
  so it offers its initial token at reset release. `set_phases` is its whole k-token train.
- **Rings, physical model = C's rule.** For any ring of mixed polarities with reset pattern
  `b`, there are two cases.
  - *Frozen*: if no stage is C-excited in `b`, every trace is frozen at `b`, for any delays
    (`ring_frozen`). By C's theorems this is exactly the case `N <= 2`, or `D in {0, N}`
    (`ring_frozen_D`).
  - *Live*: under the gate relations and the chain's timing rows, every node circulates
    forever (`ring_nodes`, `ring_toggles`, `ring_inf`). The hypotheses then imply
    `3 <= N` and `0 < D < N` (`ring_cond`). With `t` loop tokens (`D = 2t`) this is
    `2t + 1 <= N` (`ring_k_tokens`).

  **Timing adds no condition to C's, and removes none.** The rows needed are those of the
  chain: H_LAT with the derived slacks, H_RT, H_WIRE_R, H_RST_LONG.
- **Refinement.** Every node that toggles at tick `t+1` is C-excited in the state sampled
  at `t` (`ring_tick`). Every sampled state is C-reachable from `b` (`ring_reach`):
  simultaneous toggles are fired in index order, by C's `persistent`. So C's `D_reach`
  holds on the physical ring (`ring_tokens`: tokens are conserved, tick by tick).
- **Converse of `ring_dead`** (`ring_reset_live`): take `K` `_set` stages with
  `0 < K < N`. The hypotheses force `N >= 3`, and then the ring circulates forever with
  `D = 2` at every tick. Witness (`RingPhysWit`), N = 3, K = 1:
  - LUT channel `Win 1 3` with actual delay 1; wires and feedback 1; reset 4;
  - period 12 per node; H_LAT met with equality;
  - the first two laps are derived from `ring_toggles` (`wit_laps`).
- **Two tokens** (`RingPhysWit2`): N = 5 (`2t + 1` exactly), stages 0 and 2 `_set`, `D = 4`,
  live, period 20 per node, the same delays. N = 4 with two tokens (`D = N`) is frozen for
  every trace, and no data satisfies the hypotheses (`two_tokens_four_frozen`).
- **(4) N = 2 is dead, not a hazard** (`ring2_dead`): for every trace, any delays and
  either polarity of either stage, both nodes keep their reset values forever.
  - The hypotheses are satisfiable (`ring2_witness`: `bd_c2n_set` + `bd_c2n`, constant
    traces).
  - No 2-stage data satisfies the live-ring hypotheses (`ring2_no_run`).
  - Every signal is constant, so no glitch is possible.

## Model

**Stages.** Stage `i` reads its request from node `prv i` and its acknowledge from node
`nxt i` (`tb_ring.v` wiring, C's `Ring.gate`).
- `StageB (b i)` is B's `Stage` (Win LUT, H_NO_REVERT, feedback `WinDelay`, H_LOOP_POS)
  with the real INIT: `bd_c2n_set` if `b i`, else `bd_c2n`.
- H_PWR: the node shows its reset value before `hi`. This is B's convention (B's reset-0
  `Stage` has "0 before `hi`").
- `WireB b0`: B's `Wire`, with its pin powering up at the driver's reset value.

**Normalised view.** Each node and pin is complemented by its own (or its driver's) reset
value (`xr`). In this view every node starts at 0, and the pins of stage `i` see segment
indices shifted by C's wavefronts:
- the request phase `j` is the upstream segment `j + 1 - [tok i]`; with a wavefront at `i`
  the first phase is present at reset release (`ρR = ash R εF`);
- the acknowledge phase `j` is the downstream segment `j + [tok (nxt i)]`; with a wavefront
  at `nxt i` the first phase waits for the downstream's first edge (`αR = εB`).

This is why `link_segK'` is needed. It generalises `link_segK` in two ways:
- `α 0 >= R` instead of `α 0 = R`;
- the pre-phase condition is the INIT's exact hold condition, `req = 0 ∨ ack = 1`.

**H_TIMES.** As for chains, every edge time is read off the traces:
`τ i j = τs (On i) lo hi (ρR i) (αR i) j`. These are definitions written as equations, and
the theorems hold for every solution.

**H_TOK.** Some `tok i` is true (`D > 0`). It is used only to show that every first edge
comes after reset release (`r_ge0`, by induction on the distance to the nearest upstream
wavefront).

**The closure.** It is `ag_time` with event `(i, k)` = segment `k` of node `i`, timed by the
segment's end. The causality side condition is unconditional:
- `t_F_*`, `t_B_*`, `t_ρ`, `t_α`: the wire and LUT minimum delays;
- `r_snd`, `r_rcv`: the departures `Es i = vl (prv i) + lo (prv i) + wl i` and
  `Ea i = wl (nxt i) + lo (nxt i) + vl i`;
- `r_spF`, `r_spB`: the round-trip spacing.

Every case split is on the two Booleans `tok i` and `tok (nxt i)`.

## Results

| theorem | assumed | proved |
|---|---|---|
| `exS_dual`, `setStage_norm` | `SetStage` | a reset-0 `Stage` of the complemented pins, node and feedback |
| `link_segK'` | `Stage`, reset, H_LAT, H_RST_LONG, `R <= ρ 0, α 0`, departures | segment `k` of the node from the phase-`k` pin shapes |
| `set_segK`, `set_phases` | `SetStage`, the same rows, the pins at the complemented levels | the node is `!vW k` on segment `k` (high first); the whole train |
| `set_reset_hold` | `SetStage`, reset | node = 1 on `[hi, R + lo)`, for any pins |
| `ring_frozen` | `StageB`, `WireB`, H_PWR, H_LUT_POS, `fh <= R`; no C-excited stage in `b` | every node and pin keeps its reset value for ever |
| `ring_frozen_D`, `ring2_dead`, `ring_dead'` | the same; `N <= 2` or `¬(0 < D < N)` / `N = 2` / all reset-0 | frozen |
| `ring_nodes` | `PRing`, `PRingT` | every normalised node is a clean step signal with edges `τ i` |
| `ring_toggles`, `ring_inf` | the same | `τ i j < τ i (j+1)` and node `i` toggles at every `τ i j`; it toggles after every `T0` |
| **`ring_cond`** | the same | `3 <= N ∧ 0 < D ∧ D < N` |
| `ring_k_tokens` | the same, `D = 2t` | `1 <= t ∧ 2t + 1 <= N` |
| `ring_tick` | the same | a node changing at `t+1` is `Ring.excited` in `st t` |
| `fire_set` | `3 <= n`, a set of excited stages | firing them in index order is a C run |
| **`ring_reach`**, `ring_tokens`, `ring_live_C` | `PRing`, `PRingT` | `Ring.Reach N b (st t)`; `D (st t) = D b`; some C-excited stage at every tick |
| `ring_reset_live` | the same, `b = resetState K`, `0 < K < N` | `3 <= N`; every node toggles at every edge; `D = 2` at every tick |
| `Wit.wit_ring`, `wit_ringT`, `wit_laps`, `wit_reach`, `wit_lat_eq` | none | N = 3 witness, all hypotheses, H_LAT equality, two laps, C-reachability |
| `Wit2.wit2_laps` | none | N = 5, two tokens: live, `D = 4` at every tick, C-reachable from `kState 2` |
| `Wit2.two_tokens_four_frozen`, `Wit.ring2_no_run` | none | no data satisfies `PRing ∧ PRingT` for N = 4 with two tokens, or for N = 2 |

## NOT covered / open

- **Existence for every `0 < D < N`.** The converse of `ring_cond` ("the token/bubble
  condition gives a run") is shown only on the two witnesses:
  - N = 3 with t = 1;
  - N = 5 with t = 2.

  Existence of a solution of H_TIMES in general is not proved. The same gap is open for
  chains.
- **H_REARM is not used.** H_REARM is a row of the LinkExact/ZeroDelayTok box model, which
  has per-pin read maps. B's `Stage` LUT reads its lumped excitation through one `Win`
  channel, and per-pin LUT arcs are not modelled (`WinFifoCausal`). In this model the
  cross-token re-arm race is covered by H_LAT together with the derived departures:
  `exc_phase_w` starts phase `j+1` at `max(ρ, α)`. Mechanising the ring in the box model,
  where H_REARM would appear as the loop race `V1_{i+1,j} + Bhi_i <= U1_{i,j+1}`, is open.
- **Sufficiency of the timing rows only.** The rows H_LAT, H_RT, H_WIRE_R and H_RST_LONG
  are sufficient. Their necessity on a ring is not proved. The witnesses meet H_LAT with
  equality.
- **Not covered:**
  - `bd_c2_set` (only `bd_c2n_set` is modelled);
  - data latches on the ring;
  - X power-up: Boolean traces only, with H_PWR at the reset value;
  - the bdc loop shape (mux/steer entry). That is C-9d's `RingReset`; bdc emits no `_set`
    link.
- **Modelling choice.** "Two laps" in the witnesses means four toggles per node (two rises
  and two falls). The run itself is infinite.
