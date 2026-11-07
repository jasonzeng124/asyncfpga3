# B-rig-token: the rig's initial token `uenv1` and C's H_START_ONCE (probe Bu)

File: `formal/lean/Formal/Cells/RigToken.lean`. It is Core Lean. It imports
`Formal.Cells.ResetContract` (B) and `Formal.Net.Handshake` (C's `cnt`, `riseB`, `Chan`,
`SendStep`, `RecvStep`, which are used, not copied). No other file was edited.

Check:

    /tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/RigToken.lean
    -> [bchk] OK: formal/lean/Formal/Cells/RigToken.lean      (about 40 s, one slot)

- There is no `sorry`, `admit`, `axiom` or `native_decide` in the file.
- I ran `#print axioms` on all 14 headline theorems in a scratch copy. Every one uses
  at most `propext`, `Classical.choice` and `Quot.sound`.

## 0. The ring, read from the RTL

From `cells/hw/gcd_rig.v`:

- `uenv0 = bd_c2n(a = res_req, b = env_c)`. Its INIT is `00B2..`; it resets to 0.
- `uenv1 = bd_c2n_set(a = env_c0, b = in_ack)`. Its INIT is `FFB2..`; it resets to 1.
- `res_ack = out0_ack = env_c0`.
- `ufork` broadcasts `env_c` as `a_req = b_req = start_req`. These are wires.
- `in_ack` is the fork's `bd_c3` (with rst) over the kernel's three acks.
- `res_req = bd_delay#16(out0_req)`. It has no rst.

`gcd_hw.v` drives every cell's rst from one net, `rig_rst = ~por_done | rst_sr[15]`. That
signal is 16 hk cycles of rst at every window edge. Each cell sees it through its own
route, so the cells release in an order the router picks.

In C's terms:
- `start.req = env_c`;
- `out0.ack = env_c0`. A rise of `out0.ack` means the environment took one result.

## 1. What is proved

**Release is order-free.** This is the precise form of C16's "uenv1 release order".
- No hypothesis relates the rst fall at one cell to the rst fall at another.
- The cell whose reset matters is **uenv1**. Its reset value, 1 with `env_c0 = 0` and
  `in_ack = 0`, is a *hold* state of the C-element, so only rst can create the token.
- uenv0's reset value 0 is forced either by rst or by its own inputs
  (`res_req = 0 ∧ env_c = 1`).

**H_UENV1_RELEASE** is the conjunction of three hypotheses:
- `H_UENV1_HOLD`: rst at uenv1's I3 is high for its loop bound `dlmax + dwmax`. This is
  exact at every fixed delay (§3).
- `H_ACK_QUIET`: until the kernel acks, uenv1's pins show `env_c0 = 1 ∨ in_ack = 0`.
- `H_RST1_ONE_FALL`: rst at the pin is not re-asserted while the ring runs. This is
  sufficient only; its necessity was not shown.

After the hold, uenv1's rst may fall at any time, in any order with the other cells. It
may even glitch *before* the ring starts, because the excitation is 1 either way
(`uenv1_release`).

| theorem | assumed | proved | NOT covered |
|---|---|---|---|
| `uenv1_release` (= `ResetContract.c2n_set_reset`) | B's window loop `LoopG`, real INIT; H_UENV1_HOLD; H_ACK_QUIET on `[t1,t2]` | `env_c = 1` on `[t1+dlmax, t2+dlmin]`, from ANY power-up state, with no glitch | the fork `c3` that makes `in_ack` (H_ACK_QUIET is assumed, not derived from c3 + kernel reset) |
| `uenv0_release` (new) | `LoopG`, real INIT; H_UENV0_FORCE (rst OR `res_req=0 ∧ env_c=1`) for the loop bound; H_RES_QUIET (`res_req=0 ∨ env_c=1`) | `env_c0 = 0` on `[t0+dlmax, t2+dlmin]`, any power-up state | that `urdly` (no rst) has flushed (that is H_RES_QUIET) |
| `cell_count` | the cell moves only to the value its pin reads of the other cell, through a monotone causal map; quiet start | `N y (t+1) ≤ N x (φ t) + k` (`k` = initial excitation) | — |
| `ring_alternation` | M1 and M0 (step form of both cells), FIFO reads, quiet start `env_c = 1`, `env_c0 = 0` | `N env_c0 ≤ N env_c ≤ N env_c0 + 1` at all times, for **any** `in_ack` and `res_req` (any kernel) | kernel behaviour |
| `set_move`, `c2n_move` | H_LUT_FIFO (output = LUT function of the pins read at ONE monotone instant σ t), H_RST_ONE_FALL, **H_FB_FIRST** (the RT_FB race: at a move, the feedback read shows the old output) | M1/M0 (and the `b` half: `in_ack = ¬O'` at the read) from the real INITs | per-pin skew inside the LUT (that is FifoFidelity's H_SEL_ORDER) |
| `start_per_result` | as `ring_alternation` | in C's `cnt`/`riseB`, on `shiftC` traces: `#rises(start.req) ≤ #rises(out0.ack) + 1` and `#rises(out0.ack) ≤ #rises(start.req)`, at every C-time | — |
| `start_once_prefix` | same | `cnt (riseB out0.ack) u = 0 → cnt (riseB start.req) u ≤ 1`: H_START_ONCE on every prefix before the first returned result | after the first result (see §4) |
| `rig_token` | the §4 timed release plus the step hypotheses of both cells, with H_WIRE_FIFO (`a1 = env_c0 ∘ ψ1`, `b0 = env_c ∘ ψ0`) | `start_per_result`'s conclusion, from reset onward | the C3 fork; whether the LoopG model and the FIFO model of one trace are consistent beyond the witness |

**Non-vacuity.** `Wit.rig_token_nonvacuous` builds one run that meets every hypothesis of
`rig_token`:
- a reset prefix of 4 ticks, with rst high on `[0,2)` at both cells;
- then an 8-tick lap that repeats forever;
- LUT delay 1, feedback delay 0, wires 0.

In that run:
- `cnt start = 3` and `cnt out0.ack = 2` at C-time 20, so the run is not degenerate;
- `Wit.four_phase` checks that both channels obey C's `SendStep`/`RecvStep` at every tick.

## 2. Plain-language statement

**Assumed.**
- Both env cells are their real LUT INITs.
- Each cell's output is its function of its pins read at one moving instant (FIFO LUT).
- Each wire between the two cells is a FIFO delay.
- rst at uenv1 is held for one loop delay.
- After reset, each cell's rst does not come back.
- Each cell's feedback wins its race against the other cell's response (RT_FB).
- The kernel does not ack before it has seen `start`.

**Proved.**
- The ring leaves reset with `start.req = 1`, the single standing offer, and
  `out0.ack = 0`. This holds whatever the release order and whatever the power-up state.
- From then on, for any kernel behaviour, the environment never offers `start` a second
  time before it has taken a result.
- It also never takes a second result before it has offered `start` again.

**NOT covered.**
- The kernel itself: that the result it returns belongs to the offered start.
- Any lap after the first, on C's side.
- RT_FB itself. It is a per-route fact, and it FAILS at `uenv1` on 2 of 4 seeds
  (see §5).

## 3. Counter-runs

- **`short_rst_many_starts`** (rst too short at uenv1). Uses B's 5b runt construction,
  transported through `set_hold_as_c2`: the INIT with `env_c0 = in_ack = 0` is `rst ∨ q`.
  - Setting: a rst pulse `0 < w < dl + dw` from power-up 0, fixed transport delays, the
    window-loop relations satisfied, and a kernel that never answers.
  - Result: `start.req` rises in every period, infinitely often, with zero results. Two
    of those rises fall after rst has fallen, so
    `2 ≤ cnt (riseB start.req)`.
  - With `uenv1_release` this makes H_UENV1_HOLD exact at every fixed `(dl, dw)`.
- **`no_rst_no_token`** (zero tokens). If rst never reaches uenv1, the all-0 run is
  legal. `start` is never offered and the ring deadlocks.
- **`Stale.stale_fb_extra_start`** (H_FB_FIRST dropped at uenv1).
  - Setting: step model with one tick per LUT. uenv1's feedback is a FIFO transport wire
    of 3 ticks. Everything else holds, including `Stale.stale_M0` for uenv0. The kernel
    acks and presents its result at tick 2, then is slow to drop them.
  - What breaks:
    - the feedback is stale at tick 4;
    - `start.req` re-rises at 4 → 5 while the kernel's ack is still 1, which breaks the
      start channel's SendStep;
    - M1 fails at tick 6.
  - Result: at C-time 11 there are **3 start offers against 1 result**.
  - This is the RT_FB failure mode, and it hits C's H_START_ONCE directly.

## 4. Against C's H_START_ONCE (`CapstoneCut.lean:145/538`)

C states H_START_ONCE as `∀ t, cnt (riseB (ch start).req) t ≤ 1`: global, for one
invocation. My conclusion is `start_once_prefix` and `start_per_result`. Four pieces of
bridging are still missing.

1. **Prefix.**
   - The rig satisfies H_START_ONCE only up to the first `out0.ack` rise, and then until
     `start` is re-offered. Over a whole rig run it is FALSE: there is one rise per lap.
   - C's `main` is an induction on `t` that uses `H_START_ONCE (t+1)` at step `t`. So a
     `T`-bounded version of `main` / `gcd_hw_forced` / `gcd_hw_circuit_safe''`
     (`∀ t ≤ T`) is mechanical.
   - C would have to add it. I may not edit `Formal/Net`.
2. **Laps ≥ 2.**
   - The rig runs laps back to back and resets only at window edges.
   - C's theorem is about one invocation from the reset state.
   - Covering lap `n` needs either "after a lap the kernel is back in its reset token
     state" or a multi-invocation H_CUT. Neither exists.
   - So today only the first lap of each window is covered on C's side. The env side
     (`start_per_result`) holds for every lap.
3. **Origin.**
   - C's `start` is a `Src` with `req 0 = false` (`Src.iz`). The rig's `start.req` is 1
     at release.
   - `shiftC` puts a virtual rise at C-step 0 → 1. Every other channel must be shifted
     the same way, and its value at `T0` must be its reset value (B's ResetGcd
     `gcd_reset_binary`).
   - This is the "UNCONFIRMED initial state" row of `gcd_hw_hypotheses.md` (line 217).
     It is not mechanised here.
4. **The start cell.**
   - C's H_CELLS makes the producer of `start` a `Capstone.Src`
     (`CapstoneNetDef.lean:386`): `req` moves only to `¬ack` of the previous tick.
   - The rig's producer is uenv1 through the fork, which reads `in_ack = C3(a_ack, b_ack,
     start_ack)`. That is not literally `Src.H_LUT_SI`. It implies it only given the
     kernel's `RecvStep` on all three inputs and the fork's c3.
   - Name for this gap: `H_ENV_REFINES_SRC`, not proved.
   - `set_move`'s `b` half (`in_ack = ¬O'` at the read) is the env half of that
     argument.

## 5. Finding for the cell owner (rig, not kernel)

- `uenv0`/`uenv1` form a bare 2-C-element ring. uenv1's response comes back through
  uenv0 in ONE LUT hop, while its feedback is on pin 1 on every seed (B-gcd-routes).
- C-10h's banded RT_FB fails there on seeds 2 and 4 (−117/−221 and −86/−243 ps per
  `gcd_hw_hypotheses.md`; JOURNAL-B quotes −114/−219 and −81/−201). So
  H_FB_FIRST1 is not established on those routes.
- `stale_fb_extra_start` shows what is then reachable in the step model:
  - `start.req` re-rises while `in_ack` is high;
  - more start offers than results.
- Either of these breaks C's H_START_ONCE and the rig's "one gcd in flight" premise.
- Options, unmeasured and for the owner to judge:
  - lock uenv1's feedback to a fast pin (A5/A6; LOCK_PINS, see Bp);
  - or lengthen the env_c → uenv0 → uenv1 response path.
- A GLS check that would show it: count `start_req` rises between consecutive `res_req`
  rises in `gcd_rig` at the fast corner on seeds 2 and 4. It must be exactly 1.

## 6. Fidelity

- **LUT.** The real INIT through `lutB`, in two forms:
  - B's window channel (§4), which allows non-FIFO delay;
  - the FIFO form, one read instant per output tick (§2), which is FifoFidelity's
    H_LUT_FIFO. Per-pin site-pin skew inside the LUT is not modelled.
- **Feedback.** A window channel in §4. In §2 only H_FB_FIRST is assumed: RT_FB in C's
  step form, at the read instant.
- **Wires `env_c0 → uenv1.I0` and `env_c → uenv0.I1`.** FIFO maps. A non-FIFO
  (`BoundedDelay`) wire could replay a stale value and is NOT covered.
- **Kernel.** Arbitrary traces `in_ack`, `res_req`. Only H_ACK_QUIET and H_RES_QUIET
  constrain them, and only during release.
- **Values.** Binary, no Kleene.

Effort: about 2.5 h.
