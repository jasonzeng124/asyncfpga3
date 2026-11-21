# B probe 5b: C-element timing under bounded delays (`bd_c2`)

File: `formal/lean/Formal/Cells/CElemTiming.lean` (549 lines, core Lean only,
imports `Formal.Cells.Prelim`, checks in ~1 s).

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/CElemTiming.lean

Status: checks clean, no warnings, no `sorry`/`admit`/`axiom`/`native_decide`.
`#print axioms` (run on a scratch copy): every main theorem depends only on
`propext`, `Quot.sound`, and (for `runt_loop`, `c2_four_phase`) `Classical.choice`.

## Model

* Time `Nat` ticks (1 tick = 1 ps intended); traces `Nat → Bool`.
* Nets: `a b rst` as seen at the LUT pins, `O` = LUT output pin, `qp` = the
  feedback net as seen at pin `I2`.
* Excitation `exc init a b q r = lutB init [a, b, q, r, 0, 0]` with the REAL
  INIT of `bd_c2` (`0x00E800E800E800E8`, pin map `I0=a I1=b I2=q I3=rst`).
  Lemmas `c2_eq`, `c2_set_eq`, `c2n_eq` prove the INITs equal
  `~rst·maj(a,b,q)`, `rst+maj(a,b,q)`, `~rst·maj(a,~b,q)` (16-row `decide`).
* `Loop init a b rst O qp dlmin dlmax dwmin dwmax` (the gate relations):
  - `H_LUT`: `O` = window-delayed excitation, delay in `[dlmin, dlmax]`
    (prjxray-db LUT I->O fast-min/slow-max; test: GLS of a lone LUT at SDF
    corners, board ring oscillator).
  - `H_FB`: `qp` = window-delayed `O`, delay in `[dwmin, dwmax]` (routed
    feedback net's prjxray min/max; test: SDF INTERCONNECT of net `q` in
    `cells/gls/`, >= 4 seeds).
  - `H_LOOP_POS`: `0 < dlmin + dwmin`.
* Delay channel `WinDelay dmin dmax x y`: `y t = x s` for SOME
  `s ∈ [t-dmax, t-dmin]` (bounded pure delay with per-tick varying delay,
  non-FIFO). It is the weakest bounded channel: `transport_winDelay` shows
  every fixed transport delay in the interval is an instance, and
  `winDelay_comp` shows LUT + wire compose to a loop channel with summed
  bounds. Positive results are proved for `WinDelay`, so hold for every
  bounded pure/transport channel. The counter-example uses FIXED transport
  delays, so it is a behaviour of every channel in the family.
* `Inertial d x y` (VHDL-style, discrete): `y (t+d) = x t` if `x` was constant
  on `[t, t+d)`, else hold. Not a refinement of `WinDelay` (it can hold an
  arbitrarily old value), so positive results are NOT claimed for it.

## Theorems proved

Let `Dmax = dlmax + dwmax`, `Dmin = dlmin + dwmin` (loop delay bounds).

1. `exc_held` / `O_held` / `qp_held` (generic, ANY INIT with this pin map):
   if the inputs force the LUT to `v` regardless of the feedback value for
   `Dmax` ticks from `t0`, and `v` stays a fixed point of the LUT up to `t2`,
   then excitation = `v` on `[t0,t2]`, `O = v` on `[t0+dlmax, t2+dlmin]`,
   `qp = v` on `[t0+Dmax, t2+Dmin]`. No assumption on the state before `t0`
   (works from any power-up value). Proof: strong induction on time; the
   sample point of the composed channel is strictly earlier because of
   `H_LOOP_POS`.
2. (a) `c2_follow_hold`: `bd_c2` with `H_PULSE` (`a=b=v`, `rst=0` for `Dmax`
   ticks from `t0`), `H_NORST` (`rst=0` on `[t0,t2]`), `H_NOT_BOTH` (on
   `[t0,t2]` at least one input is `v`) settles to `v` and holds, with the
   windows above. `c2_reset`: `H_RST_PULSE` (`rst=1` for `Dmax` ticks) and
   `H_RELEASE` (afterwards `a,b` not both 1) give 0 throughout.
3. (b) `runt_loop` + `runt_oscillates`: concrete closed-form traces, for any
   `dl, dw` with `D = dl+dw > 0` and pulse width `0 < w < D`: `a = 1`,
   `rst = 0`, `b = 1` exactly on `[t0, t0+w)`; excitation `= [t ≥ t0 ∧
   (t-t0) mod D < w]`, `O` = that shifted by `dl`, `qp` shifted by `D`.
   `runt_loop`: they satisfy every gate relation (`Loop` with
   `dlmin=dlmax=dl`, `dwmin=dwmax=dw`). `runt_oscillates`: after `t0+w` the
   inputs are constant forever (`a=1, b=0`, where a C-element must hold), yet
   `qp(t0 + D(n+1)) = 1` and `qp(t0 + D(n+1) + w) = 0` for every `n`, and `O`
   likewise: perpetual oscillation with period `D`, high time `w` (runts of
   width `w` on `O`). A numeric instance (`dl=120, dw=300, w=200` ps) is
   checked by `decide`. Hence the `Dmax` bound in (a) is EXACT: for fixed
   delays it is tight for every `w < D`.
4. (c) `c2_four_phase`: hypotheses `H_ALT` (targets `V k` alternate),
   `H_ORDER` (`c` increasing), `H_BOTH` (both inputs at `V k` at `c k`),
   `H_NEXT` (on `[c k, c(k+1))` at least one input still `V k`), `H_NORST`,
   `H_ACK` (from `c k` on, an input leaves `V k` at `s` only if the
   environment saw `O = V k` at some `u ∈ [c k, s-E]`), `H_ENV_LATENCY`
   (`Dmax ≤ dlmin + E`), `H_RESET_DONE` (`O = !V 0` on `[c 0, c 0 + dlmin)`,
   discharged by `c2_reset`). Conclusion: for every phase `k`, `O = V k` on
   `[c k + dlmax, c(k+1) - 1 + dlmin]` and `qp = V k` on
   `[c k + Dmax, c(k+1) - 1 + Dmin]`. Only the transition windows of width
   `dlmax - dlmin` after each `c k` are unconstrained. The minimum pulse width
   of (a) is derived (by induction over phases) from the environment latency;
   also derived: `c(k+1) ≥ c k + Dmax`.
5. Inertial: `inertial_runt_lost` (channel lemma) and `c2_inertial_runt_lost`
   (closed loop: inertial LUT with threshold `dl`, transport wire `dw`): with
   `a = 1`, a `b` runt of width `w < dl` and the cell at 0 before, `O` and
   `qp` stay 0 forever: the event is LOST.

## Findings

* The exact condition is the minimum pulse width `Dmax = dlmax + dwmax`: an
  enabling input combination must persist for the full maximum loop delay
  (LUT plus feedback wire), not just the LUT delay. Proved sufficient for the
  window channel (hence all bounded pure/transport), and shown necessary by
  the transport counter-trace.
* Four-phase alone is NOT enough. The discipline needs
  `E ≥ dwmax + (dlmax - dlmin)`: the environment, after seeing the ack on `O`,
  must not move an input before the ack has gone round the feedback wire.
  The repo proves this condition SUFFICIENT (`c2_four_phase`). The
  independent audit (claude/audit REPORT, row 51 / findings B #4) proved it
  NECESSARY: `drop_env_latency_cex` in `audit/lean/B/W_CElem.lean`
  (claude/audit branch; dl = 1, dw = 2, E = 1) satisfies every hypothesis of
  `c2_four_phase` except H_ENV_LATENCY, and O glitches to 0 at t = 7, inside
  the promised window. So the fork condition is necessary, not only
  sufficient (necessity is the audit's theorem, not in this repo's Lean).
  This is an isochronic-fork condition on the fork `O -> environment` vs
  `O -> I2`. With fixed delays (`dlmin = dlmax`) it reduces to
  `E ≥ dwmax`. In the library the environment's latency is at least another
  LUT plus a route, and the feedback route is short and local, so it should
  hold with margin; it is a check worth adding to the timing checker
  (track 10): routed delay of each C-element's own feedback net vs the
  minimum delay of every path from its `O` back to one of its inputs.
* Delay channel: transport/bounded-pure (window) admits all positive proofs
  easily. Inertial changes the shape of the failure, not its existence: a
  runt shorter than the LUT's inertial threshold is swallowed (event lost,
  proved); a runt between the threshold and `D` circulates (oscillation, as
  with transport, NOT proved here); a runt whose gap `D - w` is below the
  threshold latches (NOT proved). Real silicon is neither: pulses shrink or
  grow per pass (involution channels), so a near-critical runt can circulate
  for a long, unbounded number of passes before dying out or latching: the
  metastability analogue. Not modelled here.

## Effort per part

* Channel defs, composition, INIT lemmas: trivial (minutes).
* Generic settle/hold and (a): easy; one strong induction plus omega.
* (b) counter-trace: moderate; closed-form mod-D traces, about 10 `Nat.mod`
  rewrites. Done for all parameters, not just numbers.
* (c): moderate; a nested induction over phases, and the right placement of
  the environment-latency hypothesis was the real work.
* Inertial runt-loss for the closed loop: moderate (joint strong induction on
  `O` and `qp`).

## Not done / unproved

* Inertial "pulse in `[dl, D)` circulates" and "gap shorter than threshold
  latches": not proved (statements above are informal).
* Involution channels; Kleene values (X on feedback); runt shrinking.
* No separate theorem for `bd_c2_set`/`bd_c2n`/`bd_c3`/`bd_c4`. The generic
  `exc_held` applies to the 4-pin cells as is (only the force/fixed-point
  side conditions change; INIT lemmas for `c2_set` and `c2n` are there).
  `bd_c3`/`bd_c4` have a different pin map and need their own `exc` (an
  hour's work).
* Glitches inside the transition window `(c k - 1 + dlmin, c k + dlmax)`:
  the window channel allows them (non-FIFO). Under FIFO fixed transport there
  is exactly one transition; not proved.
* The four-phase theorem takes the environment as hypotheses on traces, not
  as a composed gate network (that is track 8).

## Verdict

Works. Main results proved, core Lean, about 3 hours as a probe. Finishing
(inertial circulation/latching, the c3/c4 pin maps, FIFO single-transition)
is about 1 day. What it buys the project: the exact C-element timing
condition (`min pulse width = Dmax`), and a NEW derived constraint that is not
in the library's rules: environment ack-to-input latency
`≥ dwmax + (dlmax - dlmin)` (sufficient here; necessary by the audit's
`drop_env_latency_cex`, audit/lean/B/W_CElem.lean). Track 10's checker could check it per cell.

## Fidelity per primitive

* LUT: binary Boolean function from the REAL INIT through `lutB`, plus a
  delay interval. Not a pass-transistor mux tree: no X, no runt shaping. The
  model is binary-faithful only while pins carry valid levels. That is what
  probe 5a's Kleene results and the involution model would refine.
* Feedback wire: a routed net with a delay interval `[dwmin, dwmax]` (meant to
  be the prjxray min/max of its pips and wires), no R/C shaping, no pulse
  degradation.
* LUT delay is lumped at the output: the LUT samples all pins at ONE instant
  and the result is delayed by `[dlmin, dlmax]`. Real per-pin I->O delays
  differ (prjxray gives them per pin). A per-pin model,
  `O t = f(a(t-d0), b(t-d1), qp(t-d2), ...)`, is NOT covered by these proofs.
  Static input-routing skew is in the input traces; only the LUT-internal
  per-pin spread is missing. The spread matters only inside transition
  windows, so the settle/hold results should carry over, but that is unproved.
* Inertial channel: a modelling alternative only, not claimed faithful.
