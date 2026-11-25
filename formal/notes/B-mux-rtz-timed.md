# B probe Lib4: the bd_mux return-to-zero race (H_MUX_RTZ) as a timing inequality

File: CLAIMED `formal/lean/Formal/Cells/MuxRtzTimed.lean` (core Lean, 430 lines).
It imports `Formal.Cells.CElemTiming` and `Formal.Cells.LibCtlMergeMux`, both
read-only. It checks clean in about 1.7 s, with no warnings. There is no
`sorry`, `admit`, `axiom` or `native_decide`.

Check:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/MuxRtzTimed.lean
    PATH=$HOME/.elan/bin:$PATH /home/user/asyncfpga3/formal/check.sh Formal/Cells/MuxRtzTimed.lean   # [audit] 267 declarations checked, [check] OK

`#print axioms` (run on a scratch copy):
- `rtz_safe`, `rtz_counter`, `rtz_exact_safe`, `rtz_inertial_lost`,
  `floop_causal` and `mux_rtz_env_safe` use `propext, Quot.sound`.
- `rtz_counter_loop` and `merge_rtz_of_latency` also use `Classical.choice`.
- `uj1_eq` uses `propext`.
- The numeric `slow_N0`, `fast_adv_N0_fails`, `fast_adv_N` and `fast_med_N0` use no axioms.

Negative control (scratch copy): weakening H_RTZ in `rtz_safe` to
`te + dlmax ≤ tr` (that is, dropping the feedback wire) makes the proof fail
(`omega`). So the feedback term is load-bearing.

Every definition is local, and Prelim, CElemTiming and LibCtlMergeMux are
untouched. The local definitions are:
- `j0C`, `zaC`, `xaC` and `qpC`: the counter-trace;
- `Causal`: event-form minimum-delay causality;
- `FLoop`: a feedback LUT with an arbitrary next-state function, of which
  `CElemTiming.Loop` is an instance (`loop_floop`);
- `INIT_uj1`: proved equal to `LibCtlMergeMux.INIT_j1` by `rfl`;
- `Lmin`, `Dmx` and `guarded`.

## Model

The model is the one in CElemTiming:
- Time is `Nat` ticks, with 1 tick = 1 ps.
- `WinDelay` is a bounded, non-FIFO pure delay. Positive results hold for every
  bounded pure or transport channel.
- `uxa` is `bd_c2` with its REAL INIT `0x00E800E800E800E8` and pins
  `I0=j0, I1=z_ack, I2=x_ack (feedback), I3=rst`. It is a LUT with delay
  `[dlmin, dlmax]`, plus its routed feedback wire with delay `[dwmin, dwmax]`.
- `uj1` uses its REAL INIT `0x0000EA800000EA80`, with pins
  `I0=y_req, I1=ctl_req, I2=s, I3=j1 (feedback), I4=rst`. Its equation
  `~rst·maj(y, ctl·s, j1)` is proved over 32 rows (`uj1_eq`).
- `uor` is LUT2 `E`. It is proved to be OR.

## Theorems

### §1 Duality
- `c2_dual`: with rst = 0, bd_c2's INIT is self-dual.
- `winDelay_not`, `loop_dual`, `inertial_not`: negating every trace of a loop
  behaviour gives another loop behaviour.

So the pending-fall race is exactly the dual of CElemTiming's minimum pulse
width, and the existing counter-traces carry over.

### §2 Cell level (uxa alone, with inputs as seen at its pins)

- **`rtz_safe`** proves sufficiency. Its hypotheses:
  - H_NORST and H_J0_LOW (`j0` low) hold on `[te, t2]`;
  - H_ZA_LOW: `z_ack` is low on `[te, tr)`;
  - H_NEXT: `tr ≤ t2`;
  - **H_RTZ: `te + dlmax + dwmax ≤ tr`**.

  Then `x_ack` is low on `[te+dlmax, t2+dlmin]`, and its feedback pin is low on
  `[te+Dmax, t2+Dmin]`. The fall completes, and z_ack's re-rise for y's token
  is harmless.

  In words: **z_ack's low pulse at uxa's pin (counted from the moment both j0
  and z_ack are low there) must last at least the LUT's maximum delay plus the
  maximum delay of uxa's own feedback wire.**

- **`rtz_counter_loop` and `rtz_counter`** give the counter-trace when the
  inequality is violated. Take any fixed `dl, dw` and any low window
  `0 < w < dl+dw`. A closed-form trace exists that satisfies every gate
  relation with transport delays: `j0 = 0` throughout, and `z_ack` is low only
  on `[t0, t0+w)`.

  After `t0+w` the pins are constant forever (j0 = 0, z_ack = 1, rst = 0), yet
  `x_ack` is 0 at `t0+dl+D·n` and back at 1 at `t0+dl+D·n+w` for every `n`.
  That is a perpetual train of low runts of width `w`.

  A four-phase x client can read a runt as x_ack's fall, raise a new x_req, and
  then read the next high as its acknowledge. That is a **spurious acknowledge**:
  x's token is consumed but never transferred, because j0 cannot fire while
  s = 1.

- **`rtz_inertial_lost`** covers the other failure mode. If the LUT is inertial
  with a threshold above `w`, the fall is lost: `x_ack` stays 1 forever, which
  is the **wrong latch**. The C-element re-latched x's old acknowledge into y's
  transaction. x stalls until y's z_ack falls, and if x reads the level rather
  than an edge, the handshakes slip.

- **`rtz_exact_safe`** gives exactness for fixed delays. Together with
  `rtz_counter`:
  - `w ≥ dl+dw` is safe;
  - `0 < w < dl+dw` oscillates.

  So the inequality is exact.

### §3 Environment level: `mux_rtz_env_safe`

This is a trace-level chain. Each stage is either:
- a gate modelled from its INIT (`uj1` as an `FLoop`, through `floop_causal`;
  `uor` as a `WinDelay`), or a routed wire (`WinDelay`), or
- a named environment hypothesis in `Causal` form: `H_CTL` for the control
  sender, `H_DLY` for the delay line's rise, `H_SRV` for the server.

The result is:

    H_RTZ_ENV:  te + dlmax + dwmax  ≤  Tzf + (wzc + dc + wcr + dl1 + wjo + dlo + dz + ds) + wux
                with te ≥ Tzf + Wux   (z_ack's fall has reached uxa; j0 is low there)

All right-hand terms are minimum delays along the control token's round trip:
1. `wzc`: z_ack from the server to the control sender;
2. `dc`: the sender's response, from seeing ctl_ack low to ctl_req rising;
3. `wcr`: ctl_req to uj1;
4. `dl1`: uj1's arc;
5. `wjo`: j1 to uor;
6. `dlo`: uor's arc;
7. `dz`: the request line's rise, `DELAY` hops;
8. `ds`: the server, from z_req to z_ack rising;
9. `wux`: z_ack's rise reaching uxa.

The left-hand side holds the maximum of z_ack's fall reaching uxa (`Wux`, the
same wire) plus uxa's LUT and feedback loop. These are all per-arc and per-net
quantities, so **the inequality can be checked on a route** like
tighten.py's rules. Two pieces are separate obligations:
- `floop_causal` discharges `H_CTL` for a bd_link sender (bd_c2n);
- it discharges `H_SRV` for a bd_link server, given that each cell has settled.

**Conservative baseline** (from the route alone):

    Wux − wux + dlmax(uxa) + dwmax(uxa fb)  ≤  Σ min(N+4 arcs) + Σ min(N+4 hops)

### §4 bd_merge: `merge_rtz_of_latency`
In bd_merge, `x_ack = C(x_req, z_ack)`. Under H_MERGE_SEQ, a new request (y's,
or x's next one) is raised only after x_ack was SEEN low. So the next z_ack rise
at uxa comes at least `E` after an instant at which x_ack = 0, and that instant
is `≥ te + dlmin`.

With CElemTiming's generic **H_ENV_LATENCY** (`dlmax + dwmax ≤ dlmin + E`),
this implies H_RTZ. **This confirms Lib3:** bd_merge has no mux-like race, only
the generic C-element feedback-versus-environment condition that every bd_c2
has.

The mux differs in one way. Its next z_ack rise is caused by z_ack's fall
(through the control sender and the already-waiting y), not by x_ack's fall.
So x_ack's fall and the next rise race in parallel.

## Is it reachable in bdc? Yes, in the emitted configuration

- `bdc/emit.py` `_op_mux` emits `bd_mux` for every 2-input `handshake.mux`.
  With more inputs it emits `bdc_muxn`, which has the same shape,
  `in_k_ack = C(j_k, z_ack)`, and the same race; its decode only adds arcs to
  `L`.
- `DELAY` is a placeholder of 12 (`compute.CELL_DELAY["wide"]`) and is cut
  post-route by tighten.py. `FASTFALL` comes from `BDC_LINK_FASTFALL`; it
  shortens z_req's fall, which shortens the RTZ phase, but it does not change
  the rise counted in `dz`.
- In Dynamatic output (e.g. `bdc/hs/corpus/bound-opti.out.mlir`) the select is
  the `%index` of a `control_merge` in the same block. That index is lowered to
  `bdc_amerge` (bd_arbiter) plus `bd_fork`, and rule 1
  (`measurability_sites`) puts a `bd_link` in front of the 1-bit select. So the
  control sender is a bd_link: `dc` = one bd_c2n arc when its input already
  holds the next token. The server is the consumer's link or fork.
- The race needs two tokens waiting when z_ack falls: the next index token
  (s = 1) at the select link, and y's token. In a loop header, x is the entry
  and y is the back edge.
- Both tokens come from the loop body, which runs concurrently with the mux's
  RTZ phase: z_ack rise, x_ack, x_req falls, j0, the DELAY line, the server,
  then z_ack falls. With a short body and an unshortened (non-FASTFALL)
  12-hop fall, the body can win. So **nothing structural excludes the race**.
- Not demonstrated: no GLS or board run was made here.
- No rule in `cells/verify/tighten.py` checks it: grep finds no uxa, RTZ or
  return-to-zero rule.

**Related, already covered:** `bd_arbiter` (inside every `bdc_amerge`, so every
merge and control_merge) has the same race on `A1 = C(g1, A0)`. 7h's RT2
`pulse` (`ArbHeldTimed`, B-arb-held-timed.md) is the analogue, with slack
`qf + wfb + Rrq + smin` and an estimated margin of 0.55–0.62 ns.

## Margin estimate: corner-consistent arcs (Lean `decide` on the arithmetic; the route numbers are assumptions)

bdc minimum loop, with `N` = the mux's DELAY:
- `N + 4` O6 arcs: ctl bd_c2n, uj1, uor, N LUT1s, server node;
- `N + 4` hops: za→ctl, ctl→uj1, uj1→uor, uor→dly1 … dlyN→server.

The z_ack→uxa wire is on both sides and cancels at one corner if rise = fall.
H_RF_ASYM is unmeasured; an asymmetry adds `fall − rise` of that wire to the
left-hand side. The uxa side is one O6 arc plus uxa's own feedback hop. Arcs
come from prjxray (B-arb-corners):
- the loop uses the corner's MIN column: SLOW_MIN 100 or FAST_MIN 45;
- uxa uses the same corner's MAX column: SLOW_MAX 124 or FAST_MAX 56.

Rise and fall are never mixed across corners. Routes:
- slow corner: the build's 434 ps minimum hop and 945 ps maximum (taken as
  uxa's feedback);
- fast corner: scaled by the f1_compare wire ratios.

Guarded means `1.155·D ≤ 0.772·L` (`GUARD_HI`, `GUARD_LO`).

| case | L (loop, min) | D (uxa, max) | raw | guarded |
|---|---|---|---|---|
| SLOW, N = 0 (`slow_N0`) | 4·(100+434) = 2136 | 124+945 = 1069 | +1067 | +414 (pass) |
| FAST, median ratio 0.55, N = 0 (`fast_med_N0`) | 4·(45+239) = 1136 | 56+520 = 576 | +560 | +212 (pass) |
| FAST, adversarial (loop hops p10 0.37 = 161, feedback p90 0.82 = 775), N = 0 (`fast_adv_N0_fails`) | 824 | 831 | **−7** | −324 |
| same, N = 2 / N = 3 (`fast_adv_N`) | 1236 / 1442 | 831 | +405 / +611 | **−6 (fail)** / +154 (pass) |

Reading:
- With zero routing the race is not close: a loop of `(N+4)·45` against `56`.
  **The margin is set by routing.** The sum of the loop's hops competes with
  uxa's own feedback route, which on this fabric leaves the site and is not
  short (bd_link's header cites ~700 ps feedback wires).
- With the DELAY placeholder of 12, the margin is several ns.
- If tighten.py cuts the mux's DELAY to 0–2 links, then in the adversarial
  fast-corner estimate the guarded margin is negative. In that case
  **H_MUX_RTZ must become a routed check.** It is cheap: one inequality per
  mux input acknowledge, built from SDF arcs and nets that tighten.py already
  reads.

The adversarial row combines per-wire fast/slow ratios from the extremes of
the observed distribution. It is pessimistic, but it is not a corner mix: the
ratios are a per-wire property within one corner.

## What did not work / not done

- Tightness of the environment-level bound is not proved: no closed-form
  environment trace in which every stage takes its minimum delay. It is argued:
  transport delays at the minimum are a legal `Causal`/`WinDelay` behaviour, and
  `rtz_counter` then applies with `w = Lmin + wux − Wux`.
- The environment stages (`H_CTL`, `H_DLY`, `H_SRV`) are hypotheses in
  `Causal` form. For bd_link, `floop_causal` discharges them given that the
  cell has settled. The bd_c2n instance and the delay-line composition
  (`winDelay_comp` N times) are not written out.
- Not modelled:
  - the runt band between `w < D` and inertial loss (involution or analog
    regime);
  - per-pin LUT delays (CElemTiming's caveat);
  - X values;
  - the x client's response to a runt. The "spurious acknowledge" story above
    is the Lib3 argument, not re-proved here.
- Found while reading, not studied: bd_link's header says req_out LEADS
  data_out by about 152 ps. With the select coming from a bd_link, the
  `ctl_req` pin can rise before `s` settles at uj0/uj1. That is Lib3's
  H_BUNDLED_S_PIN, and it is worth a routed check of its own.

## Verdict

**Works.**
- The exact cell-level inequality is H_RTZ (`te + dlmax + dwmax ≤ tr`). It is
  proved sufficient, and shown exact for fixed delays by an all-parameter
  counter-trace (oscillation) plus an inertial "fall lost" trace.
- The environment-level form is proved as a trace-level chain through the real
  uj1/uor INITs and named environment hypotheses.
- bd_merge has no analogous race beyond the generic H_ENV_LATENCY (Lib3
  confirmed).
- The race is reachable in bdc's emitted configuration: a loop-header mux with
  its select from a control_merge index through a bd_link.
- The margin is large at the DELAY placeholder. It may be negative at the fast
  corner if DELAY is tightened to 0–2.

Effort to finish: about 1 day.
- Write out bd_link as the `H_CTL`/`H_SRV` instance.
- Write the closed-form tight environment trace.
- Add the check to tighten.py: about 0.5 day, outside formal/.

What it buys: a missing timing rule for bd_mux, bdc_muxn and (via 7h)
bd_arbiter acknowledges. It also gives the header of `cells/rtl/bd_mux.v` the
assumption it does not state.

## Fidelity

- **LUT** (uxa, uj1, uor): a binary function of the REAL INIT through `lutB`,
  lumped delay window `[dlmin, dlmax]`. No X, no runt shaping, no per-pin
  delays.
- **Feedback** (uxa, uj1): a routed wire with its own delay window; no
  instantaneous feedback.
- **Wires**: window channels. The z_ack→uxa wire is ONE channel carrying both
  edges.
- **Environment** (control sender, delay line, server): event-form minimum-delay
  causality only (`Causal`). Their maximum delays and their own hazards are not
  modelled.
- **Inertial**: a modelling alternative, used only for the "fall lost" trace.
