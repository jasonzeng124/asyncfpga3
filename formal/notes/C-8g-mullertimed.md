# C probe 8g: the gate-level Muller chain under bounded delays

## Verdict

**Works for n = 1, 2, 3 stages; for general n it works with effort (2 to 4
days, see below).** H_FB_BEFORE_INPUT, which 8c assumed, is now derived
from delay bounds:

- **Sufficiency.** Take every node of 8c's real `bd_link` chain: the
  `bd_c2n` LUT6, the LUT1 req path, the ack route, the free O→I2 feedback
  route, and the source and sink. Make each one an inertial channel with its
  own bounds `[lo_i, hi_i]` after its real LUT function. Then, if

      hi(f_k) < lo(w_k) + lo(c_{k-1}) + lo(b_{k-1})     (pin I0 loop; k = 0: lo(w_0) + lo(src))
      hi(f_k) < lo(b_k) + lo(c_{k+1}) + lo(w_{k+1})     (pin I1 loop; k = n-1: lo(b_{n-1}) + lo(snk))

  holds for every stage k, every timed trace is a run of 8c's rt semantics.
  Hence the trace has the four-phase protocol on every link, token order,
  and no glitch on any node (no excitation is ever withdrawn).
- **Necessity.** When the I1 inequality fails, there is a concrete inertial
  trace with every delay inside its interval, using 11b's numbers, that
  breaks the protocol and glitches. This lifts 8c's `free_hazard_n1` to time.
- **The shipped cell.** With 11b's independent fast-min/slow-max bounds, the
  shipped cell does **not** meet the inequality in general. Whether it holds
  depends on placement and must be checked per route (see "Numbers").

Everything is core Lean. There is no sorry, axiom or native_decide. The
axioms used are propext, Classical.choice and Quot.sound.

## What checks

    cd /home/user/asyncfpga3/formal && ./check.sh Formal/Net/MullerTimed.lean \
        Formal/Net/MullerTimedInst.lean Formal/Net/MullerTimedCx.lean
    # -> [audit] 724 declarations checked, [check] OK  (final run, all three files, current versions)

Also checked directly (axiom listing and the n = 4 eval):

    cd formal/lean && export PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$PWD/.lake/build/lib/lean
    ../slot.sh lean Wip/C8g/Axioms.lean      # #print axioms of every main theorem; #eval checkT 4 = true

All of these pass. Cost: `checkT_3` by `decide +kernel` takes about 42 s
wall. The memory is moderate; 8c's whole `MullerSI` needs about 6 GB.

## Files

- `formal/lean/Formal/Net/MullerTimed.lean` contains everything generic in n:
  - the timed semantics;
  - the loops (`guards`), `level` and the certificate checker `checkT`, with
    `checkT_sound`;
  - the timing lemma `fb_settled`;
  - the bridge `timed_good`;
  - the consequences;
  - `FbBound`, the explicit inequality.
- `formal/lean/Formal/Net/MullerTimedInst.lean` contains `checkT_1/2/3` by
  `decide +kernel`, plus the n = 1, 2, 3 corollaries built on 8c's
  `rt_good_n`.
- `formal/lean/Formal/Net/MullerTimedCx.lean` contains:
  - the fixed-delay inertial simulator, proved to produce timed traces;
  - the converse witness;
  - the boundary function hazard;
  - the non-vacuity witness.
- `formal/lean/Wip/C8g/Axioms.lean` contains the axiom listing and
  `#eval checkT 4`.

## Theorems (namespace `Formal.Net.MullerTimed`)

Generic, for any n:
- `checkT_sound`: `checkT n = true → Cert n`.
- `fb_settled`: H_FB_BEFORE_INPUT, derived. It assumes the trace is an rt
  run up to t and the loop inequality holds. Then, if a pin driver of `c k`
  changes at t, the feedback has caught up: `f_k = c_k` at t.
- `timed_good` / `timed_reach` / `timed_enabled` / `timed_step_run`: the
  bridge. Given `Timed`, `Cert n` and `FbGuards`, every timed state is
  rt-reachable, and every ps, serialized, is an rt run.
- `timed_protocol`, `timed_token_order`, `timed_hazard_free`: these assume
  8c's `Good .rt n` invariant.
- `FbBound.guards`: the explicit inequality implies the guard form.

Instances:
- `checkT_1`, `checkT_2`, `checkT_3`, `cert_1..3`.
- `timed3_reach`, `timed3_step_run`, `timed3_protocol`,
  `timed3_token_order`, `timed3_hazard_free`.
- `timed1_protocol`, `timed1_hazard_free`, `timed2_protocol`,
  `timed2_token_order`, `timed2_hazard_free`.

Converse and witnesses:
- `sim_timed`: the fixed-delay inertial simulation, for any n and delays, is
  `Timed n d d`.
- `inertial_widen`, `Timed.widen`: bounds can be widened.
- `cx_timed`: the witness is `Timed 1` within the 11b-shaped intervals.
- `cx_violates`: only the sink-side inequality fails.
- `cx_events`: the states the witness passes through.
- `cx_protocol_broken`: `RecvStep` fails on (src, w0) at 1192 ps.
- `cx_glitch`: the source's excitation is withdrawn at 1193 ps.
- `boundary_function_hazard`.
- `ok_timed`, `ok_bound`, `ok_protocol`: non-vacuity.

## Model

- **Network.** These are 8c's nodes for an n-stage chain:
  - `src`, the active source;
  - `snk`, the passive sink;
  - per stage: `c k` (`bd_c2n` LUT6, INIT `0x00B200B200B200B2`, through B's
    `lutB`), `b k` (req path: LUT1 `2'h2` plus its routes, lumped), `w k`
    (ack route) and `f k` (the O→I2 feedback route, a FREE wire).

  The gate function is `nextVal .free n`, which is the physical network. I
  proved it equal to 8c's `.rt` function (`nextVal_free_rt`); rt only adds
  the scheduling restriction.
- **Timed trace** (`Timed`). `x : Nat → Nat` is a bitmask per ps; reset is
  all 0. Every node `i` obeys `Bridge.Inertial (lo i) (hi i)` from its gate
  value to its output. That is 8d's channel:
  - cause: a change delivers a value the gate held for the last `lo` ps;
  - settle: a gate value held for `hi` ps is on the output.
- **Loops (`guards`).** Each input pin of `c k` has one loop: the chain of
  nodes through which `c k`'s own transition causes that pin's driver to
  move. `level` counts how many loop nodes have fired since `c k` did. It
  is read off the state through a per-node polarity: done iff the node equals
  `c k`, or differs from it.
- **Certificate (`checkT`).** The checker runs a BFS over the rt-reachable
  states, checks closure, and then checks four things on every state:
  - (EP) enabledness persistence, i.e. persistence relative to the RT
    constraint. Two enabled nodes stay enabled after either fires, so a ps in
    which several nodes change can be serialized in any order. This is the
    bridge variant that the brief asked for: 8d needs plain persistence,
    which the free network lacks.
  - (E) When `c k` is enabled, no loop node is excited, and the level after
    `c k` fires is 0.
  - (M) While `f k` is in flight, the level only moves by +1, and only when
    the next loop node fires.
  - (X) While in flight, if loop node j is excited then level ≥ j.

  Statically, it also checks that every pin driver restricted by
  `Muller.allowed` ends some loop.
- **Proof of `fb_settled`.** Let τ be the last change of `c k` before t.
  - Inertial cause shows `f k` cannot leave its old value in [τ+1, t], so it
    is in flight there.
  - Settle gives t ≤ τ + hi(f).
  - By (E), level(τ+1) = 0.
  - Induction on j: to reach level j+1, loop node j must fire (M). That node
    was excited throughout its inertial window, which starts after τ by (E),
    and at the window's start the level was already ≥ j (X). So
    level j+1 is reached no earlier than τ + 1 + Σ_{i≤j} lo.
  - Hence the driver fires no earlier than τ + Σ lo, which together with
    t ≤ τ + hi(f) contradicts hi(f) < Σ lo.

  The proof is generic in the loop and in n.
- **Negative controls on the checker** (`#eval`, scratch):
  - Swapping the loop order fails for every stage.
  - Appending a non-causal node (`src`) to an inner loop fails.
  - Dropping a node, e.g. `[w_k, b_{k-1}]`, passes. That is sound, but it
    certifies a WEAKER inequality (a sub-chain has a smaller Σ lo). So the
    certified loops are exactly 8c's informal path inequalities, and the
    checker cannot accept a loop that is not causal.

## Numbers (11b, `formal/notes/C-11b-fasm.md`, `Formal/Net/Fasm/CePairS*.lean`)

These are the per-pin route bounds `(fast_min, slow_max + Elmore)` in ps,
taken over 4 seeds of the routed `ce_pair` test design (which is not a
`bd_pipe`):

| route | values |
|---|---|
| C-element O→own pin (8 cells) | (76,288) (213,709) (71,283) (209,690) (261,863) (213,708) (209,690) (125,431) |
| C-element→C-element (q1→q2, 4 seeds) | (262,859) (72,287) (218,718) (72,284) |
| LUT6 / LUT1 | [45, 124] |

Take an inner stage with independent bounds. The loop sum is
lo(w) + lo(c) + lo(b) = r_w + 45 + (r_1 + 45 + r_2), where the r's are route
lower bounds, so Σ lo = 3r + 90.
- With the smallest observed route (72 ps), Σ lo = 306. Then only feedback
  routes with hi ≤ 305 pass: (76,288) and (71,283). The brief's
  **[213,709] fails**.
- With 11b's seed-1 inter-cell route (262), Σ lo = 876, and [213,709]
  passes. (261,863) passes only if 3r ≥ 774.
- The end-of-chain loops use the environment's response: lo(b)+lo(snk) and
  lo(w)+lo(src). With b = route + LUT1 + route at the 72-ps minimum
  (189 ps) and a 45-ps sink LUT, the sum is 234, which is far below 709.
  That is exactly `cx_violates`.

**Answer: the shipped cell does not meet the inequality by construction.**
It holds only when the three neighbour-loop routes sum to at least
hi(f) − 89 ps (≥ 620 ps for [213,709]). That is placement-dependent, and
nothing in the flow checks it (8c: `--ignore-loops`). It is a natural row
for the verified timing checker (track 10), applied per route at every
`bd_c2n`.

Caveat: the comparison mixes corners, putting the feedback's slow_max
against the others' fast_min, as 11b's `pinDelay` provides. A
corner-consistent check would compare slow_max(f) with slow_min(loop) and
fast_max(f) with fast_min(loop). prjxray has all four corners, but
`pinDelay` keeps two. Adding slow_min to fasm2lean is a one-line change
(not my file), and it would very likely make the inner stages pass.
Larger SDELAY (longer delay lines in b) makes the I1 loop longer and helps.

## The converse witness (`MullerTimedCx.lean`)

- **Delays.** n = 1 with these delays:
  - src 800;
  - snk 45;
  - c0 45 (11b LUT);
  - b0 187 = 71 + 45 + 71;
  - w0 71;
  - f0 709 (11b slow max).
- **Intervals.**
  - c0 [45,124] and f0 [213,709] are 11b's;
  - w0 is [71,709] and b0 is [187,1542];
  - the environment is snk [45,124] and src [800,2000].

  The route intervals are illustrative, bounded by 11b's observed routes.
- **Timeline.** src↑ 800, c0↑ 845, w0↑ 916, b0↑ 1032, snk↑ 1077. At 1077 the
  LUT sees I0 = I1 = 1 (hold) while I2 still reads 0, because the feedback is
  due at 1554. The LUT recomputes 0 and c0 falls at 1122: the token is
  retracted. The feedback pulse (277 ps < 709) is swallowed. w0 falls at 1193
  while req is still high, and the protocol breaks on the input link. The
  source had been excited since 916 to drop req; that excitation is
  withdrawn, so `ack_in` carries a runt.
- **What is kernel-checked in this timeline.** Only the states in
  `cx_events` are kernel-checked: at 1077 snk = c0 = 1 and f0 = 0; at
  1192 src = w0 = 1; at 1193 src = 1 and w0 = 0. The intermediate times
  (c0 falling at 1122, the swallowed feedback pulse) come from working the
  delays by hand. They are consistent with the checked states, but no
  theorem pins them. The `#eval` timeline dump was truncated, so it does not
  confirm them either.
- **Proof method.** These are kernel evaluations (`decide +kernel` with
  maxRecDepth 100000) of the simulator. `sim_timed` proves the simulator's
  output is an inertial timed trace, generically.
- **Boundary.** At hi(f) = Σ lo, I1 and I2 arrive in the same ps. The atomic
  LUT of the timed model sees no glitch, but (1,0,0)→(1,1,1) crosses the
  function hazard (1,1,0) ↦ 0 of the real INIT (`boundary_function_hazard`).
  So the strict inequality is the right one for a mux-tree LUT.
  Equality is not proved either way in the timed model; it would need
  B's Kleene LUT in time.

## Hypotheses and fidelity of each primitive

- **H_INERTIAL** (every LUT, route and environment node is 8d's inertial
  channel `[lo, hi]`).
  - The proof uses the lower bound `lo` (cause window) on loop nodes, and
    the upper bound `hi` (settle) on the feedback only.
  - It is stronger than 8d's `NoOvertake`, because the loop argument needs
    `lo`. Pulse filtering itself is not used for loop nodes, only the
    statement that a change was preceded by `lo` ps of excitation.
  - Test: in GLS, a pulse-train through LUT + route at both corners, checking
    that output edges lag their cause by ≥ lo; on the board, an injected
    pulse in a ring.
  - Fidelity: plausible for a buffered route. Pulse shrinking (involution)
    is not modelled.
- **H_LUMP** (the req path b_k = route + LUT1 + route is ONE inertial channel
  with summed bounds).
  - A cascade of inertial channels is not exactly one inertial channel. The
    lumped lo is the true minimum latency, which is what the proof uses.
  - Test: GLS of the routed `bd_delay`.
- **H_ATOMIC_LUT** (a LUT is one Boolean function of its pins at one ps, as
  in 8c/8d).
  - Multi-pin changes inside a ps are not resolved through the mux tree.
  - In the rt runs this matters only at the boundary noted above, and for
    the concurrent I0/I1 change 8d discussed.
- **H_RESET_CLEAN** (`x 0 = 0`; reset release not modelled), as in 8c.
- **H_ENV** (the source and sink are idealised four-phase parties with
  inertial response `[lo, hi]`).
  - `lo(src)` and `lo(snk)` enter the end-of-chain inequality. That is the
    timed analogue of B's H_ENV_LATENCY (`CElemTiming.c2_four_phase`),
    which reads `dlmax + dwmax ≤ dlmin + E`; here the C-element's own LUT
    delay is part of the loop.
- **Discrete time.** One tick is 1 ps (Nat), as everywhere in shard C.
- **Delays are independent per node.** There is no corner correlation.
  Correlation would only help (see the caveat in "Numbers").

## What does not work / open

1. **Generic n.** All theorems are generic given `Cert n` (from
   `checkT n = true`) plus 8c's `Good .rt n`.
   - Kernel-certified: n ≤ 3.
   - n = 4: `#eval checkT 4 = true`, uncertified. The in-kernel BFS of 6076
     states runs out of memory (8c), and the checker would need 8c's chunked
     literal certificate (`Wip/C8c/Rt4Cert.lean`, about 25 min kernel).
   - All n: a stage-cut induction is NOT done. It needs a hand invariant of
     the rt-reachable set for general n (each stage's local phase,
     `(c_{k-1}, b_{k-1}, w_k, c_k, f_k)` patterns). From it, (EP), (E), (M)
     and (X) are local, because every loop spans only stages k-1..k+1.
     Estimate: 2 to 4 days. The local structure suggests a 3-stage window
     argument would do: every check involves nodes of at most stages
     k-1, k, k+1 plus their pins.
2. **Equality case** hi(f) = Σ lo: see above; it needs a Kleene timed LUT.
3. **Corner-consistent numbers**: these need slow_min in `pinDelay` (11b's
   tool).
4. **A real `bd_pipe` route**: 11b's design is `ce_pair`, not a pipe. Running
   fasm2lean on a routed `bd_pipe` would give the actual r_w, r_1, r_2 and
   feedback per stage, and the inequality could then be decided per seed.

## What it buys the project

- The only timing condition of the default link control is now a theorem,
  with an exact, machine-readable form (`guards`/`loSum`: one inequality per
  pin per stage), and it is proved necessary by a concrete witness.
  This is a candidate row for B's `cell_constraints.json` and for the
  verified checker: `hi(fb route) < lo(ack route) + lo(LUT6) + lo(req path)`
  at every `bd_c2n` in a pipe.
- Bridge pattern for non-persistent networks. It needs persistence relative
  to an RT constraint, plus a certified causal-loop level argument. The
  argument is generic in the network's loops, so it should carry over to
  other C-element networks (forks, joins, `bd_link_dctl`) by listing their
  loops.
- The numbers say the cell is not safe by construction. Whether it is safe
  depends on routing, and with 11b's minimum routes it can fail. This
  argues for adding the check to the flow before relying on `bd_pipe`
  margins.

## Surprises

- The checker accepts every causal sub-chain of a loop. So the guards are not
  forced to be the full neighbour loop: dropping a node certifies a weaker but
  still valid inequality. The full loops are the strongest ones it accepts;
  wrong or non-causal loops are rejected.
- Enabledness persistence holds in 8c's rt semantics: kernel-checked for
  n ≤ 3, and `#eval` gives true for n = 4. The free network is not
  persistent, yet the rt-restricted one is, even for enabledness. That is
  what makes the "persistence relative to RT" bridge work.
- With 11b's smallest routes, the sink-side loop (234 ps) is shorter than
  every routed feedback except the in-slice ones (71-76 / 283-288 ps).
