# Shard C: the route from the decoded circuit to the token graph (S2/S4), as of 2026-11-02

What exists (all Lean-checked, standard axioms):
1. `Formal.Net.GcdHw.Seq.gcd_hw_seq` (token level, S5): bdc's gcd_hw graph closed with a sequential env
   returns `ps.map gcd`, in order, for any number of pairs, every schedule; no deadlock, bounded.
2. `Formal.Net.CViewPS.collapsed` / `view_complete`: every one of the 19,878 logic gates of THE target's
   circuit reads its sources through its routing with a composite delay that is a sum of Adm delays (CGateOK);
   the copy map is kernel-checked against `DecodedPS.net`.
3. `Formal.Timing.SpecLoop`: on CGateOK gates, settle windows (`cgate_stable`), forced outputs
   (`cgate_force`), storage nodes holding a confirmed value through their routed loop (`cgate_hold`) and a
   clean switch when the forcing lasts at least the loop's Σdmax (`cgate_switch`).
4. Older, model level: CapNet (bdc's graph as 465 cell-level channels) refines the token graph for ONE pair
   under H_CELLS (Ops gate models), H_BUNDLE, H_START_ONCE (`KCap.kernel_circuit_safe`).

Added later on 2026-11-02 (all Lean-checked unless marked):
5. `CViewPS.comb_ranked`: every loop of THE target passes through one of its 4,597 storage LUTs (acyclic rest,
   depth 96). `SpecLoop`: `cgate_cause` (no spontaneous change), `light_cone` (changes travel no faster than the
   fastest delay path), `settle_ranked`/`settle_value` (once storage+env are quiet, the logic settles to its
   zero-delay values), `quiet_forever` (a quiet circuit with a quiet env never moves again);
   `CViewPS.settle_PS`, `quiet_PS` instantiate them on THE target.
6. Simulation (untrusted, tools/cview/hufsim.py): the Huffman abstraction (storage nodes + zero-delay logic) is NOT
   speed-independent (wrong gcd), but with "data latches fire before other storage nodes" it gives the right
   results, the same firing count on every order and no persistence violation (11 pairs x 6 orders). So the
   intended proof shape is: SI control network + bundling (latch before control) + settle windows + per-node
   switch obligations.
7. tcheck on THE target's route: every rule row passes at both consistent corners; binding row rule A umux21,
   κ* ≈ 0.080 at g = 1 (a sufficient-condition margin).

8. THE theorem's conclusion for zero pairs: `CViewPS.correct_n0` (any p, delay hypotheses), `correct_n0_p1`
   (g = 1, κ = 0, R ≥ 353,248 ps), `correct_n0_all` (every g > 0, κ < 1, R ≥ ⌈(1+κ)g⌉·353 ns), via the 414-node
   idle island (`island_PS`), no H_ARB, no SeqEnv.

9. Witnesses (Lean-checked behaviours of the decoded circuit): `witness_n0` (n = 0 hypotheses satisfiable) and
   `w1_hyps_and_correct` (a run computing gcd(12, 18) meeting every NetCorrectSeq hypothesis, T ≥ 220 ps, and
   Correct). Tools: tools/cview/witn0.py, witn1.py, gen_wit0.py, gen_wit1.py.

Next steps for C (in order):
- n ≥ 1: the island shows the control returns to the same idle island between pairs (simulation: only arbiter
  sites differ, and the island ignores them). The per-pair argument needs the handshake-level dynamics of the
  ~412 control storage nodes (latches first): the cell-level composition of S4.

What the structure of THE target forces (tools/loops/loops.py): after cutting all 4,597 storage self-loops
and all pins outside their INIT support, the circuit still has one strongly connected component of 86,684
nodes (control + data of the loops) and 128 data rings (one bit of a loop variable round bdc's 3-stage loop
link and header mux). So no static (topological) certificate covers the kernel: obligations must be stated
per event (per handshake phase), which is what rules A/E/F/J do informally.

The missing pieces, in order:
- (a) Cell instances on the collapsed view: group the logic gates into bdc cell instances (bd_link ctl/latch,
  bd_mux, bd_merge/arbiter, delay chains, compute units) and check each group's INITs and internal wiring
  against the frozen library (an LVS of the collapsed view; 11g did this for BQ#1 at instance level).
- (b) Per cell type, a Spec-level handshake theorem (shard B, S3): from CGateOK of its gates and its
  storage nodes' `cgate_switch` obligations, the cell's ports follow its four-phase spec. The obligations are
  inequalities between composite delay sums (path races), evaluated per instance on the collapsed arcs.
- (c) Channel level: each bd link is a bundled channel; the bundling obligation (data settled before the
  request arrives, held until the ack) is a `cgate_stable` window per data bit, again a path-sum inequality.
- (d) Composition (C): (b)+(c) give, for every behaviour, a handshake-level trace of the cell network;
  that trace is an execution of CapNet's channel model, which refines the token graph (4, extended from one
  pair to the sequential env using 1).
- (e) Liveness (S6): the env offers a pair only after the previous result (SeqEnv); under the obligations,
  every enabled handshake completes within a bound (no runt-oscillation: `fb_runt_oscillates` shows this is
  exactly what the switch obligations exclude).

## Update 2026-11-06 (shard C)
- Proved (core Lean): `Net/Keller.lean` (persistent + commuting moves: one terminating run fixes the end
  state, the firing multiset and a bound on every schedule) and `Net/WinInv.lean` (a windowed invariant
  checked locally holds in every reachable state; pairwise persistence from a join check).
- Found (simulation, tools/huff): the latches-first abstract machine of THE target is NOT persistent under
  an env with arbitrary delays: falling excitations of mux input-ack C-elements (12 muxes) and of three
  arbiter grant C-elements (ucontrol_merge{4,6,10}.uarb1.ua1) are withdrawn; results stay correct. With 30
  relative-timing orders "c fires before b" (tools/huff/out_rt_pairs.txt) no withdrawal is seen in
  ~10^8 moves. So the proof shape is: SI control + latches first + 30 RT orders (timed race obligations)
  -> Keller on the RT machine -> one checked run decides every order.
- Not working: per-node windows for WinInv (too coarse; 395/412 nodes flagged); the single-chain race
  estimate (tools/huff/rtmargin.py; unsound/too crude). Next: cell/channel-structured windows; a
  time-separation bound for the 30 orders; adversarial timed simulation (tools/huff/simadv.py).

## Update 2026-11-07 (shard C): where a positive theorem can live
- Upper end of the (g, κ) frontier (fast corner, one pair (1071, 462), R ≥ 400 ns via `Net/Stretch`): THE statement
  fails at κ = 0.44 (g = 1) and at g = 1.6 (κ = 0), with and without H_RUNT(20) (simulation + independent checkers;
  Lean CexR44 / CexRg16 building, see JOURNAL-C). The binding mechanism is a feedback race of one link stage-0
  C-element (SLICE_X32Y45.A6): the stage's acknowledge returns before its own rise has gone round its routed
  feedback. Shard B's RaceTablePS row for that node (sufficient: κ ≤ 0.415 / g ≤ 1.56) is within 0.025 / 0.03.
- So a positive theorem for n ≥ 1 must be stated at (g, κ) inside B's bound, and its S4 proof must use B's race
  rows as the per-cell switch obligations (the `cgate_switch` premise of route step (b)); nothing weaker survives.
- Single-pin adversary sweeps at κ = 0.40 (412 control nodes x pins): 1,315/1,316 correct; the one failure is a
  runt ring through arbiter 0 that needs H_ARB with T ≥ 7.2 ns and disappears under H_RUNT(20). Data bundling
  (every latch data cone slow, all control fast) stays correct up to κ = 0.68; it gives a wrong value at 0.8.
  So, in simulation, the control races (B's table) are what bind, not bundling.
- Tools for future refutations: `Net/Stretch` (any reset length), `Net/Periodic` (never-quiet runs that repeat),
  per-arc slow lists in the witness checks (CexR44/CexRg16 KBase/RBase), tools/huff/{hazsweep, bundadv, adv}.py.

## Update 2026-11-08 (shard C): the occurrence-net route (proved generic pieces, and the plan)
Proved today (core Lean, standard axioms; JOURNAL-C 2026-11-08):
- `Net/OccNet`, `Net/OccNetDec`: one partial order of events (a certificate, e.g. the causal order of one recorded
  run) plus a check that is LOCAL per node (over bound-respecting count vectors of the node's dependency list)
  decides every interleaving of an abstract machine: reachable states = ideal states, every maximal run fires
  exactly the certificate's events and ends in its final state, no deadlock, bounded length. Boolean checker.
- `Net/TimedOcc`: the same certificate and local check, plus separations along causes (`SepOK`) and pairwise skew
  obligations per gate (`TO`: if b's pin can be read later than a's, the certified separation must cover
  hi_b - lo_a), make every bounded-delay behaviour (per-pin transport reads, Spec's GateOK shape) follow the
  certificate (`timed_follows`, `timed_prop`), and fire every event, then go quiet (`gate_fires`, `timed_live`).
  The feedback race (B's race rows), isochronic forks (rule A) and the RT orders of 11-06 are all TO rows or
  extra cause edges; the timing obligations are generated from the certificate and complete by construction.

The plan from here to THE theorem (each step generic first, then instantiated):
1. **Data layer (Kleene phase nodes).** Datapath gates glitch (concurrent latch updates), so they cannot be exact
   event nodes. Model each data node by epochs: a value per epoch and a stable window [τ(A)+a, τ(B)+b) relative to
   control events A, B; between windows it is X. Control gates read data in Kleene semantics (bd_steer: req & s is
   0 when req = 0 whatever s is); a control gate's local check must be definite on every tuple where its data
   inputs may be X, and per (gate, data input) a guard claim (data stable whenever the gate is sensitive) reduces to
   two separation inequalities (Sep lower bounds only). The data windows themselves are checked gate by gate
   (inputs' windows + Σmin/Σmax of the pin ⇒ output window), again needing only Sep lower bounds.
2. **Spec bridge.** CGateOK (collapsed view) gives TBeh's read model; corner c fixed per behaviour, lo/hi per
   corner, TO checked at c = 0 and c = 1 (affine in c); quiet start from the idle island (`correct_n0` route).
3. **One pair** (e.g. (12,18) at (g, κ) = (1, 0)): generate the certificate (events, causes, L, Sep, D, data
   epochs) from one simulated run and discharge every check by `decide` in chunks. This is the first theorem
   "for every admissible delay the target computes gcd(12,18)".
4. **All pairs.** Periodic certificates: the run is a concatenation of loop-iteration segments of finitely many
   types (branch outcomes); the local checks only see a bounded neighbourhood of segments, so they are checked
   on all short windows of segment types; data values symbolic per epoch, tied to the token-level
   `gcd_hw_seq` by the datapath's zero-delay function.

### Status at 08:2x (2026-11-08)
Generic chain now complete for ONE input pair (all core Lean, standard axioms): `OccNet` (abstract), `TimedOcc`
(exact nodes), `TimedOccX` (+ data claims), `TimedOccRT` (+ RT edges justified by lower/upper separations),
`TimedBridge` (CGateOK at corner c ⇒ the read model). Safety (`timedR_follows`) and liveness (`timedR_live`).
Abstract-machine evidence (tools/occ, untrusted): with 36 RT orders the local check passes on 3 pairs.
Gaps, in order:
1. Instance for one pair: generator for CP/CF/L/Sep/Up/D/claims/guards from one simulated run, then Lean checks.
   Size: the abstract check visited 1.4-2.7 M local ideals with latches as events; in TimedOccRT latches are data
   claims, so the exact event sets are control-only and smaller. Kernel `decide` cost still unknown.
2. Environment: `envEn` is state-based; SeqEnv and "n pairs offered" need counts. Plan: virtual exact nodes
   (a phase bit "out0 handshake completed since the last request", a pair counter) defined from the Spec
   behaviour, so the theory stays as is.
3. Quiet start: exact nodes constant on [t0 - H, t0] after reset (from the n0 island results) and initial data claims.
4. All pairs: gcd_hw runs Stein's binary gcd (shift loops, compare/subtract loop), so the control path is a word over
   a finite set of iteration types (branch outcomes), length ≤ ~100. Certificates as concatenations of segment
   types; every check is local (bounded lookback), so it suffices to check all short windows of segment types;
   data claims symbolic per epoch, tied to `gcd_hw_seq`'s token-level values. Needs a generic window lemma.

### Instance design note (08:5x): corner-generic certificates
Each behaviour has its own corner c, so the timed net N_c (lo/hi = corner sums, `TimedBridge`) and every numeric
separation depend on c. An instance should therefore store PATHS, not numbers: a separation entry is a path of
(event, pin-route) steps; its value at corner c is the sum of `loC` along it (so `SepOKR`'s forms hold by construction:
extending a path by a cause adds that pin's `lo'`); an upper bound is the same with `hiC`. Every remaining numeric
obligation (TO rows, RT margins `Σlo - Σhi ≥ 1`, claim windows, guards) is an inequality between sums of corner-
rounded bounds, discharged for all c ∈ [0,1] by one rational check at c = 0 and one at c = 1 (`TimedCorner`,
`skew_all_corners`). The Boolean checkers then run once, not once per corner.

### Status at end of morning (2026-11-08): the current chain is `Net/AO/*`
A first Python certificate for THE target (tools/tocc) showed the AND-only chain cannot fit the circuit: OR-causality
(~1,400 control gates fire on the first of two inputs), over-strong skew rows (a = b; a = reader), one global L.
`Net/AO/Occ`, `Net/AO/Timed` (`timedA_follows`, `timedA_live`), `Net/AO/Dec`, `Net/AO/DecT` repair all four and add
the reader's own-history premise (`own_readA`). The older `OccNet`/`TimedOcc*` files stay as checked special cases
(and their toys as non-vacuity evidence of the shared machinery); new instance work should target `Net/AO`.
Re-measurement of the (12,18) certificate against the AO model: in progress (subagent).

### Status at 09:3x (2026-11-08): environment bridge, UpOKA repair, AO measurement
* Gap 2 (environment) is handled by counts, without virtual nodes.
  * `timedA_follows` takes `hEnvE`: an env change at s is an enabled event at the counts of s-1, given the ideal.
    The local check is now demanded only at gates.
  * `AO/EnvHS` derives `hEnvE` from `ReqMoves`/`AckMoves` for four-phase channels.
  * `AO/EnvData` derives the input bus claims (`hEnvC`, also given the ideal) from `EnvIn`'s setup and hold
    clauses.
  * Still open here: the SeqEnv extra causes (out0) of THE target's request events, and the Offered count bound
    (both are per-instance facts).
* `UpOKA`'s previous-event clause may now be met by a separation (prev ≤ e0).
* AO measurement of the (12,18) certificate (tools/tocc/ao.py, untrusted): 601 (c=0) / 282 (c=1) local-check
  failures. They are mostly at readers whose skew rows fail, so L was lowered there. 37 per corner would remain
  even with every row passing. Under diagnosis: real race vs certificate artefact.
* Gap 3 (quiet start): existing `reset_state`/`settle_PS`/`quiet_PS`/`correct_n0` cover much of it. Coverage of
  the certificate's exact nodes, and the 9 arbiter states that reset does not force, are under measurement.

### Status at end of session (2026-11-08 afternoon)
* Lean (all check.sh OK):
  * `AO/Timed`: count-based env moves; `UpOKA` previous event and causes may use a Sep to e0; `hEnvE`/`hEnvC`
    may assume the ideal.
  * `AO/EnvHS`: req/ack four-phase moves imply `hEnvE`.
  * `AO/EnvData`: input bus claims from `EnvIn`.
  * `CViewPS/RIslData`: the reset-island member list. Its check and theorem are in Wip/RIsl, not compiled.
* Control certificate (untrusted, tools/tocc): 0 local-check failures at c = 0/1 for (12,18) and (17,5); one
  structure for both corners.
* Data layer (untrusted): not passing.
  * 46 of 264 guards fail at c=1 for (12,18), plus more at c=0, where the window fixpoint did not converge.
  * They need orderings that pass through environment or arbiter events (R1), or hold orderings at truncated latch
    chains (R2/R3).
  * About 170 adversarial simulations found no data-driven control change and no wrong gcd.
* Next:
  * formulate what upper bound an environment/arbiter event can carry (from Spec's Env/ArbOK) and add it to
    `UpOKA`;
  * trace the R2 latch holds;
  * a monotone window fixpoint;
  * then the instance generator.
