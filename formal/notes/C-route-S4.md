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
