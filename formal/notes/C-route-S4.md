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

Next steps for C (in order):
- Non-vacuity: a Lean witness behaviour of `circuit DecodedPS.net DecodedPS.boundary` under Env (n = 0): a consistent
  power-up assignment under rst = 1 (latches and arbiter states chosen), then the event-driven run of the reset
  release with fixed admissible delays (f i t = t - d_i); GateOK per gate is a finite check around its transitions
  (A's WitCut/V9V4c approach; expect a multi-hour chunked build).
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
