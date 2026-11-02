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
