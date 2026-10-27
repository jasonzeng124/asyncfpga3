# C-8b: Kahn determinacy and the gcd loop (track 8, composition: dataflow)

Status: IN PROGRESS (skeleton written first so a dead session leaves something).

Plan: abstract LTS determinacy (diamond => unique terminal state, bounded run
length) -> token dataflow semantics (FIFO channels, nodes fire nondeterministically)
-> diamond for graphs of deterministic nodes with one producer / one consumer per
channel -> gcd loop graph (the C kernel's bb9-bb11 loop) -> output = C loop = Nat.gcd.

Source: the gcd C kernel is not in kernels/ (it is Dynamatic's integration-test);
its CF/handshake MLIR is in cloud/fixtures/frontend/gcd/comp/. It is BINARY gcd
(Stein), not Euclid: transcription in cells/hw/uniform_oracle.py k_gcd.

## progress
- KahnLTS.lean (abstract diamond => terminal_unique, no_divergence): checks.
- Kahn.lean (FIFO token semantics, Node with Kahn-monotone firing, WF = unique
  producer/consumer, wf_diamond, wf_determinate, node library strict/op1/op2/
  fork/branch/sink/mux, merge counterexample merge_not_determinate, merge_not_wf): checks.
- next: KahnGcd.lean (graph of the C loop bb9-bb11, cLoop, gcdC = Nat.gcd).
- KahnGcd.lean: checks (gcdC_eq, cLoop_gcd, G_wf, dataflow_eq_cLoop, dataflow_gcd).
- KahnGcdCM.lean (control_merge header, Inv = one control token): checks.
- KahnBounded.lean (capacity-bounded channels, wfB_diamond, cap-1 gcd): checks.
- Wip/C8b/sim_two_invocations.py: two invocations through the control_merge
  graph -> output ORDER is schedule-dependent ((1,7) vs (7,1)); values stay right.
- trying: nested strip loop (bb11) as a real inner dataflow loop.
