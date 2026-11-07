# Shard C: persistence of THE target's control network without listing its states (2026-11-06)

## Why
Every route from the decoded circuit to NetCorrectSeq for n >= 1 passes through the 11-02 finding
(simulation): THE target's 412 control storage nodes behave as a speed-independent, determinate
network once data latches fire first. To use that in a proof, two things are needed:
1. **determinacy from persistence** (one checked run decides every order): `Formal/Net/Keller.lean`
   (proved: `keller`, `keller_terminal`, `keller_bounded`, `diamond_of_persistent`);
2. **persistence on the reachable states**. Listing the states is out: tools/huff/huffx.cpp found
   40 M distinct states for ONE operand pair before the DFS got past move 911 of ~1,118 (no violation
   in them). So persistence must come from a check that scales with the circuit.

## The check
`Formal/Net/WinInv.lean` (proved, generic): windows W (small variable sets) with allowed tuples R;
`closeOK` per window and move is a finite join check; if all pass and the initial state is allowed,
every reachable state is allowed in every window (`inv_reach`); `persistOK` then gives persistence
pairwise (`persist_of_check`).

## The abstraction checked (tools/huff/winfix.py, untrusted)
Variables: 412 control nodes, env req / pend_ack / out0_ack and a "waiting for out0" bit, and the
32 frontier nodes through which control reads data (23 one-bit data latches: mux select / condition
tokens; 9 pure-data logic nodes: comparator and OR outputs over 32-65 data latches). Every control
node's next-state function is its zero-delay logic cone over these (support <= 14 variables).
Frontier nodes are free inputs, but a frontier node may change only when no reader's next-state
depends on it at that moment: that is the **bundling obligation BO_f** (data stable while control
can see it), assumed by the abstraction and listed for the timing side (S4(c)).
Windows: W_c = {c} ∪ supp(c) per control node, plus one env window.

## Results (2026-11-06; untrusted tools)
- Per-node windows are too coarse: plain and context-consistent closures reach the same 49.5 k-tuple
  fixpoint with 927 flagged (node, mover) pairs on 395 of 412 nodes; concrete walks see 6 k tuples.
- **The machine is not persistent** (random walks with arbitrary env delays, all results correct):
  C-elements at 1 lose their falling excitation before firing: mux input-ack C-elements (uxa/uya of
  umux2..18) and arbiter grant C-elements ucontrol_merge{4,6,10}.uarb1.ua1 (re-enabled by
  ucontrol_mergeN_f). The withdrawn node is not re-excited (`--tri`): the two orders diverge locally
  and reconverge later. So `Keller`'s diamond fails; each site is a runt opportunity whose timing
  must be bounded (B's static race tables give the margins; merge10's is on B's κ* = 0.298 path).
  Trace: tools/huff/out_trace_merge10_ua1.txt.

## What it does not cover
The timed behaviours (that a behaviour of the circuit is a run of this abstract machine needs the
switch obligations, settle windows and BO_f), the data values (token level), liveness under timing.
