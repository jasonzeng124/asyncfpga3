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

## Results
(see JOURNAL-C, 2026-11-06)

## What it does not cover
The timed behaviours (that a behaviour of the circuit is a run of this abstract machine needs the
switch obligations, settle windows and BO_f), the data values (token level), liveness under timing.
