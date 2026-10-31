# B-finite-net-bound (probe Belab, 2026-10-31): gcd_hw's gate-level network with pin drivers bound to the netlist

Answer to audit P12b row 22 and SelfAuditB9. File: `formal/lean/Formal/Cells/FiniteNetBound.lean`
(core Lean only; checked with `formal/tools-B/privbuild.py`, see the journal for the run).

## Problem statement

**Question.** B's network theorems (`gcd_hw_safe_fin_net` and relatives) were described as
"links, forks, joins, steers, ORs gate-modelled". The auditor and SelfAuditB9 showed the
hypothesis `FGcdNetOK` never says WHO drives a tied cell's pins: `GPin.drv` is free and the cell
set is free, so a link may take both of its environment pins from fresh pinless cells whose
contract is just "my node is clean". Then "the link's environment is derived from gate models"
is not enforced by the theorem.

**What is now assumed (`FGcdNetOKB`).** Everything `FGcdNetOK` assumes, plus: for every pin of
every tied cell, if the NETLIST determines the cell that drives that signal, the pin's `drv` is
that cell. The netlist (C's generated `opAt`/`prodOf`/`consOf`) determines:
* a request's driver: the producer's link controller, steer branch or 2-input join C-element,
  looking through 2..4-way forks (a fork's request side is a wire);
* an acknowledge's driver: the consumer's link controller, steer acknowledge OR or 2..4-way fork
  C-element, looking through 2-input joins (a join's acknowledge side is a wire);
* nothing (`none`) when the driver is an operator B does not gate-model (mux, muxn, amerge,
  source, sink, wider join, fork tree N >= 5): that side stays a contract.
The steer acknowledge OR's two pins are now also tied to the two branch acknowledge traces
(they were untied in `FGcdNetOK`).

**What is proved.**
* `reqSrc_tied`, `ackSrc_tied`, `tied_pins_ne`: a driver the netlist determines is a tied cell,
  and every tied cell has pins, so its contract is a B gate model, never the bare pinless claim.
* `link_env_bound`: for a link whose two drivers the netlist determines, both of its pin drivers
  ARE those gate-modelled cells. `bound_census` counts, by kernel, how many of the 175 links are
  bound on both sides, one side, or neither (numbers in the journal entry and the file).
* `gcd_hw_safe_fin_netB`: C's gcd_hw safety (every out0 token carries gcd a b) under
  `FGcdNetOKB` plus C's `H_OTHER`, `H_BUNDLE`, `H_CM_FORCED`.

**What it does NOT cover.**
* The proof of `gcd_hw_safe_fin_netB` is the old proof through the forgetful map `toOK`: binding
  restricts the hypothesis, it adds no new derivation. Its value is that the hypothesis now
  means what the earlier prose said, for the links counted as bound.
* NO joint witness. It is not shown that `FGcdNetOKB` and C's hypotheses can hold together on any
  run. On C's unit-delay run chW they cannot (`FiniteNetSrc.chW_steer_unwired`). If they could
  not hold on any run, the theorem would be vacuous; this is open.
* C's `H_CELLS` for the 192 non-link operators remains a hypothesis; B's gate models are used only
  to derive link environments.
* Contract cells may still be pinless; links next to them take that side from a contract.

## The witness: what is needed (plan, not done)

1. **A gate-timed run.** C's operator models are speed-independent (`Steer.lut`: a branch request
   that changes must change to the excitation of the previous tick), so they accept any gate delay
   as long as excitations stay stable. A run where every tied gate is LUT 1 + wire 1 (2 ticks
   channel to channel, links included: C's link `c` := B's node, out.req/in.ack = c one tick later)
   fits B's existing checkers (`FiniteNetWit2Lib`: `celB`/`stB`/`orB`/`linkB`, all at lo = hi = 1,
   wires 1). Uniform time dilation of chW does NOT work: links would need 4 ticks, the other tied
   cells 2. So the run must be re-simulated (C's `tools/capwit/sim.py` with 2-tick tied gates and
   1+1 links), then C's checkers (`kChk`, `heldChk`, generic in the event lists) re-run by kernel;
   `yW_walk` is token-level and should carry over.
2. **The obstacle in B's own specs.** The checkers' soundness lemmas need each pin driver's edge
   function to be the pin's event list for EVERY index j (`hτd`), and each tied spec fixes its
   own edge function for every j (`H_TIMES : ∀ j`). With bound drivers, a driver's edge function
   is the tied cell's `H_TIMES` definition, which beyond the last real edge is not the list's
   default; and along req/ack cycles of tied cells the definitions are mutually recursive.
   Either (a) weaken `H_TIMES`/`hτd` to existing edges (`L c j`) in the specs and their users, or
   (b) define the edge functions by recursion on (edge index, rank of the tied request DAG) and
   prove the checkers under agreement below the edge count. (a) is the faithful fix: edge times
   past the last edge mean nothing physically.
