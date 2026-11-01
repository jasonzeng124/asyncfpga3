# For research and the owner: THE goal (the gcd_hw bitstream theorem)

Started 2026-11-01 by shard A. Counterexamples to THE theorem go here first (PROGRAM.md). The older,
rule-by-rule list is `formal/out/FOR-RESEARCH.md`.

## 1. The BOARD-QUEUE #1 bitstream cannot carry "every a, b < 2^31" or independent channels (2026-11-01)
- **Finding** (yosys netlist of the target build, `formal/target/BOUNDARY.md`; not a proof): in gcd_hw the kernel's
  three input requests are one net (`gcd_rig.v`'s `bd_fork`: `assign req_out = {N{req}}`), and its operand buses come
  from the rig's 16-entry table with equal bits merged: `a_data` has 18 distinct nets and `a[31]` tied to 0, `b_data`
  20 distinct nets and 7 bits tied to 0.
- **Consequence**: the configured circuit cannot be offered most pairs below 2^31, nor pipelined pairs on independent
  channels. THE theorem is written (formal/lean/Wip/Target/Spec.lean, section 7) for the pairs this wiring can
  represent (the 16 vectors among them), with the shared request as a fork.
- **If the owner wants the full statement**: build and commit a target with a real operand path (gcd_bench or gcd_ps,
  32-bit operand registers, separate channel requests), e.g. as a BOARD-QUEUE item, and name it. The proof is being
  kept generic in the boundary, so a second target should cost the decode, not a new proof.

## C1. Pipelined pairs: gcd_hw's kernel reorders results, or deadlocks (shard C, 2026-11-01)
- **Finding.** With the kernel boundary of Spec.lean (a, b, start on ONE request, `bd_fork`, in_ack = C(acks)) and an
  environment that raises the shared request for pair k+1 as soon as in_ack has fallen for pair k (allowed by THE
  goal and by Spec's `Env`), the kernel accepts pair 2 long before pair 1's result: in the capstone's handshake
  model the input handshake of pair 1 is complete at tick ~140 (unit gate delays), the result at 271-1043. Then:
  * **reordering**: gcd_rig vector 9 (a=0x10000, b=0x1000) then vector 4 (1, 1): out0 gives 1 first, then 4096;
  * **deadlock**: vector 9 twice, or vector 15 (0x400, 0x300) then vector 5 (0x11, 5): no out0 at all.
  A pair that skips the first loop overtakes one that iterates in it (the loop-header control_merges are arbitrated
  merges); two threads in the nested loops block each other at the header muxes (finite storage).
- **This contradicts gcd_rig.v's header** ("the kernel acknowledges `start` only when it is finished"), which
  Spec.lean section 7 currently cites for "the target would not hold two pairs". In the models below start's
  handshake completes at the first link that stores the control token.
- **Evidence.** Lean (kernel, standard axioms): `Formal/Net/PipeGcd.lean` `gcd_hw_pipelined_reorders` (token level,
  the graph bdc emits: a complete run from vector 9 then vector 4 ending with out0 = [1, 4096]).
  `Formal/Net/PipeWit.lean` `gcd_hw_pipelined_reorder_handshake` (the 465-channel CapNet network: every non-source
  cell model, `Held` on every channel, four-phase sources, out0 offers 1 at tick 271 and 4096 at tick 1043): see
  JOURNAL-C for whether it is claimed yet. Simulation only: the deadlocks; random per-node delays 1..4 ticks keep
  both effects (formal/tools/pipe/hwsimgen.py on the generated-netlist model).
- **Not shown.** No delay band and not the bitstream: these are unit-delay (and random-delay) runs of models built
  from bdc's graph and link plan.
- **For research (to confirm or refute on the target).** Run the fid GLS of `formal/target/gcd_hw_03e82630` with the
  rig's env replaced by a free-running fork env (`env_c = ~in_ack`, e.g. uenv1 as an inverter of in_ack, which is
  `sim.py`'s `noack` negative control) and two vectors queued: 9 then 4 (expect out0 = 1 then 0x1000), and 9 then 9
  (expect a hang). Check also when `start_ack` rises relative to `out0_req` for one vector.
- **For the owner.** The theorem as stated (pipelined environment) is false for this kernel. Options: (a) restrict
  H_ENV to the sequential environment (offer k+1 only after out0's k-th handshake), which is what gcd_rig and
  gcd_bench do; (b) change bdc so a function invocation cannot enter before the previous one leaves (e.g. a
  token-count gate between start and end).
