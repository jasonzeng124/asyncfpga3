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
- **GLS of the target route (added later the same session).** Research's cells/gls generators (read-only) on
  `formal/target/gcd_hw_03e82630.routed.json.xz` + `.sdf.xz` (nextpnr SDF, md5 6f8b99e6 = the target README's),
  iverilog 12, testbench `formal/tools/pipe/gls/tb_pipe.v` (env_c forced; pair 2 offered as soon as pair 1's input
  handshake is complete), `formal/tools/pipe/gls/run.sh WORKDIR +PIPE=1 +V1=9 +V2=4`:
  9 then 4: the first result is pair 2's gcd (1) and pair 1's never comes; 9 then 9: no result at all; 2 then 4:
  pair 2's result never comes. Sequential controls (PIPE=0) for the same pairs: both results, correct.
  Table: formal/notes/C-pipe-cex.md; acceptance gate (gate.vvp): ANNOTATE_DONE, 0 SDF warnings/errors. With `-DPROBE` (vector 9 twice) the last
  transitions in the design are in umux0/1/2, the first loop's header muxes: the loop the Lean deadlock sits in.
  **Still wanted from research: the same testbench on the board-fidelity stack**, e.g.
  `GLS_SDF=<xray_delay.py SDF> GLS_SDF_FIELD=<corner> GLS_MODEL=fid cells/gls/fid/build_fid.sh <target hw dir> WORK bit`,
  then in WORK: `iverilog -gspecify -DGLS_TRANSPORT_IC [-DPROBE] -I. -o pipe.vvp formal/tools/pipe/gls/tb_pipe.v
  netlist_baked.v cells/gls/prims.v` (check `urig.in_ack`'s wire in nets.map against tb_pipe.v's `IN_ACK`) and
  `vvp pipe.vvp +PIPE=1 +V1=9 +V2=4`, `+V2=9`, and `+PIPE=0` as the control. prjxray is not installed in shard C's
  sandbox.
- **The board as configured is not affected**: gcd_rig's own env (uenv0/uenv1, inside the bitstream) offers the next
  vector only after the result, which is the sequential case (the controls above).
- **For research (to confirm or refute on the target).** Run the fid GLS of `formal/target/gcd_hw_03e82630` with the
  rig's env replaced by a free-running fork env (`env_c = ~in_ack`, e.g. uenv1 as an inverter of in_ack, which is
  `sim.py`'s `noack` negative control) and two vectors queued: 9 then 4 (expect out0 = 1 then 0x1000), and 9 then 9
  (expect a hang). Check also when `start_ack` rises relative to `out0_req` for one vector.
- **For the owner.** The theorem as stated (pipelined environment) is false for this kernel. Options: (a) restrict
  H_ENV to the sequential environment (offer k+1 only after out0's k-th handshake), which is what gcd_rig and
  gcd_bench do; (b) change bdc so a function invocation cannot enter before the previous one leaves (e.g. a
  token-count gate between start and end).

## 2. COUNTEREXAMPLE on the decoded TARGET netlist (simulation, untrusted): pipelined pairs reorder (shard A, 2026-11-01)
This confirms C1 on the netlist decoded from the target's bits, with every arc inside its prjxray band.
- **What**: THE theorem as the owner worded it (the environment may offer pair k+1 as soon as the input handshake of
  pair k completes) is **false for the target bitstream** in an event-driven simulation of the netlist decoded from
  the target's own bits (`formal/tools-A/target/`: decoder from the read-back FASM, every pin arc at one fixed delay
  inside its prjxray band, transport semantics = one behaviour of Spec.lean's `Behaves`).
- **Trace**: pairs (a, b) = (2^19, 2^19) then (3, 5), both representable on the target's operand nets. The shared input
  request rises at 20.0 ns, `start_ack` rises at 141.0 ns (the input handshake of pair 0 completes at 183.3 ns, all
  acks low), pair 1 is offered at 183.3 ns, and out0 delivers **1 at 936.8 ns, then 524288 at 1854.0 ns**: gcd(3,5)
  overtakes gcd(2^19,2^19). Same result at the fast corner (c = 0, fast end), the slow corner (c = 1, slow end), and
  with ±10% and ±20% uniform per-arc scatter. Output: `formal/tools-A/target/out/cex_pipelined_reorder.txt`.
  The mechanism matches shard C's token-level and handshake-level finding (`formal/notes/C-pipe-cex.md`): pair 1 skips
  the k-loop that pair 0 iterates in.
- **gcd_rig.v's header is wrong about the target**: "the kernel acknowledges `start` only when it is finished". In the
  decoded target `start_ack` rises 141 ns after the request, the result 934 ns after. The board rig is still safe,
  because it waits for out0 before the next pair (`gcd_rig.v`'s env is two stages), not because of start_ack.
- **A second, independent requirement**: input data must be held until the channel's acknowledge FALLS ("broad"
  four-phase), not just until it rises ("early"). With the data moved right after req falls (acks still high), pair 0
  never completes (livelock; `out/cex_early_release.txt`); moved at each ack's fall, both pairs are right
  (`out/ok_broad_sequential.txt`).
- **Lean (2026-11-01, later)**: `FormalWit.V9V4.Refute.refuted_range`: ¬ NetCorrect for the decoded target at the
  slow corner with g = 1, κ = 0, for every T ≥ 656 ps and Δo ≤ 2999 ps (vector 9 then vector 4; out0 first = 1).
  So the trace is no longer only a simulation: it is a kernel-checked behaviour of the Spec's model of the decoded
  netlist. Still not shown: that the decoded netlist is the target's configuration beyond H_DECODE (untrusted
  decoder; Python round trip; C's independent import agrees), and research's fid GLS with a pipelined env.
- **Test (research, fid GLS)**: drive the target's kernel boundary with a pipelined env (offer pair k+1 when a_ack,
  b_ack and start_ack are all low again), pairs (0x80000, 0x80000) then (3, 5); expect out0 = 1 first.
- **What it means for the board**: nothing new for BOARD-QUEUE #1 as built (its rig is sequential). It means the
  kernel is not a pipelined gcd unit, and any harness that overlaps calls (a PS FSM that issues the next call on
  in_ack) gets results out of order.
- **Rig vectors on the decoded target (07:49, `formal/tools-A/target/out/pipe_*.txt`)**, pipelined env, broad data rule,
  corner 0.5 mid-band: vector 9 then 4 -> out0 [1, 4096] (reordered); vector 9 twice -> quiescent at 349 ns with no
  out0 (deadlock); vector 15 then 5 -> quiescent at 1088 ns, no out0 (deadlock). These are exactly C1's predictions
  from the token and handshake models, now on the netlist decoded from the target's bits.

## 3. Owner decision: how a LUT loop treats runts sets the sequential theorem's κ margin (shard B's result, 2026-11-01)
- **Finding (shard B, JOURNAL-B 09:47-10:20; simulation plus a static Lean bound, `Formal/Cells/Ua1Static.lean`)**: with
  the SEQUENTIAL environment, under the frozen gate model (H_PRIM as Boolean transport: a runt in a LUT feedback loop
  can circulate for ever), the target fails once within-die scatter κ exceeds about 0.155 (g = 1, corner 0.2-0.5):
  one C-element (`ua1` of arbiter 0, SLICE_X2Y18.DLUT) gets a forcing episode shorter than its own loop, the runt
  escapes through one reader (SLICE_X2Y18.CLUT, an OR), and the circuit locks up. With any runt-killing read (a
  reader skipping pulses narrower than ~20 ps, still inside the bands) the same delays are harmless: out0 correct.
  The next storage node would bind only at κ ≈ 0.36.
- **What it means**: the sequential theorem's κ margin is ~0.15 under the pessimistic semantics PROGRAM requires, and
  at least ~0.36 (in this evidence) if silicon kills narrow runts. Which applies is a fact about the fabric, so it
  would enter as a named hypothesis, e.g. H_RUNT(w): "a LUT input pulse narrower than w ps is not propagated".
- **Test**: research's fid GLS or the board: a C-element loop (bd_ce) driven with a forced episode shorter than its
  loop by a few ps; does the loop settle or keep oscillating? `tools-B/target/` has the delays.
- **Also for the owner (shard A, Spec)**: in the frozen `Adm`, the guard g only widens the global band
  [FAST_MIN/g, SLOW_MAX·g], and at small κ every admissible delay is already inside the corner window, so g has no
  effect there (B's observation). So "the largest g" is not a margin by itself; the margin is a (g, κ) frontier. A fix
  (g scaling the corner window: [(1-κ)·lerp(FAST_MIN,SLOW_MIN,c)/g, (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)·g]) is proposed but
  NOT applied: six B/C files build on the current shape (one claimed lemma, C's `adm_le_dmax`, would become false).
  It needs an audit row and the shards' agreement.
