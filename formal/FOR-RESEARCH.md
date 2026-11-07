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
  decoder; Python round trip; C's import agrees but shares the walker code, so it is not independent), and research's
  fid GLS with a pipelined env.
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
- **Audit T6 (claude/audit af485141, findings/T6.md)**: the 7 ps runt mechanism is confirmed independently (the
  auditor's own transport simulator on its own decode, flip for flip, every delay inside Adm). Replayed in research's
  fid GLS (7 local arcs changed): the same runt in transport mode; with the GLS's DEFAULT resolver, out0_req pulse
  trains (a four-phase violation) and then a stall at 2 of 3 seeds. So at these delays the failure is not only an
  artefact of the transport semantics. Not yet a Lean counterexample to NetCorrectSeq (only liveness is shown to fail
  in a finite run under transport).
- **What it means**: the sequential theorem's κ margin is ~0.15 under the pessimistic semantics PROGRAM requires, and
  at least ~0.36 (in this evidence) if silicon kills narrow runts. Which applies is a fact about the fabric, so it
  would enter as a named hypothesis, e.g. H_RUNT(w): "a LUT input pulse narrower than w ps is not propagated".
  Stated in Lean as an addition: `Formal/Target/SpecRunt.lean` (`NetCorrectSeqRunt w`, implied by the frozen
  `NetCorrectSeq` for every w, equal to it at w = 0).
- **Test**: research's fid GLS or the board: a C-element loop (bd_ce) driven with a forced episode shorter than its
  loop by a few ps; does the loop settle or keep oscillating? `tools-B/target/` has the delays.
- **Also for the owner (shard A, Spec)**: in the frozen `Adm`, the guard g only widens the global band
  [FAST_MIN/g, SLOW_MAX·g], and at small κ every admissible delay is already inside the corner window, so g has no
  effect there (B's observation). So "the largest g" is not a margin by itself; the margin is a (g, κ) frontier. A fix
  (g scaling the corner window: [(1-κ)·lerp(FAST_MIN,SLOW_MIN,c)/g, (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)·g]) is proposed but
  NOT applied: six B/C files build on the current shape (one claimed lemma, C's `adm_le_dmax`, would become false).
  It needs an audit row and the shards' agreement.
- **APPLIED 2026-11-01 (owner decision 3, PROGRAM.md)** by shard A: `Spec.Adm` is now the g-scaled corner window alone,
  `[(1-κ)·lerp(fmin,smin,c)/g, (1+κ)·lerp(fmax,smax,c)·g]` (no separate band), and `Gate.start` is ⌈(1+κ)·smax·g⌉.
  Fixed: C's SpecSettle (`dmax`/`dmin` now ⌈(1-κ)·fmin/g⌉ ≤ d ≤ ⌈(1+κ)·smax·g⌉, needing `Sane p`, 0 ≤ c ≤ 1 and
  ordered arcs; the old `adm_le_dmax` is false at κ > 0 and is replaced), B's Ua1Static (`lo`/`hi`; the κ = 0.15/0.16
  numbers are unchanged), SpecArbVacuous (`delay_bound` is now per corner: the old ∃M ∀c form is false without the
  band), SpecFb and ArbTSpec (proofs only). **AUDIT: please add a row** for this change to the frozen Spec.

## C2. COUNTEREXAMPLE (Lean-checked 2026-11-06 10:4x: `Formal.Net.CexPS.not_netCorrectSeq`) to the sequential theorem on THE target (gcd_ps) at g = 1, κ = 21/25, w = 0 (shard C)
- **What:** a transport-delay behaviour of `circuit DecodedPS.net DecodedPS.boundary` in which every arc delay is inside
  `Adm` at g = 1, κ = 0.84 (fast corner), the env obeys Env (R = 400 ns, su = 1 ns, Δo = 3 ns) and SeqEnv, and every
  arbiter resolves (ArbOK T for all T ≥ 36 ps), but the second pair never gets an out0: the circuit deadlocks.
- **Delays:** `umux16.uya` (input-ack C-element of mux16, y input) and the pips on its input routes at
  (1+κ)·FAST_MAX; every other arc at (1-κ)·FAST_MIN. Pairs (12,18) -> 6, then (1071,462) accepted, quiet from 520.8 ns.
- **Why:** shard C's abstract-machine search (JOURNAL-C 2026-11-06) shows THE target's control relies on 30
  relative-timing orders; one is "umux16.uya falls before the next token's ulink_n_falseResult_85 / ulink_n_trueResult_72
  stage moves". Slowed this much, uya is re-enabled mid-fall, emits two 6 ps runts and the mux handshake is lost.
- **Scope:** w = 0 (no runt filtering). Under H_RUNT(20 ps) these runts are filtered: open. Correct at κ = 0.82 with
  this adversary; B's sufficient bound is κ ≤ 0.415, so the g = 1 frontier is in [0.415, 0.84) if both hold.
- **Evidence:** formal/tools/huff/cex/k84b_dump.json.xz (every node's flips), checked by tools/huff/gatecheck.py (all
  186,871 gates, 0 mismatches, 0 arcs outside Adm) and envcheck.py (Env, SeqEnv, ArbOK T ≥ 36, Correct fails).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 12,18 1071,462 --corner 0 --kappa 0.84
  --slow SLICE_X36Y47.C6 --slowroutes --nextreq seq --datachange broad --R 400000 --su 1000 --full` (net.json, bnd.json
  from `tools/cview/lean2json.py lean/Formal/Target/NetPS`). **Lean:** one-pair version (1071, 462), exact integer delays
  (`--exact --data0`), `not_netCorrectSeq : ∀ T su Δo, 36 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeq net boundary arbs ⟨1, 21/25⟩ T 400000 su Δo`,
  standard axioms (`lake build Formal.Net.CexPS.Refute`). **Also at κ = 18/25 = 0.72** (`Formal.Net.CexPS72.not_netCorrectSeq`, T ≥ 62):
  uya plus the four storage nodes of its support slowed (⌊43·FAST_MAX/25⌋), all else at ⌈7·FAST_MIN/25⌉. Simulation:
  a runt-ring livelock at 0.70, correct at 0.67 with these adversaries.
- **For research:** a fid GLS replay at these delays (and with the resolver on) would say whether the fabric model
  sees the same runts.

## A4. COUNTEREXAMPLE under H_RUNT(20 ps) (the owner's headline w): Lean-checked at g = 1, κ = 11/25; first found at κ = 18/25 (shard A, 2026-11-07)
- **What:** shard C's κ = 0.72 deadlock (C2, `CexPS72`) does NOT depend on runts. Re-run with a Spec-faithful H_RUNT(w)
  on every LUT pin (`SpecRunt.GateOKRunt w`: a LUT pin reads at the greatest time ≤ t - d lying in no pulse narrower
  than w, inside its Adm window; pips, hops, MUXF, CARRY4 transport), the same adversary (uya + 4 support storage
  nodes and their input routes at ⌊43·FAST_MAX/25⌋, all else at ⌈7·FAST_MIN/25⌉, LUT pins raised to ≥ w ps, still
  inside Adm) still accepts (1071, 462) and deadlocks quietly at 467.65 ns with no out0, for every w ≤ 25 ps. At w ≥ 26
  this adversary is no longer a behaviour (one LUT pin, SLICE_X32Y45.A6 pin 0, would have to skip a pulse longer than
  its window allows) and the run is correct.
- **Meaning (now Lean, at a much smaller scatter):** `Formal.Target.CexRunt44.not_netCorrectSeqRunt20` (standard
  axioms, check.sh OK): the headline statement is false at g = 1, κ = 11/25 for every T ≥ 123 ps, every su, Δo ≤ 3 ns;
  `FrontierRunt.not_seqRunt_le20_above44` carries it to every g ≥ 1, κ ≥ 11/25 and every w ≤ 20. **So H_RUNT(w) does
  not lift the margin for any w up to the owner's headline 20 ps: with or without runt filtering the g = 1 margin is
  below 0.44, and the one race that binds it is B's (safe to κ ≤ 0.41).** Audit T37 confirms the run independently.
- **Limit of this witness (checked, shard A 09:5x):** at w = 40 the same adversary at κ = 0.44 is CORRECT (out0 = 21),
  and it is not even admissible there (the slowed pin sits at the top of its window, so it has no room to skip a
  pulse: `INFEASIBLE 1`). At κ = 0.72 the cap is w ≤ 25. So nothing here says the statement is false for w > 20; a
  wider-filter refutation needs an adversary that leaves ≥ w slack on its slow pins. Research question unchanged: what
  is the fabric's real w?
- **Evidence:** `formal/tools-A/target/out/k72w20_dump.json.xz` (every node's flips), from `tools-A/target/simrunt.py`
  (C's simadv.py + `--w`); checked by the independent `tools-A/target/gatecheck_runt.py` (filtered waveforms rebuilt
  separately: all 186,871 gates, 274,930 checks, 0 mismatches, 0 arcs outside Adm, 0 read-lag violations, 0 reads in a
  narrow power-up interval) and C's `tools/huff/envcheck.py` (Env + SeqEnv OK, ArbOK for every T ≥ 61 ps, out0 never rises).
  Reproduce: `python3 formal/tools-A/target/simrunt.py net.json bnd.json --pairs 1071,462 --corner 0 --R 400000 --slow
  SLICE_X36Y47.C6 SLICE_X32Y45.A6 SLICE_X32Y28.A6 SLICE_X37Y47.D6 SLICE_X34Y47.A6 --kappa 0.72 --exact --data0
  --slowroutes --su 1000 --dout 3000 --full --datachange broad --dfall 3000 --nextreq seq --w 20`.
- **For research:** κ = 0.72 is a large within-die scatter; the point is that the runt filter is not what protects the
  circuit here: the binding relative-timing order (umux16.uya before the next token's link stage) is a plain race.

## C3. CANDIDATE COUNTEREXAMPLES at much smaller margins: κ = 0.44 (g = 1) and g = 1.6 (κ = 0), with and without H_RUNT(20) (shard C, 2026-11-07; simulation + independent checks; Lean building)
- **What:** ONE C-element, `ulink_n_falseResult_85` stage 0 (SLICE_X32Y45.A6, b = C(x, ¬ack), INIT 0x2200332222003322),
  with its feedback route slow (its pin-0 arc and the 6 pips/hops of its self-loop route at the slow end; 7 arcs), and
  every other arc of the circuit at the fast end. Pair (1071, 462), SeqEnv env (R = 400 ns, su = 1 ns, Δo = 3 ns),
  corner 0: the acknowledge comes back before b's own rise has gone round its feedback route, so b = fb ∧ x reads
  fb = 0 and falls; b oscillates with its loop period (~570 ps), the stage's handshake is lost, out0 never rises.
- **Margins (this adversary):** w = 0: correct at κ ≤ 0.40, livelock at 0.44, quiet deadlock at 0.48 and 0.60; at κ = 0:
  correct at g ≤ 1.58, deadlock at g = 1.59, 1.6, 1.7, 1.8. **w = 20 (H_RUNT(20), the headline):** quiet deadlock at
  κ = 0.44 and at g = 1.6 (pulses here are ~80-570 ps, far wider than 20 ps); correct at κ = 0.40.
- **Meaning:** this is shard B's binding race row (RaceTablePS: safe for g²(1+κ)/(1-κ) ≤ 2.433, i.e. κ ≤ 0.415 at g = 1,
  g ≤ 1.56 at κ = 0). The row bound is tight within ~0.03 in each direction, and the runt filter does not help. If the
  Lean versions check, THE statement's frontier (fast corner) is: g = 1: κ* < 0.44 (w = 20) / < 0.48 (w = 0);
  κ = 0: g* < 1.6. A sound positive theorem must sit below B's bound on this row.
- **Evidence:** formal/tools/huff/cex/{k48_dump, g16_dump, k44w20_dump, g16w20_dump}.json.xz, delay classes
  cex/k48_classes.json. Checked by tools/huff/gatecheck.py (w = 0; per-arc `@classes`, `GFRAC=8/5` for g) and
  tools/huff/gatecheck_runt_c.py (shard A's independent H_RUNT checker + per-arc lists; negative control: the w = 20
  dumps read as w = 0 give 22 / 36 mismatches), envcheck.py (Env + SeqEnv OK, ArbOK T ≥ 113-136 ps, no out0).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 1071,462 --corner 0 --kappa 0.48 --classes
  formal/tools/huff/cex/k48_classes.json --cdefault F --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq`
  (add `--w 20`, or `--kappa 0 --gfrac 8/5`). **Lean (building):** Formal/Net/CexPS48 (⟨1, 12/25⟩, w = 0) and
  CexPSg16 (⟨8/5, 0⟩, w = 0); the w = 20 versions need A's GateOKRunt witness check.
- **For research:** the fid GLS at these delays (feedback route of one stage-0 C-element slowed by ~1.5x relative to the
  ack path) would say whether the fabric oscillates the same way; the design-side fix is a longer acknowledge path or a
  shorter feedback route on link stage 0 (the stage reads its ack after one LUT + short routes).
- **Update 2026-11-07 09:5x: Lean-checked, and at a much smaller scatter.** Shard C's κ = 0.44 run (C3: one C-element's
  feedback route slow) is a behaviour under H_RUNT(20) too, and `Formal.Target.CexRunt44.not_netCorrectSeqRunt20`
  (standard axioms) refutes the headline statement at g = 1, κ = 11/25, T ≥ 123; `FrontierRunt.not_seqRunt_le20_above44`
  carries it to every g ≥ 1, κ ≥ 11/25, w ≤ 20. The κ = 0.72 entry above is superseded. For research: the runt filter
  is not the protection the circuit needs; the C3 race (ack faster than the C-element's own loop) is.
