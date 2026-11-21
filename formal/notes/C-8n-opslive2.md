# C-8n: Ops gate models bound to generated cells (O4), circuit liveness with bounded delays (O5)

Shard C, probe 8n, 2026-10-27. About 3 h. Core Lean only, no sorry/axiom/native_decide.

## Verdict

- **O4: works.** Every hand-written Ops gate field of fork, join, steer, mux, muxN, amerge
  (acknowledges and the `R0` function), link, src and sink is derived from the generated
  cell's gate (`Formal/Gen/Cells.lean` read by `Netlist.gateN boolSem`), plus one named
  timing condition per feedback LUT: **H_FB_FIRST**, the step form of shard B's C2. The
  Ops fields the generated cells cannot give are listed (H_DELAY_LUMPED, H_SEL_PIN,
  H_WIRE_DI, H_DATA_COMB, the arbiter's `H_ARB*`).
- **O5: works for a linear pipeline of any length; the ring is open.** With bounded
  (inertial) delays on every gate AND every route, a request offered at the input of an
  `n`-stage link pipeline is acknowledged by the sink within
  `Σ_{k<n} (hi(c_k) + hi(r_{k+1})) + hi(a_n)`. That is `(2n+1)·H` for a uniform bound `H`,
  and `(2n+2)·H` from reset. The bound is exact at unit delay. The ring and gcd_hw's
  structure are not done; why, and what is needed, is below.

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/OpsGen.olean Formal/Net/OpsGen.lean            # ~3 s
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/OpsTimedLive.olean Formal/Net/OpsTimedLive.lean  # ~3 s
    ../slot.sh lean Wip/C8n/Axioms.lean
    ../check.sh Formal/Net/OpsGen.lean Formal/Net/OpsTimedLive.lean
    # -> [audit] 2399 declarations checked, [check] OK  (14 s)

These modules need the existing oleans of Gen.Cells, the Ops* modules, CapstoneSrc and Bridge.
The lead must add `Formal.Net.OpsGen` and `Formal.Net.OpsTimedLive` to `Formal.lean`; I do not
own that file.

Axioms (`Wip/C8n/Axioms.lean`):
- every O4 binding theorem uses `propext` only, and `snk_wire` and `fbFirst_of_gap` use none;
- the liveness theorems use {propext, Classical.choice, Quot.sound}, from `byContradiction`
  in `reach_step` and from core `simp`.

## Files

| file | contents |
|---|---|
| `formal/lean/Formal/Net/OpsGen.lean` | O4. `LutFb`, `LutSI`, `FbFirst`, `Gap`, `SettleFrom`, `fbFirst_of_gap`, `settle_of_{bounded,inertial,noOvertake}`, `lutFb_si`, `genF`; per cell `*_gate` (decide +kernel on the generated netlist) and `*_bound`/`*_cel`; assembled `fork_of_gen`, `join_of_gen`, `link_of_gen`, `src_of_gen`; negative control `fb_stale_breaks`, `fb_stale_run` |
| `formal/lean/Formal/Net/OpsTimedLive.lean` | O5. Generic `cause1`, `hold`, `first_rise`, `reach_step`, `quiet`, `chain`, `sumD`; pipeline `pf`, `pipe`, `pipe_ctl_gen`, `pipe_src_gen`, `pipe_closed`, `pipe_quiet`, `ctl_stays`, `req_stays`, `ev`, `pipe_step`, **`pipe_latency`**, `pipe_offer`, **`pipe_latency_empty`**, `sumD_dd`, `sumD_le`, **`pipe_latency_uniform`**, **`pipe_ops_link`**, **`pipe_live_unit`**, **`pipe_unit_exact`** |
| `formal/lean/Wip/C8n/Axioms.lean` | `#print axioms` (proves nothing) |

## O4: binding the Ops gate models to the generated cells

**The physical gate.**
- A feedback LUT (C-element, mux join, link controller) reads its own output through the
  routed copy `qp` on its feedback pin, not through `o`.
- `LutFb F p qp o` is that physical SI relation: `o` changes only to `F (p t) (qp t)`.
  Here `F` is literally `genF nl cell pin nets`, the generated netlist's gate function,
  written inside the hypothesis.
- The Ops models read `o t` in place of `qp t`.

**H_FB_FIRST and where it comes from.**
- `FbFirst qp o`: at every output change, the feedback pin already shows the output.
  `lutFb_si` turns `LutFb` into the Ops form under this condition.
- `fbFirst_of_gap` derives it from `Gap hi o` (consecutive output changes are at least `hi`
  apart, the first at least `hi` after reset) for any feedback route with a settle bound
  `hi`. That route can be B's `WinDelay`, `Prelim.BoundedDelay` or Bridge's
  `Inertial`/`NoOvertake`.
- `Gap` is B's C1/C2 separation: B's `c2_four_phase` derives `c(k+1) ≥ c k + Dmax` from
  `H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E`.
- So the obligation the Ops models add on top of the generated LUT is exactly B's
  C2/H_ENV_LATENCY (per-pin: C3). Its status is UNCHECKED by any rule (B-obligations C2,
  C3). C-10d measured RT_FB failing on 12/64 muller64 stages.

**Negative control (`fb_stale_run`).**
- Setting: the generated fork LUT, the node `ack` at 1, the feedback pin stale at 0,
  branch acks 1 and 0.
- `ack` falls. The trace satisfies `LutFb` with the generated function and violates
  `Fork.cel`, so H_FB_FIRST is not vacuous.

| Ops field | generated cell (Gen) | theorem | extra hypothesis |
|---|---|---|---|
| `Fork.cel` (N=2), whole `Fork` | `bd_fork_N2` `u.genblk1.g2.u.u`; `req_out[*]` = `req` net | `fork2_gate`, `fork2_cel`, `fork2_wires`, `fork_of_gen` | H_FB_FIRST; H_WIRE_DI and H_DATA_WIRE stay (route skew) |
| `Join.cel` (N=2, 3), whole `Join` | `bd_join_N2`, `bd_join_N3` | `join2_gate`, `join3_gate`, `join2_cel`, `join3_cel`, `join_of_gen` | H_FB_FIRST; H_DATA_COMB |
| `Steer.lut`, `Steer.orr` | `bd_steer` `u` O5 = `req ∧ ¬s`, O6 = `req ∧ s`, `uack` | `steer_gate`, `steer_bound` | H_SEL_PIN (the `s` pin reads `sel (j.dat)`; its delay is H_STEER_SEL) |
| `Mux.cj0/cj1/xa/ya` | `bd_mux_W2` `uj0 = C(x, c∧¬s)`, `uj1 = C(y, c∧s)`, `uxa.u`, `uya.u` | `mux_gate`, `mux_bound` | H_FB_FIRST (4 LUTs), H_SEL_PIN |
| `Mux.zr` (function only) | `uor → udly.chain.g[0] → g[1]` = `j0 ∨ j1` | `mux_zr_chain` | **H_DELAY_LUMPED** (3 nodes read as 1: not derived) |
| `Mux.ca`, datamux | `ctl_ack` is the `z_ack` net; `udat` O5 = `s ? y : x` per bit | `mux_wires` | H_WIRE_DI (generalisation) |
| `MuxN.cj/xa` | `bd_c2` (`emit_muxn` instantiates one per join and per ack) | `c2_gate`, `muxn_bound` | H_FB_FIRST; H_SEL_PIN on the decode `ctl_req ∧ (s == k)` (yosys logic, not a library cell) |
| `AMerge.xa/ya` | `bd_arbiter` `ua1.u = C(g1, A0)`, `ua2.u = C(g2, A0)` | `arb_gate`, `amerge_ack_bound` | H_FB_FIRST |
| `AMerge.zr` (function only) | `ustate` O5 (`R0`) = `ugrant` O5 ∨ O6, on all 16 inputs | `arb_r0_or` | H_DELAY_LUMPED. `R0` is computed in parallel from `r1, r2, q`, not from the grant nodes, so the Ops reading "z_req follows `g1 ∨ g2`" is an abstraction. `H_ARB1/2`, `H_ARB_EXCL` stay B's |
| `Link.H_CEL_SI`, whole `Link` | `bd_link_W2` `ctl.u.u` = B's `ctlB`; `ack_in` = `req_out` = node | `link_gate`, `link_bound`, `link_wires`, `link_of_gen` | H_FB_FIRST; the latch fields stay H_LATCH_COMB |
| `Src.H_LUT_SI`, whole `Src` | `bd_src_W2` `u` = LUT1 `¬ack`, constant data ports | `src_gate`, `src_bound`, `src_of_gen` | none |
| `Sink.wire` | `bd_snk_W2` has no cell, `ack` port = `req` net | `snk_wire` | H_WIRE_DI (generalisation) |

**Not bound.**
- Fork/join C-trees for N ≥ 4. They are two LUT levels; Ops lumps them (H_CTREE_ATOMIC),
  and B's `CTree` covers that.
- The 3-input control_merge cascade's first stage. Its `R0`/`A0` are internal, as in 8l.
- Every data path (H_DATA_COMB / H_LATCH_COMB). Only bit-level functions are checked.

**Why `decide` and not a 2^n step proof.** Every gate lemma is a per-cell `gateN` equality
over at most 2^5 inputs, so the file checks in about 3 s. C-11d's whole-netlist step proofs
are a different statement: the unit-step reading, with feedback as an input.

## O5: liveness and a latency bound

**Obstacle 1 (the Ops model forces nothing) is removed by adding the upper bound.**
- Model: a `Bridge.Net` timed trace (`Bridge.Timed`). Every gate, and every route made into
  a buffer gate, is an inertial channel `[lo i, hi i]` with `lo i ≥ 1`.
- `cause1`: such a gate changes only to its excitation one tick earlier. That is exactly
  the Ops SI field. So every timed trace is also an Ops trace (`pipe_ops_link` shows it per
  stage), and the safety theorems (`link_op`, `net_refines`) apply to the same runs.
- Only the `settle` half (upper bound) is used for progress.

**Generic method (any network).**
- `reach_step`: if gate `g` is excited towards `v` for as long as it has not yet shown `v`,
  it shows `v` within `hi g`.
- `quiet`: the region ahead of a not-yet-arrived front stays at 0, if its excitations are 0
  whenever the region and the front node are 0. This is "nothing downstream moves before
  the token arrives", proved from `cause1` by time induction. No SI serialization and no
  persistence are needed.
- `hold`: a node keeps `v` while its excitation is `v`.
- `chain` sums the steps.

**Pipeline instance (`pipe n`, any n ≥ 1).**
- Nodes:
  - the source: the generated `bd_src` LUT, `pipe_src_gen`;
  - `n` controllers: the generated `bd_link` `ctl.u.u` LUT, `pipe_ctl_gen`;
  - every request route `r_k` and acknowledge route `a_k` as its own buffer gate, so the
    wires are delay-insensitive with their own bounds;
  - the sink `a_n`: a wire copy of `r_n` (`bd_snk`).
- Ids are in token order (`r k = 3k`, `c k = 3k+1`, `a k = 3k+2`). This makes the quiet
  region of a front node `g` simply "all ids > g" (`pipe_closed`).

**Theorems.**
- `pipe_latency`: from an empty state at `T` (H_EMPTY), a request offered at `t0 ≥ T` is
  acknowledged by the sink by `t0 + Σ_{j=1}^{2n+1} hi(ev j)`.
  - The events are r0 → c0 → r1 → c1 → … → c(n−1) → r n → a n.
  - `sumD_dd` gives the closed form `Σ_{k<n}(hi(c_k) + hi(r_{k+1})) + hi(a_n)`.
- `pipe_offer` / `pipe_latency_empty`: from reset the source offers within `hi(r0)`.
- `pipe_latency_uniform`: with all upper bounds `≤ H`, the sink acknowledges within
  `(2n+2)·H`.
- `pipe_live_unit`: **non-vacuity.** Bridge's unit-delay trace from reset satisfies every
  hypothesis.
- `pipe_unit_exact`: the bound is exact at unit delay (n = 3: acknowledge at t = 8 = 2n+2,
  not at 7).

**Hypotheses, each named, with fidelity and test.**
- **H_BOUNDED_DELAY (inertial), per LUT and per route** (`Bridge.Timed`).
  - Fidelity: as in C-8d. The proof uses only the settle bound and `cause1`. Pulse
    filtering is not used.
  - Bounds: `hi` from prjxray-db slow-max for the LUT arc plus the route. The test is a
    GLS step-response per arc.
- **H_FB_SETTLED.** The controller reads its own node (the gate is atomic). By O4 this is
  `FbFirst`, i.e. B's C2. It is unchecked by any rule and should become a tcheck rule
  (RT_FB, C-10d).
- **H_ISO is NOT assumed for routes.** Each fork branch of `c_k` (`r_{k+1}` forward and
  `a_k` back) is its own gate with its own delay.
- **H_EMPTY.** All nodes are 0 at `T`. That holds at reset (B's C5 reset width) and under
  H_ONE_INVOCATION before the first token.
  - It is NOT shown that a pipeline returns to an all-zero state between tokens.
  - So the theorem bounds the first token after reset, or any token entering an empty
    pipeline.
  - A steady-state throughput bound is open.

## What is open, and why

1. **Single ring of op cells (not done).**
   - What exists: 8d's `timed_ring_every_stage` already bounds every stage of the real
     `bd_c2n` ring to toggle in every window of `(N(N−1)+1)·H` (isochronic wires,
     H_NO_OVERTAKE).
   - What I scoped: a linear bound `≈ (N+1)·H` for the stage-`j` toggle, by the same
     quiet/chain method.
     - Track the wavefront nearest behind `j`. With D = 2 and N ≥ 3 it is blocked only
       when it sits at `j` with the other wavefront at `j+1`.
     - The region between it and `j` is wavefront-free and stays so (a `quiet` argument on
       `tok`, from `cause1`).
     - Each step therefore takes ≤ `hi`, and the last ≤ 2·`hi`.
   - Missing: the modular index bookkeeping on `prv`/`nxt` (or a rotation-invariance lemma
     for `ringNet`'s timed traces). Estimate 2-3 h.
   - For a ring of OP cells (entry mux, links, exit steer) the first lap is the pipeline
     argument verbatim: ahead of the front is quiet.
   - Later laps need the return-to-zero wave to have cleared the entry. That is a
     two-front invariant, which is exactly `Ring.D = 2` for the plain ring and must be
     re-proved per op-cell ring. Estimate 1 day for a fixed small ring with a kernel
     reachable-set certificate (BridgeWire's `check` style).
2. **gcd_hw's structure (not done).**
   - Needs (1) for each of its rings, using `gcdhw_ring_ge3` (≥ 3 links per cycle) as the
     `N ≥ 3` hypothesis.
   - Needs O1's circuit-to-token simulation. The number of loop iterations is
     data-dependent (the bound is `iterations × lap + exit`), and the steer/mux selects
     must follow the token run.
   - Needs C-8l's capacity argument (`link_capacity`, one place per link, under
     H_ONE_INVOCATION).
   - Estimate 2-3 days after O1, unchanged from C-8l.
3. **Steady state.** A return-to-empty lemma for the pipeline (the RTZ wave clears within
   `Σ hi` after the sink acknowledges) would give a per-token period bound. Estimate
   0.5 day with the same method (the falling front is a chain too).
4. **H_DELAY_LUMPED** for `Mux.zr`/`AMerge.zr`.
   - A chain of inertial nodes is not one inertial node.
   - The pipeline proof shows the way: make each delay LUT its own gate. The Ops-level
     relation then needs the delay line's own SI invariant (it carries at most one
     transition at a time, true in a four-phase handshake).
   - Estimate 0.5 day.

## What it buys

- **O4 closes C-8l's binding gap.**
  - Every operator theorem of the composition framework (`fork_op`, `join_op`,
    `steer_op`, `mux_op`, `muxn_op`, `amerge_op`, `link_op`, `src_op`, `sink_op`) now
    applies to nodes that obey the yosys-generated LUTs, not to hand-written functions.
  - The one extra condition is B's C2, named and with a counterexample.
  - A change of an INIT in `cells/rtl/` breaks `*_gate` (through C-11d's regeneration).
- **O5 gives the first circuit liveness theorem of the Ops track with a number in it.**
  - It holds for any pipeline length.
  - It needs no fairness assumption and no isochronic routes, and it is exact at unit
    delay.
  - The `quiet`/`reach_step`/`chain` method is generic. It needs no reachable-set
    enumeration, so it scales to any n.

## Fidelity of the primitive models used here

| primitive | model | fidelity |
|---|---|---|
| feedback LUT | `LutFb` with the generated function, feedback pin `qp` | exact logic (yosys INIT through Core `Lut.eval`). Atomic gate: no mux-tree hazard (B's C4 / H_KLEENE_LUT) |
| feedback route | any channel with a settle bound | as general as B's `WinDelay` |
| LUT/route in O5 | `Bridge.Inertial [lo, hi]` | C-8d: inertial ⇒ no-overtake; the fabric's H_NO_OVERTAKE is plausible, untested on silicon |
| request/ack routes | separate buffer gates | DI wires, more general than the fabric |
| sink | wire copy of `req` | `bd_snk` is literally a wire |
| select/decoder pins | H_SEL_PIN (zero-delay data) | as C-8f; the real delay is H_STEER_SEL / H_MUX_SEL (tcheck rows) |
