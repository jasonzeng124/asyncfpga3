# C-O4: binding the Ops operator models to the generated cells (track 8 capstone, item O4)

Shard C, probe O4, 2026-10-29. Core Lean only (no Mathlib), no sorry/axiom/native_decide.

## Verdict

- **H_CELLS is replaced by hypotheses on LUTs, wires and delay chains: works.**
  `CellBind.Gcd.gcd_hw_circuit_safe_gen` (and `gcd_rig_all_gen`) is `gcd_hw_circuit_safe3`
  (`gcd_rig_all`) with H_CELLS replaced by H_GEN: every one of gcd_hw's 367 operator instances
  obeys its generated netlist (yosys INITs, `genF`) under the per-gate SI model, plus named
  hypotheses. Every operator kind gcd_hw uses is covered (fork N = 2..6, compute join N = 1, 2,
  branch join, steer, mux, muxN, amerge stage, link, src, sink).
- **Three real gaps between the netlists and the Ops models, each with a counterexample run
  and a named hypothesis:** (1) side-tapped delay chains (bd_delay FASTFALL / gated, the
  compute, muxN and amerge request lines; bd_link's FASTRISE `uack`, DACK = 6) can emit a runt
  under end-only persistence (`Chain.fastfall_hazard`): **H_CHAIN_SETTLED** (every stage has
  followed before the input moves again) is a genuine timing condition; plain buffer chains
  need only the protocol's end-only persistence (`CellBind.buf_settled`, any length).
  (2) bd_fork N = 5, 6 are two-level C-trees; without **H_LEAF_PERSIST** the lumped `Fork.cel`
  fails (`Gcd.tree_needs_persist`); the same holds for a C-element / OR node in front of a
  delay chain (compute join, mux, muxN). (3) netlist wires that are the SAME net (fork
  `req_out`, join `ack_out`, mux `ctl_ack`, bd_snk `ack`, bd_link with DELAY = 0) violate the
  Ops wire field (`CellBind.ident_wire_breaks`): **H_WIRE_DI** (a route of ≥ 1 tick) is
  needed, not a generalisation.
- **Not bound (copied as named hypotheses):** data paths, select pins, the arbiter's grants,
  `R0` vs. the grant nodes (**H_R0_ISO**, an isochrony), bdc_muxn3's `|j` logic, reset values.
- **A flipped INIT bit breaks the proof:** `Wip/CO4/Mutant.lean` (bd_fork N = 2, INIT bit 1)
  fails to check (`decide` proves the gate lemma false); `Gcd.mut_breaks` is the mutant's
  violating run, checked.
- **Non-vacuity:** joint, but quiet only (`Wit.gcd_gen_witness`: 8t's run frozen at tick 0
  satisfies H_GEN, H_BUNDLE, H_START_ONCE). No active whole-network run satisfying H_GEN.

## Run

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/CellBind.lean Formal/Net/CellBindNets.lean Formal/Net/CellBindChain.lean \
               Formal/Net/CellBindOps.lean Formal/Net/CellBindGcd.lean Formal/Net/CellBindWit.lean
    ./slot.sh lake env lean Wip/CO4/Mutant.lean        # MUST fail (negative control)
    python3 lean/Wip/CO4/chain_bfs.py                    # chain-variant search (below)
    lean/Wip/CO4/gen_extra.sh                            # regenerates CellBindNets.lean (needs yosys)

The lead must add `Formal.Net.CellBind`, `CellBindNets`, `CellBindChain`, `CellBindOps`,
`CellBindGcd`, `CellBindWit` to `Formal.lean` (I do not own it). Build order: CellBind,
CellBindNets → CellBindChain → CellBindOps → CellBindGcd → CellBindWit. Dependencies with
existing oleans: OpsGen, CapstoneNetDef, CapstoneWalk, CapstoneRigAll, CapstoneWitness3.

## Files

| file | contents |
|---|---|
| `Formal/Net/CellBind.lean` | generic: `NetSI` (per-gate SI), `Settled` (H_CHAIN_SETTLED), `PersistEnd`, **`mono_net`** (monotone constant-preserving network behind a settled input = one lumped node), **`buf_settled`/`buf_chain`** (buffer chains: end-only persistence suffices, any length), **`cel_inv`/`cel_lumped`** (C-element node + downstream lumped node + H_LEAF_PERSIST), **`or_inv`/`or_lumped`** (same for OR), `ident_wire_breaks` |
| `Formal/Net/CellBindNets.lean` | GENERATED (`Wip/CO4/gen_extra.sh`, gen.sh's yosys flow): `bd_fork` N = 3, 4, 6 (targets.txt has only N = 2, 5). Not covered by `gen.sh --check` |
| `Formal/Net/CellBindChain.lean` | generated chain stages are buffer / AND / OR (`rdly_gate`, `uack_gate`, `ff_gate`, `fr_gate`, `gated_gate`, `sym_gate`), `stage_mono`; **`fastfall_hazard`**, `ff_not_settled` |
| `Formal/Net/CellBindOps.lean` | `CNode`, `LeafPersist`, `Stage`, `GenChain`, `GenBufChain`, `chain_lumped`, `bufchain_lumped`; per kind `GenFork`/`ForkTree`/`tree_cel`, `GenBJoin`, `GenJoin`, `GenSteer`, `GenMux`, `GenMuxN`, `GenAMerge`, `GenLink`, `GenSrc`, `GenSink` and `*_of_gen`; **`GenCell`, `cell_of_gen`** |
| `Formal/Net/CellBindGcd.lean` | `cells_of_gen`, **`gcd_hw_circuit_safe_gen`**, `GenCellR`, **`gcd_rig_all_gen`**, `tree_needs_persist`, `mut_gate_false`, `mut_breaks` |
| `Formal/Net/CellBindWit.lean` | `gen_frozen`, `gcd_ops_shape`, **`gcd_gen_witness`** |
| `Wip/CO4/Mutant.lean` | negative control, must NOT check |
| `Wip/CO4/chain_bfs.py`, `chain_path.py` | brute force of the chain variants; shortest hazard run |
| `Wip/CO4/gen_extra.sh`, `Wip/CO4/json/` | generator of CellBindNets.lean and its yosys JSON |

## The model

Per-gate SI (the brief's "each LUT output moves only to its function of the previous tick's
inputs"): `LutSI F p o` / `LutFb F p qp o` (8n's definitions), with `F` literally `genF` of
the generated netlist. Delays unbounded; an excitation that disappears before the gate fires
is cancelled. Named assumptions of the model itself:

- **H_LUT_SI** (per LUT) as above. Fidelity: the SI abstraction of an inertial gate with
  delay ≥ 1 tick (8n `cause1`); not the mux-tree hazard model (H_KLEENE_LUT is a separate,
  finer layer, not used here).
- **H_FB_FIRST** (per feedback LUT) = 8n / B's C2. Unchanged from 8n.
- **H_PIN_EQ** (convention): a non-feedback LUT pin reads the trace of the net that drives
  it; channel traces are taken at the reading pins. Every route that the proofs need as a
  delay is an explicit node (a `Stage.buf` stage, or H_WIRE_DI). A route between two LUTs
  that is NOT made explicit is assumed zero-delay; `buf_chain` shows how to discharge one
  (a route is a buffer stage; end-only persistence suffices), but that discharge is not
  applied to every pin of the 367 operators (open).

## Results per operator kind (gcd_hw counts in brackets)

| Ops kind [count] | generated netlist used | Ops fields derived | extra hypotheses (named) |
|---|---|---|---|
| link [175] | `bd_link_W2` `ctl.u.u` (8n), `rdly` stages (LUT1), `uack` stages (LUT1, LUT2 OR) | `H_CEL_SI`, `H_REQ_DI` (`bufchain_lumped`), `H_ACK_DI` (`chain_lumped`) | H_FB_FIRST; H_REQ_PERSIST on rdly; **H_CHAIN_SETTLED on uack** (FASTRISE, DACK = 6 in the gcd_kernel.v found under formal/tools/rulek/build/tree_d; DACK = 0 still needs the route); H_LATCH_COMB (`H_LATCH_OPEN/HOLD` copied) |
| forkG/forkH [44: N=2 ×25, 3 ×8, 4 ×8, 5 ×2, 6 ×1] | `bd_fork_N2`, `bd_fork_N5` (Gen); `bd_fork_N3/N4/N6` (CellBindNets) | `cel` (`tree_cel`), `ne` | N ≥ 5: **H_LEAF_PERSIST**, internal nodes start equal to `ack`; H_WIRE_DI on `req_out` (same net in the netlist); H_DATA_WIRE; H_PORT_ORDER (list order = `ack_in[k]`, matters for N = 5, 6) |
| bjoin [38] | `bd_join_N2` | `cel` | H_FB_FIRST; H_WIRE_DI on `ack_out`; H_DATA_COMB |
| join (compute) [20: N=1 ×11, 2 ×9] | `bd_join_N2` (N = 2), wire (N = 1), `uor` + request delay as `Stage`s | `cel` (`cel_lumped` ∘ `chain_lumped`) | **H_CHAIN_SETTLED** (bd_delay_gated, default BDC_FASTFALL=1); N = 2: **H_LEAF_PERSIST**; H_WIRE_DI; H_DATA_COMB |
| steerC/steerD [38] | `bd_steer` LUT6_2 and `uack` (8n) | `lut`, `orr` | H_SEL_PIN; H_DATA_WIRE |
| mux [21] | `bd_mux_W2` `uj0/uj1/uxa/uya` (8n), `uor` LUT2 OR, `udly` (LUT1) | `cj0`, `cj1`, `xa`, `ya`, **`zr`** (`or_lumped` ∘ `bufchain_lumped`) | H_FB_FIRST ×4, H_SEL_PIN, H_REQ_PERSIST, **H_LEAF_PERSIST** on j0/j1, H_WIRE_DI on `ctl_ack`, H_DATA_COMB. (FASTFALL opt-in builds would need H_CHAIN_SETTLED: use `GenChain`) |
| muxn [1] | `bd_c2` ×6 (8n) | `cj`, `xa`, **`zr`** | H_SEL_PIN (decode); **H_MUXN_OR** (`|j` is yosys logic of the emitted unit, no generated cell); H_CHAIN_SETTLED; H_LEAF_PERSIST; H_WIRE_DI; H_DATA_COMB |
| amerge [9] | `bd_arbiter` `ua1/ua2` (8n), request delay as `Stage`s | `xa`, `ya`, `zr` (from `R0` through the chain) | H_CHAIN_SETTLED; **H_R0_ISO**; `H_ARB1/2`, `H_ARB_EXCL`, `H_AMERGE_RTZ`, data: copied (B's domain) |
| src [3] | `bd_src_W2` LUT1 (8n) | `H_LUT_SI` | H_DATA_CONST |
| sink [18] | `bd_snk_W2` (no cell) | `wire` | H_WIRE_DI (the netlist's ack IS req) |

What "derived" means: the Ops field is a theorem from the generated LUT relations and the
listed hypotheses; the stage *topology* of a chain is existentially quantified (any
predecessor/tap wiring of generated buffer/AND/OR stages works, because the proof uses only
monotonicity and constant preservation), so the chain proofs do not pin bdc's exact wiring.

### Finding 1: side-tapped delay chains need H_CHAIN_SETTLED (counterexample)

`Chain.fastfall_hazard` (Lean, generated `bd_delay_N3_FF`, rows a, s1, s2, z at t = 0..9):

    a  0 1 1 1 1 0 0 1 1 1
    s1 0 0 1 1 1 1 1 0 0 0
    s2 0 0 0 1 1 1 1 1 0 0
    z  0 0 0 0 1 1 0 0 1 0

Every node obeys its generated LUT of the previous tick, `a` moves only when `z` shows it
(end-only persistence, which is all the protocol around a request line gives), and `z`
falls at 8→9 while `a` = 1: after a quick fall/re-rise of `a` the slow head `s1` lags, the
taps let `z` re-rise from the stale `s2` and drop again: a runt on the request (the "flush and
re-ripple" glitch that `bd_delay_gated`'s header warns about). `chain_bfs.py`: the same for
FASTFALL, FASTRISE and gated+anchor chains of every length 3..5; none for plain chains
(proved for all lengths: `buf_settled`) or length ≤ 2. So in gcd_hw H_CHAIN_SETTLED applies to
every compute unit's request line, the muxN and amerge request lines, and every bd_link
`uack` with DACK ≥ 2 stages + route ≥ 3 nodes. It is a timing condition (the input's next
edge after every stage has settled); likely what tighten.py's rule F guards for the fast
fall, NOT checked against rule F here. No tcheck row exists for it (open).

### Finding 2: two-level C-trees need H_LEAF_PERSIST (counterexample)

`Gcd.tree_needs_persist`: the generated bd_fork N = 5 tree (`chunk[0]` C4 node `m`, `utop`
C2), every LUT obeying H_LUT_SI and H_FB_FIRST: leaves a0..a3 high, `m` rises; a0 withdraws;
the root rises from `m = a4 = 1` while a0 = 0, violating `Fork.cel`. The Ops field is
unconditional, so the tree satisfies it only if leaves move only while they equal the root
(H_LEAF_PERSIST), which the four-phase protocol of the branch channels gives (a branch ack
changes only after the fork's input request moved, which waits for the fork's ack). That
derivation from the protocol is circular in the current proof structure (the capstone derives
the protocol FROM the Cell fields), so it is kept as a hypothesis; proving it would need a
simultaneous induction with the Ops protocol proof (open). Same for the compute join and
mux/muxN OR nodes in front of their delay chains.

### Finding 3: identity wires violate the Ops wire field

`ident_wire_breaks`. The Ops wire fields require the copy to lag by one tick; the netlist has
`req_out[k] = req` etc. So H_WIRE_DI is a hypothesis on routes (each branch a route with delay
≥ 1 tick, the inertial/pure channel of Bridge with lo ≥ 1), not a harmless generalisation.

## The composition

`cell_of_gen : GenCell ch sv k → Cell ch sv k` for every `k : CapNet.K n` (any network, also
ipow/collatz/xorshift: their K constructors are the same, but their fork/join widths were not
checked against `shapeB`; only the gcd capstone is restated). `gcd_hw_circuit_safe_gen`:

    a, b < 2^31,  H_GEN : ∀ o, GenCell ch (srcV a b) (opAt o),  H_BUNDLE,  H_START_ONCE
    ⟹ every token closed on out0 carries gcd a b, and out0's closed values are all gcd a b.

`gcd_rig_all_gen`: the rig theorem with `GenCellR` (source without reset clause), RigEnv,
H_BUNDLE ⟹ every value out0 offers or latches is gcd a b.

What it does NOT cover: liveness; H_BUNDLE (unchanged); the data path; the arbiter's grant
behaviour; H_PIN_EQ for unlisted routes; a whole-network run with transitions.

## Hypotheses and non-vacuity

| hypothesis | where | non-vacuity witness |
|---|---|---|
| H_LUT_SI + H_FB_FIRST (CNode, LutSI) | every LUT | quiet run (`gcd_gen_witness`); active single-cell runs: `fastfall_hazard` (stages), `tree_needs_persist` (fork N=5 LUTs), 8n's `pipe_live_unit` (link) |
| H_CHAIN_SETTLED (`GenChain`) | uack, compute/muxN/amerge request lines | quiet run; any run with ≥ chain-length ticks between input edges (not built) |
| H_REQ_PERSIST (`GenBufChain`) | rdly, mux udly | quiet run; `ff_persist` shows the persistence shape on a run |
| H_LEAF_PERSIST | fork N=5,6; compute join N=2; mux; muxN | quiet run |
| H_WIRE_DI, H_DATA_*, H_SEL_PIN, H_LATCH_COMB, H_MUXN_OR, H_R0_ISO, H_ARB*, reset | per field | quiet run (fields as in 8t's run at tick 0) |
| joint: H_GEN ∧ H_BUNDLE ∧ H_START_ONCE | gcd_hw_circuit_safe_gen | `gcd_gen_witness` (quiet; a = 12, b = 18) |

## Not done / open

- An active whole-network witness for H_GEN (8t's run has no internal chain nodes; refining
  its time base to insert them is the way).
- H_LEAF_PERSIST and H_REQ_PERSIST from the protocol (simultaneous induction).
- Pinning chain topology to bdc's netlists; ipow/collatz/xorshift restatement (needs `shapeB`
  per kernel); a tcheck row for H_CHAIN_SETTLED.
- CellBindNets is outside `gen.sh --check`'s drift check; the lead may prefer adding
  `bd_fork_N3/N4/N6` to targets.txt (shard C's Gen) instead.
