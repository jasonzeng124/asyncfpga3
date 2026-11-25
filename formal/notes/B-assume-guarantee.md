# B-assume-guarantee (probe Bnet): closing the cell/environment circle network-wide

Lean (core only, no Mathlib in the closure), each checked OK with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/<file>` (autoImplicit=false, no warnings):

- `formal/lean/Formal/Cells/AssumeGuarantee.lean`: the generic rule and the counter-example
  (no imports);
- `formal/lean/Formal/Cells/AssumeGuaranteeLinks.lean`: segment lemmas, chains of links,
  rings (imports `LutFbBridge2Env`);
- `formal/lean/Formal/Cells/AssumeGuaranteeFork.lean`: the rule on any network of segment
  contracts, and link + 2-way fork;
- `formal/lean/Formal/Cells/AssumeGuaranteeCap.lean`: C's gcd_hw `CapstoneNet`.

No sorry, axiom or native_decide. `#print axioms` (companion file, since removed) on the 29
headline theorems gives `[propext, Classical.choice, Quot.sound]` or a subset (`ag_step`,
`ag_wf`, `nonstrict_unsound`: none; the kernel census theorems: `propext`).

## The question

Bfb2 (`B-lutfb-bridge2.md`) left a circle:

- a cell's behaviour follows from its environment `Env1` (`link_lutFb`, `link_guar`);
- `Env1` follows from the neighbours' behaviour (`link_link_env`, `fork_env`).

Only the 2-stage pipe broke it (`WinFifoCausal.pipe_fifo`). This probe asked for a
network-wide break, by induction over time.

## (1) The rule, and why strictness is needed (`AssumeGuarantee`)

- **`ag_time`**: events `e`, each with a time `time e : Nat`. Assume:
  - H_CELL: every guarantee follows from its own assumption;
  - H_ENV: every assumption follows from the guarantees of the events at **strictly
    smaller** times.

  Then every guarantee holds. `ag_wf` is the same rule for any well-founded "depends on"
  relation. `ag_step` is the stratified form: `G i 0`; `(∀ i', G i' n) → A i n`;
  `A i n → G i (n+1)`. The strictness is the `+1`.
- **The causality side condition, precisely:** an event's assumption may use only events
  whose time is strictly smaller than its own. In the circuits, an event is "segment `k`
  of cell `c`'s node", and its time is the segment's END `τ c k`. Every dependency is
  then strictly earlier, because of three facts:
  - each cell's edge comes at least `lo ≥ 1` (H_LUT_POS) after the pin edge it reads;
  - each wire adds at least `wl ≥ 1`;
  - the edge times are read off the traces (`nt`).

  These inequalities are unconditional consequences of the definitions (`nt_lo`); they
  are not hypotheses.
- **Counter-example without strictness:**
  - `nonstrict_unsound`: abstractly, the non-strict premises hold and the conclusion fails.
  - `zero_delay_cex`: two zero-delay buffers in a loop, `x = y` and `y = x`, on the trace
    `x = y = 1`. Each buffer meets its contract: "if my input was 0 before n, my output
    was 0 before n". All the premises of the non-strict rule hold, yet `x` is not 0.
  - `unit_delay_ok`: the same loop with a one-tick delay meets the strict rule, which
    proves `x = y = 0`.

## (2) Instances

**Per-segment cell lemmas** (`AssumeGuaranteeLinks`). Each lemma needs only the
phase-`k` pin shapes and the unconditional departure bounds:

- `wire_segK`: a wire carries segment `k` of a node to the pin.
- `link_segK`: segment `k` of a link controller (B's `Stage`, real `bd_c2n`).
- `celc_segK`: the same for `bd_c2` (`CelC`).

The proofs reuse `exc_phase_w`, `node_win` and `nt_before`. This truncated form is what
was missing: `link_guar` and `celG_guar` take the infinite `Env1`/`EnvG`.

**Chains of links** (`Chain`, `ChainT`):

- The chain is a source, `N` links and a sink.
- The ends are not gates. Each end is given by an assume-guarantee contract:
  - `SRC_SEG`/`SNK_SEG`: segment `k` holds if the input pin's segments `< k` / `≤ k` hold;
  - plus a wait of at least `lo` for its input.
- `chain_cell` (H_CELL) and `chain_env` (H_ENV, with the time inequalities) give
  `chain_nodes` through `ag_time`.
- `chain_env1` follows: **every link's `Env1` and `Timing1` are derived**, with
  `Es = vl + lo + wl` and `Ea = wl + lo + vl` (exactly `link_link_env`'s slacks).
- `chain_lutFb` gives C's `LutFb`/`FbFirst` for every link.
- Witness `chain_witness N`, for every `N`:
  - every link is B's `Wx.stage_sq` (LUT band `[1, 3]`); the wires have delay 1;
  - H_LAT and both derived slacks are met **with equality**.

**Rings** (`ring_dead`, `ring_no_env1`, witness `ring_witness`). Take any closed network of
B's links, in which every request and acknowledge pin is driven by some link's node. Such a
network is 0 forever, so no link in it has `Env1`. The circle closes on no all-link ring.
A live ring needs a `_set` (token) stage, and B's `Stage` does not model one.

**Any network** (`AssumeGuaranteeFork.net_closed`). This is the rule in reusable form:

- each cell has input pins (driver, wire, offset 0 for request-like pins, 1 for
  acknowledge-like pins);
- H_CELL is a segment contract per cell;
- H_WAIT (`lo ≥ 1`) is the causality side condition;
- H_SP and H_MONO are wire spacing and monotonicity.

**Link + 2-way fork** (`Fork`, `ForkT`):

- Cells: a source, an upstream link `U`, the fork's `bd_c2` `F`, consumer links `L0` and
  `L1`, two sinks; 11 wires. This is `fork_env`'s network with every neighbour present.
- Proved:
  - `fork_nodes`, `fork_pins`;
  - `fork_env1U`, `fork_env1L0`, `fork_env1L1`; `U`'s `Ea` is the **slower** branch cycle;
  - `fork_envCF` (Bfb's `EnvC` of `F`, with the two branch cycles);
  - `fork_lutFb` (C's `link_bound` ×3 and `fork2_cel` premises).

  None of these assumes an environment on any of the four gates.
- `fork_witness` is a live run of the **real** cells: transport LUTs of the real
  `bd_c2n`/`bd_c2` excitations (`keyU`, `keyL`, `keyF`), phases of 7 ticks, and a
  2-tick wire into `L1`.
  - `F`'s pins disagree for one tick each phase, so `F` holds through its feedback.
  - `L0`'s request and acknowledge disagree for 3 ticks, so `L0` also holds through its
    feedback.
  - `EaU = 6` is met with equality.

## (3) gcd_hw `CapstoneNet` (`AssumeGuaranteeCap`)

**Kernel-checked census** (`decide +kernel` over C's `opAt`/`prodOf`/`consOf`):

- The 175 links form exactly **100 maximal link chains** (`heads_count`, `tails_count`).
  The chains cover all 175 links (`chains_cover`), so there is no all-link cycle.
- Chain lengths (`chain_lengths`): 37 chains of 1 link, 51 of 2, 12 of 3. Inside the
  chains are the 75 link-to-link channels.
- Head producers (`head_classes`): steerD 39, forkG3 15, forkH2 12, mux 9, forkH4 9,
  join2 4, steerC 4, forkG2 4, forkG4 4.
- Tail consumers (`tail_classes`): mux 63, join2 17, join1 11, amerge 5, muxn 4.
- No source or sink touches a link.

**`gcd_hw_safe_chains`** is C's `gcd_hw_circuit_safe` with `H_CELLS` of every link replaced
by `InChain`:

- `InChain` says the link is cell `m+1` of a `Chain` of B's physical links, and that
  chain's pins are C's channel traces.
- `physLink_of_inChain` derives Bfb2's `PhysLink`. **Its `Env1` is derived, no longer
  assumed.**
- Witness: `inChain_witness`.

**Which neighbour classes still lack a behaviour lemma.** All 200 chain ends do. These are
the END contracts `SRC_*`/`SNK_*`, assumed inside `InChain`:

| class | count | why there is no lemma |
|---|---|---|
| steerD/steerC | 43 heads | a branch fires only on selected tokens, so its segment index is not the input's; that needs a token enumeration plus H_SEL_STABLE (Bfb2's `gated_phases`) |
| mux | 9 heads, 63 tails | same reason; `muxJ0_lutFb` exists only in the infinite `EnvG` form |
| muxn | 4 tails | same as mux |
| forkG3/forkG4/forkH4 | 28 heads | the ack is a C-tree for N ≥ 3 (Bfb2); no segment lemma, and the n-pin `CelG` has only the infinite `EnvG` form |
| forkG2/forkH2 | 16 heads | the ack C-element has a segment lemma (`celc_segK`), but a fork's request is its upstream's node through a wire, so the fork's upstream class is needed too |
| join2 | 4 heads, 17 tails | the request C-element is covered by `celc_segK`; the join's other input's producer is not |
| join1 | 11 tails | the gate is a pass-through, so the class beyond it is needed |
| amerge | 5 tails | the arbiter: events interleave nondeterministically, so no segment contract |

## Not covered (precisely)

- **End contracts.** No END contract is proved for any gcd_hw class.
- **`InChain` is per link.** It is one existential per link, not one chain datum per
  chain. The real chain discharges all of them, but the theorem does not force the 175
  data to agree.
- **H_TIMES.** H_TIMES is stated as equations (the edge-time definitions). Existence and
  uniqueness of their solution is not proved; the witnesses have solutions.
- **Infinite runs only**, as with `Env1`.
- **Timing hypotheses are sufficient, not proved weakest.** These are H_RT, H_CYC,
  H_WIRE_R and H_WIRE_SPREAD. Exception: the witnesses meet H_LAT and the derived slacks
  with equality.
