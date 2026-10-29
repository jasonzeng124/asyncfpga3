# B-assume-guarantee-ends (probe Bseg): segment lemmas for the chain-end classes, gcd_hw as one network

Lean (core only, no Mathlib in the closure), each checked OK with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/<file>` (autoImplicit=false, no warnings):

- `formal/lean/Formal/Cells/AssumeGuaranteeEnds.lean`: the general network rule, the
  segment lemmas (C-element with any pins, steer branch), the real-cell laws, witnesses;
- `formal/lean/Formal/Cells/AssumeGuaranteeEndsNet.lean`: cell specs, the mixed network
  closed, `Env1` of a link derived, witness;
- `formal/lean/Formal/Cells/AssumeGuaranteeEndsCap.lean`: gcd_hw census and
  `gcd_hw_safe_net`.

No sorry, axiom or native_decide. `#print axioms` (companion file, since removed) on the 22
headline theorems gives `[propext, Classical.choice, Quot.sound]` or a subset: the laws and
kernel census theorems give `propext`; `steer_wait` gives `propext, Quot.sound`;
`ctree1_wire` gives none.

## The question

Bnet (`B-assume-guarantee.md`) closed the circle by a strictly causal induction over node
segments. On gcd_hw, though, the 200 chain ends (100 heads, 100 tails) stayed assumed
contracts inside `InChain`. This probe asked for two things:

- segment lemmas for the end classes (join, fork, steer, mux);
- `net_closed` instantiated on `CapstoneNet`.

## (1) The rule, generalised (`AssumeGuaranteeEnds` §1)

`net_closed` reads a pin at a fixed offset: segment `k` reads the pin's segments up to
`k - off`. A steer branch reads only some of its input's tokens, so this does not fit it.

- **`net_closed_gen`**: each pin carries a dependency bound `nb`. Segment `k` of the cell
  reads the pin's segments `k' < nb k`.
- The causality side condition is H_WAIT: `gE k' + lo c ≤ τ c k` for every read segment,
  with `lo ≥ 1`. The rule needs no monotonicity hypothesis.
- `net_closed_of_gen` recovers Bnet's `net_closed`, with `nb k = k + 1 - off`.
- `net_pins_gen`: every pin is clean too.

## (2) Segment lemmas

**C-element with any number of pins:**

- `celG_segK` / `celG_cell` (Bfb2's `CelG`, any `G` with `CelLaw`). Segment `k` of the node
  follows from:
  - the pins' phase-`k` shapes only;
  - the departure bounds `H_SND`.
- `c j` is the last pin arrival. `cmax` over `Fin n` meets `H_ARR`/`H_LAST` by
  construction (`cmax_arr`, `cmax_last`).
- `celG_wait`: H_WAIT, unconditional.
- Laws of the REAL cells, by `decide +kernel` on the generated netlists:

  | lemma | cell | used for |
  |---|---|---|
  | `c2_gen`, `lawC2` | `bd_c2` | fork N=2 acknowledge; join and bjoin N=2 request |
  | `c3_gen`, `lawC3` | `bd_ctree` N=3 | fork N=3 |
  | `c4_gen`, `lawC4` | `bd_c4` | fork N=4 |

- **Correction to Bnet's table:** forks with N = 3 and N = 4 are ONE flat LUT each
  (`bd_ctree` instantiates `bd_c3`/`bd_c4` for N ≤ 4; `bd_ce.v`). They are not C-trees, so
  `celG_segK` covers them.
- Only forkH5 (2) and forkH6 (1) are trees. No chain end touches them.

**Join N = 1** (`ctree1_wire`): `bd_ctree` N=1 has no cell; its output is its input net. A
join1 is a wire, not a gate. It needs no lemma, and it has no `lo ≥ 1`, so it cannot be a
`net_closed` cell either. The class beyond it is the relevant one.

**Steer branch:**

- `gated_segK` is the segment form of Bfb2's `gated_phases`. Segment `k` of `r ∧ (s == b)`
  follows from the input's segments `≤ sN κ k`, where `sN κ k = 2·κ(k/2) + k%2`, under:
  - H_SEL_STABLE;
  - an enumeration `κ` of the tokens steered to `b`.
- `lutnf_segK`: a feedback-free `Win` LUT with H_NO_REVERT carries one excitation segment to
  its node.
- `steer_segK`: the real `bd_steer` `u` (O5/O6). `steer_wait`: its H_WAIT, unconditional.

**Witnesses:**

- `celG_witness`: the real `bd_ctree` N=3 LUT, band `[1, 2]`. Its pins disagree at t=4, so
  it holds through its feedback. Every segment follows.
- `steer_seg_witness`: the select alternates per token, so branch 0 receives only the even
  tokens (`κ m = 2m`). It is low during token 1 although the input request is high
  (`sq 4 12 = true`, `Ow 13 = false`).

**No segment lemma:**

- **steer acknowledge OR (`uack`):** its excitation is clean only if the two branch acks
  interleave in token order. That is an inequality between edge times of different cells,
  and no segment shape gives it.
- **`bd_mux`:**
  - `uxa`/`uya` = C(j0/j1, z_ack). `z_ack` also carries the OTHER input's tokens, so the
    pin is not four-phase in the cell's own numbering, and `CelG`'s environment does not
    apply. These cells hold through the foreign tokens, which needs a different hold
    argument.
  - `uor` has the steer OR's problem.
  - `uj0`/`uj1` would follow from `celG_segK` plus `gated_segK`, but are not packaged.
- **`muxn`, `amerge`:** no lemma.

## (3) Mixed networks (`AssumeGuaranteeEndsNet`)

**Cell specs.** Each is B's gate model plus H_TIMES (the node's edges read off its own
pins), with no environment and no contract:

| spec | cell | real LUT |
|---|---|---|
| `LinkSpec` | link | `bd_c2n` |
| `CelSpec G n` | C-element | `bd_c2` / `bd_c3` / `bd_c4` |
| `SteerSpec` | steer branch | `bd_steer` `u` |

- The departure bounds (`H_SND`, `H_RCV`, `H_RST_EARLY`; for a steer `H_SPACE`, `H_INC`) are
  **edge-time inequalities**.
- Every other cell is a `Contract`: a segment contract plus its H_WAIT.

**Proved:**

- H_CELL and H_WAIT per class: `*_spec_cell`, `*_spec_wait`.
- `mixed_closed`: every node is clean. `mixed_pins`: every pin is clean.
- `link_spec_env1`: a link cell's `Env1` and `Timing1` are DERIVED.
- Witness `Wit.mixed_witness`: Bnet's live chain `wD 1` as a mixed network.
  - Cells: a real `bd_c2n` link as a `LinkSpec`; source and sink as `Contract`.
  - Departure bounds met with equality.

## (4) gcd_hw (`AssumeGuaranteeEndsCap`)

**Kernel census** (`op_classes`), over gcd_hw's 367 operators:

| | count | classes |
|---|---|---|
| tied | 301 | links 175; forks N≤4: 41; joins N=2 (`join2` 9, `bjoin2` 38): 47; steers (`steerC`, `steerD`): 38 |
| not tied | 66 | `join1` 11 (no cell), `mux` 21, `muxn` 1, `amerge` 9, `src` 3, `sink` 18, `forkH5` 2, `forkH6` 1 |

"Tied" means every handshake cell is gate-modelled. For a steer, only the two branches are;
its acknowledge OR is not.

**Chain ends by the neighbouring operator's class** (`head_tied`, `tail_tied`):

- Heads: 91 of 100 have a tied producer: steer 43, fork 44, join2 4. The 9 mux heads are
  open.
- Tails: only the 17 join2 tails are tied. The open ones are mux 63, join1 11, amerge 5,
  muxn 4.

**`gcd_hw_safe_net`** is C's `gcd_hw_circuit_safe` with `H_CELLS` of all 175 links
discharged by ONE gate-level network of gcd_hw (`GcdNet`, `GcdNetOK`). It has NO `InChain`
and no chain-end contract.

- The tied cells carry B's gate models, with C's channel traces as their pins:
  - link: `(ch i).req`, `(ch o).ack`;
  - fork: `(ch o_k).ack`;
  - join: `(ch i_k).req`;
  - steer branch: `(ch j).req`.
- `gcd_net_nodes`: every node is clean.
- `physLink_of_net`: Bfb2's `PhysLink` for every link, with `Env1` derived.

**Exactly what stays assumed** (beyond C's `H_CELLS` of the 192 non-link operators,
H_BUNDLE and H_CM_FORCED):

- **Segment contracts**, for:
  - the 38 steer `uack` ORs;
  - every cell of the 21 muxes;
  - the muxn;
  - the 9 amerges;
  - the 3 sources and 18 sinks;
  - the 3 fork trees.
- **Edge-time inequalities:**
  - each tied cell's departure bounds;
  - H_SP for every wire;
  - for steers: H_INC, H_SPACE, H_SEL_STABLE and the enumeration `κ`.
- **Per link:** the two outgoing wires, H_WIRE_SPREAD and the latch data fields (as
  `PhysLink`).

## Not covered (precisely)

- **Not a strengthening on every axis.** `Chain` derives the departure bounds and the wire
  spacing from delay constants (H_RT, H_WIRE_R). `GcdNetOK` assumes them as edge-time
  inequalities. Deriving them on a mixed network is a path argument along each handshake
  cycle (each H_WAIT adds `wl + lo`), and it was not done.
  - So `gcd_hw_safe_net` trades the 200 end contracts for edge-time timing hypotheses.
  - It does not imply `gcd_hw_safe_chains`, and is not implied by it.
- **The elaboration is abstract.** The hypotheses fix every tied cell's B model and pin
  TRACES, not the pins' drivers. Which chain ends border only tied cells after resolving
  pass-throughs (a fork's request and a join's acknowledge broadcast are wires) is not
  kernel-checked.
  - By the census, the 4 join2 heads do (both neighbours are links).
  - Every steer head borders a `uack` contract.
- **No witness for all of `GcdNetOK`.** That would need a live run of all of gcd_hw. The
  specs are witnessed individually (`celG_witness`, `steer_seg_witness`,
  `Wit.mixed_witness`).
- **Infinite runs only**, as with `Env1`. A steer branch needs infinitely many tokens
  (`κ` total).
