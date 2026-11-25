# B-assume-guarantee-mux (probe Bmux2): mux cells, sources, the ORs; gcd_hw with fewer contracts

Lean (core only, no Mathlib in the closure). Each file checked OK with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/<file>` (autoImplicit=false, no warnings):

- `formal/lean/Formal/Cells/AssumeGuaranteeMux.lean`: the generic C-element segment lemma,
  the mux joins and acknowledges, the source, the sink (no cell), witnesses;
- `formal/lean/Formal/Cells/AssumeGuaranteeMuxOr.lean`: the steer/mux ORs, the brackets
  derived from causality, the negative result, witnesses;
- `formal/lean/Formal/Cells/AssumeGuaranteeMuxNet.lean`: four new cell specs,
  `mixed_closed2`, the gcd_hw census and `gcd_hw_safe_net2`.

No sorry, axiom or native_decide. `#print axioms` (companion file, since removed) on the 30
headline theorems: `[propext, Classical.choice, Quot.sound]` or a subset (`snk_wire`: none;
the kernel census and gate lemmas: `propext`).

## (1) The ORs (`AssumeGuaranteeMuxOr`)

Steer `uack` = `ack₀ ∨ ack₁`; mux `uor` = `j₀ ∨ j₁` (then the `udly` buffers). Token `n` is
carried by branch `σ n`. `cnt σ b n` counts the earlier tokens on branch `b`
(`kappa_cnt`: it agrees with the steer's own enumeration `κ_b`).

- **`or_exc_segK`.** Segment `k` of the OR excitation, edges `oe` (token `n`'s edges on its
  own branch), from the branch segments `sx σ b k` and the brackets `Brk` of tokens
  `≤ k/2`. `Brk n`: the idle branch's last fall is before token `n`'s acknowledge rise, and
  its next rise is after token `n`'s acknowledge fall.
- High segments read only the active branch.
- `uack_segK`, `uor_segK`: node segments of the REAL LUTs (`uack_gate`, `uor_gate`).
- **`brk_of_causal`: the interleaving is derived.** From two edge-time facts:
  - `C1`: a branch acknowledge rises for token `n` only after the input request rose for
    `n`;
  - `C2`: the input request rises for `n+1` only after the active acknowledge fell for `n`;
  - plus `H_LATER` (the idle branch gets a later token).
  `c1_of_kappa`: `C1` from `gc κ_b γ j ≤ α_b j`, i.e. H_SEL_STABLE + `κ_b` (through
  `gated_segK`'s phase starts) and the H_WAIT chain branch → consumer → wire.
- **Negative, `Wit.or_not_causal`.** A low segment must read the IDLE branch at a segment
  that ends at its NEXT rise. On the witness: segment `k = 2` reads the idle branch up to
  `20`; the OR's node edge is `13`.
  - So no dependency bound that includes that segment meets `net_closed_gen`'s H_WAIT.
  - Dropping it fails too: a trace that matches every earlier segment and every edge (so
    every bracket) but pulses high on `[9, 11)` breaks segment 2.
  - The OR's low segment depends on a PREFIX of a later-ending segment. The end-ordered
    segment rule cannot discharge any OR, under any `nb`.

## (2) The mux (`AssumeGuaranteeMux`)

- **`celX_segK`**: a C-element segment from the phase's excitation condition alone: at each
  instant either all pins show `Vph j`, or one does and `nt + E` has passed.
- **`muxj_segK`** (`uj0`/`uj1`): `celG_segK` ∘ `gated_segK`. Reads `x_req` at segment `k`,
  `ctl_req` at `≤ sN κ k`. `uj0_cel`/`uj1_cel`: the REAL LUTs are the `G2` model.
- **`muxa_segK`** (`uxa`/`uya` = `C(j, z_ack)`): `z_ack` carries every output token. The
  cell holds through the other input's tokens under exactly:
  - `H_SNDZ`: the next `z_ack` edge of ANY token comes `E` after the cell's edge;
  - `H_ZFALL`: `ζ (2κm − 1) ≤ ρ (2m)`, i.e. `z_ack` has fallen for all earlier tokens
    before the join rises for this input's token `m`.

  No `σ` is needed. Reads stay strictly causal (`z_ack` segments `≤ sN κ k`).
  `muxa_conds_tight`: a violation of either condition makes the excitation `1` in the low
  phase (`C(1,1) = 1`; `C(0,1; q=1) = 1`). Physically both conditions are H_WAIT chains:
  - `H_ZFALL`: the join rises after the control's next token, which follows `ctl_ack = z_ack`
    falling;
  - `H_SNDZ`: the next `z_ack` rise needs a new `z_req`.
- **Buffers** (`BufSpec`, `udly_id`): the `udly` LUT1s are `lutnf_segK` cells.

## (3) Source and sink

- **`src_segK`** (REAL `bd_src`, LUT1 `¬ack`, no reset). It keeps `src_lutSI`'s
  H_PWR_SRC: before `hi` the output may only rise.
  - Edges `srcE`: the power-up rise, then `nt` after each ack edge.
  - Segment `k` reads ack segments `< k`. `src_wait`: its H_WAIT.
  - A request already high at reset release is tolerated by `muxj_segK` (its
    `R ≤ max(...)`), but not by a `LinkSpec` consumer (`H_RST_EARLY`). Bseg's `head_tied`
    shows no gcd_hw link is fed by a source. `OpsGcd` has `srcA`/`srcB` feeding the muxes;
    the third source's consumer was not checked here.
- **`snk_wire`**: `bd_snk` has no cell (`ack` IS the `req` net). It is not a contract at
  all: the producer's ack pin is the routed path producer → sink → producer, a `Wire`
  (H_WIRE).

## (4) gcd_hw (`AssumeGuaranteeMuxNet`)

- **Specs.** `MuxJSpec`, `MuxASpec`, `SrcSpec`, `BufSpec`, each with `*_spec_cell` and
  `*_spec_wait`.
- **`mixed_closed2`** closes a network whose cells are the Bseg specs, these four, or
  contracts. Also `mixed_pins2`, `link_spec_env1_2`, and the witness `mixed2_witness`
  (Bseg's live chain).
- **`gcd_hw_safe_net2`**: C's `gcd_hw_circuit_safe`, with all 175 links' `H_CELLS`
  discharged by ONE network (`GcdNetOK2`) in which, beyond Bseg's tied cells:
  - every mux `uj0`, `uj1`, `uxa`, `uya` and both `udly` buffers carry B's gate model
    (21 × 6 cells);
  - every source does too (3).
- **Contracts left** (`op_classes2`, kernel census): the 38 steer `uack` and 21 mux `uor`
  ORs; muxn 1; amerge 9; forkH5 2; forkH6 1. `join1` (11) and `sink` (18) have no cell.
  Down from Bseg's list: −21 muxes (all but `uor`), −3 sources; the sinks are cell-free.

## Not covered (precisely)

- **The ORs (59 cells) cannot be closed by the segment rule.** That needs a time-indexed
  rule: prefix guarantees ("clean up to `T`") for every class (link, C-element, steer
  branch, wire, mux, source). Not done. The OR lemma itself is ready for it: its reads
  are per token.
- **Departure bounds are edge-time inequalities**, as in Bseg: `H_SND*`, `H_ZFALL`,
  `H_SPACE`, `C1`/`C2`. They are not derived from delay constants. `C1`/`C2`/`H_ZFALL`
  are named H_WAIT chains, not proved as path lemmas on `GD`.
- **The elaboration is abstract** (`GcdNet2`). There is no witness of the whole
  `GcdNetOK2`. Each spec is witnessed individually with the REAL LUT and nonzero delays:
  `muxj_witness`, `muxa_witness` (foreign token), `src_witness`, `uack_witness`.
- **Infinite runs.** Edges are total and `κ` is total (as in Bseg). The OR bracket's
  second half needs `H_LATER`; without a later token on the idle branch (a finite run)
  it is an inequality on the edge of an event that never happens. That is Bfin's ground.
