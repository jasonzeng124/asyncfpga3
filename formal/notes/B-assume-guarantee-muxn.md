# B-assume-guarantee-muxn (probe Bmn): muxn and the fork trees as cell specs; gcd_hw with fewer contracts

2026-10-29. Follows Bmux2 (`B-assume-guarantee-mux.md`, `gcd_hw_safe_net2`) and, at the lead's
request mid-probe, Bfin2's time-indexed rule (`B-finite-net.md`, `fmixed_closed`,
`gcd_hw_safe_fin_net`). Each file below was checked OK with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/<file>`. All are core Lean only, with no warnings.

| file | content |
|---|---|
| `formal/lean/Formal/Cells/AssumeGuaranteeMuxN.lean` | muxn decode (segment form), `DecSpec`, `ua_cel`, `buf_init`, the 3-way witness, the FASTFALL negative result |
| `formal/lean/Formal/Cells/AssumeGuaranteeMuxNTree.lean` | `Tree5`/`Tree6` → `CelSpec` per node, `fork5_nodes`, gate-level network witnesses for both trees |
| `formal/lean/Formal/Cells/AssumeGuaranteeMuxNFin.lean` | truncated forms: `tdec`, **`tmuxa`**, `tand`, `FDecSpec`/`FMuxASpec`/`FBufSpec`/`FAndSpec`/`FMuxJSpec`, `FTree5`/`FTree6` |
| `formal/lean/Formal/Cells/AssumeGuaranteeMuxNFinWit.lean` | finite-run witnesses (`tmuxa`, `tand`); witnesses with every edge set `True` (decode, trees) |
| `formal/lean/Formal/Cells/AssumeGuaranteeMuxNNet.lean` | censuses, `gcd_hw_safe_net3` (segment form), `gcd_hw_safe_fin_net3` (truncated form) |

There is no sorry, admit, axiom, native_decide, extern or unsafe in these files.
`#print axioms` was run on 31 headline theorems (output in `/tmp/claude-0/probes/Bmn/ax.out`;
the companion file has been removed):
* 21 give `[propext, Classical.choice, Quot.sound]`;
* 6 give `[propext, Quot.sound]`;
* 4 give `[propext]`.

## The muxn's cells (`bdc_muxn3_32`, `emit_muxn`, BDC_FASTFALL = 1)

| cell | count | model | segment rule | time-indexed rule |
|---|---|---|---|---|
| decode `sel[k]`, an inferred LUT3 (H_YOSYS_MAP) | 3 | `dec_segK`, via `dgated_segK` → Bseg's `gated_segK` on the trace `code(s0,s1) == k` | `DecSpec` | `tdec`, `FDecSpec` |
| join `uj_k = bd_c2(in_k_req, sel[k])` | 3 | both pins are four-phase in the join's own numbering | Bseg's `CelSpec GC2` | Bfin2's `FCelSpec GC2` |
| acknowledge `ua_k = bd_c2(j[k], z_ack)` | 3 | `ua_cel`: the real `bd_c2` is `G2` | Bmux2's `MuxASpec` | **`tmuxa`** (new), `FMuxASpec` |
| `uor` LUT1, line stage 0 LUT1 | 2 | buffers (`buf_init`) | `BufSpec` | `FBufSpec` |
| line stages 1..11, LUT2 `8` = `s[i] ∧ |j` | 11 | **not segment-causal** (`gstage_not_causal`) | contract | **`tand`**, `FAndSpec` |
| `|j`, LUT3 `FE` (3-input OR) | 1 | — | contract | contract (Bfin2's `tor_ex` handles only 2 branches) |

Notes on the table:
* **Decode.** The select is a 2-bit index. H_SEL_STABLE is stated per bit: while `ctl_req` is
  high for token `n`, `s0 = bit0 (σ n)` and `s1 = bit1 (σ n)`. H_S_RANGE requires
  `σ n < 4`; the code-3 case is a liveness question, not a safety one. Each decode is its own
  cell: its node feeds `uj_k` through a wire (`H_NJ`: `(pv 1).drv = nd o k`).
* **Acknowledge, segment form.** `MuxASpec` applies unchanged to 3 inputs. `κ` lists input
  `k`'s tokens; the foreign tokens are the other two inputs' tokens.
* **Acknowledge, time-indexed form (`tmuxa`).** This also covers `bd_mux`'s `uxa`/`uya`,
  which Bfin2 left open. `H_ZFALL` now also requires that the edge EXISTS: before the join
  rises for token `m`, `z_ack`'s fall for token `κ m − 1` has happened. Without that, in a
  run that stops, a foreign token could stay high forever.
* **FASTFALL stage (`tand`).** The node's edges are the later rise and the EARLIER fall
  (`xe`). It needs two hypotheses:
  - `H_SAME`: both pins have the same edge set;
  - `H_OVL`: each pin's edge `j` comes before the other pin's edge `j+1`.

  It needs no order between the two falls.
* **The negative result (`gstage_not_causal`).** A FASTFALL stage falls from `|j` before its
  data pin falls. On the witness run the data segment ends at 16 and the stage's edge is at
  13, so H_WAIT fails for any `nb` that includes that segment. Dropping the segment does not
  work either: a data trace with a single dip at `t = 10` breaks the excitation. This is the
  same shape as Bmux2's `or_not_causal`.

**Witnesses.** All use the real INITs, band `[1, 1]`, feedback 1 and reset 4.
* `Wit.muxn_witness` is one 3-way run (codes 0, 1, 2, 0, …):
  - decode 0 fires only on every third token (`κ m = 3m`);
  - `uj0` joins it with `in0_req`;
  - `ua0` holds low through the other two inputs' `z_ack` pulses (`t = 22`).

  Every hypothesis of `dec_segK`, `celG_segK` and `muxa_segK` holds, and every node segment
  follows.
* `tmuxa_fin_witness` is a FINITE run:
  - input 0's token, then a foreign token, then input 0's second token, then quiet;
  - `H_ZFALL` is used non-vacuously, for the second token;
  - the node is clean at every `T` and is low forever after 27.
* `tand_fin_witness` is a FINITE run with one token, in which the stage falls (13) before its
  data pin (16).
* `tdec_witness` runs the 3-way run with every edge set `True`.

## The fork trees (`forkH5` ×2, `forkH6` ×1; `tree_classes`)

* **Shape.** `bd_ctree` N = 5 is `C2(C4(a0..a3), a4)`; N = 6 is `C2(C4(a0..a3), C2(a4,a5))`.
  Every node is a C-element whose pins are four-phase in the node's own numbering, so it is
  Bseg's `CelSpec` (Bfin2's `FCelSpec`). The network rule then composes the nodes; the tree
  needs no special closure argument.
* **The one tree-specific fact is `H_SND` of an inner node.** The leaves answer the ROOT,
  not the inner node.
  - `Tree5`/`Tree6` (and `FTree5`/`FTree6`) assume `H_ACK`, the leaves' bound relative to the
    root, as in `CTreeExact`, plus each node's gate model.
  - `tree5_cel`/`tree6_cel` (and `ftree5_cel`/`ftree6_cel`) derive every node's departure
    bound by composing edges along the tree:
    - `snd_up`: a node's edge comes `lo` after its pins' edges;
    - `snd_wire`: a wire adds `wl`;
    - `snd_down`: an inner node's edge comes `wl + lo_root` before the root's.
  - The inner node's latency budget is `E + wl + lo_root`. This is sufficient, not exact:
    there is no `MaxMin` credit as in `CTreeExact.tree_box_exact`.
* **Real LUTs.** `fork5_nodes` checks the two LUTs of the generated `bd_fork_N5` against the
  `bd_c4`/`bd_c2` equations by kernel decide. N = 6 has no generated netlist in
  `Formal.Gen.Cells`, so its node INITs come from `bd_ctree`'s recursion in `bd_ce.v`; this
  is named **H_TREE6_MAP**.
* **Witnesses.** `Wit.tree5_witness` and `Wit.tree6_witness` are gate-level networks (`GD` on
  7 and 9 cells) with the real LUTs, skewed leaves (the C4's pins disagree at `t = 5`),
  `E = 2`, and wires of 1. `ftree5_witness`/`ftree6_witness` are the same networks with
  every edge set `True`. They are infinite runs only; there is no finite tree witness.

## gcd_hw (`AssumeGuaranteeMuxNNet`)

### Segment form: `gcd_hw_safe_net3`

`GcdNetOK3` contains `GcdNetOK2` (`toOK2`): every new spec gives a segment contract. So the
theorem is `gcd_hw_safe_net2` applied to a strictly weaker contract set.

* **Census.** `op_classes3`: the operators left not fully tied are `join1` 11 and `sink` 18
  (no cell) and **`amerge` 9**.
* **Contracts remain on:**
  - 38 steer `uack` ORs and 21 mux `uor` ORs;
  - the muxn's `|j`;
  - the muxn's 11 FASTFALL stages;
  - every cell of the 9 amerges.
* **Removed from Bmux2's list:** the muxn's decodes, joins, acknowledges and two buffers; all
  7 tree nodes.

### Truncated form: `gcd_hw_safe_fin_net3` (runs that stop)

`FGcdNetOK3` contains Bfin2's `FGcdNetOK` (`toOK`).

* **Census.** `op_classes_fin3`: `join1` 11, `sink` 18, `amerge` 9, `src` 3.
* **Contracts remain on:**
  - the muxn's `|j` (1 cell);
  - the 3 sources (no truncated `src` lemma);
  - every cell of the 9 amerges.
* **Removed from Bfin2's list:**
  - all cells of the 21 muxes: joins `FMuxJSpec` (a wrapper of `tmuxj`), acknowledges
    `tmuxa`, delay buffers `FBufSpec`, `uor` via Bfin2's `FOrSpec`;
  - the whole muxn except `|j`;
  - all tree nodes.

## Not covered (precisely)

* There is no joint witness of `GcdNetOK3` or `FGcdNetOK3`; each cell spec is witnessed
  separately. The elaboration (which cell drives which pin) is abstract.
* Departure bounds (`H_SND*`, `H_ZFALL`, `H_ACK`, `H_OVL`, `H_SEL_STABLE`) are edge-time
  inequalities, not derived from delay constants.
* The muxn `|j` needs a 3-branch version of `tor_ex`. Not done; that is OR work (Bfin2).
* The tree and decode witnesses are infinite runs. The finite-run witnesses cover only
  `tmuxa` and `tand`.
* The tree condition is the last-arrival sufficient form, not `CTreeExact`'s exact per-node
  condition.
* H_YOSYS_MAP (decode INITs) and H_TREE6_MAP (the N = 6 node INITs come from RTL, not from
  a generated netlist) are named, not checked against a routed netlist.
