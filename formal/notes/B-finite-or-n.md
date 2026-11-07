# B-finite-or-n (probe Bor3): the n-branch truncated OR; muxn's `|j` gate-modelled

2026-10-29. Follows Bfin2 (`B-finite-net.md`: `tor_ex`, `tuack`, `tuor`, 2 branches) and
Bmn (`B-assume-guarantee-muxn.md`: `gcd_hw_safe_fin_net3` left a truncated contract on
`bdc_muxn3_32`'s `|j`, the 3-input OR of the join outputs `j[0..2]` that feeds `uor` and
gates the FASTFALL line).

## File

| file | result | content |
|---|---|---|
| `formal/lean/Formal/Cells/FiniteOrN.lean` | **OK** (`/tmp/claude-0/btools/bcheck.py Formal/Cells/FiniteOrN.lean`, core Lean only, no warnings) | `cntN`/`oeN`/`LorN`, `tor_exN`, `tor_ex_of_N`, `or3_real`, `or3_any_order`, `or3_init_unique`, `tor3`, `FOr3Spec`, `for3_spec_cell`, `muxn_count`, `FGcdNet3'`/`FTied3'`/`FGcdNetOK3'`, `gcd_hw_safe_fin_net3'`, `Wit3.or3_witness`, `Wit3.for3_spec_witness` |

No sorry, admit, axiom, native_decide, implemented_by, extern, unsafe. Axiom printout
(14 theorems, `/tmp/claude-0/probes/Bor3/ax.out`, the companion file was removed): `tor_exN`,
`tor_ex_of_N`, `tor3`, `for3_spec_cell`, `FGcdNetOK3'.toOK3`, `gcd_hw_safe_fin_net3'`,
both witnesses: `[propext, Classical.choice, Quot.sound]`; `cntN_bool`, `or3_real`,
`or3_any_order`, `or3_init_unique`, `or3_iff`, `muxn_count`: `[propext]`.

## (1) The n-branch OR

The branches are indexed by any type `β` with decidable equality. Token `n` is carried by
branch `σ n` (for the muxn, `σ n` is the decoded select code of control token `n`), and
`κ b` enumerates branch `b`'s tokens. `cntN σ b n` counts the tokens before `n` on branch
`b`. The merged edges are `oeN σ α (2n + r) = α (σ n) (2·cntN σ (σ n) n + r)`, and edge
`k` exists (`LorN`) iff that branch edge exists. This is Bfin2's `oe`/`Lor` with `Bool`
replaced by `β`.

`tor_exN`: assume
* every branch is clean on `[0, T)`;
* the per-branch enumerations;
* **H_DOWN_N**: merged edges exist in order;
* **H_ORD_N**: merged edges that exist increase, i.e. the branches interleave in token
  order;
* `H_OR`: `x t` iff some branch is high.

Then `x` is clean on `[0, T)`, with edges `oeN` and edge set `LorN`. These are the same
hypotheses as the 2-branch rule. Nothing new appears for n > 2: the active branch is
high, and every idle branch is between its own tokens, so it is low. A branch that never
fires again is constant.
`tor_ex_of_N` derives Bfin2's `tor_ex` from it (`β = Bool`; `cntN_bool`, `oeN_bool`,
`lorN_bool`), so the generalisation loses nothing.

Inherited convention, stated: `κ b` is an infinite enumeration, so `σ` is an infinite
select sequence that hits every branch infinitely often. A finite run has finitely many
EXISTING edges; the tokens after it are virtual (as in Bfin2's `WitOr`).

## (2) The real `|j` LUT

* The INIT is `8'hFE` on `[j2, j1, j0]` (`AMergeGates.or3`). It was taken from the yosys
  0.62 run of the emitted `bdc_muxn3_32` recorded in `B-amerge.md` (H_YOSYS_MAP). The
  RTL is `bdc/emit.py` `emit_muxn`: `LUT1 uor (.I0(|j))` and
  `bd_delay_gated udly (.a(either), .gate(|j))`. The re-emitted gcd Verilog
  `/tmp/claude-0/probes/Bsa5/gen/gcd.v` was read and shows the same text.
* Kernel `decide` proves three facts:
  - `or3_real`: the LUT is `j0 ∨ j1 ∨ j2`;
  - `or3_any_order`: `8'hFE` is the OR under every pin order, so the pin order recorded
    in H_YOSYS_MAP does not matter;
  - `or3_init_unique`: `8'hFE` is the only LUT3 INIT (of 256) that computes the 3-OR.
* So H_YOSYS_MAP shrinks, for `|j`, to one claim: yosys maps `|j` to ONE LUT3 on the three
  `j` nets. Given that, the INIT is forced.
* `tor3`: the real LUT with B's `Win` + H_NO_REVERT model, H_PWR and the floor
  (via `tnode`).

## (3) gcd_hw

* `FOr3Spec` is the `|j` cell spec. Its fields are:
  - pins `[ap 2, ap 1, ap 0]`;
  - the real INIT and gate model;
  - H_TIMES on `oeN` of the pin edges;
  - H_CNT, giving `LorN`;
  - the enumerations, H_DOWN_N, H_ORD_N and H_FLOOR.

  `for3_spec_cell` proves that it gives `FCellOK`.
* `muxn_count` (kernel census): gcd_hw has exactly one muxn.
* `FGcdNet3'` adds the `|j` cell `nor`. `FGcdNetOK3'` takes `FGcdNetOK3`'s fields
  verbatim and adds `H_FNOR`: the `|j` spec, with pin `k` driven by the join `nj o k`.
  Its `H_REST` asks for contracts only outside `FTied3'`. `FGcdNetOK3'.toOK3` proves that
  `FGcdNetOK3'` contains `FGcdNetOK3`.
* **`gcd_hw_safe_fin_net3'`** gives C's gcd_hw safety for runs that stop.
  - Truncated contracts remain only on the 3 sources and the cells of the 9 amerges.
  - The operator census (`op_classes_fin3`: `join1` 11, `sink` 18, `amerge` 9, `src` 3)
    is unchanged. join1 and sink have no cell, and the muxn was already counted as tied
    at operator level. What is new is that every cell of the muxn is now tied.

## (4) Witnesses

`Wit3.or3_witness` is a finite run.
* **Tokens.** There are 4 control tokens with codes `0, 1, 2, 0`, so every branch fires
  and branch 0 fires twice.
* **Branch traces.** `j[0]` is high on `[4, 8)` and `[22, 26)`, `j[1]` on `[10, 14)`, and
  `j[2]` on `[16, 20)`. After that the run is quiet forever.
* **The OR cell.** It uses the REAL INIT, with LUT window `[2, 3]` and an actual delay
  of 2.
* **What holds.** Every hypothesis of `tor3` holds:
  - the enumerations `κ b m = 3m + b`;
  - H_DOWN_N;
  - H_ORD_N on the 8 merged edges `4, 8, 10, 14, 16, 20, 22, 26`;
  - `Win`, H_NO_REVERT, H_PWR and the floor.
* **Result.** The node is clean at every `T`. Its 8 edges are at
  `6, 10, 12, 16, 18, 22, 24, 28`, it is low from `28` on, and each branch has an
  existing token.

`Wit3.for3_spec_witness` is a 4-cell `GD`: three driver cells, whose edges come one tick
before their pins' (pin windows `[1, 1]`), and the `|j` cell. It meets every field of
`FOr3Spec`, and so `FCellOK`. `FNetW`, i.e. the `Wire` relation and the floors, is not
part of the spec and is not checked there.

Degenerate parts, stated:
* The branch traces are given; they are not produced by real joins `uj_k`.
* The spans of different tokens do not overlap in this run: each branch falls before the
  next one rises. That is what H_ORD_N demands, so it is not a special choice.

## What remains (exactly)

* **Contracts in the truncated gcd_hw theorem:** the 3 sources (`src`; Bfin3's probe) and
  every cell of the 9 amerges (Barb5's probe). join1 and sink have no cell.
* **H_ORD_N / H_DOWN_N for the muxn** are EDGE-TIME hypotheses: join `j[σ(n+1)]` rises
  only after `j[σ n]` has fallen. They are not derived from delay constants or from the
  joins' and acknowledges' specs. The natural derivation goes through
  `z_ack → ua_k → in_k_req → uj_k`, the muxn's own four-phase cycle, and is not done.
* There is no joint witness of `FGcdNetOK3'`; each spec is witnessed separately. The
  elaboration is abstract.
* H_YOSYS_MAP for `|j` (one LUT3 on `j[0..2]`) has not been checked against the full
  gcd_hw synthesis JSON or a routed netlist.
* The segment-form `gcd_hw_safe_net3` keeps its `|j` contract. The OR is not
  segment-causal (Bmux2's `or_not_causal`), so only the time-indexed rule carries it.
