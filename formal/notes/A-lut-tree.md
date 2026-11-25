# A-lut-tree: the LUT as a pass-transistor mux tree (track 4, shard A)

Files:
- `formal/lean/Formal/Core/LutTree.lean`: proved. It checks cleanly, with no sorry, axiom, native_decide or bv_decide. Core Lean only, no Mathlib.
- `formal/lean/Wip/LutTree.lean`: the next steps (conjectures, not built).

Check command:

    cd formal/lean && ../slot.sh lake env lean Formal/Core/LutTree.lean

The command gives no output, in about 10 s. `#print axioms` on the main theorems shows only
`propext`, `Quot.sound` and `Classical.choice` (from `simp`/`omega`).

## What the silicon is (research)

- **Structure.** UG474 and the LUT6_2 primitive docs (UG953/UG974) say the same thing. The LUT6 is two LUT5s
  sharing A1..A5. O5 is the lower LUT5 (INIT[31:0]), and O6 = A6 ? upper : lower.
  In dual-LUT5 use, A6 is tied high. So A6 drives the **root** mux, and O5 is
  tapped one level below it.
- **Which pin drives which level.** Vivado documents A6/A5 as the fastest pins and A1/A2
  as the slowest (UG903/UG912 LOCK_PINS, UG904 critical-pin optimisation). In a pass-transistor
  tree, a select near the root has the shortest path to the output. A select at the leaves
  drives the most muxes and passes through every level, so it is slowest (Elmore
  delay grows with depth: IPSJ DAS2016018). So A6 is at the root and A1 at the SRAM side. This is inferred
  and not documented: Xilinx publishes no transistor schematic. Note that prjxray-db's
  `zynq7/timings/CLBLL_L.sdf` gives **all six A*→O6 arcs the same delay**
  (0.045::0.056 fast, 0.100::0.124 slow). The sign-off model lumps them, so it
  cannot be used to recover the tree order. The A*→O5 arcs do differ slightly (A5 is
  the fastest there).
- **Glitches.** Vendor folklore holds that a LUT gives no glitch on a single input change (Altera staff on
  the Altera forum; Xilinx app notes from the XC3000/4000 era, as cited in an MSU
  thesis; K. Stevens' FPGA async work treats LUTs as free of logic hazards for SIC
  in fundamental mode). None of this is a current 7-series datasheet guarantee. Multi-input
  changes are agreed to glitch when the function has a function hazard.
- **The GLS model** (`origin/claude/research:cells/gls/prims.v`, `SLICE_LUTX`)
  builds the tree with **A6 at the leaves and A1 at the root**, which is the reverse of the silicon order. It
  uses Verilog `?:`. With an X select, `?:` keeps the bits on which both sides agree and makes the rest X, which is
  exactly `kmux`. So by `evalTree_eq_tableEval` and `evalTree_swap`, its zero-time X behaviour
  is exactly the INIT-table Kleene semantics, and the reversed order is harmless
  there. It differs from silicon only in timing. It has one lumped inertial specify delay per
  pin, so it neither models per-level skew nor passes runts shorter than about 124 ps.

## What checks (theorem names)

1. `evalTree` is the mux-tree Kleene evaluation. Inputs are root first `[A6,…,A1]`, and the INIT is
   addressed MSB first (`addrOf`, `initFun`: bit = A6·32+…+A1).
2. **Fidelity:** `evalTree_eq_tableEval` holds for every k, every INIT and every K3 vector.
   The tree equals `tableEval` ("1 if all consistent entries are 1, 0 if all 0, else X").
   It is proved by induction on k, with the key step `summ_join`. Supporting lemmas:
   `mem_addrs_iff` (the enumerated entries are exactly the `Consistent` ones),
   `tableEval_eq_one_iff`, `tableEval_eq_zero_iff`, `evalTree_ofBool` (Boolean agreement).
   **Order independence:** `kmux_swap_levels` and `evalTree_swap`. Swapping two adjacent levels
   with the INIT permuted to match gives the same Kleene function, so the Kleene LUT does not depend
   on the order of inputs in the tree.
3. **Timed hazard model** (`PhysTree n`). Each node `p` has its own select-arrival delay
   `dsel p` and its own per-child data delays `ddat p b`. Each level's pin has an arbitrary
   3-valued waveform. The delays are arbitrary integers, with no bounds and no ordering assumed.
   - `PhysTree.node_sound` / `root_sound`: under `H_sram` and `H_mux_kleene`, every node
     at every instant is ⊒ its static Kleene value. This is the monotone/X-passing argument
     (`kmux_mono`).
   - `PhysTree.glitch_free`: if every entry consistent with the pins' abstraction is
     `c`, the output is `c` at every instant, for ANY delays and any order and skew of
     the changing pins, even if they dwell mid-rail or ring. So a mux tree has no *logic*
     hazards, only function hazards.
   - `PhysTree.sic_glitch_free`: if old and new pins differ in ≤ 1 position and the entries are equal,
     there is no glitch, whatever level the pin drives.
   - Exact model `exactNode`/`exactTree` (each mux IS kmux of its delayed inputs):
     `exact_H_sram` and `exact_H_mux` show it is an instance, so the hypotheses are consistent.
     `exact_sic`: with a single changing pin, the output equals ONE mux on that pin, delayed by the
     active path's delay `D`, between the old and new entries. `exact_sic_clean`: a clean pin edge
     (b, X on [t1,t2), ¬b) gives at most one clean output transition at [t1+D, t2+D).
     The tree order shows **only** through `D`, which depends on the pin's level and on the
     active address path.
   - Kleene abstraction vs physical tree on a function hazard: in `and_abstraction_X`
     (AND, (0,1)→(1,0)), the Kleene abstraction gives X. `and_glitch`: with A arriving
     first, the exact model really outputs 0,1,0. `and_no_glitch_other_order`: with B
     first, it stays 0.
4. **Input buffers:** these are modelled as `dsel p`, a per-mux-copy arrival delay. Different copies of
   one input pin may switch at different times (distribution skew). The glitch-freedom theorems hold
   for any such skew. For multi-input changes WITH a function hazard, the outcome depends on the
   arrival order *at the specific muxes on the active path*, not at the pins. That is why
   `and_glitch` and `and_no_glitch_other_order` differ.
5. LUT6_2: `lut6O6_eq` (O6 = kmux A6 O5 upper) and `initFun_lower` (O5 reads INIT[31:0]).
   There are sanity examples on INIT=0x8 (AND2) and a majority-3 LUT holding its feedback with one input X.

## Explicit hypotheses (not known about the silicon) and how to test them

| Hypothesis | Where | Test |
|---|---|---|
| `H_mux_kleene`: if the select is mid-rail and both data inputs are equal and valid, the node stays at that level, with no charge-sharing dip below a valid level (output restorer/buffer holds). If the select is valid, the selected data input passes. | `PhysTree.H_mux_kleene` | Board: drive an input of a LUT with INIT constant on that input (e.g. O = A2) with a slow edge or a ring-oscillator-rate toggle, and count output edges with a fabric counter (async-reset ripple counter clocked by O). A nonzero count falsifies the hypothesis. Repeat with the toggled pin on A1 (leaf) and on A6 (root). GLS cannot test this: there are no transistor models. |
| `H_sram`: SRAM leaves are static and undisturbed by reads. | `PhysTree.H_sram` | This is implied by normal LUT operation. It is low risk. |
| A6 at the root, A1 at the leaves (only affects `D`). | notes only; theorems are order-free | Board: measure per-pin A_i→O6 delay with a ring through one LUT, rerouting the ring input to each pin (LOCK_PINS) and holding the routing equal. Expect A6 < … < A1 if the inference is right. |
| Exact model (transport delays, kmux exactly). It is used only for `exact_sic*` and the glitch example. | `exactNode` | GLS: replace SLICE_LUTX's inertial specify delays with a per-level transport model and compare against the board for glitch counts on a hazardous two-input change. |
| A monotone select gives a monotone output (no runt inside the X window). This is NOT assumed in the proved file. | Wip `sic_monotone_under_H_mux_monotone` | Same counter experiment as above, but with an INIT that does depend on the pin: count exactly one output edge per input edge. |

## Verdict

**Works.** The fidelity theorem, order independence, and SIC / no-function-hazard glitch
freedom under explicit, testable hypotheses are all proved. The exact timed model
is shown to be consistent with those hypotheses. The single-change path-delay theorem and a
concrete multi-input glitch are also proved. Effort to finish:
- unate multi-input change gives a single transition (Wip conjecture, needed for C-element/majority
  LUT arguments): about 1–2 days;
- unify `K3`/`kmux` with `Formal/Core/Kleene.lean`. Constructor names already match
  (`zero/one/X`, `Le`, `ofBool`), so this is about 1 hour for the lead;
- connect `tableEval` to the other probe's INIT semantics on `Fin k → K3`: about half a day.

What it buys: a proof that the GLS's zero-time LUT (Verilog `?:` on X) equals the
silicon-shaped tree in Kleene semantics, whatever the pin order. A license to treat every
LUT-built C-element, latch or guard as hazard-free on any transition whose spanned INIT
entries agree, for any internal delays. The precise list of transitions that can glitch is the
function hazards, and their outcome depends on per-mux arrival order. This is what the cell proofs (shard B) need to
discharge LUT hazards, and it reduces the silicon question to two board experiments.
