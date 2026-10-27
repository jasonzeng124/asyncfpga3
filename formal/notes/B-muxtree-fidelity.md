# Probe Bf: fidelity of H_KLEENE_LUT (mux tree vs closure semantics)

File: `formal/lean/Formal/Cells/MuxTree.lean` (core Lean, imports only
`Formal.Cells.Prelim`, checks in about 3 s, no warnings).

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/MuxTree.lean

Status: **checks clean.** `#print axioms` (run on a scratch copy) for
`muxTree_eq_lutK`, `Tree.evalK_eq_lutK`, `Tree.evalK_order_indep`,
`build_evalK_eq_lutK`, `lut6_silicon_order` gives only
`[propext, Classical.choice, Quot.sound]`. No sorry, admit, axiom or
native_decide. (A grep for "admit" finds only `K3.admits`, Prelim's name.)

## 1. What is proved

Shared defs added in this file (namespace `Formal.Cells.MuxTree`; Prelim is
untouched):
- `clo vs`: the closure verdict over a list of Booleans (all 1 -> t, all 0 -> f, else x).
- `cloF G ins`: closure semantics of a function table `G : List Bool -> Bool`;
  `cloN g ins` the same for a `Nat`-indexed table. `lutK init ins = cloF (lutB init) ins`
  and `= cloN init.testBit ins` hold by `rfl` (`lutK_eq_cloF`, `lutK_eq_cloN`).
- `Tree`: a decision tree of 2:1 muxes (`node i lo hi` = mux selected by
  input `i`; leaves are SRAM bits), with `evalK` (every mux is a Kleene
  `K3.mux`) and `evalB` (Boolean).
- `Tree.Free S T`: read-once (each mux selects on an input in `S`, and no input
  is tested twice on any root-leaf path). The order is free and may differ
  between subtrees.
- `build G order acc`: the full tree that splits on `order` (head = output mux).

Theorems:
| name | statement |
|---|---|
| `muxTree_eq_lutK` | Prelim's `muxTree init.testBit ins = lutK init ins`, every INIT, every K3 input list of any length (I0 at the output mux). |
| `muxTree_eq_cloN` | the same for any table `g : Nat -> Bool`. |
| `cloF_cons`, `cloN_cons` | the closure at the head input is exactly ONE Kleene 2:1 mux over the two closures with that input pinned. |
| `cloF_split` | the same at ANY input position `i < length`: `cloF G ins = K3.mux ins[i] (cloF G (ins.set i f)) (cloF G (ins.set i t))`. |
| `mux_mux_comm` | two adjacent Kleene mux levels commute (`join` is AC). |
| `Tree.evalK_eq_cloF` | any read-once tree with inputs in range evaluates (Kleene) to the closure of its own Boolean function. |
| `Tree.evalK_eq_lutK` | any read-once tree that implements `lutB init` on vectors of the input length computes `lutK init` on every K3 input. |
| `Tree.evalK_order_indep` | two read-once trees with the same Boolean function give the same K3 output everywhere: which input sits at the root does not matter. |
| `build_evalK_eq_lutK` | for every permutation `order` of `0..n-1`, the tree built in that order computes `lutK`. |
| `lut6_silicon_order` | instance: order `[5,4,3,2,1,0]` (A6 at the output mux, A1 at the SRAM end, as on silicon). |
| `lut6_gls_order` | instance: order `[0,1,..,5]` (A1 at the output mux, as `prims.v` on claude/research writes it). |
| `not_free_counterexample` | read-once is necessary: a tree testing input 0 twice computes constant 1 but its Kleene evaluation on `[x]` is `x`, while the closure is `t`. |

Hypotheses: none beyond the definitions. The only modelling assumption is
the per-mux one, `K3.mux` (H_KLEENE_LUT for ONE 2:1 mux), which is the
definition of `evalK`/`muxTree`.

Consequence: the Kleene LUT semantics of every cell proof in shard B needs a
hypothesis about one pass-transistor 2:1 mux only, plus the structural fact
that a LUT is a read-once mux tree (each input buffer drives the selects of
exactly one level). Tree depth, input order (A6 or A1 at the root), and the
mismatch between the GLS's order and the silicon's do not matter for the
static K3 value.

## 2. What did not work / not done

Nothing is unproved in the claimed file. Not attempted:
- `o6K init ins = K3.mux ins[5] (o5K init ins) (lutK (init / 2^32) (ins.take 5))`
  (O6 as the A6 mux of the two 5-LUTs). It follows from `cloF_split` at
  `i = 5` plus a lemma relating `completions (ins.set 5 f)` to
  `completions (ins.take 5)` and `Nat.testBit_mod_two_pow`; about 1 h.
- The theorem is static (values only). It says nothing about the timing or
  the glitches of the tree; those are section 3.

## 3. Fidelity research

### How a 7-series LUT is built (what is public)
- Architecture (UG474): each 6-LUT is two 5-LUTs on A1..A5 sharing inputs;
  `O5` is the lower 5-LUT, `O6 = A6 ? upper : lower`. So A6 drives the last
  (output-side) 2:1 mux, and there is a buffered internal node (O5) between
  the 5-LUT trees and the A6 mux.
- Circuit (Xilinx patents and the academic FPGA circuit literature, e.g.
  Ahmed/Rose, the Toronto FPL 2013 transmission-gate study): 64 SRAM config
  cells, a 64:1 tree of NMOS pass transistors (one transistor per switch),
  input buffers that generate each select and its complement, periodic
  re-buffering inside the tree (a K-deep chain of pass transistors is slow),
  and an output inverter/buffer with a weak PMOS level restorer (feedback),
  because an NMOS passes a 1 only up to `V_G - V_t`. Some Xilinx patents
  (US6667635, "FPGA lookup table with transmission gate structure for
  reliable low-voltage operation") use transmission gates instead at low
  VDD. Which of the two the 28 nm 7-series LUT uses is not public.
  The exact transistor-level 7-series LUT is not published.
- Fast vs slow pins, measured: prjxray-db `zynq7/tile_type_CLBLL_L.json`
  gives the site-pin (input buffer + select) delay per LUT pin, corners
  [fast min, fast max, slow min, slow max] in ns:

      A1 0.172 0.214 0.416 0.516
      A2 0.170 0.212 0.409 0.507
      A3 0.107 0.133 0.278 0.344
      A4 0.086 0.107 0.229 0.284
      A5 0.033 0.042 0.091 0.112
      A6 0.002 0.002 0.004 0.005

  Monotone A1 slowest to A6 fastest: A1 sits at the SRAM end (its buffer
  drives the most pass gates and its edge has to ripple through all levels),
  A6 at the output mux. The `CLBLL_L.sdf` cell arcs `A_i -> O6` are uniform
  (45/56 ps FAST_MIN/FAST_MAX, 100/124 ps SLOW_MIN/SLOW_MAX, both edges; first
  written here as "rise"/"fall", corrected after the audit, REPORT row 10:
  prjxray `makesdf.py:63` writes `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`;
  consistent-corner arbiter values in `ArbCorners`, B-arb-corners.md), so the per-pin difference lives entirely
  in these site-pin delays (up to ~0.5 ns at slow max). Worth checking that
  the research GLS's delay calculator includes them; nextpnr's SDF used today
  sets every `TA_iO6` to the same nominal value.

### Mid-rail select, equal data
- A static mid-rail voltage on a LUT pin first meets the input buffer
  (inverter chain). The chain has high gain, so the band of pin voltages that
  leave its output away from the rails is very narrow (roughly
  `V_DD / gain^n`). A slowly moving or late input becomes a clean digital
  edge at the select, at an uncertain time (the buffer threshold varies with
  PVT). So at LUT inputs, X is mostly a **timing** phenomenon: "the edge
  happens somewhere in an interval". A K3 `x` at a pin should be read as
  "this pin may switch at any time during the interval", which is exactly what
  `K3.mux`'s "equal legs pass" covers when the legs are stable.
- The exception is a metastable source that holds the pin near the buffer
  threshold (the LUT arbiter's own loop, bd_arb). Then the select and its
  complement are both intermediate and both pass transistors are partly on.
  - Legs both 0: an NMOS with gate at ~VDD/2 still has `V_GS > V_t` and
    passes 0 strongly. Kleene holds.
  - Legs both 1, node already 1 (the usual case: the select was valid before
    and chose a 1 leg): nothing discharges the node and the restorer holds it.
    Kleene holds.
  - Legs both 1 but the node starts at 0, i.e. the data legs RISE while the
    select is mid-rail: an NMOS-only tree can pull the node only to about
    `V_mid - V_t`, below the output inverter threshold. The output stays 0 or
    intermediate where Kleene says 1. **This is the scenario in which
    H_KLEENE_LUT can fail on an NMOS-only tree.** A transmission-gate tree
    (or boosted select levels) would pass it. Which applies is not public.
- Equal legs, one input switching cleanly (no X): the two legs of the
  switching mux are at the same level. Possible artefact: charge sharing when
  the newly connected internal node sits at `V_DD - V_t` (an NMOS-passed 1
  without its own restorer) and the output-side node at `V_DD`. The dip is
  about `V_t * C_int / (C_int + C_out)`, normally well under the inverter
  threshold, and the restorer recovers it. That makes a runt at the output
  buffer unlikely but not excluded. Internal re-buffering (the O5 node)
  bounds `C_int`. No published measurement of 7-series LUT hazards was found.
  Static-hazard freedom for a single-input change with equal leaves is
  therefore plausible but unverified.

### What the board-fidelity GLS on claude/research models
`cells/gls/prims.v` (`SLICE_LUTX`): a zero-time Verilog mux tree with A6 at
the SRAM end and A1 at the output mux (the opposite of the silicon order, which
does not matter for values by `Tree.evalK_order_indep`). Verilog `?:` with an
`x`/`z` select merges the two legs bitwise (equal bits pass, else x), so the
GLS implements exactly `K3.mux` per level and hence `lutK`
(`lut6_gls_order`). Timing is one inertial specify path per pin (nominal 124
ps, SDF-annotated), so narrow pulses are swallowed. Internal hazards on
multi-input changes are not modelled, charge sharing is not modelled, and
metastability resolves in zero time (research/PROGRAM.md lists all three as
gaps). Unrouted pins are tied (A1..A5 = 0, A6 = 1). The GLS and this model
therefore agree on LUT values by construction. Neither has the physics that
could falsify H_KLEENE_LUT, so agreement between them is no evidence.

## 4. Verdict

**Works.** The tree-to-closure reduction is fully proved, for every input
order and every table, in about 400 lines of core Lean that check in 3 s.
Effort spent: about 1 h. The O6 = A6-mux-of-two-O5 corollary would take about 1 h more.
What it buys: every shard-B Kleene proof rests on one named, physically
local hypothesis (one 2:1 mux), not on an assumption about a whole 64:1
LUT. The arbiter's Kleene probe can cite this. Read-once is shown to be
necessary, so this is the right structural fact to state about the LUT.

## 5. Fidelity grade for H_KLEENE_LUT (per 2:1 mux)

- Clean edges at select, equal and stable legs: **high** (static values are
  physically right; the residual risk is a charge-sharing runt, judged small).
- X at select as a timing uncertainty (late or slow edge, buffer restores):
  **high**. This is the main use in the cell proofs.
- Truly mid-rail select (held metastable source) with stable equal legs:
  **medium**. 0 passes. 1 holds only by retention and the level restorer.
- Mid-rail select while equal data legs change (especially rise): **low /
  unknown**. It fails for an NMOS-only tree without boosted selects. Any proof
  that leans on Kleene through a metastable select while data moves must say so.

Overall: **B (plausible, physically motivated, untested on this silicon)**.

Experiments that would test it:
1. Board, glitch counter: a LUT with INIT making O6 independent of A1 (for
   example O6 = A2), A1 toggled by a fast ring oscillator, A2 static. O6
   drives the clock of a ripple counter (a runt above threshold counts).
   Expect 0 counts over 1e10 toggles. Repeat with the toggling input on A6
   (output-side mux) and A1 (SRAM side) to separate the charge-sharing
   geometries.
2. Board, metastable select: drive a LUT select pin from bd_arb's grant with
   near-simultaneous requests (the MTBF rig in `cells/hw/arb_mtbf_measure.py`),
   data legs equal. Case (a): legs static 1. Case (b): legs rising during the
   contest. Capture O6 and the grant with two FFs, and compare the error rate
   of O6 against the grant's own metastability rate. Kleene predicts O6
   error = 0 in (a). An NMOS-only tree predicts errors in (b).
3. GLS (cheap, a regression and not a fidelity test): force a SLICE_LUTX pin to
   `x` with equal legs and check that O6 stays defined and produces no event.
   This holds by the Verilog semantics, and it confirms the GLS matches `lutK`.
4. SPICE (if a 28 nm PDK model is available): a 2:1 NMOS mux with restorer,
   select swept through mid-rail, legs equal at 0 and at 1, with and without
   a rising leg. This decides case (b) per tree style.

Sources: prjxray-db (f4pga/prjxray-db, `zynq7/tile_type_CLBLL_L.json`,
`zynq7/timings/CLBLL_L.sdf`); Xilinx UG474 (7-series CLB); AMD UG912
LOCK_PINS ("A6 and A5 the fastest physical LUT inputs",
https://docs.amd.com/r/2022.2-English/ug912-vivado-properties/LOCK_PINS);
Friedrichs/Fuegger/Lenzen, "Metastability-Containing Circuits"
(https://arxiv.org/abs/1606.06570): an AND-OR mux is not metastability-containing,
which is why a CMUX is needed. A pass-transistor mux with equal legs is closer
to a CMUX but has the NMOS weak-1 caveat above. Toronto FPL 2013 TG-FPGA paper
(https://www.eecg.utoronto.ca/~vaughn/papers/fpl2013_tgate_fpgas.pdf):
NMOS pass-transistor degradation, level restorers, transmission gates.
Xilinx patent US6667635B1 (transmission-gate LUT for low voltage).
`cells/gls/prims.v` and `research/PROGRAM.md` at origin/claude/research (read-only).
