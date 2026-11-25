# B-necessity-merge: exact own-loop condition of bd_merge's uxa/uya (and the one-node ctree)

Probe Bmg (shard B), 2026-10-27. New file (core Lean only):
`formal/lean/Formal/Cells/NecessityMerge.lean`. JSON draft (JSON untouched):
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bmg/draft_constraints.json`.
No route, board or toolchain run. Follow-up of Bsx (B-necessity.md section 4).

## Verdict

Bsx's cancellation argument is right. `bd_merge.uxa_feedback` (S_XA_ZA) and
`bd_merge.uxa_req_latency` (S_XA_R (1), (2)) are NOT necessary. The exact
condition in the per-pin box is ONE pair of inequalities. It has no wire
spread and no input-pin hi bound in it:

    H_XA_LOOP:  Qhi <= Xlo + Eo + Alo   and   Qhi <= Xlo + Eo + K + Blo

with
- `Qhi` = uxa's loop: feedback wire hi + I2 site pin hi + I2 arc hi;
- `Alo` = x_req -> uxa.I0 read: wire + site pin + arc, lo;
- `Blo` = z_ack -> uxa.I1 read: wire + site pin + arc, lo;
- `Xlo` = uxa.O6 -> x client wire, lo;
- `Eo` = the client's minimum reaction;
- `K` = minimum request edge -> z_ack edge (`wo + Lor.lo + Dz.lo + Es`, the JSON's `Kz`).

For uya, swap in the y names.

**Why.** Every next input edge at uxa is caused by uxa's own output edge τ,
through the client (x_req), and through the client and then the server
(z_ack). Both bounds are measured from τ. How late the follow input arrived
only moves τ, so its spread cancels.

## Model (named hypotheses, Int ps)

- H_PIN_READ (`UxaEq`): for t >= 0, O = the REAL bd_c2 INIT
  (`LibCtlMergeMux.c2B`, rst read 0) of:
  - x_req read at `pa.σ t`, with `pa` in [Alo, Ahi];
  - z_ack read at `pb.σ t`, with `pb` in [Blo, Bhi];
  - O read at `pq.σ t`, with `pq` in [Qlo, Qhi] and Qlo >= 1.
- H_PIN_FIFO (`Mono`): the input read maps are monotone. Pins are
  independent. The feedback map is arbitrary (it may be non-monotone).
- H_RESET: O = 0 before 0.
- H_CLIENT / H_SERVER (`HClient`, `HServer`). Take an edge τ of `idl`, the
  zero-delay C-element of the pin reads. Every x_req edge that the pin had not
  yet read at τ is launched at >= τ + Xlo + Eo. Every z_ack edge that the pin
  had not yet read at τ is launched at >= τ + Xlo + Eo + K.
  - The bounds are stated on `idl`'s edges. These equal the output's edges
    up to the first deviation (the same practice as CElemStrict's
    input-defined phase start).
- Spec (`UxaOK`): q = idl for every feedback map in the box. That is, no
  glitch and no lost edge. Whether `idl` has the right edges (the protocol) is
  for `bd_merge.seq` / `isochronic_forks` to say.

## Results (all `[bchk] OK`; axioms only propext / Classical.choice / Quot.sound)

| theorem | statement |
|---|---|
| `cel_box_exact` | generic, any pin count, `cSpec` law: q = idl for every feedback map in [Qlo,Qhi] **iff** HHold. HHold: whenever the reads disagree at t, idl is constant on [t-Qhi, t-Qlo] and equals idl t. Pointwise; no env. Necessity: adversarial map `advQ` + trace constructor `run`. |
| `merge_hhold`, `uxa_ok` | sufficient: H_CLIENT + H_SERVER + H_XA_LOOP give UxaOK, for any monotone input maps in the box |
| `uxa_box_exact` | **headline**: UxaOK for every driver pair, every monotone input map in the box and every env obeying H_CLIENT/H_SERVER **iff** H_XA_LOOP. Side conditions: windows >= 0, Qlo >= 1, Xlo >= 0, Eo >= 1, K >= 0. |
| `wit_*` | necessity witness, one x token with constant pin delays: x_req high on [0, α1), z_ack high on [K, β1). Timing: z_ack rises K after x_req; α1 = τ1 + Xlo + Eo; z_ack falls K (+1 ps on the x_req branch) after x_req falls. The run is physical, meets H_CLIENT and H_SERVER, and breaks HHold whenever H_XA_LOOP fails by any amount. |
| `glitch` | numbers: pins 100, Xlo 50, Eo 300, K 400, loop 451 (1 ps over). x_ack = 1 at 949 and 0 at 950, while z_ack is still read high and idl = 1. |
| `nonvacuous` | same numbers with loop 450 (equality): the hypotheses hold, every trace rises at 500 and falls at 1351, and a trace exists |
| `old_imply_new` | the old S_XA_ZA plus S_XA_FORK (`isochronic_forks` form 0), per pin with flat O6 arcs, imply H_XA_LOOP (strict). Replacing them is safe. |
| `old_not_necessary` | box numbers. Wires: z_ack [300,1500], x_req [200,600], feedback [50,300]. Site pins: A2 [170,507], A4 [86,284], A1 hi 516. O6 arc [45,124]. Xlo 150, Eo 600, Kz 1000. Old S_XA_ZA FAILS (2948 > 2735), H_XA_LOOP holds (941 <= 1081), and `uxa_ok` gives every run correct. |
| `old_not_necessary_R` | x_req wire [200,2000]: old S_XA_R(1) FAILS (3225 > 2551). H_XA_LOOP is unchanged and every run is correct. |
| `c2_cspec`, `c3_cspec`, `c4_cspec` | bd_c2/c3/c4 real INITs (rst 0) = `cSpec`, so `cel_box_exact` is the exact per-node loop condition for every ctree node |
| `ctree1_box_exact` | one-node bd_ctree (bd_c2 root, two port wires, leaves wait E after the root edge): exact **iff** Qhi <= E + min(Alo, Blo) |

Binary model: the exact condition is `<=`. The JSON's strict `+1` (Bs,
Kleene X window of the release pin's select) stays on top. The draft keeps
margin_ps 1.

## Findings for the cell owner / JSON

1. **Replace the uxa rows with H_XA_LOOP.** Replace `bd_merge.uxa_feedback`
   (2 forms) and `bd_merge.uxa_req_latency` (4 forms) by H_XA_LOOP (2 forms
   per C-element, so 4 in all). The new forms are launched at uxa.O6.
   - The checker no longer needs `Wzx.hi`, `Wxc.hi` or the I0/I1 site pins'
     hi for this race.
   - It does need the **I2 (feedback) arc and site pin hi** on the data side.
     The old forms charged the I1 arc. That is equal for flat O6 arcs and
     differs for O5 per-pin columns.
   - The old forms are implied by (old ZA + old FORK) => new (`old_imply_new`).
     Hence nothing that passed before fails now.
2. **The loop term in `bd_merge.isochronic_forks` form 0 (S_XA_FORK) is not
   needed in y phases (argued, NOT proved).** In y phases x_req = 0 and
   uxa's state is 0. There the fork race is between y's z_ack fall read at
   uxa.I1 and x's next x_req rise read at uxa.I0, and uxa's loop plays no part.
   In x phases the loop part of that form is exactly H_XA_LOOP's x_req
   branch, which has no Wzx spread. The cell-level spec here does not cover
   the protocol, so this stays an argument. Next probe: a protocol-level
   spec (idl's edges = x's tokens) with the same per-pin reads.
3. **`bd_ctree.node_fork` (proved only for a one-node tree).** For a single
   node with port wires the row charges the port wires' spread, which
   cancels. It also misses the port wire's lo on the right (`ctree1_box_exact`).
   For depth >= 2 (NOT proved) the same argument gives the proposed per-node
   condition
   `Qhi_n <= dist_min(n -> root) + E + min over children c (MaxMin(c) + read_lo(c -> n))`,
   where `MaxMin(leaf) = 0` and `MaxMin(m) = max_j (MaxMin(j) + read_lo(j -> m))`.
   The node-level half is `cel_box_exact`. What is missing is the tree-level
   causal bound: the root's edge >= τ_n + dist_min, and a C-element child moves
   only after its LATEST input, hence MaxMin. This needs a per-pin `Run` over
   `CTreeTimed.S`. Non-monotone windows do not bring the spread back: input
   pins must be FIFO in any case, or a C-element glitches with no race, and
   the feedback map's monotonicity does not matter (`cel_box_exact`).

## NOT covered

- The protocol (which edges `idl` has).
- The uor / delay-line / server path is abstracted into one lower bound `K`.
- Correlated corners: the box treats pins and edges independently; for a
  corner model, apply the theorems per realisation.
- Kleene X windows.
- bd_ctree depth >= 2.
- The JSON is not edited (draft only).

## Check

    /tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/NecessityMerge.lean
    -> [bchk] OK: formal/lean/Formal/Cells/NecessityMerge.lean

Axiom audit: `/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bmg/ax.lean`,
11 theorems. No sorry, admit, native_decide or axiom.
