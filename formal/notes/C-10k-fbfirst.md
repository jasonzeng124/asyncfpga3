# C-10k: the capstone's unchecked timing hypotheses as tcheck races, on the 4 gcd_hw routes

Shard C, probe 10k, 2026-10-27. About 3 h. Core Lean only; no sorry, axiom or native_decide.

## Verdict

**Works.** Four new obligation families are now proved-checker rows on the 4 gcd_hw routes (seeds d, 2, 3, 4).
Every row passes at the unguarded corners. Some fail only under the 0.772/1.155 band, as before.
H_FB_FIRST's relation to RT_FB is decided and proved in Lean.

- **H_FB_FIRST vs RT_FB.** They are not the same obligation, but RT_FB implies H_FB_FIRST.
  - `fbFirst_of_resp` proves: H_RESP_AFTER (RT_FB on traces), plus any bounded-delay feedback route and
    `qp 0 = o 0`, gives `FbFirst`. This holds for any LUT function.
  - Rc PASS discharges H_RESP_AFTER under H_RESP_ONLY. That hypothesis is a protocol fact, not a timing
    fact.
  - So H_FB_FIRST is discharged wherever Rc passes. By C-10h, that is everywhere except the rig's
    `uenv1` under the band (seeds 2 and 4).
- **H_AMERGE_RTZ (rule Z).** It is discharged on all 4 routes at all 6 corner models, on both cascade
  stages of the 3-input control_merge.
  - Worst margin: +383 ps (fastG, seed 3, `ucontrol_merge12.uarb2#2`).
  - It is conditional on H_FF_DRAINED for the cell's own z_req line (rule Fd). That condition fails under
    the band for `ucontrol_merge12` on seeds 3 and 4, so cm12's Z rows are discharged there only at the
    unguarded corners and sdf.
  - C-8l's "thin stage-1 race" is not thin. Nothing reads the stage-1 index at `acc_req`; the reader is
    the final consumer latch, behind stage 2 and the whole matched delay.
- **H_FF_DRAINED (rule Fd).** Rule F is NOT sufficient: F and Fd are incomparable.
  - Seed 4 `ushrsi3.udly` slowG: F (Fc) +252 PASS, Fd −160 FAIL. This is B's D2 missing term
    `hop_hi(i→i+1) − tap_lo(i+1)`.
  - Seed d `ucmpi8.udly` fastG/slowG: Fc −498/−497 FAIL, Fd +142/+291 PASS.
  - Fd passes on 29/29 lines per route at sdf, fast and slow. Under the band it fails on `ucontrol_merge12.udly`
    (seed 3 slowG −343; seed 4 sdfband −14, fastG −131, slowG −522) and `ushrsi3.udly` (seed 4 slowG −160).
- **H_MUX_RTZ / B's X1 plus the arbiter A3 "pulse" (rules X, Xi).** 63 acknowledge C-elements per route,
  81 rows per route counting every root of an OR'ed z_ack.
  - 0 failures at sdf, sdfband, fast and slow on every route.
  - Under the band there are 6 to 13 slowG and 2 to 8 fastG failures per route, all on muxes whose z_ack
    is a steer's OR of two branch acks. The worst is −2858 (seed 3 umux16).
  - Failure mechanism 1: the shared prefix (the z driver's DACK slow-fall ripple, about 10 ns) is charged
    with 1.155 on the data side and 0.772 on the late side.
  - Failure mechanism 2: in plain X, an OR-causal artefact through the inactive branch.
    Xi (with H_OR_IDLE) removes it: 0 band failures on seeds d and 2; seeds 3 and 4 keep umux16 and umux10
    (worst −2208).
  - The arbiter rows (B's A3 pulse, estimated at 53 ps box from arcs) pass with ≥ +970 ps at fastG.

## What checks (exact commands)

    cd formal/tools/tcheck
    ./run10k.sh d 2 3 4    # sync --check; lake build (FORMAL_SLOT_CWD); toy, cert and pair self-tests;
                           # per seed in parallel: extract.py --no-hi --rules10k FZX -> build/obl10k_S.tc,
                           # tcheck -> build/t10k_S.out; summarize10k.py -> results/r10k_rows.tsv,
                           # results/summary10k.txt   (~5 min on 4 CPUs; ~1 GB per extract)
    FORMAL_SLOT_CWD=$PWD ../../slot.sh lake env lean test/Axioms.lean      # incl. pverdict_sound
    cd formal && ./check.sh Formal/Timing/FbFirstRt.lean                    # [check] OK (2374 decls)

- 906 instances per seed (Fd 174, Z 54, X 486, Xi 192), 0 ILLFORMED, 0 CERTBAD. The .tc files are about
  135 MB each.
- `sync.sh --check` passes. The existing self-tests are unchanged and pass (`toy`, `toycert`). The new one,
  `toypair`, is described under Files.
- `run4.sh` is untouched. Its instances use neither `cut` nor `pair`, so its verdicts cannot change.
- The routes are C-10e's (`build/tree_*`, same sha as C-10h). No rerouting.

## Files (all mine)

| file | what |
|---|---|
| `formal/lean/Formal/Timing/FbFirstRt.lean` | `RespAfter`, `last_change`, `const_of_steps`, `step_of_ne`, `qp_const`, **`fbFirst_of_resp`**, `si_of_resp`, `maj`, **`fbFirst_witness`** (non-vacuity), **`cel_next_needs_all`** (H_CEL_NEXT for rule X). Imports `Formal.Net.OpsGen` (read-only). The lead must add it to `Formal.lean`; I do not own that file |
| `formal/tools/tcheck/Tcheck/Cert.lean` | `Late.cut` (arcs dropped in both phases; `expand` honours it; `lateOK_eq` unchanged); **`pverdict`**, **`pverdict_sound`** (per-pair verdict) |
| `formal/tools/tcheck/Main.lean` | parses `cut A B ...` and `pair D X PH`; pair report (margin = least pair margin) |
| `formal/tools/tcheck/certs.py` | `out_arcs` honours `cut` (mirrors `Tcheck.expand`) |
| `formal/tools/tcheck/rules10k.py` | rules Fd, Z, X, Xi; `emit_pairs` (one potential per variant, cap = largest target distance) |
| `formal/tools/tcheck/extract.py` | `--rules10k FZX` hook (ctx shared with rules2) |
| `formal/tools/tcheck/run10k.sh`, `summarize10k.py` | pipeline and report |
| `formal/tools/tcheck/test/toypair.tc`, `.expected` | self-test: per pair PASS where the cross product fails; a failing pair; a potential that is only valid with `cut`, refused (CERTBAD) without it |
| `formal/tools/tcheck/test/Axioms.lean` | adds `pverdict_sound` |
| `results/r10k_rows.tsv`, `results/summary10k.txt` | per row margins (6 variants × 4 seeds), summary |

## The Lean (what is proved, and what is not)

**`FbFirstRt.fbFirst_of_resp`.**
- Assumptions:
  - `LutFb F p qp o`, for any `F`. With `F := genF …` it is C-8n's generated gate.
  - `BoundedDelay lo hi o qp`, the feedback route.
  - `qp 0 = o 0`.
  - `RespAfter hi p o`: every change of a non-feedback pin happens when `o` has been stable for the last
    `hi` ticks, and not before `hi`.
- Conclusion: `FbFirst qp o`.
- Proof: strong induction on the output edges.
  - An edge caused by the feedback pin alone is impossible, by `FbFirst` at the previous edge.
  - An edge with an input change needs that change to come at least `hi` after the previous edge. The
    route has then settled.
- **Relation to C-8n's `Gap`:**
  - `Gap` constrains the output; `RespAfter` constrains the inputs.
  - Neither implies the other in general.
  - `Gap` also needs a quiescent reset; this theorem does not.
- **Relation to tcheck's Rc (argued, not mechanised):**
  - Rc PASS proves (`cverdict_sound`) that every pin change launched by o's edge comes at least
    `resp_lo ≥ fb_hi` later.
  - **H_RESP_ONLY** turns that into `RespAfter`. It says that every non-feedback pin change of a handshake
    C-element is caused by its own previous output edge (the four-phase DI protocol: an input moves only
    after the output has agreed with it, so the output is stable from that edge until the change).
  - The mechanised bridge from a tcheck `Run` to these step traces is the same open item as for every
    tcheck rule (C-10h, "identification").
- **C3 (per-pin):** the same inequality with the physical site-pin delays. tcheck's prjxray columns
  already price every LUT-pin arc to its site pin (C-10f), so Rc's fast/slow/fastG/slowG columns are C3.
  Only the `sdf` column is C2 without the per-pin term.

**Non-vacuity.** `fbFirst_witness` builds a `maj` C-element with a feedback delay of 1, both inputs
rising at 5 and the output rising at 6. It meets every hypothesis and has a real edge. C-8n's
`fb_stale_run` is the negative control: without the condition, the generated LUT breaks the Ops field.

**`cel_next_needs_all` (H_CEL_NEXT).**
- Statement: between two consecutive edges of a `maj` C-element under H_FB_FIRST, BOTH inputs changed.
- Rule X uses it: D's next edge is lower-bounded by the first change of the one handshake input whose
  first change is latest.

**`Tcheck.pverdict_sound`.**
- Assumptions: the same two `Run` hypotheses as `cverdict_sound`.
- Conclusion: every change of each pair's data node precedes every change of THAT pair's target, by at
  least `setup`.
- `cut` changes only `lateNet`, so `potOK_sound` applies unchanged. A cut is a modelling claim (the cut
  arc carries no transition in this window), named per rule below.

Axioms (`#print axioms`): propext, Classical.choice and Quot.sound only, for all of the above.

## The rules (shape, hypotheses, fidelity)

Every rule has the same structure:
- the data side is a 10a DAG of upper bounds (latest);
- the late side is the whole cyclic routed graph through a `Late` phase rule, with a checked potential;
- the pairs are checked one at a time, not as a cross product.

The prjxray numbers, Elmore, site hops, H_ONE_CORNER, band and H_FALLBACK_BAND are C-10h's, unchanged.
None of the new instances contains a fallback arc (`fallback=0/n` on every row).

**Fd: H_FF_DRAINED, per fast-fall line and per side-tapped stage j ≥ 1.**
- Data: stage j−1's fall, bounded as in rule F (side tap alone, H_CONTROLLING), plus the hop
  `out(j−1) → chain pin(j)`.
- Late: Fc's phase rule. Phase 0 is the falling wave to the tail, with no FASTRISE taps and without
  leaving storage. A switch at the tail starts phase 1, which is any path back to the gate source.
- Target: (side pin of stage j, phase 1).
- Meaning: when the gate rises at stage j, its chain input is already 0. The AND then rises only through
  the ripple (H_KLEENE_LUT: a held controlling 0 gives no hazard).
- This is B's D2 per-stage form. It also implies that z gets its low pulse.

**Z: H_AMERGE_RTZ, per arbiter acknowledge `ua_k` whose output reaches a consumer latch D pin without
crossing storage.**
- Only `ua2` qualifies: the index `won = g2 | A2` and the data mux read it. `g1`/`A1` have no index
  reader, which matches C-10j.
- Launch: the storage driver of A0. That is the fork node `ucontrol_merge*_f`, or for cm12's stage 1, stage 2's `ua1`.
- Data: A0 → ua_k (crossed as a pass-through; **H_GK_LOW**: g_k fell before A0, by the protocol) →
  won/index/data LUTs → consumer latch D → latch output → its own feedback pin. This is rule I's endpoint.
- Target: the latch-enable pin of the same latch bit's controller.
- Late: one phase over the whole graph, with **`cut` = the fast-fall side taps of the cell's own z_req
  line** (H_FF_DRAINED, discharged by that line's Fd row).
- The critical late path: A0 → ustate → q → O5 (R0) → uor → the delay chain (ripple) → consumer ctl →
  enable.

**X: H_MUX_RTZ and B's X1, plus B's A3 "pulse", per acknowledge C-element `u = C(j, z)` (`umux*.u[xy]a`,
`umux21.ua*`, `*.uarb*.ua*`).**
- Launch: a storage root D of z (z can pass through LUTs, e.g. a link's DACK line or a steer's `uack` OR).
  There is one row per root.
- Data: D → z pin → u → u's feedback pins. **H_J_LOW**: z is u's last enabling input, by the protocol.
- Target: (z pin, phase 1), i.e. z's NEXT edge at u.
- Phase 1 is entered by switches:
  - at D's handshake input whose first change is latest (H_CEL_NEXT, `cel_next_needs_all`, needs D's
    H_FB_FIRST, its Rc row);
  - in X, at the output of every other root (that root's first change);
  - in Xi, at that other root's latest input (**H_OR_IDLE**: the inactive steer branch's C-element is at
    rest at the launch, so it too needs all its inputs to change).
- `two = 1`, with no polarity rule. That is sound but conservative.

**Not made into rules here (decided):**
- **B's X4 / M3 weak isochrony.** The z_ack → {uxa, uya, ctl} part IS rule X: X's late side includes
  every path through the ctl branch. The ctl_req → {uj0, uj1} part is not covered.
- **C7 (C-tree depth).** Not done.
- **Rule I's missing feedback-pin term (B's L1).** Not mine.

## Results (results/summary10k.txt; per-row: results/r10k_rows.tsv)

Minimum margin in ps per seed (d / 2 / 3 / 4). FAIL counts are rows.

| rule | rows/seed | sdf | sdfband | fast | slow | fastG | slowG |
|---|---|---|---|---|---|---|---|
| Fd | 29 | 2175 / 2349 / 1359 / 1127 | 905 / 941 / 242 / **−14 (1)** | 1061 / 986 / 809 / 576 | 1735 / 1923 / 1272 / 1060 | 142 / 263 / 26 / **−131 (1)** | 74 / 345 / **−343 (1)** / **−522 (2)** |
| Z | 9 | 3667 / 4193 / 3358 / 3516 | 1818 / 2363 / 1599 / 1666 | 1600 / 1845 / 1617 / 2072 | 3233 / 4186 / 3493 / 4618 | 436 / 665 / 383 / 780 | 693 / 1570 / 815 / 1802 |
| X | 81 | 3385 / 3405 / 3466 / 3393 | 1246 / 730 / 2 / 892 | 1502 / 1833 / 1246 / 1629 | 2308 / 3351 / 1673 / 2677 | **−271 (2) / −267 (3) / −895 (8) / −693 (5)** | **−1373 (9) / −1276 (6) / −2858 (13) / −2260 (11)** |
| Xi | 32 (multi-root) | 5325 / 5311 / 4863 / 4971 | 2031 / 2149 / 1077 / 1303 | 2562 / 2698 / 1558 / 2275 | 5276 / 4928 / 2517 / 3983 | 623 / 567 / **−657 (2)** / **−220 (2)** | 916 / 572 / **−2208 (4)** / **−1252 (4)** |

**Fd vs Fc on the same lines (t5_*.out).**
- The difference Fd − Fc ranges from −860 to +3154 ps, depending on the line and corner.
- Flips:
  - ucmpi8 seed d: Fc FAIL, Fd PASS (Fd credits `tap_lo`).
  - ushrsi3 seed 4 slowG: Fc PASS, Fd FAIL (the hop term).

**Where X/Xi fail.**
- Every failing row is a mux whose z_ack is a steer's OR of two branch acks.
- In X, every failing row's critical late path enters phase 1 at the OTHER root. The path runs through
  the inactive branch (`umux.uya` → the other link's ack chain), and in OR-causal timing that branch moves.
- In Xi, the remaining failing rows (umux10, umux16 on seeds 3 and 4) have a genuine loop path:
  D → DACK → steer OR → fork → … → cmpi → steer LUT → D's input.
  - The data side is D's DACK slow-fall ripple, 6 stages, about 12.5 ns at slowG hi.
  - The same 6 stages are in the late path at 0.772.
  - So these are band-on-shared-prefix findings, like J0 against Jx.
  - Unguarded, the same rows have ≥ +1246 (fast) and ≥ +1673 (slow).

## Hypothesis status table (for the lead to merge into C-gcd_hw-hypotheses.md §3)

| obligation | where | tcheck rule | 4-route result (this probe) | grade |
|---|---|---|---|---|
| H_FB_FIRST (C-8n O4's condition, B's C2) | every feedback LUT the Ops models bind | **R/Rc** via `fbFirst_of_resp` (+ H_RESP_ONLY) | discharged wherever Rc passes: all kernel C-elements, all models; rig `urig.uenv1` fails under the band on seeds 2 and 4 (C-10h), passes unguarded | B (H_RESP_ONLY is a protocol hypothesis; the trace bridge is argued) |
| H_FB_SETTLED (C-8n O5) | link controllers of the O5 pipeline | same as H_FB_FIRST | same | B |
| C3 per-pin | same | Rc's prjxray columns (site pins priced) | as Rc | B |
| H_AMERGE_RTZ | 8 control_merges, 9 index-reading `ua2` (both cm12 stages) | **Z** (new) | **discharged on all 4 routes at all 6 models**, min +383 (fastG). Conditional on H_FF_DRAINED of the cell's line: cm12 on seeds 3/4 has Fd band failures, so there it is discharged at sdf/fast/slow only | B |
| first-stage RTZ of the 3-input cm (C-8l) | cm12 uarb1 | **Z** | same row as above (+436..+932 fastG). Not thin: the reader is behind stage 2 and the matched delay | B |
| H_FF_DRAINED (C-10j index form; B's D2) | 29 fast-fall lines per route | **Fd** (new); F/Fc are NOT sufficient (incomparable, see flips) | all lines pass at sdf/fast/slow; band failures: cm12 (seed 3 slowG −343; seed 4 sdfband −14, fastG −131, slowG −522), ushrsi3 (seed 4 slowG −160) | B (H_CONTROLLING, H_KLEENE_LUT) |
| H_MUX_RTZ (B's X1), muxn ack, arbiter A3 pulse | 63 ack C-elements per route | **X** (no extra hypothesis), **Xi** (+H_OR_IDLE for OR'ed acks) | all rows pass at sdf/sdfband/fast/slow. Band failures only on steer-OR'ed muxes (X: 2-8 fastG, 6-13 slowG per route; Xi: umux10/umux16 on seeds 3/4, worst −2208). Arbiter rows ≥ +970 fastG | C under the band (shared-prefix double charge, not yet credited); B unguarded |
| mux isochrony X4 (z_ack branch) | every mux | covered by X | as X | B |
| mux isochrony X4 (ctl_req → uj0/uj1), M3 | every mux / merge | none | UNCHECKED | C |
| C-tree depth latency (C7) | wide joins | none | UNCHECKED | C |

## What does not work / open, with effort

- **Shared-prefix credit for X/Xi (about ½ day).** This would remove most band failures.
  - Split each row at the deepest node X that dominates the data path into two obligations:
    - (a) launched at X, under H_CLEAN_EDGE at X;
    - (b) launched at D, with X blocked in phase 0 only, and the data side's `hi(D→X)` added.
  - Needs a phase-0-only `blocked` in `Tcheck.Late`, which is a small Lean change.
- **A max node (C-element AND) in the late semantics (about 1 day).** X currently picks ONE input
  (`cel_next_needs_all`); the max over inputs would be exact. The same node would remove H_OR_IDLE.
- **Mechanised bridge from tcheck `Run`s to the Ops step traces.** This is the open "identification" item
  of C-10h. It is what would make "Rc PASS ⇒ RespAfter" a theorem rather than an argument.
- **cm12's z_req line under the band.** Its Fd margin goes to −522 (seed 4 slowG). It is a 24-stage line
  whose gate fan-out is long. Every other amerge line passes Fd under the band.

## Decisions (no one to ask)

- **Per-pair verdicts instead of a cross product.** Fd's and Z's physical requirement is per pair. The
  cross product would fail rows that are safe: `toypair` shows the case.
- **One potential per variant with cap = the largest target distance.** min(dist, C) is a valid potential
  for any C, so no per-target certificates are needed (file size about 135 MB per seed).
- **X's late side lower-bounds the next edge by ONE input.** The latest of D's handshake inputs is used,
  justified by `cel_next_needs_all`. The first input (OR-causal) gave unguarded failures of −1110 ps that
  were artefacts. Reset/constant pins are excluded: they have no storage root.
- **Both X and Xi are reported.** Xi adds a protocol hypothesis, so X stays the hypothesis-free row.
- **Z's target is the consumer latch's enable pin, not the latch output.** That is conservative by one LUT
  arc against rule I's form.
- **No git; nothing outside my files was edited.** `formal/notes/C-gcd_hw-hypotheses.md` is not mine;
  the table above is for the lead to merge.
