# C-10o: H_CHAIN_SETTLED, exactly, and on the routes (track 10)

Shard C, probe 10o, 2026-10-29. Core Lean only, no sorry/axiom/native_decide.

## Verdict

- **H_CHAIN_SETTLED has an exact bounded-delay form, proved: works.** In Semantics' per-arc
  BoundedDelay model, for any single-source AND (FASTFALL/gated) or OR (FASTRISE `uack`)
  network, the tail is low (high) on [A, B) in EVERY run iff the canonical forced set `Lc`
  covers [A, B) (`low_iff`, `settled_iff`, `or_high_iff`); a hole is a runt in some run
  (`runt_of_gap`, numeric `runt_example`). No side conditions (B's H_LO_ORDER/H_BAL_HI not
  needed). A PASS at the late side's lower bound holds for every later return (`settled_mono_T`).
- **On 16 routes (gcd_hw ×4, collatz/xorshift/ipow ×4), 944 chains per variant: 0 failures at
  sdf, fast and slow.** `uack` (744 rows, new, tcheck `Fu` + exact): 0 failures in all six
  models, worst +12 ps (xorshift s2 slowG). FASTFALL (200 rows): band failures only — 9 lines
  (gcd cm12 s3/s4, ushrsi3 s4; collatz uselect0/uaddi0; xorshift uxori1/2), worst −589 ps.
- **Rule F does not cover it.** Rule F passes every one of those 9 band failures (margins
  463–2948 ps; it is an SDF-point rule), never sees the 744 `uack` lines (rule H assumes them
  settled), and overstates the exact SDF margin by up to 437 ps (its stage falls are at
  outputs, not at the next stage's pins). On these routes its SDF verdict happens to agree
  (all PASS). The exact rows equal C-10k's Fd failures except 2 rows Fd passes (+26/+21 ps,
  exact −5/−10): Fd ignores the per-pin LUT arc difference hi(I0→O) − lo(I1→O).
- **H_WIRE_DI** (checked, not proved): every routed LUT→LUT arc has lo ≥ 1 ps at both prjxray
  corners on all 16 routes; the only zero-lo arcs are SDF-fallback MUXF7/F8 hops and OBUF→PAD.

## Prior work this builds on (read before reading this note)

- O4 (`notes/C-O4-cells.md`): H_CHAIN_SETTLED in the per-gate SI model (`CellBind.Settled`:
  the input changes only when every stage shows it), counterexample `fastfall_hazard`.
- Shard B, `Formal/Cells/LibGapDelay.lean` (probe Bdg): for `bd_delay_gated` in a per-pin
  read-map box model, per-stage **H_GFLUSH** is sufficient (`flush_of_gflush`) and, under the
  side conditions H_BAL_HI / H_LO_ORDER, necessary (`box_exact_flushed`); without them it is
  NOT necessary (`rescue_flushed`).
- C-10k (`notes/C-10k-fbfirst.md`): tcheck rule **Fd** (H_FF_DRAINED = B's per-stage form) on
  the 29 FASTFALL lines per gcd_hw route; "rule F is NOT sufficient: F and Fd are
  incomparable". Fd covers FASTFALL lines only; the bd_link `uack` (FASTRISE) lines had no row.

So the new content here is: (1) the EXACT condition with no side conditions, in Semantics'
per-arc BoundedDelay model, for any single-source AND/OR network (every library chain,
including FASTRISE), with the converse; (2) rows for the 169 `uack` lines per gcd_hw route
(new) and exact rows for all chains, on 16 routes; (3) the rule-F comparison.

## 1. Lean

Files: `Formal/Timing/ChainSettle.lean` (network theorem), `Formal/Timing/ChainSettleChain.lean`
(pulse, N = 2 closed form, numeric runt). `./check.sh` on both: OK, 192 declarations, axioms
only propext / Classical.choice / Quot.sound.

### Model (named hypotheses)

Semantics' `Netlist` (arcs `[lo, hi]` ps, `WF`). Node 0 = the chain input (side-tap source).
`AndRun net inp sig` = Semantics' `Run` with
- **H_INPUT** instead of H_LAUNCH: node 0 carries a given trace `inp` (the environment);
- **H_AND**: every other node is the AND of the pins of its in-arcs (LUT1 buffer = AND of one;
  `bd_delay` FASTFALL stage LUT2 INIT 8); `OrRun` for OR stages (FASTRISE, INIT E), by duality;
- **H_BOUNDED_DELAY**: Prelim's `BoundedDelay lo hi` per arc, unchanged (delay may vary per
  event; pulses shorter than `hi` may pass or vanish). H_QUIESCENT not needed for soundness.
- **H_PULSE** (`pulse F T`, ChainSettleChain): input 1 before F, 0 on [F, F+T), 1 after.

### Results (what the Lean says)

- `lowPin lo hi L t` := ∃ s, hi ≤ s ≤ t, source low on [s − hi, max s (t − lo)].
  `pin_low`: every BoundedDelay output is 0 where `lowPin` holds. `ext_bd`: the trace
  "1 unless lowPin" is itself a BoundedDelay output (`ext_zero`: quiescent) — so `lowPin` is
  exact per arc.
- `Lc net inp v`: forced-low set by recursion over the netlist. **`cert_sound`** (any
  certificate is sound), **`low_iff`**: `(∀ runs, sig v t = false) ↔ Lc net inp v t`.
  `extRun` (the extremal run), `extRun_quiet`.
- **H_CHAIN_SETTLED, exact**: `Settled net inp z A B := ∀ t ∈ [A, B), Lc z t`.
  `settled_iff`: z is 0 on [A, B) in every run ↔ Settled. **`runt_of_gap`**: if
  `Lc z x`, `Lc z y`, `¬ Lc z t`, then some run has z = 0, 1, 0 at x, t, y (a runt).
- FASTRISE: `or_sound`, `or_high_iff`, `or_runt_of_gap` (forced-HIGH set = `Lc` of `!inp`).
- Interval calculus (what chainck computes): `lowPin_Ico` (lo ≤ hi: [x, y) ↦ [x+hi, y+lo)
  if x + hi < y, else ∅), `lowPin_union_gap` (sets separated by a point outside both map
  separately ⇒ maximal intervals map one by one), `lowPin_mono`, `Lc_mono_inp`.
- `chain2_settled_iff` (N = 2, `bd_delay #(.N(2),.FASTFALL(1))`): with every pulse longer
  than the arc it crosses, z is 0 on all of [F+ph, F+T+hl+rl) in every run ⇔
  **hh + rh ≤ T + pl** (head's latest fall at z's chain pin no later than the input's next
  rise at z's tap pin) — the per-stage form (B's H_GFLUSH, rule Fd), exact for N = 2.
- `runt_example` (kernel-checked converse on numbers): head [300,400], hop [200,300], tap
  [150,250], T = 500: a quiescent run with z low at 1250, HIGH at 1650, low at 1700 — a runt,
  350 ps before the matched rise (2000). `settled_example`: T = 600, no runt in any run.

- `settled_mono_T`: Settled on [A, F+T+Lr) for pulse length T ⇒ Settled on [A, F+T'+Lr)
  for every T' ≥ T (`Dil`, `lowPin_dil`, `Lc_dil`, `pulse_dil`).

What it does NOT say: when the input moves again (T is chainck's late-side lower bound,
H_REUSE_CAUSAL); LUT mux-tree hazards (H_KLEENE_LUT; a LUT is its function on pins);
that chainck's Python interval code computes `Lc` (it mirrors `lowPin_Ico` /
`lowPin_union_gap`; untrusted, like every tcheck front end; the tcheck `Fd`/`Fu` rows ARE
decided by the proved checker, but they are the per-stage sufficient form);
the bridge to O4's SI-model `CellBind.Settled` / `GenChain` (not composed: this replaces the
hypothesis on the timed side, it does not discharge O4's Lean hypothesis).

Non-vacuity: `AndRun` / `OrRun` are inhabited for every input (`extRun`, `negOr`);
`Settled` holds in `settled_example` and fails in `runt_example`.

## 2. chainck (formal/tools/chainck)

`chainck.py` imports tcheck's `extract.py` unchanged (graph, prjxray intervals per variant,
certs) and registers `rulesU.py` as extract's `rules10l` hook; it also runs C-10k's `rules10k F`
(Fd). Per side-tapped chain (`.chain.g[i]` with side taps from one net):
- **exact row** (Python mirror of `Lc`): every routed arc from the side-tap source through
  the head segment (LUT1 buffers) and every stage pin, input pulse [0, T), T = the late side
  of Fd/Fc (tail's earliest change, then the shortest routed path back to the source; FASTFALL
  phase 0 without FASTRISE taps; `uack` phase 0 every arc = no credit). PASS iff the tail's
  forced set is ONE interval [A, B) with B ≥ T + Lrip (Lrip = lo-sum of the ripple path: the
  matched length) = `Settled z A (T + Lrip)` and no earlier runt. Reported: T, T* (least
  passing T, binary search), margin_exact = T − T*, margin_stage (per-stage overlap, = B's
  H_GFLUSH with per-pin LUT arcs), binding reason at T*−1 (gap / short / empty).
- **tcheck row `Fu`** (new, `uack` only): Fd mirrored (stage rises bounded by the side tap
  alone, H_CONTROLLING for OR; target = side pin j, phase 1), decided by `pverdict_sound`.
- **H_WIRE_DI census**: per variant, routed arcs (non-cell, non-tie-off) with lo = 0.

Run: `formal/tools/chainck/run.sh` (16 routes, two at a time, ~25 min; results.txt,
build/rows_*.json, build/compare_F.tsv, build/rows_FR.tsv, build/t_*.out, build/wire_*.json).
tcheck binary: formal/tools/tcheck/.lake/build/bin/tcheck after `sync.sh --check` and the three
self-tests (run.sh does both).

Routes (not re-routed; committed fixtures, fasm sha in build/sha_*.txt): gcd_hw seeds d,2,3,4 =
formal/tools/tcheck/build/tree_* (C-10e route.sh, byte-identical to C-10m's); collatz /
xorshift / ipow seeds 1-4 = formal/tools/kcheck/build/*/s* (C-10n, `--freq 100`). nextpnr
fingerprint 9c732bc6303458df (toolchain.txt of each route, all patches ok). The gcd_hw fixtures
were built by build_hw.sh without NEXTPNR_FREQ (C-10e's choice; I did not re-route them).

## 3. Results (16 routes; FF = FASTFALL/gated lines, FR = bd_link `uack`)

| model | FF rows | FF exact FAIL | Fd FAIL | FR rows | FR exact FAIL | Fu FAIL |
|---|---|---|---|---|---|---|
| sdf | 200 | 0 | 0 | 744 | 0 | 0 |
| sdfband | 200 | 1 | 1 | 744 | 0 | 0 |
| fast | 200 | 0 | 0 | 744 | 0 | 0 |
| slow | 200 | 0 | 0 | 744 | 0 | 0 |
| fastG | 200 | 9 | 7 | 744 | 0 | 0 |
| slowG | 200 | 9 | 9 | 744 | 0 | 0 |

Per route: gcd_hw 29 FF + 169 FR, collatz 7 + 8 (7 timed), xorshift 7 + 7 (6 timed), ipow 7 + 5 (4 timed); see §6 for the untimed entry links.
No row contains a fallback arc. Worst FR margins: sdf +1385, fast +528, slow +924, fastG +46,
slowG +12 (xorshift s2/s4 `ulink_n_*Result*.many.stage[1].u.uack`). Worst FF at consistent
corners without band: gcd fast +904 (s d cm12), xorshift fast +507 (uxori1).

### Row-by-row against rule F (tighten.py `audit_fastfall`, recomputed on the same graph;
matches the printed tighten logs, e.g. gcd d cm12 1343, uori0 2077)

FF failures under the band (exact margin / Fd margin / rule F margin, ps):

| route | line | model | exact | Fd | rule F (sdf) |
|---|---|---|---|---|---|
| gcd 3 | ucontrol_merge12.udly | fastG | −5 | +26 | +673 |
| gcd 3 | ucontrol_merge12.udly | slowG | −410 | −343 | +673 |
| gcd 4 | ucontrol_merge12.udly | sdfband / fastG / slowG | −63 / −162 / −589 | −14 / −131 / −522 | +463 |
| gcd 4 | ushrsi3.udly | fastG / slowG | −10 / −227 | +21 / −160 | +1836 |
| collatz 2 | uselect0.udly | fastG / slowG | −313 / −221 | −282 / −154 | +2883 |
| collatz 3 | uselect0.udly | fastG / slowG | −227 / −322 | −196 / −255 | +2096 |
| collatz 4 | uselect0 / uaddi0 | fastG | −317 / −61 | −286 / −30 | +2057 / +2090 |
| collatz 4 | uselect0.udly | slowG | −393 | −326 | +2057 |
| xorshift 1,2 | uxori1.udly | slowG | −193, −274 | −126, −207 | +836, +658 |
| xorshift 2 | uxori2.udly | fastG | −107 | −76 | +2948 |
| xorshift 3 | uxori1.udly | fastG / slowG | −43 / −272 | −12 / −205 | +695 |

- **Does rule F cover H_CHAIN_SETTLED? No.** (1) Rule F is evaluated on nextpnr's SDF (slow-max
  only, flat LUT arc); every band failure above is a rule-F PASS by 463–2948 ps. (2) Rule F skips
  `.uack` lines entirely; rule H (the ack-fall hold) times the uack fall through the ripple
  without taps, i.e. it ASSUMES the uack chain settled: the Fu/exact rows are the missing check
  (they pass). (3) At the SDF point rule F's margin is not a lower bound on the exact margin:
  exact − ruleF ranges −437 (xorshift 1 uxori2: 2046 vs 2483) to +1941 ps over the 200 FF rows;
  rule F measures each stage's fall at its OUTPUT against the input's return at the SOURCE,
  while the exact condition compares the previous stage's fall at the next stage's chain pin
  (+ that pin's LUT arc hi) against the return at the tap pin (+ tap LUT arc lo). Its 200 ps /
  20 % guard happens to absorb the difference on all 200 rows (worst rule F margin 463 vs worst
  underestimate 437), so on these routes the SDF verdicts agree (all PASS). C-10k already showed
  F and Fd incomparable; this confirms it against the exact form.
- **Fd vs exact.** On every failing row exact = margin_stage (the per-stage form is exact on
  these routes: B's side conditions hold in practice). Fd is 31–67 ps more optimistic because it
  compares at the stage's PINS (the AND evaluated at pin instants) and so drops
  hi(I0→O) − lo(I1→O) of the stage LUT; under per-pin BoundedDelay arcs that difference is a
  real hazard window. Two rows flip: gcd 3 cm12 fastG and gcd 4 ushrsi3 fastG (Fd PASS, exact
  FAIL by 5 and 10 ps). Whether the LUT's per-pin arcs can differ that way inside one corner is
  H_KLEENE_LUT/mux-tree territory (open).
- gcd_hw itself: all 198 chains per seed PASS at sdf, fast, slow on all 4 seeds (min +904 fast,
  +1711 slow, both s d cm12); under the band cm12 (s3, s4) and ushrsi3 (s4) fail, as C-10k's Fd.

## 4. H_WIRE_DI and H_LEAF_PERSIST

- **H_WIRE_DI** (census, untrusted Python, not a theorem): over every routed non-tie-off
  INTERCONNECT arc (gcd_hw 44,970 per route), arcs with lower bound 0 ps at the prjxray corners:
  gcd 688, collatz 197, ipow 107, xorshift 5 — all SDF-fallback `MUXF7/F8 OUT -> MUXF8/MUXF7`
  site-internal hops plus OBUF→PAD (gcd_2 breakdown in build/wire_gcd_2.json). No LUT→LUT route
  (the class of fork req_out / join ack_out / mux ctl_ack / snk ack nets) has lo = 0 at fast or
  slow. In nextpnr's SDF, 2,640 arcs are 0 (LUT→MUXF7, LUT→CARRY4 S, in-slice). So the
  ≥ 1-tick route O4 needs holds at 1 tick = 1 ps on every LUT net of the 16 routes; the mapping
  from O4's Ops tick to ps is NOT formalised.
- **H_LEAF_PERSIST**: not derived. Analysis only: a leaf ack of fork N = 5, 6 can withdraw only
  after the fork's request moved, which is causally after the root's rise (the fork's ack); the
  timing content that remains is the internal C4 node's own feedback (H_FB_FIRST, tcheck Rc rows),
  so it is a protocol induction (O4's open item), not a new chain-type timing row.

## 5. Hypotheses and their status

| hypothesis | where | status / witness |
|---|---|---|
| H_INPUT, H_AND/OR, H_BOUNDED_DELAY | ChainSettle | model; inhabited by `extRun` / `negOr` for every input |
| H_PULSE | ChainSettleChain | model of the environment; `pulse` |
| H_CHAIN_SETTLED = `Settled` | the conclusion's exact form | holds: `settled_example`; fails: `runt_example` |
| H_REUSE_CAUSAL (T ≥ late side) | chainck rows | as Fd/Fc (C-10k): untrusted extractor for the phase rule; potentials checked in Fd/Fu |
| H_NAMES (chain stages are the RTL's LUT1/AND/OR, found by `.chain.g[i]`) | chainck | INIT not re-read from the bitstream here (track 11 did it for route d) |
| H_KLEENE_LUT (LUT = its function on pins) | model | open (fidelity table) |

## 6. Not done / open

- Composing `Settled` into O4's SI-side `GenChain` (needs a timed→SI bridge for chains).
- The `uack` phase-0 credit (FASTFALL taps cannot carry a rise) is not taken; rows pass anyway.
- Untimed chains: in each kernel route the entry link `ulink_n1__1.uack` (collatz 8 → 7 exact
  rows, xorshift 7 → 6, ipow 5 → 4) has no routed path from its tail back to its source (the
  soak harness closes that loop outside the graph), so no lower bound on T exists: its exact row
  is skipped, and its `Fu` row's target is unreachable (cap = INF, a vacuous PASS — do not count
  it). The environment's timing there is unchecked.
