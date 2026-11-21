# sizerule: where the 1.4-1.8x in the matched-delay sizes comes from, and one rule for every kernel

PROGRAM.md "General first" item 2 (owner, 2026-11-17). Subagent of research, 2026-11-17 evening. Nothing here was
committed by the subagent; nothing in cells/rtl/, bdc/ structure, JOURNAL, BOARD-QUEUE or PROGRAM was touched.
nextpnr 9c732bc6303458df (toolchain.sh OK). Local routes rebuilt bit-for-bit where a board item exists: collatz item 31
seed 20 (sdf 7aefc4bd), xorshift item 33 seed 27 (7f0c0592), collatz64 item 32 seed 22 (842dd4d7); ipow item 29's
sizes on seed 3 (63955bc9; FFMUX-FLAG, used for sizing only, not as a board route).

## 1. How a size is computed today (file:line)

There is no single rule; every size in an item's file is the per-cell MAX of several layers, never lowered by a later
one unless a proposal on every route agrees:

| layer | tool | quantity | corner | guard | rounding / floor |
|---|---|---|---|---|---|
| ratchet (T3, T9, T4) | bdc/size_kernel.py:12-30 | tighten rule A (request at the cell's own join vs latest data), H, I, skew rule E asks | nextpnr's SDF: flat 124 ps LUT = SLOW_MAX, wires nextpnr's estimate: one corner for chain and data | tighten.py:1129 `max(0.2*t_data, 200 ps)`; skew.py:248-249 GUARD_LO 0.772 / GUARD_HI 1.155 (95/95 tolerance on 5 rings) | per-cell max over seeds, never lowered; `--headroom` +1 on every compute cell; tighten.py:1269 line_links: removal priced at the dearer of own/legacy, ceil on padding |
| global factor (s50, s75) | research/tools/shrink_sizes.py | -- | -- | -- | ceil(f*n), floor 1 |
| per-route proposal | research/tools/corner_audit.py (default `worst`) | A' (from each upstream link's C node, storage-crossing walk), A (bundled), E, M, F, H, I | chains 0.21 (`--inst-rx`, :563-564), LUT/wire 0.288 (`--band`, :535), CARRY4/F7F8/FF at SLOW_MAX (`--cell`, :536); also `nom` = everything 0.288 (eval_task.sh step 2) | `--guard-lo/hi` 0.97/1.03, rule-A guard max(0.03 t, 50 ps) (:531-534) | shortened line priced D(m) = min(D - (n-m)*c_rm, lut_lo + (m-1)*c_lo), c_rm the line's DEAREST step, c_lo the route's single CHEAPEST hop (:639-649); select paths never shortened unless --shrink-selects (:659); floor 1 |
| aggregation | research/tools/fifteen/farm_max_sizes.py / max_sizes.py | -- | both corners | -- | per-cell max over all routes and both corners; a route that does not mention a line keeps the base |
| hold pads | research/tools/fifteen/hold_pads*.py | H/I rows | worst + nom | as above | +1 per round |

So the data side is at SLOW_MAX for CARRY4 and at 0.288 for LUT/wire, and the matched delay is at 0.21: the corner
mix the audit's REFUTED row forbids, inside the request-vs-data comparison itself. The draws (bench_gate.sh draw:K)
take chains and rest each from U[0.20, 0.31] independently and CARRY4/F7F8/FF from U[0.20, 1.0].

## 2. Decomposition on the critical lines (farm data, no new build)

Sources: proposals of the items on their own 23-28 EQUIVALENT routes (farm fxa, fcsel3a, fisel3m, fc64sel3p:
research/tools in the scratch `props.py`), the as-routed need (elements for margin 0 at the line's own per-element
cost: line_account.py on fcsel3m_la / fipowrh_la / fc64eq_la, and margin / 380-420 ps on the items' own report rows),
and the draws (shrink5/4, shrink9, shrink8, shrink10b). Median (range) over routes.

| kernel line (item size) | today's rule: proposal worst / nom, median (max) | as-routed need worst / nom, median (max) | draws pass | draws fail |
|---|---|---|---|---|
| ipow ushrsi0 (23) | 21 / 18 (23) | 11 (8..16) / 9 (6..13) | 17 (x0.70); 13 (x0.55) on 20 clean routes | -- |
| ipow ucmpi2 (18) | 17 / 18 (18) | 6 (4..9) / 5 (3..8) | 10 | -- |
| ipow umuli1 (36) | 35 / 32 (36) | 17 (10..21) / 15 (9..19) | 20 | -- |
| ipow umux3 (4) | 4 (selects kept) | 2 (1..4) | 4 (x0.70) | 3 (x0.55, route 12: static A' -457 nom) |
| collatz uaddi0 (9) | 9 / 5.5 (9) | 5 (3..7) / 3 (1..5) | 5 (32 routes) | -- |
| collatz ucmpi0 (8) | 8 / 7 (8) | 5.5 (3..7) / 4 (2..6) | 5 on 31 routes | 5 on route 30 (A' -834 nom, CARRY 0.75 / 0.91) |
| collatz umux2 (11) | 11 (selects kept) | 6 (4..8) | 7 | -- |
| xorshift uxori1/2 (5) | 5 (5) | 4 (2..6) / 3 (2..5) | 3 | 2 (x0.40a) |
| xorshift ucmpi1 (9) | 9 (12) | 7 (4..10) / 6 (3..9) | 5 | 4 |
| xorshift umux3 (9) | 9 (selects kept) | 3 (1..5) | 5 | 4 |
| collatz64 uaddi0 (23) | 19 / 13 (23) | 10 (6..14) / 7 (3..11) | 17 (x0.70 so far) | TBD (shrink10b) |

Ratios, item size : what the draws accept (~1.4-1.8x), attributed term by term (typical line, range over the lines):

| term | factor | evidence |
|---|---|---|
| history: sizes from the nextpnr-SDF ratchet (0.2 t / 200 ps guard, +1 headroom, never lowered) and select lines the default proposal may not touch | 1.0-1.1 on lines corner_audit re-sized; 1.5-3 on the select-protected lines (xorshift umux3 9 vs need 3, collatz umux2 11 vs 6) and never re-sized ones (ipow T9s75) | props tables; itercost README "item 19's sizes are x0.75 of an older round, never re-sized" |
| corner_audit's shortening price (dearest own step out, route's single cheapest hop as the rebuilt chain's cost) | **1.6-2.0** (largest single term) | ca_prop vs n_need on the same route: ushrsi0 21 vs 11, ucmpi2 17 vs 6, uaddi0 (c64) 20 vs 10, uaddi0 (col) 10 vs 5 |
| corner mix (chain 0.21 vs data LUT/wire 0.288 vs CARRY4 SLOW_MAX) | 1.1-1.2 on LUT/wire lines (ps_el 388 vs 429: a LUT/wire arc at 0.21 is 0.92x its 0.288 value), 1.4-1.7 on carry lines (uaddi0 5 vs 3; logic 1464 vs 726 ps: CARRY4 at SLOW_MAX is ~1.75x its 0.288 value) | la worst vs nom; the CARRY share is the one the draws also take to 1.0 |
| per-route max over 25-32 routes | 1.2-1.5 (max/median of n_need) | n_need ranges above |
| guard (0.97/1.03, max(0.03 t, 50)) | < 0.4 element (50-150 ps at ~400 ps an element) | report rows |
| floor 1 / ceil | acks and stage pads only (1-6 -> 1) | proposals: "floor 1" |
| rule A pessimism (A'm pairing of peers no common source reaches, full-range carries no vector toggles, data that only has to settle before the latch CLOSES) | 1.0-1.4: xorshift passes every draw at sizes BELOW the median as-routed need (uxori 3 vs 4, ucmpi1 5 vs 7; x0.55a is static-negative at both corners on all 26 clean routes); collatz/ipow need ~= draws (static nom flagged exactly the two failing routes) | conf tables below |

Static rule vs draws, one route = one row, EQUIVALENT ffmux-clean routes (corner_audit at nom / worst, any sized row < 0):

| sizes | static clean & every draw passes | static negative & every draw passes | static negative & a draw fails | static clean & a draw fails |
|---|---|---|---|---|
| xorshift x0.55a (nom) | 0 | 26 | 0 | 0 |
| xorshift x0.40a (nom) | 0 | 10 | 5 | 0 |
| collatz x0.55 (nom) | 15 | 12 | 1 (route 30) | 0 |
| collatz x0.70 (nom) | 21 | 3 | 0 | 0 |
| ipow x0.55 (nom) | 13 | 7 | 1 (route 12) | 0 |
| ipow x0.70 (nom) | 14 | 7 | 0 | 0 |

Never a draw failure on a statically clean route; the static rule is conservative but not by much on collatz / ipow.

## 3. The rule change (one, every kernel): `CA_SIZERULE=1` in research/tools/corner_audit.py

Opt-in; unset, corner_audit is byte-identical (checked: report.txt, lines.tsv, sizes.vh, verify.txt, soak.sdf and
stdout of HEAD's corner_audit vs the edited one, default flags, collatz route 7aefc4bd -- see "checks").

1. **One band for the matched delay and the data's LUTs and wires** (0.21: the board's kernels sit at 0.211-0.225;
   the chain was already at 0.21). The data's LUT/wire part was at 0.288 while the chain was at 0.21. CARRY4 / F7F8 / FF
   stay at SLOW_MAX: not a corner mix but the upper bound of a cell type nobody has measured (BOARD-QUEUE item 36
   measures it; when it does, set `--cell` to its band). Guards unchanged: 0.97/1.03 and max(0.03 t, 50 ps) are already
   the measured within-die scatter (ring residual 0.76%, setting M 1.34%), not the band.
2. **A shortened line is priced at its own mean link step as routed**, D(m) = D(n) - (n-m) c_own, instead of
   "dearest step out, single cheapest hop of the route as the rebuilt chain". Re-placement of the chain is a
   route-to-route spread, and the per-cell max over routes (or the draws on the rebuilt route) already carry it.
   `CA_SIZERULE_MLO=1` restores a milder cap (lowest whole-chain mean on the route, c_mlo; 283 ps on collatz 7aefc4bd vs
   c_lo 182) if the farm shows the plain price is too short.
3. **Select paths sized like any line** (implies --shrink-selects): the select rule was withdrawn 2026-11-15; rules E
   and M (which fail their negative controls on every family, research/data/selneg) are what this tool sizes them on.
4. `CA_SIZERULE_FLOOR=floor_<kernel>.vh`: never below the largest size that failed a draw; +1 on lines the static check
   named on the failing routes (research/tools/sizerule_floor.py). Floors: xorshift = x0.40a (+1 on uxori1/2, ucmpi0/1,
   umux0-2, ucontrol_merge1, the H/I links named); collatz = x0.55 (+1 ucmpi0); ipow = x0.55 (+1 umux3); collatz64 =
   x0.55 provisionally (+1 ucmpi0, umux0, umux2: shrink10b x0.55 routes 19 and 30 timed out on every draw so far, not yet
   read as a timing verdict).

Why this and not a smaller guard: the guard is < 0.4 element; the price and the corner are the two terms that carry
the factor, and both are statements about the circuit (one die, one corner; a chain costs what it costs), not tuning.

## 4. What it gives (one route per kernel, local), against x0.55 / x0.70 of the item

RESULTS_TABLE

## 5. Farm request

research/cluster/requests/sizerule1.sh (drafted, not submitted): every kernel, routes 1-16; per task the item's sizes
are built, the rule sizes that route, the route is rebuilt with them, then 4 default draws and the `worst` gate.
It needs research/tools/corner_audit.py, research/tools/sizerule_floor.py and research/data/sizerule/floor_*.vh
committed first.

## Checks

CHECKS

## What this does not show

- No draw has run on any size this rule produced. The tables in section 4 are one route each.
- The decomposition's as-routed need ignores rule E on compares (ucmpi* are often bound by E at a steer) and uses
  380/420 ps per element on the items' report rows; the line_account numbers are on items 28 / 19 / 26's routes, not
  31 / 29 / 32's.
- The CARRY4/F7 band is still the draws' assumption [0.2, 1.0]; collatz x0.55 route 30 fails only above 0.75.
- The rule merges chain and rest bands; the draws still draw them independently, and 4 draws per route rarely land on
  chains 0.20 / rest 0.31. The `worst` gate in sizerule1 is the targeted check of that mismatch.
