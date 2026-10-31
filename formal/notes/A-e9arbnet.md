# A-e9arbnet (probe E9ArbNet, shard A): lifting the cell-level arbiter core to the netlist

STATUS (2026-10-31 07:55, lead): CLAIMED as left by the 2026-10-29 session (which died before claiming).
Events9ArbNet / ArbNetRows / ArbNetEdge / ArbNetMain checked on 2026-10-31 by the lead with Lean 4.35.0,
-DautoImplicit=false, in a scratch overlay of the tree (plain `lean`, same sources; lake build pending),
axiom audit: only propext / Classical.choice / Quot.sound. What is proved:
- `arb_core`, `harb_of_arbs`, `design_verdict9arbnet`: design_verdict9par with HARB7' and HRst
  replaced by the decidable checks ArbOK (bd_arbiter's four LUT functions read off the INITs, every
  read path, request nets, corrected-core shape and bands), OwnOK, RsOK, FixShape, and the
  per-arbiter TRACE conditions ArbCond (hypotheses).
- `Events9ArbNetEdge.arbCond_of_edge`: ArbCond follows from the decidable rows ArbRowsOK (B1 rows and
  start bounds) plus the edge-window hypotheses ArbEdge: QClean (q makes clean transitions: the
  digital no-metastability hypothesis), a quiet start, a settle bound H (`stall`; no band bounds it,
  and for a near tie none exists), and per reader RdEdge (no re-request while the arbiter switches
  away; settledness windows after request rises / literal flips; A0 high around request falls).
- `Events9ArbNetRows.Rows`: DEFINITIONS of printed margins only. No theorem says the printed rows imply
  ArbEdge. The run tables (results/xan_*) are from 2026-10-29: ArbOK 9/9 on all 16 rows; the printed
  B1 margin is negative on some arbiters (seed d slow: merge6.uarb1 g1 -2 ps, s1 -190 ps; merge4.uarb1
  s1 -32 ps), so ArbRowsOK fails for those arbiters at that corner and arbCond_of_edge does not apply
  to them there.

Plan
1. ArbNet check: for each arbiter named in the certificate, a decidable check over A's parsed
   design `d` that its ustate/ugrant LUTs are bd_arbiter's (INITs ARB_ST/GRANT, pin wiring),
   and a theorem SatPin on d + per-reader conditions => the cell-level ArbPin behaviour =>
   (core_of_en_rst) HARB7'/HRst at that arbiter.
2. B1/B2/C/settle as decidable rows over the band file's per-pin arcs and the certificate's
   walks; executable; run on 16 rows.
3. What remains: Unc W, metastability (settle bound H not available for near ties).

## 2026-10-31 (lead): ArbRowsOK evaluated on the 16 rebuilt rows

Rebuilt gcd_hw R5 d/3/4/5 from `git archive 520a43f` (toolchain restored from the cache branch,
toolchain.sh 9/9, nextpnr 9c732bc6303458df; BD_SIZES=gcd_hw_sizes_R5.vh, BDC_SELECT_PADS=gcd_hw_pads.json,
BD_RLOC=v4, no --freq): all 8 SDF / routed-JSON md5s equal events5/builds.txt. e8mux/bands.sh (new
variant) reproduces the recorded skeleton md5s; par/run.sh reproduces all 16 committed xe9p results byte
for byte; arbnet/run.sh reproduces the committed xan results (before the edit below).

`xarbnet` now also evaluates `decide (ArbRowsOK d a T T0)` (T = `--T`, default 20000 = rig_rst release
at 20 ns; T0 = `t0Min`, the least quiet-start time the start-bound conjuncts allow) and prints the
negative conjunct margins. Table (`results/rows_table_1031.txt`): arbiters with ArbOK and ArbRowsOK, of 9:

| corner | d | 3 | 4 | 5 |
|---|---|---|---|---|
| slow | 7 | 3 | 7 | 5 |
| fast | 7 | 4 | 7 | 6 |
| indep | 0 | 0 | 0 | 0 |
| gb | 1 | 0 | 1 | 0 |

Only the four B1 conjuncts ever fail (start bounds and the `2 <=` side conditions always hold). Worst
margins: slow -131..-243 ps, fast -54..-103, gb -657..-910, indep -1442..-1893.

**What a failing B1 row means.** B1 (`RdOK` clause 1) asks: if a reader sees the request high and the
state literal lost at `t`, the reader's output was already low at `t - 2`. The real grant is an AND of its
request read and its q read. The row `hi Dr + 2 <= lo DrQ + lo Dq` makes the grant's request pin see a
request fall no later than ustate's request pin plus the grant's q pin. When it fails, the trace that
breaks the proof is: the request falls, ustate sees it and flips q, and the grant falls through its q pin
while its own request pin still reads the old high request. The grant falls AFTER the request fell (four-
phase order kept), but the corrected core's grant (a two-input C-element on request and ctl) cannot fall
while its request input is high. So the failure is a limit of the abstraction. It is not shown to be a
circuit failure, and no counter-run of the real cell was built for it. Consequence: `design_verdict9_full_arb`'s
checked premises hold on NO gcd_hw row (each needs 9/9). A core whose grant may fall from either input (an
AND, not a C-element, on the fall) would remove this row; that changes Events9Arb's virtual node kind, not
done.

**Lean support for that reading** (`Core/XAudit/Events9ArbB1.grant_fall_after_req_fall`, check.sh OK):
for the real grant `y = s(wr) && e(wq)`, under ustate's flip property and NoReReq only (no B1 row), every
grant fall at `t > lo Dr + lo Q + lo Dq` is preceded by a time `u` with `wr(t-1) < u` (after the grant's
last high read of the request), `s u = false`, and `u + min(lo Dr, lo Q + lo Dq) <= t`. So req↓ → grant↓
holds whichever pin the fall came through. Not covered: exclusion, rises, the downstream readers.

**B1 and the within-corner spread (2026-10-31, diagnostic, no theorem).** xarbnet now also prints, for each
failing arbiter, B1 with EVERY arc at the same end of its band (`b1Corr`: all at lo, all at hi; B1 is
linear in a shared position, so both ends >= 0 means it holds at every shared position). On gcd_hw slow and
fast, all 4 seeds, every reader of every failing arbiter (104 reader rows): min 51 ps at the lo end, 59 ps at
the hi end, i.e. B1 HOLDS. So the B1 failures come only from letting arcs inside one corner sit at
opposite ends of their prjxray [MIN, MAX], independently per arc. Whether that spread is shared (the
H_SPREAD_CORRELATED / κ question of gcd_hw_hypotheses.md) decides it. Under a corner model with a shared
position inside [MIN, MAX] and a local scatter κ, B1's margin of >= 51 ps over paths of ~1-2 ns suggests a
κ threshold of a few percent; that threshold is NOT computed or proved here.
