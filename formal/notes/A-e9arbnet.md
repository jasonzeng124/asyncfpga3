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

**B1 under the corner model (2026-10-31).** Lean (`Events9ArbB1`, check.sh OK): `b1_of_ord` gives B1 from the
behaviour's own read order `fQ (wq t) ≤ wr (t-2)` (no band row); `ord_of_transport` gives that order for fixed
path delays with `Dr + 2 ≤ DQ + Dq`; `corner_ord` gives that from delays within `1 ± kn/kd` of shared nominals
when `(kd+kn) Pr + 2kd ≤ (kd-kn)(PQ+Pq)`. xarbnet prints that threshold κ = (PQ+Pq-Pr-2)/(PQ+Pq+Pr), taken
at both band ends (`b1Kappa`, untrusted arithmetic; nominals = every arc at the same band end). Smallest
over the failing readers (`results/b1_kappa_1031.txt`, ×1e-6): slow d/3/4/5 = 0.0597/0.0671/0.0548/0.0613,
fast 0.0537/0.0547/0.0467/0.0536. So if the in-corner spread is shared and the local path scatter is ≤ ~4.6%,
B1 holds on every gcd_hw arbiter reader that fails it in band form. This is close to B's server-free arbiter
threshold 0.0443 (OnGcdArbKappa). NOT done: plugging the corner-model order into arbCond_of_edge (it takes the
band row ArbRowsOK, not HOrd), and the readers that pass in band form were not re-checked under κ.

**gcd_hw with the read order assumed (2026-10-31).** `Events9ArbB1.arbCond_of_ord` = `arbCond_of_edge` with
the four B1 band rows replaced by `ArbOrd` (per reader, the behaviour's read order); `ArbRowsOKS` = the
remaining (start) conjuncts, decidable; `ord_of_row`: a reader whose band row holds satisfies its order for
every behaviour, so ArbOrd is a real assumption only at the readers whose band row fails.
`Events9FullArb.design_verdict9arbnet_ord` is the par verdict with ArbOK/OwnOK/RsOK/FixShape/ArbRowsOKS
checked and ArbEdge + ArbOrd assumed. xarbnet: ArbRowsOKS 9/9 on all 16 rows. With xevents9par CLEAN, all
checked premises hold on **10 gcd_hw rows: slow and fast on d/3/4/5, gb on 3/4**
(`results/gcd_ord_table_1031.txt`). What is assumed for those rows: SatPin, constants/reset, ArbEdge (QClean,
quiet start, settle bound, edge windows), ArbOrd at the B1-failing readers (supported, not proved, by the
corner model: shared band position plus path scatter κ <= ~0.047, via ord_of_transport/corner_ord and the
untrusted b1Kappa print), SelOK, SelPart.

**QClean reduced to quiet reads (2026-10-31).** `Events9ArbB1.qclean_of_quiet` (check.sh OK): for any self-loop
`q t = F (X t) (q (f2 t))` (own-feedback warp lower delay >= 1, upper hi2), if the cell's OTHER reads `X` are
constant for `hi2` after each change of q, then QClean holds. For ustate O6 this replaces the no-runt hypothesis
on q by a condition on ustate's input reads (requests, reset, A0): no input read changes within one q-feedback
delay of a q change. A contested near tie violates it, as it must. (`st_stable`: the real INIT is also
one-step stable, not needed by this proof.) Not done: instantiating it inside ArbEdge (QClean is still the field).

**Scope of every "row covered" statement in this note (self-audit, 2026-10-31):** it means the decidable
premises evaluate to true on that row. No witness shows SatPin + constants/reset + ArbEdge (or QQuiet and the
rest) + ArbOrd + SelOK + SelPart jointly satisfiable on that route, so no row is shown non-vacuous.

**Untrusted simulation check (2026-10-31; `tools-A/xaudit/arbnet/simq.py`, results `results/simq_1031.txt`).**
sim0.py's fixed-delay behaviour (slow lo ends, rst at 20 ns, selects frozen at 0 or 1) on the rebuilt
skeletons, seeds d/3/4/5: grant exclusion OK, ArbOrd (fixed delays) OK on every grant reader, QQuiet "OK". But
each run has at most ONE q flip before the frozen-select skeleton goes quiet, and the negative control (QQuiet
window 1e9 ps) is also "OK", i.e. the check could not fail on these runs. So this is **no evidence** for QQuiet;
it only confirms that ArbOrd holds at fixed lo-end delays (which b1Corr already showed). A useful run needs
live selects (a select model from the data path), not done.

**From S on (2026-10-31).** The GLS run (tools-A/xaudit/glsq) shows QQuiet false during power-up (3-7 ns, rst high)
and true after reset. So `Events9ArbB1` adds pointwise flip lemmas (`flipAway1'`/`flipAway2'`),
`qcleanFrom_of_quiet` (QClean after S from quiet reads after S plus q settled on `(S - hi2, S]`), `ArbRowsOKSS`
(decidable), `ArbEdgeS`, `arbCond_of_ordS`, `cleanS_of_arb`, and `Events9FullArb.design_verdict9arbnet_ordS`. xarbnet
evaluates ArbRowsOKSS with S = T: 9/9 on all 16 gcd_hw rows. With xevents9par CLEAN, the same 10 gcd_hw rows
meet every checked premise of `design_verdict9arbnet_ordS`, whose arbiter hypotheses are: QQuiet after S and q
settled just before S (both observed on the seed-5 research GLS, 16 vectors, no scatter), the quiet start,
settle bound and edge windows (ArbEdgeS minus cleanS), ArbOrd at the B1-failing readers.

## Proposed next probe: AND-grant core (drops ArbOrd) — NOT started

Why: ArbOrd (B1) is a condition of the corrected core's C-element grant, and the research GLS shows it can fail
while the circuit works (σ = 0.10 draw 2). Shape of the fix:
- In `Events9Arb.VRd`, give the virtual reader's request input TWO copies, combined by AND (the Events7 node
  framework already has multi-copy AND pins, `PK.multi` with `op`): copy 1 = the reader's own request read `wr`
  (band Dr), copy 2 = the request read at ustate's request-read time of the reader's q read, warp `fQ ∘ wq`
  (band `[lo Q + lo Dq, hi Q + hi Dq]`).
- Why it matches the real AND grant `s(wr) && e(wq)`: a fall through q comes from a flip away at `τ ≤ wq t`,
  for which ustate read the request low at `fQ τ ≤ fQ (wq t)`, so with NoReReq copy 2 is already low. A rise
  needs `e(wq t)` on the branch, set after ustate read the request high at `fQ τ ≤ fQ (wq t)`, so with no
  withdrawal before the grant copy 2 is high. That is the argument of `grant_fall_after_req_fall`, turned around.
- Work: the VRd/CoreFix/`core_of_settle` proofs in Events9Arb (B1 clause replaced), the virtual-node bands in
  ArbOK (`rdG`/`rdS` gain the second copy), `par/cert9p.py` + `events4/model.py` (emit the 2-copy pin), and a
  rerun. Expected: ArbRowsOK without the B1 rows, i.e. ArbRowsOKS, on all 16 gcd_hw rows, and no ArbOrd.

**`b1_and` (check.sh OK) and its row on gcd_hw.** With the two-copy request pin, B1 needs only `lo Dr ≤ lo Q + lo Dq`.
xarbnet prints that margin for every reader of every arbiter: minimum over 4 seeds = slow 148, fast 53, indep 53,
gb 113 ps, i.e. it holds on ALL 16 gcd_hw rows, in band form, with no correlation assumption. So the AND-grant
core would remove ArbOrd entirely. The core itself (the B2/C clauses and the EnOK matching with the second copy,
the cert generator, ArbOK's bands) is still the proposed probe above.

**Caveat on the AND-grant proposal (found 2026-10-31 while writing its matching lemma).** `b1_and` fixes the B1
clause only. With the AND request input, `and_cel`'s matching gains a case the C-element cannot follow: copy 2 low
(ustate already read the request low) while the grant's own request pin is still high. If the enable is then also
low, the virtual C-element falls while the real AND grant is still high (its own pin is stale and q has not yet
flipped away in its view), i.e. the virtual grant falls EARLIER than the real one. If the enable is high there,
the virtual grant holds, which needs "the grant was already high" (a new clause). So the proposed core needs
either extra trace conditions for these cases or a different virtual node (e.g. an AND node with separate
rise/fall rules in the count semantics), and is not the drop-in replacement the section above suggests.
