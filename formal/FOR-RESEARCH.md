# For research and the owner: THE goal (the gcd_hw bitstream theorem)

Started 2026-11-01 by shard A. Counterexamples to THE theorem go here first (PROGRAM.md). The older,
rule-by-rule list is `formal/out/FOR-RESEARCH.md`.

## C15. Your two asks of 2026-11-16 (FOR-FORMAL 1b00b6ae): C10's routes with a 12 ns host, and fcsel3a seed 20 (shard C, 2026-11-16; search, untrusted)
`formal/tools/margin/run.sh` with `HOSTDELAY=12000` (the host moves the next operand 12 ns after the acknowledge it
reacts to; still a Spec.Env behaviour), every race class, each reported race traced to two paths and timed at your SDF
(farm fm_c_margin_r12; files there and in `formal/tools/margin/out/`). The kappas only order the search.
**C10's routes, 12 ns host.** The falseResult_3 stage-0 races C10 reported are gone on every route (they were
input-hold races against a 1-ps host, as the audit and C11 said). What the search still breaks:
| route | first finite failure (kappa) | the race, in ps | hang (kernel acks a/b, not start) |
|---|---|---|---|
| fcsel2 s1 (5b538ca5) | none <= 0.45 | -- | 0.37: `ulink_n_falseResult_7` stage 1 ctl feedback (4 routing arcs) vs rdly g[0] -> stage 2 ctl -> back: +132 worst in-band, **+904 SDF** |
| fcsel2 s2 (fb1efc41) | 0.44, a steer cone (not traced to two paths) | -- | 0.45 |
| fcsel1 s24 (afab5445) | none <= 0.45 | -- | 0.09: falseResult_7 st0 ctl feedback (5 routing arcs): **+45** worst in-band, +406 SDF (C13) |
| fcsel1 s1 (4445b56c) | 0.42: a fork near `ulink_n_falseResult_9` stage 0's latch (SLICE_X17Y54.D6 pin 0 direct vs pin 4 through 2 LUTs) | +111 worst in-band, +657 SDF | 0.40 |
| fcsel0 s24 (bb5fbbdb) | 0.37, a steer cone (got [0]; not traced) | -- | -- |
**fcsel3a seed 20 (7aefc4bd).** 1-ps host: the first race is again the input-hold race at falseResult_3 stage 0 (through
the host: +393 worst in-band, +1216 SDF). 12-ns host: no single-route or capture race below 0.45; the falseResult_7
controllers hang the kernel: stage 0 from 0.24 (no filter): feedback 1 LUT + 5 routing (SDF 772) vs rdly g[0] -> stage 1 ->
back (SDF 1536): **+174 ps worst in-band, +764 ps at your SDF** (0.71 / 1.06 x the worst short-ring error); stage 1 from
0.44: +399 / +1117. **uselect0's line** does not appear among the races our search breaks up to 0.45 on this route
(single routes, whole data cones, steer cones); its own slack in ps (its data vs its request) is not computed yet --
the tool explains races it breaks, and this one it did not break.
**fcsel3a seed 20, capture races swept to kappa 0.90 (12-ns host; fm_c_margin_usel2).** The first one broken (0.46) is
the select link's own latch, `ulink_n_index_11.many.stage[0].lat.odd`, against `ucontrol_merge1`'s bundle: common launch
`ucontrol_merge1.uarb1.ustate`; path A (data): `uarb1.ugrant` -> merge1's data LUT -> latch pin: 3 LUTs + 12 routing,
740 ps fast mid, SDF 1555; path B (enable): `ustate` -> merge1's matched delay `udly.chain.g[1]` -> the link's ctl ->
latch enable: 4 LUTs + 16 routing, 850 ps, SDF 1985. Slack **+110 ps fast mid, +430 ps at your SDF (0.46 x the worst
short-ring error), and -93 ps at the worst split inside the fast band** (A at its band maximum, B at its minimum). So
merge1's matched delay (two elements here) covers its data by about 0.1-0.4 ns. uselect0 is on neither path, and on none of the
paths explained for the other captures that fail up to 0.90 (ulink_n14__1 at 0.82, +1679 ps SDF; three others at
0.84-0.88 with 2.2-9.6 ns of SDF slack; three more traces were rejected as inconsistent). **uselect0's line itself (farm c_margin_usel3, `conenames.py`):** the only capture whose data cone runs through
uselect0 is `ulink_n_falseResult_9.many.stage[0]` (32 latch bits; cone includes uselect0's data LUTs and `uselect0.uz_n29`).
With that whole cone slowed to (1+k) x its fast-band maximum and everything else at (1-k) x the minimum, the kernel is
correct at k = 0.45 (20 ps filter; fm_c_margin_r12 task 7) and the run at k = 0.90 is undecided (event cap). So
uselect0 at 7 holds its capture far beyond every race above in this search. Its slack in ps is not computed (the tool
traces races it breaks). **Checked (farm c_verify1): this race alone does
NOT fail** -- with exactly path A slowed to (1+k) x its fast-band maximum and everything else at (1-k) x the minimum,
the kernel is correct at every k from 0 to 0.45. The -93 ps split is arithmetic on two path sums; the latch does not
lose a value from it on these vectors. The cone failure at 0.46 needs more of the data cone slow at once. Same
structure on item 27 (C12): +1418 / +1423 ps SDF there.
**fbslack.py agrees.** Run on the farm's SDFs, the static screen gives the same controller slacks as the dynamic traces:
fcsel3a s20 st0 ctl +764 ps, fcsel2 s1 st1 ctl +904 ps (both identical to explain.py). So `fbslack.py BUILD.sdf --grep .ctl.`
is a 5-second check of this race on any route of yours.

## C14. The ulink_n13 race (item 28's and item 26's first finite failure) in picoseconds: a kernel race with 2.5-3.1 ns of slack at your SDF (shard C, 2026-11-16; search, untrusted)
Traced by `tools/margin/explain.py` (trigger chains; farm fm_c_explain6). KERNEL race on both: the enable of a
`ulink_n13` latch bit against the NEXT value reaching its data pin after ulink_n13's acknowledge reopens the upstream link.
| build | path A: ulink_n13.ctl -> enable pin | path B: ctl -> uack chain -> umux1.uya -> falseResult_5 st1 ctl -> its latch -> umux1 data -> data pin | slack mid / worst in-band / SDF | x 8.5 % / x 47 % (SDF) | your row |
|---|---|---|---|---|---|
| item 28 (lat.pair[6] LUT6) | 1 LUT + 7 routing: 609 ps mid, SDF 1142 | 6 LUTs + 34 routing: 1958, SDF 4273 | +1348 / +965 / **+3131** | 8.6 / 1.56 | H +1337 (enable 1241, data 2628); hold_bits ulink_n13 min 1566 ps |
| item 26 (lat.pair[6] LUT5) | 1 LUT + **12 routing**: 964, SDF 1975 | 8 LUTs + 38 routing: 2179, SDF 4523 | +1215 / +710 / **+2548** | 6.6 / 1.20 | (not looked up) |
| fcsel3m seed 24 (item 28's structure; host 2 ns): `ulink_n10__3.lat.pair[20]` (LUT5), launch `ucond_br7.uack` | ulink_n10__3.ctl -> enable: 2 LUTs + **22 routing**: 1518 mid, SDF 3337 | ufork8 -> ulink_n10__4 ctl -> ufork3 -> umux0.uya -> falseResult_9 st1 ctl -> its latch -> umux0 data -> pin: 8 LUTs + 48 routing: 2930, SDF 6373 | +1413 / +670 / **+3036** | 5.6 / 1.01 | (not looked up) |
- Your rule H and our trace agree on the enable side (1241 vs 1142 ps at the SDF) and differ on the data side (2628
  vs 4273): our path B is the chain that actually fired in the run (through umux1 and falseResult_5's stage 1 latch);
  your H takes the earliest possible sender, which can be shorter. Both say clean by more than a nanosecond.
- The kappa (0.42 on item 28, 0.26 on item 26) is only this slack's ratio: the race is lost once (1+k) x path A's
  fast-band maximum exceeds (1-k) x path B's fast-band minimum: k = (1872 - 1162) / (1872 + 1162) = 0.23 on item 26.
  Item 26 sits lower because its enable route is 12 routing arcs long, not because its kernel is closer to failing at
  the SDF. For the audit (T119, replay correct with this arc at 1.26 x FAST_MAX and the kernel at 0.74 x FAST_MIN):
  formal's prjxray fast band puts path A at [1162 max] and path B at [1872 min] ps; if the audit's FAST_MIN for
  path B's routing is larger than prjxray's, the replay keeps a positive margin (393 ps there), which would explain it.

## C13. A race none of your rules checks: a link controller's own feedback against the next stage's acknowledge (`ulink_n_falseResult_7` stage 0; shard C, 2026-11-16; search, untrusted)
The hangs in C12 (the kernel acknowledges a and b, never start, and stops) come from one controller,
`ulink_n_falseResult_7.many.stage[0].u.ctl` (a C-element LUT that reads its own output). Traced by `tools/margin/explain.py`
(farm fm_c_explain4; KERNEL race: neither path goes through your host):
- Common launch: that controller's output.
- Path A (must arrive first): its own feedback route back into it (the state it holds).
- Path B: through stage 0's request delay `rdly.chain.g[0]` (one element) to stage 1's controller and back into stage 0's
  controller as the acknowledge.
| route | path A (feedback) | path B (rdly g[0] -> stage 1 ctl -> back) | slack mid / worst in-band / your SDF | x 8.5 % / x 47 % (SDF) | kappa (search order) |
|---|---|---|---|---|---|
| fcsel1 seed 24 (sdf afab5445) | 1 LUT + **5 routing arcs**, 384 ps mid (SDF 851: routing 727) | 3 LUTs + 10 routing, 570 (SDF 1257) | +186 / **+45** / +406 ps | 3.8 / **0.69** | 0.09 |
| item 28 = fcsel3m seed 20 | 1 LUT + 2 routing arcs, 290 (SDF 419) | 3 LUTs + 12 routing, 744 (SDF 1536) | +454 / +335 / +1117 ps | 8.6 / 1.55 | 0.36 (no filter) |
- So the controller has to see its own new state before stage 1's acknowledge comes back, and with stage 0's request
  delay at one element that return is only three LUTs long. On fcsel1 seed 24 the placer gave the feedback route five
  routing arcs (727 ps at your SDF), and the slack inside the fast band is 45 ps. Your rows on that route:
  H +936 / I +467 at stage 1's ctl and F (matched-delay drain) rows elsewhere. None of them is this race (a C-element's
  own feedback against the acknowledge it waits for). We have not found it in your rule set.
- What the failure looks like: the controller misses its state for one event, the link's handshake is left half done,
  and the kernel stops after acknowledging a/b but not start. Formal's frozen Spec calls such runs vacuous; on a board
  this is a hang. A proposed fix in formal's Spec (`SpecWF`) would count it.
- Suggestion: a check that every link controller's feedback route is shorter than its shortest acknowledge return,
  with a guard, on every route. It is a one-route quantity, so it moves with placement (5 routing arcs on one seed,
  2 on another): measure it over routes.
- **A screen you can run on any route now:** `python3 formal/tools/margin/fbslack.py BUILD.sdf --grep .ctl.` (formal's
  branch, needs only your nextpnr SDF, ~5 s): for every LUT that reads its own output, A = its feedback interconnect +
  that pin's IOPATH, B = the fastest SDF path from its output back to another of its pins, slack = B - A, also as a
  multiple of 8.5 % and 47 %. On item 25's route it gives `ulink_n_falseResult_7.many.stage[0].u.ctl` A 419, B 1536,
  slack +1117 ps through rdly g[0] -> stage 1's ctl, the same race and numbers explain.py traced dynamically on item
  28. B is the fastest STRUCTURAL return, so a small slack is a race to check, not a failure. Outputs for items 23, 25,
  BAD xf2_1 and gcd_ps: `formal/tools/margin/out/fbslack/`.

## C12. Item 27 (xorshift board candidate) and item 28: the races formal's tool breaks first, in picoseconds, beside your rows (shard C, 2026-11-16; search, untrusted)
All from farm runs of `formal/tools/margin/run.sh` with every race class (single routes, whole data cones, steer
cones) and the checks of C11; files `origin/claude/cluster:results/fm_c_margin_all2/<task>/` and
`fm_c_explain3/7/explain_*.txt`. "Slack" = path B minus path A from their common launch (positive: the required order
holds), at the prjxray fast-band midpoint, at the worst split inside the fast band, and at YOUR nextpnr SDF; then as a
multiple of the ring data's median error (8.5 %) and worst short-ring error (47 %, 7-link rings). The kappa column is
only the order in which our adversary breaks things.
**item 27 (sdf a9bdac53 = your fxd seed 2).** No single route breaks it in our range; two capture races do:
| latch (capture) | common launch | path A (must be first) | path B | slack mid / worst in-band / SDF | x 8.5 % / x 47 % (SDF) | your rows | kappa |
|---|---|---|---|---|---|---|---|
| `ucontrol_merge0_olink.lat.odd` | `ucontrol_merge0.uarb1.ustate` | data: 3 LUTs + 11 routing, 767 ps (SDF 1397) | enable via the olink ctl: 6 LUTs + 27 routing, 1484 (SDF 3173) | +716 / +451 / **+1776 ps** | 6.6 / 1.2 | none found in fxd seed 2's files (your fr3 build fxf4_s seed 2 has H +3492 at the olink ctl) | 0.39, wrong count (2 of 4 answers), checked |
| `ulink_n_index_15.many.stage[0].lat.odd` (a select link) | `ucontrol_merge1.uarb1.ustate` | data: 3 LUTs + 12 routing, 787 ps (SDF 1540) | enable: 6 LUTs + 25 routing, 1284 (SDF 2958) | +498 / **+243** / **+1418 ps** | 5.6 / **1.0** | your hold_bits on fxd seed 2: the same LUT (SLICE_X14Y33.B6) is the tightest hold bit, min 1159 ps (fxf4_s, fr3: H +1394 at the st0 ctl) | 0.28-0.29: the kernel acknowledges a/b, not start, and stops |
(Update, farm c_verify1: with the host moving data 12 ns after the acknowledge, the olink capture race first fails at
kappa 0.61, not 0.39 as with a 1-ps or 2-ns host, and that 0.61 run breaks Spec.Env (not a counterexample). So although
both of its paths are inside the kernel, how early your host offers the next operand changes whether it bites.)
Both are KERNEL races: neither path goes through your host (unlike C10's and item 25's, which close through the host
releasing the next input; formal's tool now separates the two, `HOSTDELAY=`). Both are setup (capture) races at the merge-arbiter's output: the arbiter's state flip reaches the latch's data through
3 LUTs and its enable through 6, so the bundling here is the difference of two short paths, about 0.5 ns. Your rules
H and hold_bits look at the other direction (hold) of the same latches; rule E looks at the mux select arrival; we have
not found a row of yours for this setup race at the latch's data pin. At your SDF the second race has a slack equal to
the worst error measured on short rings. Path A is the data path that is critical in the all-fast reference run; the
adversary slows the whole data cone, so the path that actually lost can be a longer one inside it (being traced). Not
yet checked on other routes of item 27 (one route is a sample).
**item 27's structure on 4 more routes (seeds 1, 3, 4, 5; sdf e2914f00, e6719b93, 32142fab, 2ae1a2b5; host moving
data 2 ns after the acknowledge, so kernel races only; farm fm_c_margin_x27r).** Seed 5 has the same capture race at
the merge1-arbiter-fed select-link latch: split `ucontrol_merge1.uarb1.ustate`, data 3 LUTs + 11 routing (SDF 1398 ps),
enable 6 LUTs + 24 routing (SDF 2821): slack **+1423 ps at your SDF (1.07 x the worst short-ring error)**, vs +1418 on
seed 2. So this race is about 1.4 ns at the SDF on two routes out of two where it shows. On all five routes the search
also breaks steer cones (a branch condition reaching its C-element late: 0.30-0.45) and finds partial-ack hangs
(0.23-0.31); the steer races are not yet traced to two paths (the tool reports them UNRELIABLE rather than guess).
**item 28 (sdf d86bdde5).** Besides A8's ulink_n13 race (your H +1337, hold_bits 1566 ps, kappa 0.42): from kappa 0.36
(no filter) the kernel can stop after acknowledging a and b but not start, at `ulink_n_falseResult_7.many.stage[0]`'s
controller reading its own output late (a feedback race). The same controller does this on fcsel1 seed 24 from kappa
0.09, on fcsel3m seeds 2 and 24 at 0.35-0.37, and on items 25 and 26 at 0.37-0.38. Formal's frozen Spec calls these runs
vacuous (A: `SpecWF`); on a board they are hangs. Picosecond form: farm c_explain4, running.
**Livelocks** (periodic, never answering; `simx --periodic`): item 28 at 0.42, item 26 0.38, fcsel3m s2 0.38, s24
0.40, item 27 0.35 (no filter).

## C11. What formal's margin tool now looks at beyond A8: whole data paths slow at once (capture races), livelocks, and three checker fixes (shard C, 2026-11-16; search, untrusted)
Item 28's single-route result is A8 (same farm builds, same numbers; C's run: `formal/tools/margin/out/farm_item28_fcsel3m_s20/`).
Per the owner's rule (PROGRAM.md, "A kappa is not a result") the kappas below only say which race our adversary
breaks first; the picosecond form of each race (both paths from their split, cells and routing, slack at your SDF,
your rule row) is what C builds next, in the tool.
- **Capture races (new class, `tools/margin/cones.py`, run.sh `CONES=1`).** A8's sweeps slow ONE route. A bundled-data
  capture fails when the whole data path into a latch is slow and its request path fast. Per link stage, the tool now
  slows the entire combinational cone into the latch bits (datapath, carry, mux data LUTs and the routes of their
  select inputs) and keeps everything else fast. `STEER=1` does the same for a C-element or steer reading data (a
  branch condition). On every collatz/collatz64 route tried, the first capture race the adversary breaks is the
  one-bit latch of **`ulink_n_index_11.many.stage[0]` (lat.odd)**, one of your select links, whose data cone is the
  index computation (~770-1550 arcs); on xorshift item 27 it is `ulink_n_index_15` stage 0 (also a select link) and
  `ucontrol_merge0_olink`'s latch. Checked so far: **item 27 fails as a capture at `ucontrol_merge0_olink`** (2 of 4
  answers, then quiet), where no single-route race fails in the same search range; fcsel3m seed 2 at
  `ulink_n_index_11` stage 0 returns a spurious first answer (106, then 111, 170 for want 111, 170, 350). These rest on
  the old checks; farm c_margin_all2 reruns all classes with the fixes below on items 28, 25, 27, 26, fcsel0 s24,
  fcsel1 s24, fcsel3m s2/s24.
- **Checker fixes that change what is reported (all in `tools/margin`, `tools/huff/envcheck.py`):** (1) runs where no
  20 ps runt filter is consistent with the delay windows are not behaviours and no longer count as failures; (2) a
  run where only the simulated harness broke the protocol (it released data on an acknowledge that then glitched) is
  re-run with a harness that holds data until its next request; (3) envcheck's "request low at the end" was stronger
  than the Spec; a run where your kernel acknowledged a and b but never start and stopped is now reported as
  PHYSICAL: a real harness hangs, but the frozen Spec is vacuous there (A proved it: `SpecWF.env_unsat_partial_ack`).
  Item 25 shows such hangs from steer-condition races without the filter.
- **Livelocks.** `simx --periodic` recognises a run that repeats for ever without answering; the tool reports it on its
  own line (liveness). On gcd_ps it finds the 0.36 livelock with period 79 ps, the period A's Lean proof found.
- **First race in picoseconds (tool: `tools/margin/explain.py`, run.sh now writes `explain_*.txt` for every reported
  race).** item 25 (sdf e001dc27), the race the adversary breaks first without the filter: latch
  `ulink_n_falseResult_3.many.stage[0]` lat.pair[12] (SLICE_X14Y55.A6). Common launch: that stage's `ctl` output
  (SLICE_X16Y38.A6). Path A, ctl -> the latch's enable pin: 1 LUT + 6 routing arcs, 550 ps at the prjxray fast-band
  midpoint (1243 slow-band). Path B, ctl -> 3 LUTs -> the kernel's input acknowledge (a_ack, SLICE_X17Y32.A6) -> the
  harness puts the next input on the bus -> 8 routing arcs -> the same latch's data pin: 1745 ps (4174), with the
  harness taking 1 ps. Slack +1196 ps = 8x the 8.5 % ring error (+838 ps at the worst in-band split). So it is a hold
  race through your harness: the kernel acknowledges its input before the latch holding it has closed, and only a
  harness that changes the data within about 1 ns of that acknowledge can break it. Formal's Spec allows a 0 ps
  harness; your clocked bench does not. Does any rule of yours look at a_ack against that latch's close? The same
  form for items 28, 26, 27 and fcsel3m s1/s2/s24 is on the farm (c_explain1); nominal-SDF slacks next (prjxray band
  midpoints for now).
- Not covered: two independent slow routes outside one cone, the slow corner, kappa_lo (none for any build).

## A10. Your rule-E question on fcsel1 / fcsel2 ("are the rows at the muxes real?"): in formal's model the mux races are the last to fail, not the first (shard A, 2026-11-16; search, checked; NOT yet in picoseconds)
Farm fm_a_selrace_fcsel: fcsel2 s1 (sdf 5b538ca5), fcsel2 s2 (fb1efc41, your E -114 ps at umux0), fcsel1 s24 (afab5445),
rebuilt = yours. Sweep of every combinational LUT feeding storage (selrun.sh; one route slow at a time, g = 1, corner 0,
vectors 27/703/77031; failures re-run and accepted by both checkers):
- no such race fails below kappa 0.45 on any of the three (435 / 433 / 432 active pins);
- the first that fail (0.66-0.75) are `ucond_br5` reading the comparator `ucmpi2.uz_n36` late, not a mux; also some
  partial-ack hangs at 0.64-0.79 that formal's frozen statement cannot even see (JOURNAL 2026-11-16, SpecWF.lean);
- `umux0`'s data LUTs (`umux0.udat.pair[*]`) first fail at **0.85-0.88** on all three routes.
For comparison, on the same routes the latch races of C10 fail at 0.21-0.32, and those are input-boundary races (A9).
**The same sweep on the board candidates and the select-link minimal pair** (farm fm_a_selrace_board; SDFs a9bdac53,
6982a9d5, 2f825834, 98809562, acc06847 = yours):
| build | combinational race below 0.45? | first combinational failure above (checked) |
|---|---|---|
| item 27 xorshift | none (408 active pins) | 0.56: `ucond_br6` reads comparator `ucmpi1.uz_n41` late |
| item 23 xorshift | none (362) | 0.56: `ucond_br6` reads `ucmpi1.uz_n38` late |
| item 26 collatz64 | none (429) | 0.75: `umux0.udat.pair[0]` reads its select from `ulink_n14__0.lat.odd` late (a true select race) |
| **BAD nc64_7** (select link ulink_n14__1 19 -> 10) | **yes, 0.36**: `uaddi1.udly.chain.g[11]` (the adder's matched delay) reads `ulink_n13.ctl` late; 27/703/77031 -> 111/42/478 | -- |
| pc64_7 (its good neighbour) | none (408) | 0.69: `ucond_br7` reads `ucmpi2.uz_n37` late |
The minimal pair separates here too, but nc64_7's combinational race is NOT at the shortened select link: it is the
adder's delay line seeing ulink_n13's controller late, the link of nc64_7's latch race (C8/C9).
So formal does not confirm rule E's negative rows as near failures: by the time a single late route into umux0 breaks
the result, every other race has long failed. **Caveats:** a kappa is a ratio within formal's search, not a measured
margin (owner, 2026-11-16); the picosecond form of the umux0 races (which pin, select or data; the slack from the
split) is not done yet; two slow routes at once and the slow corner are not covered. Files:
`origin/claude/cluster:results/fm_a_selrace_fcsel/<1..3>/{sel,sel95}/`.

## A9. On the other collatz routes the race formal breaks first is at the kernel's INPUT: a latch still closing when the operand may change (shard A, 2026-11-16; search + trace, untrusted)
**Audit correction (T124b, 2026-11-16 ~06:30; accepted by A):** every picosecond slack in A8 and A9 is the smallest
gap among the arrivals that formal's three vectors (27, 703, 77031) make, so only the low operand bits (<= 17) are
exercised. They are not slacks over all bits. The audit's static check over all 32 bits, at FAST_MIN, finds smaller ones:
fcsel0 s24 177 ps (lat.pair[26]; pair[16] 330 ps), and on **item 28 an input race of 771 ps (bit 19) that is smaller
than ulink_n13's 929 ps** in the audit's own rule H. So A8's "the first race on item 28 is entirely inside the
kernel" is withdrawn: over all bits, item 28 also has an input-boundary race, and it comes first. All of these slacks
stay positive, and the input ones assume a sender with zero data hold (the board's PS is µs slow). The mechanisms named
below are CONFIRMED by the audit.

The latch-enable race that C10 and A8 list at `ulink_n_falseResult_3.many.stage[0]` (fcsel3m seeds 24 and 7, fcsel0
seed 24, and by the same link probably the other C10 rows and item 25's w 0 row) has its DATA pin on the kernel's
input bus: the stage-0 latch bits read `n`'s data nodes (`a_data` in the bench boundary) directly. Traced in formal's
simulation at the mid of the fast window, no slow arc, research's vectors (`race_ps.py`, boundary flip times):
| route | stage-0 ctl closes | enable reaches the latch bit | kernel drops a_ack | env changes the operand | new bit at the latch | slack |
|---|---|---|---|---|---|---|
| fcsel3m s24 (`lat.pair[16]` LUT5) | 2,174,155 | +725 ps | +977 ps | +978 ps | +1,376 ps | **651 ps** (1,644 at slow mid) |
| fcsel3m s7 (`lat.pair[6]` LUT6) | 410,731 | +864 ps | +1,405 ps | +1,406 ps | +1,781 ps | **917 ps** (2,393 at slow mid) |
| fcsel0 s24 (`lat.pair[16]` LUT5) | -- | -- | -- | -- | -- | 616 ps (data from a_data; not broken down) |
- **Which two signals race.** Split: the stage-0 controller's close. (Traced, not inferred: in both runs the a_ack fall's flip-by-flip cause chain passes through that close, at 2,174,155 and 410,731 ps.) Path 1: its enable route to the latch bit (725-864
  ps, all routing plus the LUT pin). Path 2: the kernel's acknowledge falling (the close propagated to `a_ack`), then
  the environment changing the operand, then the bit's route to the latch. The environment in formal's statement
  (Spec.Env, four-phase with the "broad" data rule) may change data the moment the acknowledge falls; the runs above
  do exactly that (1 ps later).
- **What it means for the board.** Your PS harness writes the next operand only after it has read the result, microseconds
  later, so on the board path 2 is µs long and this race cannot fail. These kappas (0.27, 0.28, 0.22) are therefore
  margins against a zero-hold sender, not against the board. Item 28's ulink_n13 race (A8) is inside the kernel, but over all
  operand bits item 28 also has an input race that comes first (audit T124b, above).
- **What it means for bdc.** Under the four-phase bundled-data contract the kernel acknowledges `n` while one of the
  latches that holds `n` can still be open at a bit: it relies on the sender keeping data ~0.6-0.9 ns after the
  acknowledge falls. A pipelined or hardware sender would break it. Your rule H looks at a link's close against its
  upstream; does any rule of yours look at the kernel's input boundary (the acknowledge to the environment against
  the slowest enable bit of every latch reading the input bus)?
- **Added 04:01 UTC: the other two board candidates, same method** (local rebuilds, SDF e001dc27 / 6982a9d5 = yours):
  | build | latch | split | path 1 (enable) | path 2 (next data) | slack, fast mid / slow mid |
  |---|---|---|---|---|---|
  | item 25 (collatz, w 0 only) | `ulink_n_falseResult_3` stage 0 `lat.pair[12]` | (through the environment: data pins on a_data) | -- | sender's next operand after a_ack falls | **1,193 ps** / 2,931 ps (input boundary, as above) |
  | item 26 (collatz64) | `ulink_n13.lat.pair[6]` (LUT5) | `ulink_n13.ctl` | 961 ps (cells 242 + routing 719) | 2,170 ps (cells 1,360 + routing 810): `ulink_n13.uack.chain.g[0..2]` -> `umux1.uya` -> `ulink_n_falseResult_5` stage 1 ctl -> its `lat.pair[6]` -> `umux1.udat.pair[6]` | **1,209 ps** / 3,240 ps |
  Item 26's race is item 28's race (the same links, n13 against falseResult_5 stage 1 through umux1), with a longer
  enable route (719 ps of routing against 354 on item 28). Both are inside the kernel; your rule H is the check.
- Not done: the same breakdown for the other C10 routes; whether formal should report these apart (C's
  boundary class E). Files: `formal/tools-A/target/race_ps.py`; numbers from local runs of C's run.sh nets.

## A8. Your collatz board candidate item 28 (fcsel3m seed 20): the race formal finds first is ulink_n13's latch enable against that latch's next data; no select-arrival race short of a very lopsided assignment (shard A, 2026-11-16; search, checked; picoseconds to follow, see the note at the top of this item)
**Audit correction (T124b, 2026-11-16 ~06:30; accepted by A):** every picosecond slack in A8 and A9 is the smallest
gap among the arrivals that formal's three vectors (27, 703, 77031) make, so only the low operand bits (<= 17) are
exercised. They are not slacks over all bits. The audit's static check over all 32 bits, at FAST_MIN, finds smaller ones:
fcsel0 s24 177 ps (lat.pair[26]; pair[16] 330 ps), and on **item 28 an input race of 771 ps (bit 19) that is smaller
than ulink_n13's 929 ps** in the audit's own rule H. So A8's "the first race on item 28 is entirely inside the
kernel" is withdrawn: over all bits, item 28 also has an input-boundary race, and it comes first. All of these slacks
stay positive, and the input ones assume a sender with zero data hold (the board's PS is µs slow). The mechanisms named
below are CONFIRMED by the audit.

**Owner's rule since 03:30 UTC (PROGRAM.md, "A kappa is not a result"): a kappa only ranks races in our search; it
is not a margin of the chip and must not be read as one, nor used to call one build better than another. The
picosecond form of this race (the two paths from their split, cells and routing apart, slack at the nominal SDF, your
rule row for it, the slack as a multiple of the measured 8.5 % ring error) is the next step; until then read the
kappa column below only as "which race our adversary breaks first".**
**The race, in picoseconds (item 28's route; formal's decoded net, prjxray arcs, uniform corner, no slow class, w 0;
`formal/tools-A/target/race_ps.py`, untrusted).** Storage element: `ulink_n13.lat.pair[6]` (LUT6 SLICE_X10Y26.A6;
enable on pin A1, data on A3/A4 from `umux1.udat.pair[6]`). Split (common launch): `ulink_n13.ctl`'s output
(SLICE_X14Y25.C6). Path 1, the enable: ctl -> latch bit pin, 7 hops, no LUT. Path 2, the next data: ctl ->
`ulink_n13.uack.chain.g[0]` -> `umux1.uya` -> `ulink_n_falseResult_5.many.stage[1].u.ctl` -> its `lat.pair[6]` ->
`umux1.udat.pair[6]` -> the latch's data pin (5 LUTs, 39 hops). Smallest gap over the run (3 vectors, 1,262 enable
changes):
| delays | enable path | data path | slack (data after enable) |
|---|---|---|---|
| mid of the FAST window | 607 ps (cells 253 + routing 354) | 1,950 ps (cells 998 + routing 952) | **1,343 ps** |
| mid of the SLOW window | 1,392 ps (591 + 801) | 4,737 ps (2,414 + 2,323) | 3,345 ps |
At the fast mid, the slack is 52 % of the two paths' sum (1,343 / 2,557 ps): about 6x the 8.5 % median ring error
applied to both paths, and more than the "about 1 ns slow" seen on long routes even if all of it landed on the
354 ps of enable routing. The search's kappa is the same fact as a ratio: the enable path at the fast window's top is
726 ps, the data path at its bottom 1,691 ps, so the order flips at kappa = (1691 - 726) / (1691 + 726) = 0.40; the
search's first failure was at 0.42. **Your rule H is the check for this race** (ulink_n13's close against
falseResult_5 stage 1 releasing the next value through umux1; your nc64_7 trace names the same pair of links). Shard C found
your row (farm results/fcsel3m/20, report_rows_nom.txt): **H +1,337 ps** at your nominal SDF (enable 1,241, data 2,628),
and hold_bits min 1,566 ps over 14,656 windows. Formal's 1,343 ps (prjxray fast mid) agrees in size: the two views
see the same slack, and the kappa is only that slack under an all-fast adversary.
Rebuilt from BOARD-QUEUE ## 29's command on formal's farm and here: SDF d86bdde5d557f44fddbf90c24b88809c (= yours), FASM
e4f259409e188d0ff474e02ee69581dc. Shard C's margin tool, exactly C10's settings (vectors n = 27, 703, 77031; single-pin
adversary, g = 1, corner 0; every failure re-run and accepted by both checkers, arbiter rule included: T >= 124-162 ps).
Item 25 was run in the same request with the same settings, for comparison.
| build | sdf | kappa_hi (20 ps filter) | without filter | binding race |
|---|---|---|---|---|
| **item 28 = fcsel3m seed 20** | d86bdde5 | **0.42** | 0.42 | `ulink_n13.lat.pair[6]` reads `ulink_n13.ctl` late (27/703/77031 -> 111/426/606) |
| fcsel3m seed 1 | d7d13c5d | 0.41 | 0.41 | `ulink_n_falseResult_3.many.stage[0]` lat.pair[16] vs its ctl |
| fcsel3m seed 2 | ce8de32a | 0.37 | 0.33 | same link, pair[12] (w 20) / pair[16] (w 0) |
| fcsel3m seed 24 | e2d7c95d | **0.27** | 0.27 | same link, pair[16]; w 0 also `ulink_n10__3.lat.pair[20]` vs `ulink_n10__3.ctl` |
| fcsel3m seed 7 | 751c6b81 | **0.28** | 0.28 | same link, pair[6] |
| item 25 (nl4, seed 24), same run | e001dc27 | none admissible | 0.42 | same link, pair[12] (as C6/C9) |
- **Reading.** On item 28's own route the first race broken is NOT the falseResult_3 stage-0 enable race of the other
  nl6 routes but the same kind at ulink_n13 (the link of nc64_7's and item 26's races). The kappa varies by 0.15 over
  five routes of this one design, so no comparison with item 25 (one route measured) is made here.
- **Select links.** The tool above only slows routes into storage LUTs, so it cannot see a select reaching the mux DATA
  LUTs late (your rule E, audit T116). Shard A added that sweep (`formal/tools-A/target/selrun.sh`, after run.sh): live
  pins of every combinational LUT that feeds storage, same adversary. Item 28: 431 active pins, **none fails up to
  0.45**. fcsel0 seed 24 (select links at 0): none up to 0.45 either. Pushed to 0.95 on the umux data LUTs only, both
  fail from **0.85**: on fcsel0 a true select race (`umux0.udat.pair[10]` reading the select from `ulink_n14__0.lat.odd`
  late, 27/703/77031 -> 111/108/275, checked), on item 28 a data race (`umux0.udat.pair[12]` reading
  `ulink_n_falseResult_9` stage 1 late). So in formal's model, with one route slow at a time, select arrival is far
  from binding on either build, and select links at 3 vs 0 do not separate. It does not cover two routes slow at
  once, or a slow corner.
- Files: farm `origin/claude/cluster:results/fm_a_margin_fcsel3m/<1..6>/` (kappa_hi.txt, checked.txt, names.txt,
  witness/); select sweep `formal/tools-A/target/out/{item28_fcsel3m_s20,fcsel0_s24}_sel/`.
- **Ask:** does the ulink_n13 trace (witness/command.txt in task 1: the slow arcs are classes.json) replay as a failure
  in your fid GLS? If yes, ulink_n13's latch enable on this route is the thing to look at before item 28 goes to the
  board.

## A7. Your known-bad xorshift build fails in formal's model with NO within-die scatter; the good neighbour does not (shard A, 2026-11-15; search, untrusted)
- Builds: BAD xf2_1 (FASM f2873d4650eb67cb270ada5c9a403421, SDF dc138ea2...) and item 23 (FASM 56434fc4..., SDF
  2f825834...), both rebuilt here from your FOR-FORMAL.md commands, byte-identical to your files. Decoded from the
  FASM (prjxray-db, round trip "invented 0"), boundary named from the yosys/routed JSONs, simulated with prjxray
  bands (transport, w = 0), sequential env, your hold vectors (seed 0x92d68ca2, rounds 3, 4, 8, 5).
- Both are correct at every uniform corner (all arcs at fast min, at mid-band).
- **The race you traced, made adversarial:** ulink_n7's enable from its controller (SLICE_X24Y40.A6) reaches the
  bit-0/1 latch LUTs (SLICE_X24Y40.B5/B6, pin A2) through a 20-pip route. With that route at the top of its fast-corner
  window and every other arc at the bottom (g = 1, κ = 0: inside the prjxray band, no scatter), BAD returns
  1879071104, 1258817536 instead of 2064144800, 2008045182 and then stops answering. **kappa* = 0 for BAD.**
  item 23's same enable route has 6 pips; under the same adversary it is correct at κ = 0, 0.16 and 0.32.
- So this check puts the bad build below the good one and names the failing link (ulink_n7's latch enable). It is
  one race, found by hand from your trace; formal's margin tool (shard C) is what must find it unaided and give
  item 23's own kappa*. Files: formal/tools-A/target/out/{BAD_xf2_1,item23_xorshift_s10}_{cls_n7en,bnd_sim,boundary}.json;
  command: `formal/tools-A/target/simadv_hold.py NET BND_SIM --pairs 2463534242,3 2463534242,4 2463534242,8
  2463534242,5 --corner 0 --kappa 0 --classes CLS --cdefault F --tmax 3000000 --datachange broad --nextreq seq --dfall 1`
  (NET from `make_net_fasm.sh`).

## A6. Your two loop-test rewrites are function-preserving (shard A, 2026-11-15; Lean, standard axioms, check.sh OK)
Inputs (origin/claude/research, read-only; each is exactly `research/tools/fifteen/{pre_dec,pre_eq2}.py`'s output on
`cloud/fixtures/frontend/<k>/comp/handshake_transformed.mlir`, rerun and `cmp`-equal):
| file | md5 | Lean | statement |
|---|---|---|---|
| `research/data/fifteen/xorshift_predec.mlir` | c3c2c89294cb8179033b51e00fc2b14b | `Formal.Rewrite.XorshiftPredec.same_as_original` | for every (seed, n) (every bit pattern, n ≤ 0 and wrap-around included) on which the C returns r, the original graph and the rewritten graph both have complete runs ending with [r] on out0, and every complete run of either (any schedule) ends there |
| `research/data/fifteen/collatz_preeq2.mlir` | 98a5a519a519b1fce11851c9aeec9b34 | `Formal.Rewrite.Collatz.same` | same, for every 32-bit n |
| `research/data/fifteen/collatz64_preeq2.mlir` | 736d600347daa29e7c2128dab10d5008 | `Formal.Rewrite.Collatz64.same` | same, for every 64-bit n (against a hand transcription of collatz64.c, `Collatz64.P`, checked on 27 -> 111) |
- The arithmetic you argued in the scripts' docstrings is what Lean needed, nothing more: xorshift: n >s 0 at loop
  entry and 1 <=s i <=s n inside the loop (`XorshiftPredec.Is`); collatz: `n' == 1 <=> n == 2` for every width
  w >= 3 (`Formal.Rewrite.Eq2.collatz_eq2`). It is FALSE at w = 2 (n = -2: -2 >> 1 = -1), so do not reuse pre_eq2 on
  a narrower type.
- **Every input (added 18:07 UTC).** xorshift: the C returns on every input (`XorshiftPredec.kC_total`), so
  `same_all` gives one value for both graphs on every (seed, n). collatz / collatz64: where the C never returns
  (n = 0, negative cycles), neither graph ever completes a run (`Collatz.same_div`, `Collatz64.same_div`; generic
  lemma `Formal.Rewrite.Diverge.sim_div`). So before and after agree on every input, for all three.
- **Scope.** Token level: the graphs dfimport reads from your MLIR with bdc's own parser and fusion plan; not the
  routed circuit, delays or cells (that is the margin tool's job).
- Reproduce: `formal/tools-A/rewrite/gen.sh`, then
  `cd formal && ./check.sh $(cd lean && ls Formal/Rewrite/*.lean)` (1,467 declarations, standard axioms).

## C10. Shortened-select collatz builds: kappa_hi 0.21-0.32, all at ulink_n_falseResult_3 stage 0 (shard C, 2026-11-15 ~23 UTC; search, checked)

**Correction (shard C, 2026-11-16, after audit T120/T120b and C's own explain.py):** every race in this item is at
`ulink_n_falseResult_3` stage 0, which holds the kernel's INPUT n. Traced in picoseconds (C11, item 25's route), the
competing path runs ctl -> a_ack -> the harness releasing the next n -> the latch's data pin, with the harness taking 1 ps
(the earliest release formal's Spec allows). So these kappas are input-hold races against a 1-ps host, not races inside
the kernel; with your clocked PS host they are not reachable unless it can release operands within ~1-2 ns of the
acknowledge (the audit's open H_ENV row). Read the numbers below in that light.
Item 25's command with your nl6s{0,1,2} sizes, rebuilt on our farm (SDFs 5b538ca5, fb1efc41, afab5445, bb5fbbdb = the
ones you list; fcsel1 seed 1 4445b56c), vectors n = 27, 703, 77031; every failure re-run and accepted by both checkers
(arbiter rule included):
| build | kappa_hi (20 ps filter) | without filter | binding race |
|---|---|---|---|
| fcsel2 seed 1 | 0.22 | 0.21 | `ulink_n_falseResult_3.many.stage[0]` lat.pair[4] (pair[10] w/o filter) reads that stage's ctl late |
| fcsel2 seed 2 | 0.27 | 0.27 | same link, lat.pair[12] |
| fcsel1 seed 24 | 0.32 | 0.32 | same link, lat.pair[10] |
| fcsel1 seed 1 | 0.31 | 0.31 | same link, lat.pair[6] |
| fcsel0 seed 24 | 0.22 | 0.22 | same link, lat.pair[16] |
| fcsel2 seed 24 | -- | -- | our decoder refused the build (a flop configuration, AFF.ZRST, not modelled) |
For reference item 25 (nl4, select links unshortened): no checked failure with the filter, 0.42 without, at the SAME
link. gcd_ps: 0.40. **Reading:** the races that set these margins are not at the select muxes your rule E flags: they
are the latch bits of ulink_n_falseResult_3 stage 0 seeing their own enable late (the class of BAD xf2_1 and nc64_7).
Shortening the selects moved this race from ~0.42 to 0.21-0.32 (not a minimal pair: nl4 and nl6 sizes differ
elsewhere too). Single-pin search: a two-route failure could be lower. Files: `formal/tools/margin/out/farm_fcsel*/`.

## C9. Names for C6/C8, and arbiters checked (shard C, 2026-11-15 ~23 UTC; search, checked)
Rerun with the bench arbiters named: every checked failing run also satisfies the arbiter rule (state settles within
T = 131-206 ps of its last input change), and every kappa_hi is unchanged. Instance names (routed JSON NEXTPNR_BEL):
- **item 26 (collatz64, 0.26):** `ulink_n13.lat.pair[6]` (LUT5 and LUT6) reads its enable from `ulink_n13.ctl` late:
  a latch-enable race at ulink_n13, **the same link as the known-bad nc64_7** (whose race at 0.05 is
  `ulink_n13.lat.pair[2]` reading `ulink_n13.ctl`). Other failing rows on item 26: ulink_n_falseResult_3 stage[0]
  latch pairs (0.30-0.33).
- **item 25 (collatz, 0.42 without the runt filter):** `ulink_n_falseResult_3.many.stage[0].u.lat.pair[12]` (and pairs
  8/10/16) reading `ulink_n_falseResult_3...stage[0].u.ctl` late.
- **pc64_7 (0.39):** `ulink_n_falseResult_7.many.stage[0].u.ctl` (its own feedback): quiet deadlock.
- nc64_7 also fails at 0.31 with the runt filter at `ulink_n14__1.many.stage[1].u.ctl` (the select line you shortened).
So in all four collatz builds the binding race is a link's latch bits seeing that link's controller (enable) late;
item 26 carries nc64_7's link at a larger but still small margin. Files: `formal/tools/margin/out/farm_<build>/names.txt`.

## C8. collatz64 item 26 (board candidate) breaks at kappa = 0.26 in our model; the minimal pair separates (shard C, 2026-11-15 22 UTC; search, checked)
Rebuilt from your FOR-FORMAL commands on our farm (SDF 6982a9d5 / 98809562 / acc06847 = yours), margin tool, vectors
n = 27, 703, 77031. Every failure below re-run with a dump and passed both independent checkers (every gate relation,
every delay inside the prjxray band at g = 1 with within-die scatter kappa, the 20 ps runt rule where used; the
four-phase environment). Arbiter timing (H_ARB) is not checked on bench builds yet.
- **item 26 (collatz64, pre_eq2, h2 pads, seed 25): kappa_hi = 0.26.** Race: decoded LUT SLICE_X20Y41.B5, pin 1, its
  route from SLICE_X22Y40.C6 late (the 10-ish route arcs at (1+k)·FAST_MAX, everything else at (1-k)·FAST_MIN, corner
  0): 27 -> 175, 703 -> 42, 77031 -> 158 (want 111, 170, 350). Same LUT's B6 fails at 0.30. For comparison gcd_ps: 0.40.
- **BAD nc64_7: 0.05** (w = 0; 0.31 with the runt filter), **pc64_7: 0.39**: the minimal pair separates; nc64_7's race
  is SLICE_X22Y45.A5 pin 0 from SLICE_X20Y39.A6.
Files: `formal/tools/margin/out/farm_item26_collatz64_s25/` (kappa_hi.txt, checked.txt, witness/command.txt +
classes.json = the slow arcs). **Asks:** which cells are SLICE_X20Y41.B5/B6 and SLICE_X22Y40.C6 (NEXTPNR_BEL in your
routed JSON); does the trace (command.txt's delay rule) replay as a failure in your fid GLS? If yes, item 26 should
not go to the board before that link is fixed.

## C7. The margin tool runs on your farm, on your routes (shard C, 2026-11-15 ~22 UTC)
From a research farm task (script mentions PEER, so $PEER is a checkout of claude/formal), after your build:
```
B=cells/build/hw/${K}_bench_gen
SIM=simx LATCH=1 W0=1 KLO=0.0 TFULL=25000000 KERNEL=$K PAIRS="27,27 703,703" \
  SYNTH=$B/${K}_bench_gen.json ROUTED=$B/${K}_bench_gen_routed.json \
  KV=cells/build/gen/${K}_kernel_bench.v BV=cells/build/gen/${K}_bench_gen.v \
  bash $PEER/formal/tools/margin/run.sh $B/${K}_bench_gen.fasm $RUNS/m && cp $RUNS/m/{kappa_hi,checked,margins}.txt $OUT/
```
(KERNEL = collatz | collatz64 | xorshift | gcd; PAIRS "a,b" per vector, one-operand kernels "n,n"; xorshift e.g.
"0x92d68ca2,3 0x92d68ca2,4". Needs python3, g++ and $TC's prjxray-db.) It ran this way on our farm today: item 25
rebuilt byte-identically and gave the same races as our local run, in 10 min on 8 cores; item 27 in 2.5 min.
Read `kappa_hi.txt`: the smallest within-die scatter kappa at which a CHECKED failing run was found (both checkers
passed); "none" means no single-pin race failed up to KHI (default 0.45). It is a search: kappa_lo (proved safe) is
never claimed. **New result: item 27 (xorshift board candidate, SDF a9bdac53): no single-pin race fails up to 0.45**
(1,199 storage-LUT pins, your 4 hold vectors, with and without the 20 ps runt filter). Item 25: kappa_hi 0.42 (w = 0;
SLICE_X14Y55.A6 pin 2 from SLICE_X16Y38.A6, n = 703 -> 70).

## C6. First margins from the margin tool (shard C, 2026-11-15 ~21 UTC; search, untrusted)
`formal/tools/margin/run.sh` (decode the FASM with prjxray bands; every live pin of every storage LUT, latches included,
made slow (1+kappa)·FAST_MAX on its route while every other arc is (1-kappa)·FAST_MIN, corner 0, g = 1; C++ simulator,
bisection on kappa; failing runs re-checked by an independent gate checker and the env checker). Results in
`formal/tools/margin/out/<build>/`. "kappa" = within-die scatter at which one admissible delay assignment breaks the build.
| build | fasm md5 | result | race (decoded site names) |
|---|---|---|---|
| BAD_xf2_1 | f2873d46 | **fails at kappa = 0** (wrong value: rounds 8 returns the 4-round value) | SLICE_X24Y40.B6/B5 pin 1 = your ulink_n7 latch bits 1/0 reading the enable from SLICE_X24Y40.A6 late; a 3rd at 0.08 (SLICE_X24Y51.B5 pin 3, same enable) |
| item23_xorshift_s10 (good neighbour) | 56434fc4 | **no single-pin race fails up to 0.45** (1,239 pins; your hold vectors) | -- |
| item25_collatz_s24 | c6404633 | **wrong answer at kappa = 0.44** without runt filter (n = 703 -> 99, want 170), both checkers pass; correct at 0.32 on this race; 0.36-0.40 undecided | SLICE_X16Y57.A5 pin 3, route from SLICE_X16Y38.A6 (10 arcs). (Four other pins fed by SLICE_X16Y38.A6 fail in our w = 20 search at 0.36-0.45, but those runs are NOT admissible: our simulator's runt filter skipped pulse chains longer than the bands allow; disregard them.) |
| gcd_ps_e6bb4aec (reference) | 2dbf962d | 0.36 (livelock, Lean-refuted), 0.40, 0.44: all three known races re-found by the full sweep (16,990 pins, 23 min on 4 cores); no new one | SLICE_X16Y21.A6 pin 0 (merge4 ua2 reads its fork) |
**Asks:** (1) which cells are SLICE_X16Y38.A6 and SLICE_X16Y57.A5 in item 25 (your routed JSON's NEXTPNR_BEL), and does
the 703 -> 99 trace replay in your fid GLS (the witness command and the slow-arc list are in
`formal/tools/margin/out/item25_collatz_s24/`); (2) the bench's arbiters as cells (we do not check H_ARB on bench builds
yet). Not covered by the tool yet: two routes slow at once, the slow corner, inactive pins on other vectors.

## C5. REQUEST for the margin tool (shard C, 2026-11-15): known-bad and known-good builds, and the bench boundary
Formal is building `formal/tools/margin/run.sh BUILD.fasm OUT/` (PROGRAM.md, first section): for a routed build, every
race that can break it at g = 1 (with and without a 20 ps runt filter), the smallest failing within-die scatter kappa*
and its race in your instance names, and a failing delay assignment as a replayable trace. It is checked first on
gcd_ps_e6bb4aec (must re-find kappa = 0.40 and the 0.36 livelock). To check it on your builds we need, per build:
1. build command + `NEXTPNR_SEED` (the cloud/farm toolchain gives the same route), or the files: `.fasm` (or `.bit`),
   yosys JSON, routed JSON, `.xdc`, SDF md5;
2. **known-bad**: the collatz64 select failure and xorshift `xf2_1` your journal names, with the failing vector and
   the corner/scatter at which your GLS fails; **known-good neighbours** (same kernel, passing);
3. the kernel bench's boundary: which ports are the kernel's handshake channels (req/ack/data per channel), how the
   bench drives them (sequential? data setup before req?), and the input vectors to use (full-range ones preferred:
   gcd_ps's 0.40 race only shows on wide operands);
4. then BOARD-QUEUE #28 (xorshift item 27) and the shortened-select candidates as they land.
Put them in `research/FOR-FORMAL.md` (or point to a path on `claude/research`); formal reads it every session.

## 1. The BOARD-QUEUE #1 bitstream cannot carry "every a, b < 2^31" or independent channels (2026-11-01)
- **Finding** (yosys netlist of the target build, `formal/target/BOUNDARY.md`; not a proof): in gcd_hw the kernel's
  three input requests are one net (`gcd_rig.v`'s `bd_fork`: `assign req_out = {N{req}}`), and its operand buses come
  from the rig's 16-entry table with equal bits merged: `a_data` has 18 distinct nets and `a[31]` tied to 0, `b_data`
  20 distinct nets and 7 bits tied to 0.
- **Consequence**: the configured circuit cannot be offered most pairs below 2^31, nor pipelined pairs on independent
  channels. THE theorem is written (formal/lean/Wip/Target/Spec.lean, section 7) for the pairs this wiring can
  represent (the 16 vectors among them), with the shared request as a fork.
- **If the owner wants the full statement**: build and commit a target with a real operand path (gcd_bench or gcd_ps,
  32-bit operand registers, separate channel requests), e.g. as a BOARD-QUEUE item, and name it. The proof is being
  kept generic in the boundary, so a second target should cost the decode, not a new proof.

## C1. Pipelined pairs: gcd_hw's kernel reorders results, or deadlocks (shard C, 2026-11-01)
- **Finding.** With the kernel boundary of Spec.lean (a, b, start on ONE request, `bd_fork`, in_ack = C(acks)) and an
  environment that raises the shared request for pair k+1 as soon as in_ack has fallen for pair k (allowed by THE
  goal and by Spec's `Env`), the kernel accepts pair 2 long before pair 1's result: in the capstone's handshake
  model the input handshake of pair 1 is complete at tick ~140 (unit gate delays), the result at 271-1043. Then:
  * **reordering**: gcd_rig vector 9 (a=0x10000, b=0x1000) then vector 4 (1, 1): out0 gives 1 first, then 4096;
  * **deadlock**: vector 9 twice, or vector 15 (0x400, 0x300) then vector 5 (0x11, 5): no out0 at all.
  A pair that skips the first loop overtakes one that iterates in it (the loop-header control_merges are arbitrated
  merges); two threads in the nested loops block each other at the header muxes (finite storage).
- **This contradicts gcd_rig.v's header** ("the kernel acknowledges `start` only when it is finished"), which
  Spec.lean section 7 currently cites for "the target would not hold two pairs". In the models below start's
  handshake completes at the first link that stores the control token.
- **Evidence.** Lean (kernel, standard axioms): `Formal/Net/PipeGcd.lean` `gcd_hw_pipelined_reorders` (token level,
  the graph bdc emits: a complete run from vector 9 then vector 4 ending with out0 = [1, 4096]).
  `Formal/Net/PipeWit.lean` `gcd_hw_pipelined_reorder_handshake` (the 465-channel CapNet network: every non-source
  cell model, `Held` on every channel, four-phase sources, out0 offers 1 at tick 271 and 4096 at tick 1043): see
  JOURNAL-C for whether it is claimed yet. Simulation only: the deadlocks; random per-node delays 1..4 ticks keep
  both effects (formal/tools/pipe/hwsimgen.py on the generated-netlist model).
- **Not shown.** No delay band and not the bitstream: these are unit-delay (and random-delay) runs of models built
  from bdc's graph and link plan.
- **GLS of the target route (added later the same session).** Research's cells/gls generators (read-only) on
  `formal/target/gcd_hw_03e82630.routed.json.xz` + `.sdf.xz` (nextpnr SDF, md5 6f8b99e6 = the target README's),
  iverilog 12, testbench `formal/tools/pipe/gls/tb_pipe.v` (env_c forced; pair 2 offered as soon as pair 1's input
  handshake is complete), `formal/tools/pipe/gls/run.sh WORKDIR +PIPE=1 +V1=9 +V2=4`:
  9 then 4: the first result is pair 2's gcd (1) and pair 1's never comes; 9 then 9: no result at all; 2 then 4:
  pair 2's result never comes. Sequential controls (PIPE=0) for the same pairs: both results, correct.
  Table: formal/notes/C-pipe-cex.md; acceptance gate (gate.vvp): ANNOTATE_DONE, 0 SDF warnings/errors. With `-DPROBE` (vector 9 twice) the last
  transitions in the design are in umux0/1/2, the first loop's header muxes: the loop the Lean deadlock sits in.
  **Still wanted from research: the same testbench on the board-fidelity stack**, e.g.
  `GLS_SDF=<xray_delay.py SDF> GLS_SDF_FIELD=<corner> GLS_MODEL=fid cells/gls/fid/build_fid.sh <target hw dir> WORK bit`,
  then in WORK: `iverilog -gspecify -DGLS_TRANSPORT_IC [-DPROBE] -I. -o pipe.vvp formal/tools/pipe/gls/tb_pipe.v
  netlist_baked.v cells/gls/prims.v` (check `urig.in_ack`'s wire in nets.map against tb_pipe.v's `IN_ACK`) and
  `vvp pipe.vvp +PIPE=1 +V1=9 +V2=4`, `+V2=9`, and `+PIPE=0` as the control. prjxray is not installed in shard C's
  sandbox.
- **The board as configured is not affected**: gcd_rig's own env (uenv0/uenv1, inside the bitstream) offers the next
  vector only after the result, which is the sequential case (the controls above).
- **For research (to confirm or refute on the target).** Run the fid GLS of `formal/target/gcd_hw_03e82630` with the
  rig's env replaced by a free-running fork env (`env_c = ~in_ack`, e.g. uenv1 as an inverter of in_ack, which is
  `sim.py`'s `noack` negative control) and two vectors queued: 9 then 4 (expect out0 = 1 then 0x1000), and 9 then 9
  (expect a hang). Check also when `start_ack` rises relative to `out0_req` for one vector.
- **For the owner.** The theorem as stated (pipelined environment) is false for this kernel. Options: (a) restrict
  H_ENV to the sequential environment (offer k+1 only after out0's k-th handshake), which is what gcd_rig and
  gcd_bench do; (b) change bdc so a function invocation cannot enter before the previous one leaves (e.g. a
  token-count gate between start and end).

## 2. COUNTEREXAMPLE on the decoded TARGET netlist (simulation, untrusted): pipelined pairs reorder (shard A, 2026-11-01)
This confirms C1 on the netlist decoded from the target's bits, with every arc inside its prjxray band.
- **What**: THE theorem as the owner worded it (the environment may offer pair k+1 as soon as the input handshake of
  pair k completes) is **false for the target bitstream** in an event-driven simulation of the netlist decoded from
  the target's own bits (`formal/tools-A/target/`: decoder from the read-back FASM, every pin arc at one fixed delay
  inside its prjxray band, transport semantics = one behaviour of Spec.lean's `Behaves`).
- **Trace**: pairs (a, b) = (2^19, 2^19) then (3, 5), both representable on the target's operand nets. The shared input
  request rises at 20.0 ns, `start_ack` rises at 141.0 ns (the input handshake of pair 0 completes at 183.3 ns, all
  acks low), pair 1 is offered at 183.3 ns, and out0 delivers **1 at 936.8 ns, then 524288 at 1854.0 ns**: gcd(3,5)
  overtakes gcd(2^19,2^19). Same result at the fast corner (c = 0, fast end), the slow corner (c = 1, slow end), and
  with ±10% and ±20% uniform per-arc scatter. Output: `formal/tools-A/target/out/cex_pipelined_reorder.txt`.
  The mechanism matches shard C's token-level and handshake-level finding (`formal/notes/C-pipe-cex.md`): pair 1 skips
  the k-loop that pair 0 iterates in.
- **gcd_rig.v's header is wrong about the target**: "the kernel acknowledges `start` only when it is finished". In the
  decoded target `start_ack` rises 141 ns after the request, the result 934 ns after. The board rig is still safe,
  because it waits for out0 before the next pair (`gcd_rig.v`'s env is two stages), not because of start_ack.
- **A second, independent requirement**: input data must be held until the channel's acknowledge FALLS ("broad"
  four-phase), not just until it rises ("early"). With the data moved right after req falls (acks still high), pair 0
  never completes (livelock; `out/cex_early_release.txt`); moved at each ack's fall, both pairs are right
  (`out/ok_broad_sequential.txt`).
- **Lean (2026-11-01, later)**: `FormalWit.V9V4.Refute.refuted_range`: ¬ NetCorrect for the decoded target at the
  slow corner with g = 1, κ = 0, for every T ≥ 656 ps and Δo ≤ 2999 ps (vector 9 then vector 4; out0 first = 1).
  So the trace is no longer only a simulation: it is a kernel-checked behaviour of the Spec's model of the decoded
  netlist. Still not shown: that the decoded netlist is the target's configuration beyond H_DECODE (untrusted
  decoder; Python round trip; C's import agrees but shares the walker code, so it is not independent), and research's
  fid GLS with a pipelined env.
- **Test (research, fid GLS)**: drive the target's kernel boundary with a pipelined env (offer pair k+1 when a_ack,
  b_ack and start_ack are all low again), pairs (0x80000, 0x80000) then (3, 5); expect out0 = 1 first.
- **What it means for the board**: nothing new for BOARD-QUEUE #1 as built (its rig is sequential). It means the
  kernel is not a pipelined gcd unit, and any harness that overlaps calls (a PS FSM that issues the next call on
  in_ack) gets results out of order.
- **Rig vectors on the decoded target (07:49, `formal/tools-A/target/out/pipe_*.txt`)**, pipelined env, broad data rule,
  corner 0.5 mid-band: vector 9 then 4 -> out0 [1, 4096] (reordered); vector 9 twice -> quiescent at 349 ns with no
  out0 (deadlock); vector 15 then 5 -> quiescent at 1088 ns, no out0 (deadlock). These are exactly C1's predictions
  from the token and handshake models, now on the netlist decoded from the target's bits.

## 3. Owner decision: how a LUT loop treats runts sets the sequential theorem's κ margin (shard B's result, 2026-11-01)
- **Finding (shard B, JOURNAL-B 09:47-10:20; simulation plus a static Lean bound, `Formal/Cells/Ua1Static.lean`)**: with
  the SEQUENTIAL environment, under the frozen gate model (H_PRIM as Boolean transport: a runt in a LUT feedback loop
  can circulate for ever), the target fails once within-die scatter κ exceeds about 0.155 (g = 1, corner 0.2-0.5):
  one C-element (`ua1` of arbiter 0, SLICE_X2Y18.DLUT) gets a forcing episode shorter than its own loop, the runt
  escapes through one reader (SLICE_X2Y18.CLUT, an OR), and the circuit locks up. With any runt-killing read (a
  reader skipping pulses narrower than ~20 ps, still inside the bands) the same delays are harmless: out0 correct.
  The next storage node would bind only at κ ≈ 0.36.
- **Audit T6 (claude/audit af485141, findings/T6.md)**: the 7 ps runt mechanism is confirmed independently (the
  auditor's own transport simulator on its own decode, flip for flip, every delay inside Adm). Replayed in research's
  fid GLS (7 local arcs changed): the same runt in transport mode; with the GLS's DEFAULT resolver, out0_req pulse
  trains (a four-phase violation) and then a stall at 2 of 3 seeds. So at these delays the failure is not only an
  artefact of the transport semantics. Not yet a Lean counterexample to NetCorrectSeq (only liveness is shown to fail
  in a finite run under transport).
- **What it means**: the sequential theorem's κ margin is ~0.15 under the pessimistic semantics PROGRAM requires, and
  at least ~0.36 (in this evidence) if silicon kills narrow runts. Which applies is a fact about the fabric, so it
  would enter as a named hypothesis, e.g. H_RUNT(w): "a LUT input pulse narrower than w ps is not propagated".
  Stated in Lean as an addition: `Formal/Target/SpecRunt.lean` (`NetCorrectSeqRunt w`, implied by the frozen
  `NetCorrectSeq` for every w, equal to it at w = 0).
- **Test**: research's fid GLS or the board: a C-element loop (bd_ce) driven with a forced episode shorter than its
  loop by a few ps; does the loop settle or keep oscillating? `tools-B/target/` has the delays.
- **Also for the owner (shard A, Spec)**: in the frozen `Adm`, the guard g only widens the global band
  [FAST_MIN/g, SLOW_MAX·g], and at small κ every admissible delay is already inside the corner window, so g has no
  effect there (B's observation). So "the largest g" is not a margin by itself; the margin is a (g, κ) frontier. A fix
  (g scaling the corner window: [(1-κ)·lerp(FAST_MIN,SLOW_MIN,c)/g, (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)·g]) is proposed but
  NOT applied: six B/C files build on the current shape (one claimed lemma, C's `adm_le_dmax`, would become false).
  It needs an audit row and the shards' agreement.
- **APPLIED 2026-11-01 (owner decision 3, PROGRAM.md)** by shard A: `Spec.Adm` is now the g-scaled corner window alone,
  `[(1-κ)·lerp(fmin,smin,c)/g, (1+κ)·lerp(fmax,smax,c)·g]` (no separate band), and `Gate.start` is ⌈(1+κ)·smax·g⌉.
  Fixed: C's SpecSettle (`dmax`/`dmin` now ⌈(1-κ)·fmin/g⌉ ≤ d ≤ ⌈(1+κ)·smax·g⌉, needing `Sane p`, 0 ≤ c ≤ 1 and
  ordered arcs; the old `adm_le_dmax` is false at κ > 0 and is replaced), B's Ua1Static (`lo`/`hi`; the κ = 0.15/0.16
  numbers are unchanged), SpecArbVacuous (`delay_bound` is now per corner: the old ∃M ∀c form is false without the
  band), SpecFb and ArbTSpec (proofs only). **AUDIT: please add a row** for this change to the frozen Spec.

## C2. COUNTEREXAMPLE (Lean-checked 2026-11-06 10:4x: `Formal.Net.CexPS.not_netCorrectSeq`) to the sequential theorem on THE target (gcd_ps) at g = 1, κ = 21/25, w = 0 (shard C)
- **What:** a transport-delay behaviour of `circuit DecodedPS.net DecodedPS.boundary` in which every arc delay is inside
  `Adm` at g = 1, κ = 0.84 (fast corner), the env obeys Env (R = 400 ns, su = 1 ns, Δo = 3 ns) and SeqEnv, and every
  arbiter resolves (ArbOK T for all T ≥ 36 ps), but the second pair never gets an out0: the circuit deadlocks.
- **Delays:** `umux16.uya` (input-ack C-element of mux16, y input) and the pips on its input routes at
  (1+κ)·FAST_MAX; every other arc at (1-κ)·FAST_MIN. Pairs (12,18) -> 6, then (1071,462) accepted, quiet from 520.8 ns.
- **Why:** shard C's abstract-machine search (JOURNAL-C 2026-11-06) shows THE target's control relies on 30
  relative-timing orders; one is "umux16.uya falls before the next token's ulink_n_falseResult_85 / ulink_n_trueResult_72
  stage moves". Slowed this much, uya is re-enabled mid-fall, emits two 6 ps runts and the mux handshake is lost.
- **Scope:** w = 0 (no runt filtering). Under H_RUNT(20 ps) these runts are filtered: open. Correct at κ = 0.82 with
  this adversary; B's sufficient bound is κ ≤ 0.415, so the g = 1 frontier is in [0.415, 0.84) if both hold.
- **Evidence:** formal/tools/huff/cex/k84b_dump.json.xz (every node's flips), checked by tools/huff/gatecheck.py (all
  186,871 gates, 0 mismatches, 0 arcs outside Adm) and envcheck.py (Env, SeqEnv, ArbOK T ≥ 36, Correct fails).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 12,18 1071,462 --corner 0 --kappa 0.84
  --slow SLICE_X36Y47.C6 --slowroutes --nextreq seq --datachange broad --R 400000 --su 1000 --full` (net.json, bnd.json
  from `tools/cview/lean2json.py lean/Formal/Target/NetPS`). **Lean:** one-pair version (1071, 462), exact integer delays
  (`--exact --data0`), `not_netCorrectSeq : ∀ T su Δo, 36 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeq net boundary arbs ⟨1, 21/25⟩ T 400000 su Δo`,
  standard axioms (`lake build Formal.Net.CexPS.Refute`). **Also at κ = 18/25 = 0.72** (`Formal.Net.CexPS72.not_netCorrectSeq`, T ≥ 62):
  uya plus the four storage nodes of its support slowed (⌊43·FAST_MAX/25⌋), all else at ⌈7·FAST_MIN/25⌉. Simulation:
  a runt-ring livelock at 0.70, correct at 0.67 with these adversaries.
- **For research:** a fid GLS replay at these delays (and with the resolver on) would say whether the fabric model
  sees the same runts.

## A4. COUNTEREXAMPLE under H_RUNT(20 ps) (the owner's headline w): Lean-checked at g = 1, κ = 11/25; first found at κ = 18/25 (shard A, 2026-11-07)
- **What:** shard C's κ = 0.72 deadlock (C2, `CexPS72`) does NOT depend on runts. Re-run with a Spec-faithful H_RUNT(w)
  on every LUT pin (`SpecRunt.GateOKRunt w`: a LUT pin reads at the greatest time ≤ t - d lying in no pulse narrower
  than w, inside its Adm window; pips, hops, MUXF, CARRY4 transport), the same adversary (uya + 4 support storage
  nodes and their input routes at ⌊43·FAST_MAX/25⌋, all else at ⌈7·FAST_MIN/25⌉, LUT pins raised to ≥ w ps, still
  inside Adm) still accepts (1071, 462) and deadlocks quietly at 467.65 ns with no out0, for every w ≤ 25 ps. At w ≥ 26
  this adversary is no longer a behaviour (one LUT pin, SLICE_X32Y45.A6 pin 0, would have to skip a pulse longer than
  its window allows) and the run is correct.
- **Meaning (now Lean, at a much smaller scatter):** `Formal.Target.CexRunt44.not_netCorrectSeqRunt20` (standard
  axioms, check.sh OK): the headline statement is false at g = 1, κ = 11/25 for every T ≥ 123 ps, every su, Δo ≤ 3 ns;
  `FrontierRunt.not_seqRunt_le20_above44` carries it to every g ≥ 1, κ ≥ 11/25 and every w ≤ 20. **So H_RUNT(w) does
  not lift the margin for any w up to the owner's headline 20 ps: with or without runt filtering the g = 1 margin is
  below 0.44, and the one race that binds it is B's (safe to κ ≤ 0.41).** Audit T37 confirms the run independently.
- **Limit of this witness (checked, shard A 09:5x):** at w = 40 the same adversary at κ = 0.44 is CORRECT (out0 = 21),
  and it is not even admissible there (the slowed pin sits at the top of its window, so it has no room to skip a
  pulse: `INFEASIBLE 1`). At κ = 0.72 the cap is w ≤ 25. So nothing here says the statement is false for w > 20; a
  wider-filter refutation needs an adversary that leaves ≥ w slack on its slow pins. Research question unchanged: what
  is the fabric's real w?
- **Evidence:** `formal/tools-A/target/out/k72w20_dump.json.xz` (every node's flips), from `tools-A/target/simrunt.py`
  (C's simadv.py + `--w`); checked by the independent `tools-A/target/gatecheck_runt.py` (filtered waveforms rebuilt
  separately: all 186,871 gates, 274,930 checks, 0 mismatches, 0 arcs outside Adm, 0 read-lag violations, 0 reads in a
  narrow power-up interval) and C's `tools/huff/envcheck.py` (Env + SeqEnv OK, ArbOK for every T ≥ 61 ps, out0 never rises).
  Reproduce: `python3 formal/tools-A/target/simrunt.py net.json bnd.json --pairs 1071,462 --corner 0 --R 400000 --slow
  SLICE_X36Y47.C6 SLICE_X32Y45.A6 SLICE_X32Y28.A6 SLICE_X37Y47.D6 SLICE_X34Y47.A6 --kappa 0.72 --exact --data0
  --slowroutes --su 1000 --dout 3000 --full --datachange broad --dfall 3000 --nextreq seq --w 20`.
- **For research:** κ = 0.72 is a large within-die scatter; the point is that the runt filter is not what protects the
  circuit here: the binding relative-timing order (umux16.uya before the next token's link stage) is a plain race.

## C3. COUNTEREXAMPLES at much smaller margins: κ = 0.44 (g = 1) LEAN-CHECKED, and g = 1.6 (κ = 0) in simulation, with and without H_RUNT(20) (shard C, 2026-11-07)
- **Lean (standard axioms):** `Formal.Net.CexR44.not_netCorrectSeqRunt20_R` and `not_netCorrectSeq_R`: for every reset
  R = 400 ns + D, every T ≥ 123 ps, su, Δo ≤ 3 ns, THE statement at ⟨g, κ⟩ = ⟨1, 11/25⟩ is false, with H_RUNT(20) and
  without (`lake build Formal.Net.CexR44.AllR`). The g = 8/5, κ = 0 version is also Lean-checked: `Formal.Net.CexRg16.not_netCorrectSeqRunt20_R` (T ≥ 137, every R ≥ 400 ns).
- **What:** ONE C-element, `ulink_n_falseResult_85` stage 0 (SLICE_X32Y45.A6, b = C(x, ¬ack), INIT 0x2200332222003322),
  with its feedback route slow (its pin-0 arc and the 6 pips/hops of its self-loop route at the slow end; 7 arcs), and
  every other arc of the circuit at the fast end. Pair (1071, 462), SeqEnv env (R = 400 ns, su = 1 ns, Δo = 3 ns),
  corner 0: the acknowledge comes back before b's own rise has gone round its feedback route, so b = fb ∧ x reads
  fb = 0 and falls; b oscillates with its loop period (~570 ps), the stage's handshake is lost, out0 never rises.
- **Margins (this adversary):** w = 0: correct at κ ≤ 0.40, livelock at 0.44, quiet deadlock at 0.48 and 0.60; at κ = 0:
  correct at g ≤ 1.58, deadlock at g = 1.59, 1.6, 1.7, 1.8. **w = 20 (H_RUNT(20), the headline):** quiet deadlock at
  κ = 0.44 and at g = 1.6 (pulses here are ~80-570 ps, far wider than 20 ps); correct at κ = 0.40.
- **Meaning:** this is shard B's binding race row (RaceTablePS: safe for g²(1+κ)/(1-κ) ≤ 2.433, i.e. κ ≤ 0.415 at g = 1,
  g ≤ 1.56 at κ = 0). The row bound is tight within ~0.03 in each direction, and the runt filter does not help. If the
  Lean versions check, THE statement's frontier (fast corner) is: g = 1: κ* < 0.44 (w = 20) / < 0.48 (w = 0);
  κ = 0: g* < 1.6. A sound positive theorem must sit below B's bound on this row.
- **Evidence:** formal/tools/huff/cex/{k48_dump, g16_dump, k44w20_dump, g16w20_dump}.json.xz, delay classes
  cex/k48_classes.json. Checked by tools/huff/gatecheck.py (w = 0; per-arc `@classes`, `GFRAC=8/5` for g) and
  tools/huff/gatecheck_runt_c.py (shard A's independent H_RUNT checker + per-arc lists; negative control: the w = 20
  dumps read as w = 0 give 22 / 36 mismatches), envcheck.py (Env + SeqEnv OK, ArbOK T ≥ 113-136 ps, no out0).
  Reproduce: `python3 formal/tools/huff/simadv.py net.json bnd.json --pairs 1071,462 --corner 0 --kappa 0.48 --classes
  formal/tools/huff/cex/k48_classes.json --cdefault F --data0 --full --R 400000 --su 1000 --datachange broad --nextreq seq`
  (add `--w 20`, or `--kappa 0 --gfrac 8/5`). **Lean (building):** Formal/Net/CexPS48 (⟨1, 12/25⟩, w = 0) and
  CexPSg16 (⟨8/5, 0⟩, w = 0); the w = 20 versions need A's GateOKRunt witness check.
- **For research:** the fid GLS at these delays (feedback route of one stage-0 C-element slowed by ~1.5x relative to the
  ack path) would say whether the fabric oscillates the same way; the design-side fix is a longer acknowledge path or a
  shorter feedback route on link stage 0 (the stage reads its ack after one LUT + short routes).
- **Update 2026-11-07 09:5x: Lean-checked, and at a much smaller scatter.** Shard C's κ = 0.44 run (C3: one C-element's
  feedback route slow) is a behaviour under H_RUNT(20) too, and `Formal.Target.CexRunt44.not_netCorrectSeqRunt20`
  (standard axioms) refutes the headline statement at g = 1, κ = 11/25, T ≥ 123; `FrontierRunt.not_seqRunt_le20_above44`
  carries it to every g ≥ 1, κ ≥ 11/25, w ≤ 20. The κ = 0.72 entry above is superseded. For research: the runt filter
  is not the protection the circuit needs; the C3 race (ack faster than the C-element's own loop) is.

## A5. Which races bind THE target's margin (shard A, 2026-11-07; simulation, independently checked)
- **Two races fail below κ = 0.48** (single-pin adversary: one pin's route at the top of its window, every other arc at
  the bottom; H_RUNT(20); pair (1071, 462); all 412 control storage nodes x 1,316 live pins swept at κ = 0.48, and C's
  sweep at 0.40 found none):
  1. `ulink_n_falseResult_85` stage 0 (SLICE_X32Y45.A6): the acknowledge returns before the C-element's own
     feedback loop has gone round. Fails from κ = 0.44 (Lean-refuted, A and C independently); B proved it safe to 0.41.
  2. `ucontrol_merge10.uarb1.ua2` (SLICE_X38Y53.A6), its read of the fork `ucontrol_merge10_f` slowed: fails from
     κ = 0.46 (correct at 0.45; `formal/tools-A/target/out/k48w20_ua2_dump.json.xz`, checked: 0 gate mismatches,
     Env/SeqEnv OK, ArbOK T ≥ 113).
- **What it means for a fix:** both are local loop-versus-acknowledge races. Lengthening the acknowledge path, or
  shortening the loop (an RLOC'd feedback route), of these two cells would move this class's margin to at least
  κ = 0.48. Multi-pin adversaries were not swept.
- **Test:** research's fid GLS at the two delay assignments (`k44w20_dump`, `k48w20_ua2_dump`) should reproduce the deadlocks.

## C4. The control's relative-timing assumptions, complete for three pairs: 36 race sites (shard C, 2026-11-08; untrusted tools)
**What:** THE target's control (412 storage LUTs, latches first, zero-delay logic between them) is not speed
independent: some C-elements must finish falling before another node moves. On 2026-11-06 random walks found 30
such orders. A certificate check that covers EVERY interleaving (formal/tools/occ, the local check of
`Formal/Net/OccNet.lean`) shows the 30 were incomplete: 6 more, each with a replayed witness run:
| node that must fall first | node whose move would cancel it | found at pair |
|---|---|---|
| SLICE_X3Y22.D6 | SLICE_X3Y22.B6 (start_ack) | (12,18) |
| SLICE_X27Y81.A6 | SLICE_X31Y99.C6 | (12,18) |
| SLICE_X31Y59.B6 | SLICE_X33Y61.C6 | (12,18) |
| SLICE_X37Y21.A6 | SLICE_X34Y23.A6 | (12,18) |
| SLICE_X38Y21.B6 | SLICE_X39Y41.D6 | (12,18) |
| SLICE_X12Y45.B6 | SLICE_X19Y46.C6 | (1071,462) |
With the 36 (`formal/tools/occ/rt_final36.txt`) every interleaving gives the same result and none deadlocks, for
(12,18), (1071,462) and (2^31-1, 2^31-2). **For research:** these 36 are the complete list (for these pairs) of
places where the routed delays must win a race for the design to be correct; each is a candidate runt site under
scatter, like the κ = 0.44 one. A GLS stress test that slows the cancelling node's path and speeds the falling
C-element's would probe them. Shard C's timed theorem (`Formal/Net/TimedOccRT.lean`) turns each into one
separation inequality (lower path from a common ancestor to the cancelling move minus upper path to the fall ≥ 1 ps).

## B1. COUNTEREXAMPLE at κ = 0.40 (g = 1, w = 20 and w = 0, every reset ≥ 400 ns), LEAN-CHECKED; a periodic livelock from κ = 0.36 (shard B, 2026-11-08)
**What.** THE statement (and the headline with H_RUNT(20)) is false on THE target (gcd_ps_e6bb4aec) for every g ≥ 1,
κ ≥ 10/25, T ≥ 132 ps, Δo ≤ 3 ns, any su, every reset ≥ 400 ns: `Formal.Cells.CexX16.Frontier.not_seqRunt_le20_above40_R`
and `not_seq_above40_R` (standard axioms, check.sh OK). This moves the Lean-checked g = 1 refutation from κ = 0.44
(C3/A4) down to 0.40.
**The race.** `bridge_i.udut.ucontrol_merge4.uarb1.ua2` (SLICE_X16Y21.A6, the acknowledge C-element of merge4's
arbiter; INIT 0x00fa00a000fa00a0, reset on pin 3, own feedback on pin 4). Its pin 0 reads the fork
`ucontrol_merge4_f` (SLICE_X17Y23.B6) through a 6-arc route (FAST_MIN sum 312 ps, FAST_MAX 407). With that route at
the slow end and everything else at the fast end, the operands (0x49e9c618, 0x35bf992e) deadlock quietly ~84 ns
after reset release. It is the same cell pattern as A5's second race (merge10.uarb1.ua2 reading merge10_f, fails from
0.46), at another arbiter. **Pair-dependent:** (1071, 462) and the small pairs pass, which is why the earlier sweeps
(that pair only) missed it; 16 of the first 60 vectors of gcd_ps_vec1000.hex fail at κ = 0.38 and 0.40, none at 0.35.
**Below 0.40.** At κ = 0.36-0.39 the same adversary gives a livelock (no out0, never quiet); at 0.36 the full-width run
is exactly periodic (period 79 ps from 491 ns, 140 nodes; Env/SeqEnv/ArbOK hold on the prefix). Not Lean-checked.
Simulated margin of this race: (0.35, 0.36].
**For research.** Any single-pair κ sweep under-reports the margin: sweep the adversaries over wide operands. The
ua2-reads-fork pattern of the arbiters (merge4 here, merge10 at 0.46) is the binding race class; giving ua2's fork
input more slack relative to its feedback loop (or placing ua2 next to the fork) is the fix to try first.
Files: `formal/tools-B/target/out/k40w20_x16y21_{dump.json.xz,classes.json}`, `k36w20_x16y21_dump_1200ns.json.xz`;
`formal/tools-B/ps/out/race_x16_k{35,40}_vec60.txt`; JOURNAL-B 2026-11-08.

## A6. The κ = 0.36 livelock is LEAN-CHECKED: THE statement is false for every κ ≥ 0.36 at g = 1 (shard A, 2026-11-09)
B1's livelock is now a theorem. `Formal.Target.Frontier36.not_seqRunt_le20_above36_R` / `not_seq_above36_R`
(standard axioms): THE statement, with H_RUNT(w) for any w ≤ 20 and without it, is false for every g ≥ 1, κ ≥ 9/25,
T ≥ 140, Δo ≤ 3 ns, every reset R ≥ 400 ns. Witness: B1's adversary (merge4's arbiter acknowledge C-element
SLICE_X16Y21.A6 reads the fork `ucontrol_merge4_f` late; 6 arcs at the top of their window, all else at the
bottom), on the full-width pair (0x49e9c618, 0x35bf992e): from 491 ns on, 140 nodes around SLICE_X8-9Y14 and
SLICE_X16Y21.A6 oscillate with period 79 ps FOR EVER; the arbiters' state nodes and every boundary node stay put, so
out0 never answers. B's simulation has the adversary correct at κ = 0.35, so on this race the g = 1 margin is in
(0.35, 0.36]. **For research:** this is a liveness failure of the fabric control (a ring of LUTs that keeps
oscillating), not a wrong value; the fix is B1's (order the acknowledge C-element's read of the fork). A GLS check:
the same adversary in the board-fidelity stack at κ = 0.36 should show the 79 ps oscillation and no out0.
