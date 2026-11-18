# ejoin: rule E's missing join credit at xorshift's loop steers (`BD_SKEW_E_JOIN=1`)

Subagent `ejoin` of research, 2026-11-17 23:55 - 2026-11-18 03:5x EST. nextpnr 9c732bc6303458df (`cells/verify/toolchain.sh`
OK, rc 0, at 00:21 EST before the loop's builds). Changed: `cells/verify/skew.py` (additions behind the flag),
`cells/verify/test_skew_walk.py` (one test), `research/tools/auto/auto_size.sh` (the flag passed through, default off).
Added: this file. cells/rtl, bdc, dynamatic, circt untouched.

**Headline.** (1) On the hand route (x55a10 seed 21, sdf 42b4fb4c) the eight negative rule-E rows at the loop steers
(ucond_br6-9, both LUTs; launch: i's link controller `ulink_n7f__1`) are a **missing credit, not a race**. The walk fires
ucmpi1's operand join on i's request alone; in a GLS of that route at the worst corner of the draw model (chains 0.20,
rest 0.31, CARRY4 / F7F8 / FF 1.0, no scatter; xor19 19/19 PASS, EQUIVALENT) **n's request is that join's last input in
3678 of 3678 firings: +1148 ps in the steady state, +3358 .. +3581 at each call's entry**, because both operand links
are started together by the compare's own acknowledge (3646 of 3678 rises) and n's link carries the recipe's
`ULINK_N11__1 = 3`. Settle gaps at the select pins **+1175 (br9) .. +1478 (br7) ps, 0 runts** (formal C48: 923) where rule
E says -382 .. -1189 (guarded; raw -98 .. -905). At the opposite corner (chains 0.31, rest 0.20, CARRY 0.20) n is again
last in 3678 of 3678 (+1116 ps; gaps 1827-2110), although there i's link is started by its own request in 3648 rises. The worst event is a 700-ps glitch of the loop test in an ordinary
iteration, not the exit. The hand recipe's UCMPI1 = 5 is in effect 5 + 3 elements on the compare's request.
(2) `BD_SKEW_E_JOIN=1` (rule E (6); opt-in, unset byte-identical): a positive C-element on the request path is credited
with its other inputs, case by case on what made the launch fire (a request into it, or the acknowledge that released
it), with joinaware's path rules (no latch, no steer, entry pins by polarity). Sound in every interleaving -- and
therefore it credits only the acknowledge case: when i's link is started by its REQUEST after the release, nothing
within one crossing (or three: `BD_SKEW_E_JOIN_DEPTH=3`, through the control token) bounds n, so br7-9 keep their rows.
On the hand route it raises br6 only (0.20 -929 -> +119, 0.31 -1189 -> -182); every negative control stays flagged
(UCMPI1 at 1, +3 / +8 ns on the compare's carry or its select wires, the mux select controls); in the GLS, +3 ns on the
carry fails the gate (14/19, runts at the very race above).
(3) **The brief's premise does not hold on the automatic flow's routes.** There ULINK_N11__1 = 0: the flag changes no E
row on su_xorshift_1_4 or se_xorshift_ss_5, and the row that pins UCMPI1 near 10-11 (se_xorshift_ss_5's br8, -267 /
-527) is a thin REAL margin: the same GLS on that route gives **404 ps** at br8 (n trails i by only 189 ps; a 70-ps
glitch of the loop test reaches br8's select 404 ps before its request), against 1070-1895 at the other steers. Rule E's
pessimism there is 189 (n) + 440 (static longest select) ps. Raising UCMPI1 by 2-3 elements buys what the hand recipe's
3 elements on n's link buy on its route (~1.1 ns).
(4) The automatic loop with the flag (suite_one.sh xorshift 1 4 4): section 6.

## 1. The races (hand route bq_x55a10_21, rule E as the auto flow runs it)

corner_audit's worker (guards 0.97 / 1.03, `BD_SKEW_AND_JOIN=1 BD_SKEW_STEER_SELF=1`), corner SDFs as `auto_size.sh`
rule() builds them (chains 0.20, CARRY4 / F7F8 / FF 1.0, rest 0.20 or 0.31; byte-identical to steerE's). Every negative
row has the same launch, `ulink_n7f__1.ctl.u.u/O6` (i's link into ucmpi1; its latch is the compare's operand), and the
same shape, `cells/verify` walk replayed (`work/diag_join.py`):

| | path (storage crossed) | 0.20 | 0.31 |
|---|---|---|---|
| select (latest) | i's C node -> enable net -> `ulink_n7f__1.lat.pair[2]` (1023 ps) -> ucmpi1's CARRY4 slice[0] CO3 (2742) -> slice[1] CO3 -> `ucmpi1.uz_n41` (3902) -> steer select pin | br6 4684, br7 4317, br8 4746, br9 4533 | 5200, 4790, 5243, 5035 |
| request (earliest) | i's C node -> `ucmpi1.ujoin` [1] (686 ps) -> UCMPI1's 5 elements -> `ucond_brK_j` [2] -> steer request pin | br6 4016, br7 4366, br8 4605, br9 4315 | 4295, 4692, 4969, 4634 |
| guarded | | **-929, -211, -421, -483** | **-1189, -382, -580, -691** |

The two positive C-elements on the request path, and what the walk does not see (AND seeding: only inputs the launch
reaches at the level count):

| C-element | input the walk takes | input it does not reach (driver) | reached from i's C node at all? |
|---|---|---|---|
| `ucmpi1.ujoin` (bd_c2) | A2, i's request (625 ps) | **A3, n's request** (`ulink_n11__1.rdly.chain.g[2]`: ULINK_N11__1 = 3) | only by a lap, level 3 (5883 ps) |
| `ucond_br6_j` | A5, the compare's request | A1, the counter's request (`uaddi0.udly.chain.g[11]`, UADDI0 12) | lap, level 2 (9191) |
| `ucond_br7_j` | A1, the compare's request | A2, x's request (`uxori2.udly.chain.g[2]`) | lap, level 3 |
| `ucond_br8_j` | A1, the compare's request | A5, n's steered token (`ulink_n11__0_folink.rdly.chain.g[2]`) | lap, level 2 |
| `ucond_br9_j` | A1, the compare's request | A2, the control token (`ucontrol_merge0_rlink.rdly.chain.g[2]`) | lap, level 3 |

So each row is the race "i's latch opens, the compare's result reaches the steer through the carry chain; the request
reaches the steer through i's request, ucmpi1's join fired by i alone, UCMPI1's line and the steer's join fired by the
compare alone". It is a real race only if n's request (and, at each steer, the steered token's) can arrive at those joins
no later than i's own.

## 2. The GLS at the worst corner: which input fires each join

`work/gls_corner.sh` (fullstack_dump.sh's stack with the corner as arguments: bits-decoded netlist, prjxray SDF, fid,
chains 0.20, rest 0.31, CARRY4 / F7F8 / FF / RAMB 1.0, no scatter, every top-level net dumped; the `w*` nets are the
ICBUF copies at each cell input pin, so a pin's wire is that pin's arrival, interconnect included), xor19 (expected values
from `kernel_oracle.sh xorshift`, = xor19.exp): **PASS 19/19, 5450 cycles, EQUIVALENT**. `work/trace_steers.py` reads
every request rise at the steers' request pins, the select's last change at the select pin before it, and the joins'
inputs (`work/trace_hand.txt`):

| steer (both LUTs equal) | request rises | min settle gap, ps (all / select changed since the last rise) | runts | steer join's last input: compare / steered token | ucmpi1 join's last input: i / n | n - i at ucmpi1's join |
|---|---|---|---|---|---|---|
| ucond_br6 | 3678 | 1412 / 1412 (89) | 0 | 62 / 3616 | 0 / 3678 | min 1148, median 1148 |
| ucond_br7 | 3678 | 1478 / 1478 | 0 | 3648 / 30 | 0 / 3678 | 1148 |
| ucond_br8 | 3678 | 1302 / 1302 | 0 | 3678 / 0 | 0 / 3678 | 1148 |
| ucond_br9 | 3678 | **1175** / 1175 | 0 | 3678 / 0 | 0 / 3678 | 1148 |

Split by what started the links (`work/timeline.py`: the last of req_in rising / c_next falling before each controller
rise): i's and n's controllers are started by the compare's acknowledge (c_next, `ufork9`'s C-tree) in 3646 of 3678 rises,
by their request in 32 (the calls' entries). Select-changing rises per steer: 58 in the steady state (n's controller
62 ps after i's; n's request 1148 ps after i's: its 3-element rdly), 31 at entry (n's controller 2272-2495 ps after i's,
n' through the decrement; n's request 3358-3581 ps after i's). In the steady state the request reaches the steer
5443-6327 ps after i's controller (rule E's earliest: 4295-4969 at this corner) and the select settles 2918-4815 ps after
it (rule E's latest: 4790-5243). The worst race, br9 at t = 103.667 us:

| ps after i's link starts | event |
|---|---|
| -705 / -196 | n's / i's req_in (umux2's / umux0's output) |
| -69 / -7 | the compare's acknowledge falls at i's / n's c_next (the release) |
| 0 / +62 | i's / n's C node |
| +706 / **+1854** | i's / n's request at ucmpi1's join -- the join fires at +1923 |
| +3183 .. +3888 | the compare's output glitches 1 -> 0 -> 1 (carry), +4607 at br9's select pin (last change) |
| +5283 / +5352 | the compare's request at br9's join / the join |
| +5782 | br9's request pin: **gap 1175 ps** |

The race that sets the minimum is not the loop's exit: at br9 the 58 steady-state select-changing rises are 30 exits
(select 1 -> 0, gap >= 2060 ps) and 28 ordinary iterations in which the compare's output GLITCHES (1 -> 0 -> 1 while i
moves to i + 1: ~700 ps wide here; the compare is `~(i > n' | i == n')`, `bdc_fused_ucmpi1`) and settles back 1175 ps
before the request; the 31 call entries (select 0 -> 1) keep >= 1916. A request inside such a pulse would take the exit
branch with i < n' -- so the glitch, not only the final value, is what the request must wait for, and rule E's longest
select path (which a glitch can take) is the right thing to bound. Rule E's row from i's controller differs from this
event by the 1148 ps of n's request (the request side) and by 428 ps of select (the static longest path through the
carry, 5035, against 4607 here). Formal C48 on this route, same corner:
923 ps at ucmpi1's steers, no runts; formal's model and vectors (xorlong) differ, the sign and size agree.

**The opposite corner** (chains 0.31, rest 0.20, CARRY4 / F7F8 / FF 0.20; `work/trace_hand2.txt`): PASS 19/19, 5638
cycles; n again the join's last input in 3678 of 3678 (+1116 ps); gaps br9 1827, br8 1904, br7 2094, br6 2110, 0 runts.
But here **i's link is started by its REQUEST in 3648 of 3678 rises** (umux0's output 241 ps after the compare's
acknowledge released it), while n's link is still started by the release (3646) -- the case the static credit cannot
bound occurs in the steady state, and n is still later, because the release came only 241 ps before umux0's output and
n's request carries its 3 elements from the release.

**So the rows stand for a missing credit, not a race**, and the credit is n's request at ucmpi1's join: in every firing of
both runs the compare's request was set by n. (At br6 the steered token, uaddi0's request, is later still: 3616 of 3678.)
What bounds it in the request case is how late umux0's next output can come after the compare's acknowledge released
i's link (241 ps at this corner; at the other, the release was last) -- a separation over the loop, not a walk.

## 3. The change (`BD_SKEW_E_JOIN=1` or `--e-join`; `BD_SKEW_E_JOIN_DEPTH`, default 1)

`cells/verify/skew.py` (6), `e_join_credit()`, `e_join_chains()`, and a `floor` / `fhit` argument of `walk()` (None
everywhere else). For a launch X that is a handshake node (a link controller, a C-tree, a mux join -- a latch output is
left to (5)), the request is checked case by case on what made X fire:

- the causes of X (`ej_causes`): every handshake node L driving one of X's inputs through combinational logic only, as
  `fwd` (a request: a link controller's req_in, any input of a C-tree, a mux join's request pins) or `ack` (the
  acknowledge on a link controller's c_next, whose FALL releases it); latch outputs (data), constants and reset are not
  causes. With `BD_SKEW_E_JOIN_DEPTH` > 1 a `fwd` cause's own causes are followed back (l summed); an `ack` cause ends
  its chain.
- in the case "L fired X", t_X <= t_L + l(L -> X), and L's same transition reaches an input ip of a positive C-element J
  no earlier than t_L + s(L -> ip) along a path that carries it as a request (`e_join_credit`, Dijkstra over (pin,
  crossings)). A path counts only if every element on it NEEDS the incoming transition for its own firing in this token,
  so that each admitted path alone is a lower bound: it crosses C-trees (any input), link controllers by req_in, and mux
  joins by ctl_req only (both joins need it; by x_req / y_req the other join can fire the mux without it); for an `ack`
  L its first crossing must be a link controller entered by c_next (released by the same fall, as X was) and only pins
  past it count; it never crosses a latch (data), X, a steer (a token past a steer is another branch or the next
  iteration: no laps), a bd_merge's request OR (either input raises it), or the gate being checked; at most K = 6
  crossings. Every such floor
  `J >= s(L -> ip) + arc(ip -> J) - l(L -> X)` enters X's request walk at once (`walk(floor=...)`: J's AND seed is
  max(reached inputs, floor)).
- the row is the WORST over the cases; a case whose request path takes no floor is the walk without the flag, so the
  flag moves a row only when every way X can have fired bounds the request later. Where a floor sets the request, the
  race is from L (request through the credited input, select through X): divergence point -l(L -> X), both legs guarded
  from L (as (5)), and a case's margin is never taken below the unflagged row (that walk's bound holds in every case).

Why it is a lower bound: X (a C-element or a link controller) rises after its last enabling transition; whichever input
that was, its source L satisfies t_X <= t_L + l(L -> X). The credit paths carry L's transition with the polarity a
request needs (a request rising into C-trees / mux joins / req_in; an acknowledge falling into c_next, which starts a
controller) through elements that each fire only after that input, so every admitted path is ON ITS OWN a lower bound
on t_ip - t_L for the token X belongs to (no steer crossed: no next iteration); the shortest of them is one too, and which
paths are left out changes how tight the floor is, not whether it holds. (The first version of this
code, which the loop's iterations 0-3 ran, also let a path enter a mux join by x_req / y_req; on every route here it
credited exactly the same rows -- the flag raised nothing in those iterations -- and the corrected version reproduces
every number of sections 3-4.) The min over the cases covers every interleaving, back-pressure included (the
`ack` case), as joinaware's credit (min over forward ancestors and acknowledge sources) does for A'j; the difference is
that the cases are kept apart (each case may credit a different join), where joinaware takes the min per sibling.

What it credits on the hand route (0.20, from i's controller; e = request at the pin, rows under corner_audit's guards):

| steer | case: umux0's join `uj0` / `uj1` fired i's link (a request) | case: the compare's acknowledge released it | worst case | unflagged |
|---|---|---|---|---|
| ucond_br6 | e 6247: uaddi0's request at br6's join (+2231), **+1128 / +1134** | e 5185: n's request at ucmpi1's join (+1169), **+178** | +178 (then n's launch binds the gate: +119) | -929 |
| ucond_br9 | no floor on the request's path | e 5484 (+1169), +624 | -483 (no case floor) | -483 |
| ucond_br7, br8 | no floor | n's credit, positive | unchanged | -211, -421 |

In the acknowledge case the credit is not merely a bound, it is the trace: at 0.31 (the GLS's corner) it puts the request
at br9 5782 ps after i's controller and at br6 5443 ps -- the GLS's steady-state arrivals to the picosecond (5782; 5443 =
br6's minimum). What it cannot do is exclude the other case.

`BD_SKEW_E_JOIN_DEPTH` 2, 3, 4: the same rows. At depth 3 (`BD_SKEW_E_JOIN_DEBUG` prints every case) the request cases of
br8 split into 8 chains: through the control token (`ucontrol_merge0_olink` -> `ulink_n12__0` -> umux0's join) n is
credited +1442 ps (n's control link `ulink_n12__2` and its request link are slower); through the counter's own data token
(`ulink_n_trueResult_6`'s pipe -> umux0's join), the entry path (`ulink_n6`), or the control link started by its
acknowledge (`uforkdec0`'s C-tree), nothing bounds n -- those chains go back into the previous iteration through the loop
steers, which a credit path may not cross. In the trace those cases do not occur in the steady state (the acknowledge
starts both links), and at the entries n is later by 2.3-2.5 ns; but nothing static here shows that they cannot.

## 4. Checks

**Byte-identical when unset.** `skew.py -v` (BD_SKEW_AND_JOIN=1) on the hand route's 0.20 corner SDF, HEAD's
cells/verify (git archive) against this one: identical below the SDF path line, for every version of the change (the
first, the refactor into module-level functions, the final one); with the flag, depth 1 and 3, the three versions give
identical output on the hand route, and identical E rows on both AUTO routes at both corners; with
`BD_SKEW_E_JOIN_DEBUG` set, stdout identical (the diagnosis goes to stderr). `auto_size.sh`: the flag is passed as
`BD_SKEW_E_JOIN=${BD_SKEW_E_JOIN:-}` (empty when unset = off); checked in /proc that the loop's corner_audit and its
workers carry it.

**Unit test.** `test_skew_walk.py::test_e_join_credit_and_cases`: a request cause credits the sibling through its req_in
(330), an acknowledge cause through its c_next (250); a request cause may not enter by c_next nor an acknowledge by
req_in; nothing past X; a latch never carries a credit (with it unblocked the 1-ps data arc would win); the chains (an
acknowledge ends one, depth 2 follows a request back, no cause = one empty case); the floor enters the walk at J only,
keeps J's predecessor, and a floor below the reached input changes nothing. 34 / 34 with test_rule_a_links.py and
test_resize.py.

**Negative controls** (hand route, rule E rows, corner_audit's worker; "< 0 / 24" and the loop steers br6 / br7 / br8 /
br9, mux joins where they move; unflagged | flag depth 1 = depth 3):

| defect | 0.20 | 0.31 |
|---|---|---|
| none | 8: -929 / -211 / -421 / -483 \| 6: **+119** / -211 / -421 / -483 | 8: -1189 / -382 / -580 / -691 \| 8: **-182** / -382 / -580 / -691 |
| UCMPI1 at 1 (its chain x 0.2) | 8: -2232 / -1515 / -1725 / -1787 \| 8: -1184 / same | 8: -2493 .. -1686 \| 8: -1486 / same |
| +3 ns on the compare's carry (slice[0] CO3 -> slice[1] CIN) | 8: -4019 / -3301 / -3511 / -3573 \| 8: -2970 / same | 8: -4279 .. \| 8: -3272 / same |
| +8 ns on the compare's carry | 8: -9169 .. -8451 \| 8: -8120 / same | 8: -9429 .. \| 8: -8422 / same |
| +3 ns on uz_n41 -> the four steers' select pins | 8: as +3 ns carry | 8: as +3 ns carry |
| +8 ns on uz_n41 -> the steers | 8: as +8 ns carry | 8: as +8 ns carry |
| +3 ns on every mux select arc into uj0 / uj1 (selneg) | 16: umux0-3 -2293 / -436 / -1885 / -2333 \| 14: the same mux rows | 16 \| 16: same mux rows |
| select links at 0 (ULINK_N12__0/1/2, ULINK_N_INDEX_15 rdly x 0) | 11: umux0 -39, umux3 -1 \| 9: same mux rows | 12: umux0 -101, umux3 -30 \| 12 |

**The same race in the GLS, made late** (the dynamic control: a check earns its place by failing). The hand route with
+3000 ps on ucmpi1's carry slice[0] CO3 -> slice[1] CIN (`sdf_inject.py` on xray.sdf; checked in netlist_baked.v: the
ICBUF on slice[1]'s CIN 0 -> 3000 ps), same corner and stack: **FAIL 14/19** (5 calls -- rounds 1000, 3, 5, 17, 100 --
with their two runs disagreeing, mism_st bit 0; odata of the last run right; EQUIVALENT), and 8 request rises per loop
steer with the select moving under the high request (runts; 0 on the clean route), among them the clean route's worst
race (br9 at t = 103.667 us, 1175 ps there). So the harness sees this race, and rule E flags this defect with or without
the flag (-2970 .. -3781).

Every control stays flagged with the flag, at both corners; the mux rows are identical (mux joins' launches are the
select links' controllers, whose causes credit nothing there); the flag moves only br6's rows, by the credit (n's
request, ~1 ns), and every defect larger than the real margin (GLS: br6 1412 ps) keeps br6 negative.

**AUTO routes** (`--e-join` depth 1 and 3, E rows, both corners): su_xorshift_1_4 (UCMPI1 18; t2_0.20 / t2_0.31's corner
SDFs): no negative E row, every row identical with and without the flag. se_xorshift_ss_5 (UCMPI1 8, steerE's build):
5 < 0 at both corners, identical rows (br8 -267 / -527 from i's controller; umux0 / umux3 joins) with and without. There
ULINK_N11__1 = 0: n's request is not later than i's by a line, so even the acknowledge case credits little, and the
request cases credit nothing at br8. skew.py's own count on these routes and on steerE's collatz / collatz64 AUTO routes
(su_*_1_4, both corners): "0 raised by a join credit in every case" everywhere (40 / 24 handshake launches split); the
hand route: 2 raised (br6's two LUTs) at 0.20.

## 5. The AUTO route at the same corner (se_xorshift_ss_5, UCMPI1 8, ULINK_N11__1 0)

The brief's premise was that this missing credit binds UCMPI1 in the automatic loop (the flagged proposal pins it near
10-11 on se_xorshift_ss_5, rule E at ucond_br8 -267 / -527 from i's controller). Same GLS, steerE's route (sdf 24f4dfb4,
bits 8fe0aba6): **PASS 19/19, 5516 cycles, EQUIVALENT** (`work/trace_ss5.txt`, pins from the route's own rows: br8 request
A4 / select A1; ucmpi1's join i A3 / n A1):

| steer | min settle gap, ps | runts | steer join's last input | ucmpi1 join's last input | n - i there |
|---|---|---|---|---|---|
| ucond_br6 | 1070 | 0 | compare 3678 / 3678 | n 3678 / 3678 | 189 |
| ucond_br7 | 1895 | 0 | compare | n | 189 |
| **ucond_br8** | **404** | 0 | compare | n | 189 |
| ucond_br9 | 1192 | 0 | compare | n | 189 |

Here n's link has no request delay: n's controller fires 87 ps BEFORE i's (both started by the compare's acknowledge in
3646 / 3678 rises, as on the hand route) and its request reaches the join 189 ps after i's (routing). The worst race
(t = 52.194 us; `work/timeline_ss5_404.txt`): i's controller at 0, n's request at the join +514, the join +583, the
compare's output glitches 1 -> 0 -> 1 at +3750 / +3820 (70 ps; i -> i + 1 in an ordinary iteration), +4646 / +4716 at
br8's select pin (896 ps of wire from uz_n41), the compare's request at br8's join +4813, br8's request pin +5120: **404 ps**.
Rule E at this corner (0.31): request 4931 (the actual 5120 minus n's 189), select 5156 (the actual glitch 4716: 440 ps
of static longest path), raw -225, guarded -527.

So on the AUTO route the row that binds UCMPI1 is NOT a missing join credit (the credit is 189 ps): it is a thin real
margin -- 404 ps at the worst corner of the draw model, no within-die scatter, from a 70-ps glitch of the loop test in
an ordinary iteration that a request inside it would turn into a premature exit. Rule E's pessimism there is
189 (n) + 440 (select) = 629 ps against a margin of the size of its guard. Raising UCMPI1 by 2-3 elements, as the loop
proposes, buys the same ~1.1 ns that the hand recipe's 3 elements on n's link buy on its route (1175 / 1302 ps at br9 /
br8). The hand recipe's "UCMPI1 = 5" is 5 + 3 elements on the compare's request in the steady state, not 5.

## 6. The automatic loop with the flag (suite_one.sh xorshift 1 4 4, BD_SKEW_E_JOIN=1, CA_JOBS=2, PNR_TIMEOUT=3600)

Flow v5 (auto_size.sh at HEAD: AUTO_START_SCALE 0.3, `BD_SKEW_STEER_SELF=1 CA_JOINAWARE=1 BD_SKEW_AND_JOIN=1
CA_SIZERULE=1`, two corners) plus `BD_SKEW_E_JOIN=1` (depth 1), seed 1, RUNS under this subagent, started 00:23 EST
(05:23 UTC) at head bf2e6ca48; the rule steps import the working tree's skew.py (the first version for iterations 0-3,
the final one from iteration 4; /proc showed the flag in every corner_audit worker). In every iteration, at both corners,
skew.log reads "0 raised by a join credit in every case, binding at 0 gate(s)": **the flag credits nothing anywhere on
the loop's routes**, so this is the v5 loop itself. A/B on the same routes (the rule re-run without the flag, CA_JOBS=1):
iterations 0 and 1 compared (then stopped, for the core budget): per-corner sizes.vh and negative_sized.tsv identical
at both corners in both iterations, the merged proposal identical; report.txt identical in iteration 1, and in iteration
0 different only in two rows' sensitivity to UCMPI1 (-2363 / -2325 with the flag against -2596 / -2595: with UCMPI1's
line zeroed, the credit binds) and in tie order -- the proposals did not move.

| it | route (sdf) | sizes in (UCMPI0 / UCMPI1 / UADDI0) | rule on it: negative rows, raised / lowered | e-join raised |
|---|---|---|---|---|
| 0 | 99577d83 | 9 / 9 / 8 (estimates x 0.3) | 1 negative; proposal 167 -> 71 / 75 links | 0 / 0 |
| 1 | e73357ba | 6 / 8 / 1 | 44 negative; raised 10 (UCMPI1 8 -> 13, ULINK_N12__0 1 -> 6, ...), lowered 3 | 0 / 0 |
| 2 | f2d9a305 | 7 / 13 / 1 | 6; raised 3, lowered 2 | 0 / 0 |
| 3 | 2da3f025 | 7 / 13 / 1 | 14; raised 6 (UCMPI0 7 -> 8, UMUX0 3 -> 6, ...), lowered 1 | 0 / 0 |
| 4 | 47c9b0f1 | 8 / 13 / 1 | 7 (A'j uaddidec0 -1028 / -1090, A'm umux1, H, E umux3.uj1 -5); raised 4 (UADDIDEC0 3 -> 10, ...) | 0 / 0 |
| 5 (phase 2, raise-only) | 2304c4e0 | 8 / 13 / 1 (UADDIDEC0 11, UMUX0 6, UMUX2 4; 67 lines, 123 elements) | **0 negative: CLEAN** | 0 / 0 |

**Result: CLEAN at iteration 5** (phase 2, raise-only, after iteration 4 was not clean at MAXIT 4): route su_xorshift_1_5,
sdf 2304c4e0, full stack (lane2_run.sh) **P = 22672 ps**, odata cd3132bf, EQUIVALENT, ffmux-clean; 67 lines, 123 delay
elements; UCMPI1 13 (pinned since iteration 1, when the it-1 route -- built at it 0's proposal, 71-75 links -- had 44
negative rows and the rule raised it 8 -> 13). On that final route rule E at the loop steers is +1993 .. +2719 ps
(guarded, both corners) and the rule's own proposal would take the kernel 123 -> 75 / 80 links (UCMPI1 13 -> 8), but
phase 2 stops at the first clean route. For comparison: the v4 loop's route (su_xorshift_1_4, UCMPI1 18) 21084 ps; steerE's
one ratchet step with the steer self-bound (UCMPI1 8) 16620; the hand recipe ~16.5-16.8 ns. The flag had no part in
any of it. Draws (suite_one.sh, bench_gate.sh draw:K, K = 10101-10104, xor19, expected values from the C at run time):
PENDING_DRAWS

## 7. What this does NOT show

- **It does not make rule E agree with the simulation at br7-9 on the hand route**, nor at br6 at 0.31 (n's launch then
  binds: -182). The credit that would (n's request at ucmpi1's join) holds in every firing of the trace, but statically
  only in the case where the compare's acknowledge started i's link; in the case where i's link is started by its request
  after that release (umux0's output last), nothing within one crossing -- or three (depth 3, through the control token)
  -- bounds n's request, because the remaining chains run back through the counter's own data token and the loop steers
  of the previous iteration. Closing it needs a time separation over the loop (when can umux0's next output come after
  the compare's acknowledge released i's link, with umux2's well before it?), i.e. TSE on the handshake's marked graph
  with min / max arcs, not a walk.
- **The traces are two corners of one route and one vector set** (chains / rest / CARRY 0.20 / 0.31 / 1.0 and
  0.31 / 0.20 / 0.20, no scatter; x55a10 seed 21; xor19, 19 calls x 2 runs, 3678 iterations each), plus the AUTO route
  at the first corner. "n is always last" holds in both hand runs; which input starts i's link does not (the
  acknowledge at the first corner, i's own request at the second, 241 ps after the release). That no reachable timing
  puts n's request before i's in the request case is NOT shown -- and it is what a sound credit would have to show.
- **The AUTO flow's UCMPI1 is not explained by this missing credit.** On the AUTO routes ULINK_N11__1 = 0: there is no
  n-side request delay to credit, the flag changes no E row there, and the rows that bind UCMPI1 at 10-11
  (se_xorshift_ss_5's br8) have a different source (section 5).
- The credit's soundness rests on the structure checks (no latch, no steer, no merge OR, entry pins by polarity and by
  need, X never expanded), on the combinational logic of a credit path being AND-like in the request it carries (true of
  the library's request paths: fork fan-out, N = 1 joins, delay lines, gated delays, a mux's OR entered only through
  ctl_req; the request ORs -- bd_merge, bdc_amerge -- are excluded or sit behind arbiter storage, which is never
  crossed), and on the 4-phase behaviour of the cells, which rule E does not check (rule H, the cells' own verification
  do). The walks are polarity-free apart from the fast-fall side taps (dropped on the earliest walk, as rule E always
  did). Exercised on xorshift only (two routes, eight loop iterations); no other kernel was run with the flag.
- No board run; GLS is not silicon.

## Commands

```
# rule E alone, verbose, with the credit (and every case printed for one request pin, on stderr)
BD_SKEW_AND_JOIN=1 BD_SKEW_E_JOIN=1 [BD_SKEW_E_JOIN_DEPTH=3] [BD_SKEW_E_JOIN_DEBUG='ucond_br8.u$LUT5'] \
  python3 cells/verify/skew.py CA/rule_0.20/soak.sdf -v
# the corner SDF as auto_size.sh's rule() (chains 0.20, CARRY4/F7F8/FF 1, rest B): research/tools/corner_sdf.py
#   XRAY.sdf ROUTED.json OUT/soak.sdf --band B --cell CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 --inst-rx '\.chain\.g\[\d+\]\.u$:0.20'
# E rows as sized (corner_audit's worker, guards 0.97 / 1.03; scale = a line at k x its chain arcs)
python3 research/tools/corner_audit.py --_worker OUT/soak.sdf '{"a_frac": 0.03, "a_min": 50, "glo": 0.97, "ghi": 1.03,
  "drop_const": true, "rule_a_link": false, "osc": [], "cut": [], "drop": [], "scale": {"bridge_i.udut.ucmpi1.udly": 0.2}}'
# the GLS at one corner of the draw model, every net dumped (fullstack_dump.sh's stack, bands as arguments)
work/gls_corner.sh HW xorshift_bench_gen W research/data/eventgraph/gate/xor19.hex xor19.exp 0.20 0.31 1.0
#   (XRAY_SDF_IN=inj.sdf for an injected defect: research/tools/fifteen/sdf_inject.py)
python3 work/trace_steers.py W HW/xorshift_bench_gen_routed.json ['{"ucond_br6": [req, sel, cmp, tok], ...}' UJ_I UJ_N]
python3 work/timeline.py W HW/xorshift_bench_gen_routed.json T0 T1      # PINS / UJ_I / UJ_N in the environment
# the loop with the flag
RUNS=... CA_JOBS=2 PNR_TIMEOUT=3600 BD_SKEW_E_JOIN=1 research/tools/suite/suite_one.sh xorshift 1 4 4
```
The `work/` scripts (gls_corner.sh, trace_steers.py, timeline.py, diag_join.py, erows.py, csdf.py, negctl.sh) are in
the subagent's out/ directory, not committed.
