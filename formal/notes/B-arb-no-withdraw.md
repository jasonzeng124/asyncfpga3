# B-arb-no-withdraw (probe Bbare): can a gcd_hw arbiter client withdraw an unacknowledged request?

Shard B, 2026-10-29. Follows `notes/B-gcd-arb-kappa-srv.md` (Bsrv).

Files:
- `formal/lean/Formal/Cells/ArbNoWithdraw.lean` (581 lines; Mathlib closure through
  `OnGcdArbKappaSrv`; it also imports C's `Formal.Net.CapstoneO1` and `CapstoneWitnessCells`).
  It checks.
- Scratch in `/tmp/claude-0/probes/Bbare/`:
  - `drv2.py`: the drivers of every arbiter request, read from the four synth netlists;
  - `set.py`, `need.py`, `need2.py`: the client latency that H_SETTLED needs;
  - `tbl.py`: generates `setTbl`/`setRows` and writes `tbl.json`.

## Question

Bsrv: gcd_hw's gate-level threshold is
- **D1** = 0.0802 if a bare-cell race can occur: a client withdraws an unacknowledged request,
  or H_SETTLED fails;
- **D2** = 0.2166 if only the held arbiter's four-phase handovers occur.

## Answer

**D2 is the relevant threshold, but only conditionally.** It needs:
- (a) the producers' own timing rows: the steer select setup/hold above all;
- (b) H_SETTLED.

H_SETTLED is a timing race through the client, and it is **not** implied by the extracted
arcs. Neither (a) nor (b) is established on the routes here.

### 1. C's network model: no withdrawal, proved

- **No withdrawal holds in C's model** (`gcd_hw_arb_no_withdraw`). Under C's H_CELLS and
  H_BUNDLE, both request channels of all 9 `amerge` stages satisfy `NoWithdraw`: the request
  falls only from the acknowledged phase.
  - `held_until_ack`: a request, once high, stays high while its ack is low.
  - It is a corollary of C's `gcd_hw_protocol`, whose `SendStep` is the four-phase sender rule.
  - Non-vacuity: C's witness run `chW` meets both hypotheses (`net_nonvacuous`).
- **Producers in C's graph** (`arb_inputs`, kernel-decided over C's `ops`). The 18 arbiter
  inputs are produced by:
  - 9 `steerC`;
  - 5 `link`;
  - 3 `forkG`: the forks of amerge-1's and amerge-6's outputs, and of a steer output;
  - 1 `amerge` (the 3-way cascade).
- **The caveat.** C's `Steer`/`Link`/`Fork` read the request and the select at one instant
  on one wire. So C's result says nothing about per-pin skew. That is what section 2 adds.

### 2. Gate level: who drives each request, and does it withdraw?

`drv2.py` reads the synth netlists (identical on all four seeds). Each of the 36 arbiters' r1/r2
is driven by one of three cells.

| arbiter | r1 driver | r2 driver |
|---|---|---|
| merge2 | steer (ucond_br18 O6) | link ctl |
| merge3 | steer (br18 O5) | steer (br22 O5) |
| merge4 | R0 of merge3 (A0 = C-join `ucontrol_merge3_f`) | link ctl |
| merge6 | steer (br26 O6, ack via C-join `ucontrol_merge5`) | link ctl |
| merge9 | steer (br35 O5) | steer (br39 O5) |
| merge10 | link ctl | link ctl |
| merge11 | steer (br35 O6) | steer (br39 O6) |
| merge12.uarb1 | steer (br10 O6) | steer (br13 O6) |
| merge12.uarb2 | R0 of uarb1 (internal) | R0 of merge11 (via `ucontrol_merge11_f`) |

The cells, in B's models (used verbatim):

- **link ctl** (`bd_c2n`, INIT 00B2…; `link_no_withdraw`, from LinkExact's `sufficient`).
  - Assumed: LinkExact's scope `Wf` and its exact conjunction `Conj`, whose rows are
    H_RST_WIDTH, H_RACE_UP, H_RACE_DN and the three latch rows.
  - Proved: for every behaviour in the box, the request node is definitely high from `U1` to
    `Rb + Blo`. `Rb + Blo` is the first instant at which the rise of ack_out can be read.
  - So the link cannot drop its request before the arbiter's A_k rose (at the A_k driver).
  - Non-vacuity at LinkExact's `P0`: the window is `[3521, 4680)` (`link_no_withdraw_nonvacuous`).
- **steer** (LibGapSteer's per-pin model).
  - Assumed: H_S_STABLE plus the two rows H_SETUP_PIN `S0 + ps.hi ≤ R + pr.lo` and
    H_HOLD_PIN `F + pr.hi ≤ S1 + ps.lo`.
  - The unselected branch is 0 at every instant (`steer_unsel_silent`), so it trivially never
    withdraws (`steer_unsel_noWd`).
  - The selected branch is definitely high on `[R + pr.hi, F + pr.lo)` (`steer_sel_held`).
  - Given H_SRC_HOLD `TA ≤ F`, it is high until `TA + pr.lo` (`steer_no_withdraw`). H_SRC_HOLD
    says the join that drives the steer does not drop before the branch's ack rose. It is
    named, not proved: it is the join C-element plus the `uack` OR plus the upstream links.
- **steer, row violated: counter-run** (`steer_withdraws`).
  - The run is LibGapSteer's own spurious-token run: H_S_STABLE and H_HOLD_PIN hold, and
    H_SETUP_PIN is violated by 100 ps.
  - The unselected branch is exactly the pulse `[1300, 1400)`.
  - It violates gate-level no-withdrawal (`NoWdI`) for every ack that is low on that window:
    a 100 ps request that no arbiter can acknowledge.
  - **So a violated steer select row turns into exactly D1's withdrawn request** (the r2 of
    `h21_7j_bare`). Example: ucond_br18's O5 is merge3's r1, and its O6 is merge2's r1.
- **R0** (7h/7j, `R0_held1`/`R0_held2`).
  - In `Scn`/`Scn2`, R0 is high up to `TR`/`TRb`, which is ≥ `ta`, its own A0's rise.
  - A0 is the C-join of the downstream acks (H_A0_CJOIN, not modelled). So R0 falls only
    after the downstream ack rose.
  - An R0 client therefore withdraws only if one of its own clients does. The recursion ends
    at steers (merge3, merge11, uarb1).

**Verdict on withdrawal.**
- No producer withdraws as long as its cell's rows hold. These are:
  - LinkExact's `Conj` for links;
  - H_SETUP_PIN/H_HOLD_PIN for steers;
  - plus H_SRC_HOLD (the join).
- A violated steer row does produce a withdrawal. These rows are B's
  `bd_steer.bundled_s_setup`/`bundled_s_hold` (exact, LibGapSteer). Their routed status is not
  re-checked in this probe.
- Not covered: rise-edge glitches inside a request's own read window. LinkExact and
  LibGapSteer leave the value arbitrary there; cleanliness is H_ROUT / WinFifo.

### 3. H_SETTLED: what it needs, and whether the arcs give it

**The derivation** (`settled1_of_causal` / `settled2_of_causal`). The causal history
`Caus_k`, all about a run of 7h's gate relations:
- A_k rose at `T`;
- A0 was low on ua_k's A0-view window before its rise `ta` (H_A0_LOW_BEFORE);
- the client released at `t0 ≥ T + L` (H_CLIENT_LAT).

From ua_k's real INIT, A_k's rise is ≥ `ta + wa0k + ckr` (`A1_rise_after`/`A2_rise_after`).
So 7h/7j's H_SETTLED (`ta + wa0s + qf ≤ t0 ∧ ta + wa0k + ckf ≤ t0`) holds as soon as:
- **H_ARC**: `wa0s + qf ≤ wa0k + ckr + L`;
- **H_ARC2**: `ckf ≤ ckr + L`, which is automatic with rise = fall.

Non-vacuous: `W1c`, a variant of 7j's W1 in which A1 actually rises, at latency 68
(`settled1_nonvacuous`).

**On the routed data** (lit reading, `Real7`: wa0s = ac+dS1+dS2+es+ps, wa0k = the ua_k A0
route, qf = aq, ckr = ackk):
- `settled_safe`: with the per-client latency `L` of `setTbl`, H_ARC holds for every
  realization at κ ≤ κS2, on all 36 × 2 clients. The certificate is kernel-checked (`set_cert`).
- `settled_L0_fails`: with `L = 0`, H_ARC fails on some realization for **65 of the 72**
  clients, at every κ ≥ κS2 (`setRows`, `row_unsafe_ex`).

So H_SETTLED is **not** a consequence of the arbiter's extracted arcs. A0's rise reaches
ustate's q later than it reaches A_k, by up to 1.59 ns at κS2. The client's release loop must
cover the difference: from the A_k driver, through the client's ack pin and its LUT(s), to the
r_k driver. Those arcs are not in Bar's extraction.

Required latency `L` (ps, κS2, certified sufficient, within a few fs of the relaxation
bound), seeds 2/3/4/d:

| arbiter | client 1 | L1 | client 2 | L2 |
|---|---|---|---|---|
| merge2 | steer | 709 / 593 / 754 / 141 | link | 517 / 496 / 754 / 459 |
| merge3 | steer | 318 / 274 / 75 / 305 | steer | 144 / 139 / 113 / 308 |
| merge4 | R0 (merge3) | 143 / 351 / 130 / 562 | link | 473 / 616 / 573 / 142 |
| merge6 | steer (forked) | 751 / 293 / 443 / 0 | link | 169 / 562 / 74 / 0 |
| merge9 | steer | 643 / 349 / 742 / 86 | steer | 0 / 848 / 318 / 1111 |
| merge10 | link | 680 / 476 / 293 / 458 | link | 276 / 422 / 327 / 361 |
| merge11 | steer | 1591 / 726 / 374 / 696 | steer | 1227 / 600 / 0 / 1037 |
| merge12.uarb1 | steer | 13 / 817 / 308 / 773 | steer | 12 / 487 / 594 / 488 |
| merge12.uarb2 | R0 (uarb1) | 561 / 30 / 0 / 416 | R0 (merge11) | 1162 / 0 / 0 / 54 |

**How much of this is 7j's conservatism (script only, not Lean).**
- 7j's H_SETTLED compares A0 at q's *output* (`+ qf`) with r_k at its *driver*.
- The physical race compares, at ustate's pins, A0's arrival (`ta + wa0s`) with r_k's fall
  (`t0 + wrks`). With flat O6 arcs the two views carry the same arc, so I believe this sharper
  form is the exact one. It is not proved: it needs 7j's `q_lo2` redone.
- Crediting `rs_k` and dropping `aq`, the need falls to at most 502 ps (seed 2
  merge12.uarb2, client 2), positive on 21/72 clients. The link clients' maximum is 135 ps
  (seed 3, merge2).
- Physically, one route plus one LUT arc may well cover that for links; for steers, the
  release loop has 3+ LUTs. Unverified.

**The rule this is.** It is the rise-side twin of rule J (H_A0_FORK, the A0 *fall* fork). The
A0 *rise* must reach ustate's hold pin before the client's release, which starts from
A0 → ua_k → A_k → client, gets back to ustate's request pin. No rule checks it today
(`cells/verify/arb_fork.py` is the fall side). With the client-loop arcs extracted, it is one
more linear row per client, decidable by the same κ machinery (`fset1/2` with `L` replaced by
the loop's arcs).

### 4. The design statement

`design_gate_held_causal`: OnGcdArbKappaSrv's `design_gate_held` (D2) with H_SETTLED
discharged.
- **Assumed.**
  - Everything of `design_gate_held` except H_SETTLED: corner model; lit reading; κ ≤ κS2;
    Real7/Real1/Real2; H_SERVER_GRAPH; H_LOOP_*.
  - A causal history `Caus_k` of the same record with the same `ta`, `t0`, in a run `sr`.
  - Client latency ≥ setTbl's `L_k`.
  - For the g1/g2 records, ua_k's A0 route and arc at their routed values.
- **Proved.** For all 36 arbiters at κ ≤ 0.216552148868: A1/A2 and g1/g2 are exclusive across
  both handovers.
- **Not covered.**
  - The A0 forks (7g) are unchanged from `design_gate_held`.
  - The bare-cell part (D1) is not needed under these hypotheses.

The derived H_SETTLED comes from a *separate* run `sr` because of a modelling finding:
- **`Scn` excludes its own cause** (`scn_excludes_caus`, `scn2_excludes_caus`). 7h/7j's
  `Scn`/`Scn2` assert their settled initial state on the **whole past**: `∀ t < t0, A1 t =
  true` (respectively A2). So no trace with an A_k rise before `t0` satisfies `Scn`. That
  includes every run from reset in which the client is ever acknowledged.
- Consequence: 7h/7j's handover theorems are statements about an idealized "settled since
  forever" prefix. Applying them to a real run needs a windowed `Scn`: every lookback is
  bounded, so only a finite window before `t0` should matter. That lemma is not proved.
- `design_gate_held_causal` therefore takes the event times' relation from the real history
  `sr` and the scenario from the idealized `s`.
- Joint satisfiability on 7j's `D0`: `W1c` (real) and `W1` (idealized), same `ta`, `t0`
  (`settled1_nonvacuous`). D0 is corner-mixed, so this is satisfiability only.
- The data-side non-vacuity is Bsrv's `design_nonvacuous` (κS2 realizable).

## Problem statement

**Assumed.**
- C: H_CELLS, H_BUNDLE (C's cell models).
- B's cell models:
  - LinkExact's Box/Env/`Wf`/`Conj`;
  - LibGapSteer's per-pin reads with H_S_STABLE/H_SETUP_PIN/H_HOLD_PIN;
  - 7h/7j `Run`/`Scn`/`Scn2`.
- H_SRC_HOLD and H_A0_CJOIN: named, not proved.
- For section 3: H_A0_LOW_BEFORE and H_CLIENT_LAT.
- A's corner model with Bar's UNTRUSTED extraction (as in Bsrv).

**Proved (Lean, checks).**
- `gcd_hw_arb_no_withdraw`, `held_until_ack`, `net_nonvacuous`, `arb_inputs`.
- `link_no_withdraw` (+ nonvacuous).
- `steer_unsel_silent`, `steer_unsel_noWd`, `steer_sel_held`, `steer_no_withdraw`,
  `steer_withdraws`.
- `R0_held1/2`.
- `A1_rise_after`, `A2_rise_after`, `settled1_of_causal`, `settled2_of_causal`.
- `scn_excludes_caus`, `scn2_excludes_caus`, `settled1_nonvacuous`.
- `settled_safe`, `setTbl_max`, `settled_L0_fails`, `design_gate_held_causal`.

**NOT covered.**
- The client-loop arcs, so whether gcd_hw's clients meet `setTbl`. This is THE open item.
- The steer rows on the routes.
- The join and `uack` OR (H_SRC_HOLD).
- The sharper H_SETTLED (script only).
- A windowed `Scn`.
- Rise-edge glitches, Kleene X, metastability, κ itself.

## Check status

- `/tmp/claude-0/btools/bcheck.py Formal/Cells/ArbNoWithdraw.lean`: **OK**, no warnings.
  `formal/scan.py` is clean.
- `#print axioms` (companion file, since removed):
  - `[propext, Classical.choice, Quot.sound]` or fewer on every headline theorem;
  - `[propext]`: `arb_inputs`, `setTbl_max`;
  - `[propext, Quot.sound]`: `held_until_ack`, `steer_unsel_*`, `R0_held*`, `scn*_excludes_caus`.
