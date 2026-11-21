# B-obligations: the catalogue of shard B's cell timing obligations

Probe Bo, shard B synthesis, 2026-10-27. No new Lean, no new route, no new
measurement. Sources read: every `formal/notes/B-*.md` (35 files),
`formal/JOURNAL-B.md`, `cells/verify/tighten.py` (rules A-L), `skew.py`
(rule E), `arb_fork.py` (rule J), `decoupled_si.py`, and, for the cells
whose notes are missing, the Lean headers of `LibEndMemMlink.lean` (Lib2) and
of three UNTRACKED files (`CTreeTimed.lean`, `PipePerPin.lean`,
`TernaryOnBits.lean`, `git status: ??`). Every theorem name below was checked
to exist with `grep "theorem <name>"` in `formal/lean/Formal/Cells/`. I did
not re-run Lean; "checks clean" is the source note's claim. Rows built only
from an untracked file are marked **[untracked]**: not in the journal, not
committed, not checked by me.

Routed numbers quoted here are all from C's committed fixtures, re-used by
probes Bt/Bt2/Bp: `link_arb` s1..s4 and `ce_pair` s1..s4, nextpnr sha256
`9c732bc6303458df`, `toolchain.sh` ok (stamped by `fasm2lean2/check.sh`);
`muller64` s1 is ONE route (C-10d), used only as a census. These are
4-seed samples of pad-driven test harnesses, not shipped designs.

## 0. Conventions

**Corner rule (B-arb-corners, `ArbCorners.prj_is_mix`).** prjxray's two
IOPATH triples are the FAST and SLOW corners, not rise and fall. Never take a
rise arc from the FAST column and a fall arc from the SLOW column (the old
56/124 numbers; `prj_is_mix`, `simArcs_is_mix` prove they were that mix).
Every inequality below is a Lean statement over intervals `[lo, hi]`; it is
instantiated physically in one of two ways:

- **box** (H_INDEP): every max-side term at SLOW_MAX, every min-side term at
  FAST_MIN, independently per element. Always sound; can be very
  pessimistic (Bp: rule-J fork fails 8/8 in the box from prjxray alone).
- **1C** (H_ONE_CORNER): both sides from the SAME column, checked once at
  SLOW_MAX and once at FAST_MIN. A SLOW_MAX-only check must add the guard
  `As - Af/k` (`ArbCorners.fast_neg_iff`; `guard_universal` gives `As - Af`
  for wire ratio `k <= 1`). Rise = fall within a column; the asymmetry
  `H_RF_ASYM` (`ArbCorners.RF`) is unmeasured.

prjxray CLB arcs used by B (ps, FAST_MIN / SLOW_MAX): O6 45 / 124 (flat over
pins); O5 from I0/I1 44 / 152; O5 from I2 42 / 150. Site pins (input buffer +
select, `tile_type_CLBLL_L.json`, ns, FAST_MIN..SLOW_MAX): A1 0.172-0.516,
A2 0.170-0.507, A3 0.107-0.344, A4 0.086-0.284, A5 0.033-0.112, A6
0.002-0.005; SLICEM A1 up to 0.531, D1 0.540 (Bp). nextpnr's SDF carries a
flat 124 ps IOPATH per LUT arc and a flat 25 ps site pip, and NO per-pin site
delay (C-10c). Notation `SP[pin]` = site-pin delay of the physical pin the
router chose (read from FASM or the routed JSON's `X_ORIG_PORT_A<k>` /
ROUTING sitewire).

**Guards in the rules.** tighten.py rules A, D, F, H, I, K, L use
`req_guard = max(0.2*t, 200 ps)` added on one side. skew.py rule E and
arb_fork.py rule J use `GUARD_LO*early - GUARD_HI*late` with 0.772 / 1.155.

**Status codes.** S = proved sufficient. N = shown necessary by a
counter-trace. E = exact (S and N, same inequality). "N (inst.)" = necessary
only at an instance / boundary witness, not a general iff.

**Rule verdict codes.** exact / conservative (rule is stronger than the
obligation, sound) / MISSING TERM (rule weaker, named term) / UNCHECKED.

---

## 1. C-elements: `bd_c2`, `bd_c2n` (= link controller `bd_link_ctl`), `bd_c3`, `bd_c4`, `bd_ctree`

Applies to every LUT C-element: link/pipe controllers, ctree nodes, the
arbiter's ack C-elements `ua1/ua2`, merge/mux `uxa/uya`.

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| C1 | minimum pulse width `Dmax` (H_PULSE) — CElemTiming:`c2_follow_hold`; CElemCore:`c2_follow_hold` (ℝ); CTreeTimed:`c3_follow_hold`/`c4_follow_hold` [untracked] | enabling input combination held at the LUT pins for `>= dlmax + dwmax` = O6 IOPATH (SLOW_MAX 124) + feedback INTERCONNECT max + SP[fb pin] max. Box or 1C at each corner; the max side only | **E** for fixed transport delays: `runt_oscillates` (CElemTiming), `runt_oscillatesR` (CElemCore), `c3_runt`/`c4_runt` [untracked]. Involution: `c2_eternal`, `c2_slow_resolution` (CElemInvolution) show runts never reliably die, so Dmax must be ENFORCED, not hoped for | UNCHECKED as such; implied inside a four-phase run by C2 (`c2_four_phase` derives `c(k+1) >= c k + Dmax`) | Bt (`c_follow_hold_s*`): Dmax 569/838/960/590, mean 739, range 569-960 ps; ×1.155 guarded mean 854. Bh P4b (`bd_c2`, wfb 295): GLS rings for S in [124, 295], transport control for every 0 < S < 419 |
| C2 | environment latency / feedback-first: `H_ENV_LATENCY` (CElemTiming:`c2_four_phase`, CElemCore:`c2_four_phase`, LinkTimed row 7, `OnNetlistTimed:c_four_phase_s*`); same thing as `H_FB_FAST` (LinkHandshake:`fb_refines`), CTree H_ATOMIC_CELL item 2, `H_LAT0/H_LAT1` (PipeTimed), `H_LAT i` (PipeTimedN), `H_LAT_ACK` etc. | `dlmax + dwmax <= dlmin + E` (lumped). `E` = min over neighbours of (node -> neighbour wire + neighbour arc + wire back to one of this LUT's input pins). Max side SLOW_MAX, min side FAST_MIN (box) or 1C at both corners | S (`c2_four_phase`). N: the audit's `drop_env_latency_cex` (claude/audit `audit/lean/B/W_CElem.lean`; timed, dl = 1, dw = 2, E = 1: every other hypothesis holds, O glitches inside the window); `LinkHandshake.fb_hazard` (untimed, N = 1); C-10d `rtOne_exact` builds the violating run for RT_FB (shard C). Superseded by C3 when per-pin delays are modelled | UNCHECKED (no rule compares a C-element's own feedback with its neighbours' answer; JOURNAL-B, LinkTimed row 7, PipeTimedN) | Bt: required `E >= 524/793/915/545` (mean 694, range 524-915) at the pins; guarded mean 820. C-10d muller64 (1 route, prjxray, routed neighbours): RT_FB fails 12/64 (slowE), 12/64 (fastE), 42/64 (indep box), and **1/64 even on nextpnr's SDF (-7 ps)** |
| C3 | per-pin form `H_SEL_ORDER` — FifoFidelity:`sel_phase`, `sel_order_of_lat`; `H_SELORD i` — PipePerPin:`pipe_ctl` [untracked] | `w_hi + SP[fb pin].hi <= E_tau + min(SP[req pin].lo, SP[ack pin].lo)`, `E_tau` = earliest departure of req or ack at its PIN after the node edge. Box: fb at SLOW_MAX, departures at FAST_MIN. New term vs C2: `SP[fb] - min SP[req/ack]`, up to +0.43 ns (fb on A1, departure on A5) | S (`sel_phase` + `pinlut_fifo_of_edges`). N: `sel_runt` (the excitation falls back), `ce_not_fifo` (counter-run oscillates, real INIT; satisfies lumped C2 with equal-pin band, fails C3); `cj_clean` (same run, fb on a fast pin, is clean); `ce_violates` [untracked] | UNCHECKED, and INVISIBLE to every SDF-based rule and to the current GLS (`FifoFidelity.gls_lut_fifo`: every GLS run satisfies H_LUT_FIFO by construction) | Bp: pin-1 (slowest) feedback in 12/36 feedback pins (4-seed fixtures), 24/64 muller64 stages, 3/4 latch-pair O6 bits. Per-pin term, slow: link ctl +166 [-2, +245], ce u2 +286 [-118, +425]; box E_need link ctl +544 [+335, +805], ce u2 +584, ua1 +332, ua2 +351. All 12 muller64 RT_FB failures have term > 0 (11 at +410..+425, fb on pin 1); 0 of 33 stages with term <= +100 fail |
| C4 | FIFO/no-static-hazard of the controller LUT: `H_LUT_FIFO` (PipeTimed/PipeTimedN `Ctl`), reduced to `H_PIN_FIFO` + `H_TREE_FIFO` + C3 (FifoFidelity) | not an inequality: one pin edge that leaves the function unchanged gives no output edge (single 2:1 mux with equal legs, H_KLEENE_LUT per mux, MuxTree:`muxTree_eq_lutK`) | assumed. Fidelity grade B (B-muxtree-fidelity); NMOS-only tree can fail for a mid-rail select while equal legs RISE | not a rule; board experiment 1/2 in B-muxtree-fidelity | none on this silicon. GLS agrees by construction (no evidence) |
| C5 | reset width `H_RST_PULSE` / `H_RST_LONG` — CElemTiming:`c2_reset`, LinkTimed row 8, PipeTimed/PipeTimedN `H_RST_LONG`, OnNetlistTimed2:`c_reset_s*` | rst held at the pin `>= dlmax + dwmax` (= C1's Dmax), released before the first request; `R >= L.hi + wh` | S. N not shown separately (same loop as C1) | UNCHECKED (testbench / top-level reset) | Bt2: 569/838/960/590 ps. Harness resets are µs-scale; low risk |
| C6 | tree four-phase with ack wait — CTree:`reachable_eq_flat`; ack wait needed: CTree:`cex_noAck5` | protocol, not timing: the environment turns phase only after the ROOT output acks | E (structural) | n/a (protocol) | — |
| C7 | tree depth latency: lifted `H_ENV_LATENCY : LatOK` — CTreeTimed:`tree_four_phase` [untracked] | for EVERY node n: `Lmax n + fmax n <= lmin_root + E`, `Lmax n` = max over root-to-leaf paths of (LUT max + wire max); uniform: `<= depth*(lmax+wmax) + imax`. Box | S [untracked, not checked by me] | UNCHECKED | none |
| C8 | metastability of the loop (no deadline) — CElemInvolution:`c2_eternal`, `c2_slow_resolution`, `window_lower`; CElemCore:`inertial_*` | not a static inequality: a runt width that never resolves always exists under an involution channel; the window of late widths is >= ~e^{-T/tau_inv} wide | E (theorem of the model) | n/a; only C1 enforcement keeps runts out | — |

---

## 2. `bd_latch` (odd LUT6, pair LUT6_2, `_rst`)

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| L1 | setup, data part `H_SETUP` — Bundling:`capture`; Latch:`holds_value` (`H_EN_OPEN`/`H_DATA`); LinkTimed:`stage_token` (`H_DATA_SETUP`, row 15); PipeTimed `H_SETUP0`/`H_I1`; PipeTimedN `H_I b` with `Dl` | `Td + dhi + fhi <= Toff + elo`, where `dhi` = D wire max + D-pin arc max, **`fhi` = feedback wire max + I2 (feedback-pin) arc max + SP[fb pin] max**, `elo` = enable wire min + I1 arc min + SP[en pin] min, `Toff` = enable fall at THIS bit. Box, or 1C at both corners | S (`capture`). N at the boundary: `Bundling.counter_rule_I` (passes rule I's inequality at zero guard, corrupts), `Latch.ct3_setup_violation`, `LinkHandshake.setup_needed`; general iff: `LinkHandshake.setup_iff` (E for fixed transport, sum over upstream stages) | **rule I, MISSING TERM**: rule I's `t_data` adds the D-pin arc and `loop_wire` but not the feedback-pin arc (`tighten.py` l.1875-1878), and no rule adds `SP[fb pin]`. Rule I uses min-over-bits of `elo` (conservative) and skips data from outside ("not audited"). **Same omission in rules K and L** (`t_data` / `t_follow` = arc + `loop_wire`, l.2009-2012, 2096-2099) — my reading of the code, not a B theorem (B has not formalised K/L) | Bh P5b: transport control flips at exactly 419 = wfb + arc (6c's H_SETUP); GLS flips at 296 (one arc short), so **a GLS pass cannot confirm this term**. Bt/Bt2 latch loop `L = dlhi + fb dw_hi`: q0 601-1029 (mean 816), q1 447-1132 (mean 961), q2 396-997 (mean 652). Bp: latch-pair O6 feedback on pin 1 in 3/4 seeds. Guard covers 124 ps of arc numerically, not arc + up to ~0.49 ns site pin |
| L2 | setup, pulse-width part `H_PW` — Bundling:`capture` (`Ton + ehi + fhi <= Toff + elo`); LinkTimed `H_PULSE_WIDTH` (row 14); PipeTimed `H_PW0`/`H_PW1`; PipeTimedN `H_PW i` | `ehi + fhi <= Won i + elo`: enable high phase AT THE BIT outlasts its own fanout spread + one latch loop. `Won i = L_i.lo + max(ER i, EA i)` (derived round trip). Box | S. N: the `j = i` term of `setup_iff` (E for fixed transport) | UNCHECKED (6c, 6d, 6e, 6f all say so; rule I's data path starts at the upstream latch, never at this bit's own enable rise) | Bt2 `stage_token_q*_s*`: required `E >= Xpw` = q0 1217-1690 (mean 1424), q1 1108-1765 (mean 1569), q2 1101-1953 (mean 1405); **the binding environment constraint on those routes**, above C2's 524-915 |
| L3 | hold `H_HOLD` / `H_RULE_H` — Bundling:`capture`; Latch:`link_latch_holds`, `hold_of_dack`; OnNetlistTimed2:`latch_rule_h_net`, `rule_h_q*_s*`; LinkTimed row 16; PipeTimed `H_H1`, `H_HOLD0`; PipeTimedN `H_H b` | `Toff + ehi <= Tnew + dlo`; in control terms `ehi_b <= aslow_b + L(b-1).lo + elo_{b-1} + dlo_b` (DACK credit = SLOWEST path's lo, the ripple). `ehi` includes SP[en pin] max, `dlo` includes SP[d pin] min. Box | S. N: `Bundling.counter_rule_H`, `Latch.ct1_hold_violation` (silent wrong token), `ct2_hold_violation_x` (X latched) | **rule H, conservative w.r.t. lumped arcs** (omits the D-pin arc, adds guard) **but MISSING the site-pin term** `SP[en] - SP[d]` (Bp §4). Rule H's `t_d` lets intermediate state nodes fire in zero time (conservative) | Bt2 rule H at pins, required `A >= E - R`: q0 223-391, q1 137-384, q2 135-929 (mean 563); guarded q2 304-1167; `rule_h_needs_ack_latency`: with A = 0 it fails on all 12 seed×bit pairs (harness is safe only via the off-chip round trip). Bp latch hold site term: pair +81 [-125, +270] slow, +258 [+123, +421] box; odd +158 [-75, +468] slow, +324 [+172, +509] box. tighten.py l.148: rule H margins move 150-200 ps per fresh seed |
| L4 | latch loop positivity / bound `H_LOOP_MIN`, `H_LOOP_MAX` — Latch:`LatchBit`, `LoopDelay.widen` | `1 <= loop <= L`; L at SLOW_MAX suffices for every faster loop (`widen`) | S | input data | Bt: O5 OUTMUX arc missing from prjxray SDF (q0 loop may be short); q0 s3 feedback max = nextpnr's figure exactly (444 = 444), s4 3 ps below: H_DW upper ends unvalidated |
| L5 | X on the enable with d != q — Latch:`en_x_d_ne_q_is_x`, LinkHandshake `latK_race` | consequence, not an obligation: a setup/hold violation leaves X in the loop; nothing in the cell resolves it | E (Kleene) | — | Bh P5b: gate build emits ONE runt of width w for 124 <= w <= 294 then keeps OLD (downstream can latch the runt) |

---

## 3. `bd_link` / `bd_pipe` (Muller stage composed; `bd_link_dctl`)

Rows C2/C3 (controller), L1-L3 (latches) apply per stage. Additional rows:

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| P1 | data before request at the pipe input `H_DATA_LEAD` — LinkTimed row 12; PipeTimed/PipeTimedN `H_DATA_LEAD` | `dS k + Sdr <= rho(2k) + Lag`; classic "request after data" is sufficient (`Bundling.classic_implies_setup`), not necessary (`setup_not_classic`) | S; not necessary for a Muller latch (closes a handshake later) | **rule A** (sender's request last, guard max(0.2t,200)): a different, stronger condition; conservative | per-design |
| P2 | depth recursion `Dl` and output bundling — PipeTimedN:`token`, `pipe_forward` (`Dl (N-1) b <= Er`); LinkTimed `stage_forward` (row 17) | `Dl(i+1) = max(ehi_{i+1}, Dl i - Rq.lo - L.lo + dhi)`; last stage `Dl <= Er` | S | the consumer's own rule (next stage I; or B/D/E at an edge-sampling consumer) | `bd_link.v`: req leads data ~152 ps/stage, 441 ps at N = 4 (cited in 6e) |
| P3 | FASTRISE (DACK) line flush `H_ACK_FLUSH b` — PipeTimed `H_ACK_FLUSH`; PipeTimedN:`orn_hold_true`, `fastrise_or` | `ahi_b <= Won_b + alo_b` (ripple's hi vs last tap's lo; every copy takes the rise before any takes the fall). Box | S only; 6e notes it is partly an artefact of the path-OR abstraction (each element rises one hop after its input), so physically much weaker | UNCHECKED (FASTRISE dual of rule F; rule F audits FASTFALL only) | none; judged low risk |
| P4 | line flush at reset `H_RST_LINES b` — PipeTimed, PipeTimedN | `L(b-1).hi + Rq_b.hi <= R`, `L_b.hi + ahi_b <= R`, `Ag_b <= R` | S | UNCHECKED | none (reset is long in practice) |
| P5 | request lines are FIFO `H_REQ_LINE`, `H_ACK_LINE` — PipeTimed:`fifo_comp`; PipeTimedN:`fastrise_or` | per-LUT FIFO (C4) composed | S | n/a | — |
| P6 | dctl `lt` settles first `H_LT_FIRST` — LinkHandshake:`dctl_ok0`, `dctl_ok1`; N: `dctl_si_hazard` | `lt` (one LUT arc + its wire) settles before a neighbour can answer through `b`/`a`: wire + LUTs + wire back. Box | S (interleaving schedule); N (`dctl_si_hazard`, 9-step trace) | UNCHECKED on a route (`decoupled_si.py --rt env` assumes it, untimed) | none |
| P7 | dctl capture / load (rules K, L) | data D arc + loop before `b -> lt -> en` closes; Q followed D before reclose | NOT FORMALISED in B (6b: "rule K is not formalised") | rules K, L exist; both omit the feedback-pin arc and SP terms like rule I (code reading, l.2009-2012, 2096-2099) — **unconfirmed by a theorem** | — |

---

## 4. `bd_delay` lines (symmetric, FASTFALL, FASTRISE, gated)

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| D1 | symmetric chain edge window and pulse width — Bundling:`sym_chain`, `sym_edge` | edge reaches z in `[N*lo, N*hi]` (hop = wire + LUT1 arc); a level survives iff `T1 - T >= N*(hi - lo)`. Box | S; N: `buf_pulse_lost` (pulse `w <= hi - lo` may be swallowed) | rules A/D/E/B/C use the chain's routed delay (SDF, flat 124 arc); pulse width UNCHECKED (handshake pulses are wide) | tighten.py header: ring scatter p90 25%, max 34.6%, 76/128 rings slower than SDF |
| D2 | FASTFALL flush `H_FLUSH` — Bundling:`slow_not_early` (uniform `2*hi + thi <= (T - F) + tlo`); exact per-stage form stated in 6c notes | per stage i: `fall_i(latest, at stage-i OUTPUT) + hop_hi(i -> i+1) <= T + tap_lo(i+1)`. Box | S (uniform `H_FLUSH`); N: `ff_counter` (glitch train), **`ff_counter_ruleF`** (passes rule F's premise, rise skips the chain). Per-stage exact form NOT proved | **rule F, MISSING TERM** `hop_hi(i -> i+1) - tap_lo(i+1)` (a value still in flight on the chain wire); covered only while that difference < guard | none per route quoted |
| D3 | FASTFALL/FASTRISE edge bounds — Bundling:`fast_edge`, `slow_arrives` | fast edge: one tap hop `thi`; slow edge in `[N*lo, N*hi + thi]` (upper bound loose by `thi`) | S | used by rules A/H/I via SDF | — |
| D4 | DACK credit — PipeTimedN:`fastrise_or`, `back_odd` | rule H credits `aslow` = the ripple path's lo (fall leaves a FASTRISE line late) | S | rule H uses `timing.early_fall(...)` to the tail: consistent with `aslow` | — |
| D5 | `bd_delay_gated` — LibEndMemMlink:`gated_gate_low`, `gated_dip_flushes` | Kleene only (gate low forces 0 down the chain); no timing theorem | — | — | — |

---

## 5. `bd_arbcell` (bare) and the arbiter state/grant LUTs

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| R1 | settled exclusion — ArbBinary:`settled_exclusion`; OnNetlist:`settled_exclusion_bits` | none (g1, g2 read the same q pin; checked on the bits: `shared_sites_s*`) | structural | — | — |
| R2 | transport exclusion `H_REQ_SEP`, `H_GRANT_SKEW`, `H_INIT_SETTLED` — ArbBinary:`exclusion_transport` | any two request edges > L apart (L = state arc + q loop); `|d6 - d5| <= L` (O6 vs O5 grant arcs) | S; N: `exclusion_needs_sep` (runt trace `runt_overlap`), `runt_overlap_needs_skew` (zero O5/O6 skew gives exclusion for every trace). H_REQ_SEP is an environment rate, not a routable fact | UNCHECKABLE statically; only probabilistic | — |
| R3 | metastable tier — ArbResolve:`no_deadline`, `prob_unresolved_dt`, `mtbf_lower`; ArbAnalog Buridan; ArbInvolution:`arb_eternal`, `arb_grants_eternal` | `P(unresolved at T) <= q * T0 * e^{-T/tau_r}`; MTBF `>= e^{T/tau_r}/(T0 f1 f2)` | E as a model statement; no fixed read time is safe (`no_deadline`) | n/a: needs `tau_r`, `T0` MEASURED (slope of log rate vs resolution time; zero-failure runs cannot give it) | none: arb_prot is zero-failure only. H_PIN_GAIN (gain depends on q's pin) is a hypothesis for the 8% |
| R4 | O5/O6 break-before-make `H_BBM1`, `H_BBM2` — ArbInvolution:`arb_grants_eternal`; N at the first edge: `first_edge_overlap`, `first_edge_iff` | at a q rise, O6 fall beats O5 rise (and mirror), as involution delay functions | S; N only at the first edge | UNCHECKED, not measurable from prjxray (needs per-output pulse-shrink curves of `ugrant`) | `sym_bbm`, `exp_bbm`: identical symmetric channels satisfy it |
| R5 | bare handover overlap — ArbHandover:`overlap_duration_r2_to_r1`; ArbCorners:`overlap_C`, `corner_no_overlap`, `skew_r2_to_r1_C`, `box_overlap_le` | overlap = `max 0 (d6 - o5q - w)`: **0 at every consistent corner, every w >= 0**; box `max 0 (37 - w)`; skew caps 0/26 ps (SLOW_MAX), 3/0 ps (FAST_MIN) | E | no obligation needed (below any filter) | Bh P3: 51/51 rows exact to the ps (cells/sim 16 - R; research GLS 0; box 37 - R) |

---

## 6. `bd_arbiter` (held; `ustate`, `ugrant`, `ua1`, `ua2`)

Notation as 7h/7j: `w*` routes INCLUDING the physical pin's site delay; `smin`
server minimum response (`H_SERVER_MIN`).

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| A1 | A0 fork `H_A0_FORK` (client 2; client 1 = `A0Fork2` of 7j) — ArbA0Fork:`no_early_ack_iff`, `client{1,2}_iff`, `box_safe_iff`; ArbHeldTimed `A0Fork`; TernaryPhases:`arb_a0_fall_ordered` | `late <= early` with `late = wAC + SP[A0 pin of ua_k]`, `early = wSt + SP[A0 pin of ustate] + aSt + wQG + SP[q pin of ugrant] + aG + wGC + SP[g_k pin of ua_k]`; shared prefix `c` and ua_k's arc cancel. Box form: `hi.late <= lo.early` | **E** (both directions, both clients, box version). N: `client{1,2}_counter`, `early_ack_latches` (latches for ever if overlap >= one ua loop), `arb_a0_fall_skewed_early_ack` | **rule J** = `box_safe_iff` on nextpnr's SDF, guarded 0.772/1.155 past `c`. Arcs: flat 2×124 exact for client 2, 26 ps conservative client 1 (`ruleJ_arcs`; 7g's "68-161 ps optimistic" WITHDRAWN). Guarded J covers FAST_MIN given >= 114 ps early routing and k <= 1 (`ruleJ_guard_covers_fast`, `ruleJ_guard_small_E`); raw J does not (`ruleJ_raw_window`, 84 ps window at k = 0.55). **MISSING TERM: site pins** `(SP[St] + SP[QG] + SP[GC] - SP[AC]) - 2*25`, up to -0.5 ns; proposed rule J' (B-arb-a0fork) | survey (168 routes): raw min +618, median +1188, guarded min -103 (2 violations). Bp (link_arb, A0 from a pad): box site correction -13..-388 on 8/8 client-seeds; guarded + box client 1 +472 [+225, +734], client 2 +452 [+209, +565]. Worst assignment totals (Bc): -337 (client 2) / -311 (client 1) at SLOW_MAX, -656 / -659 box: ~0 left at the survey minimum. Bh P1b: GLS hides 0 < delta <= 123 (transport acks from delta = 1); GLS gate build leaks one A2 runt for 124-294 |
| A2 | RT1 grant exclusion (client 1 -> 2) — ArbHeldTimed:`rt1_exclusion`; ArbCorners:`RT1_iff`, `rt1_fast_structural` | `wr1g + g1f1 <= wr1s + Rf1 + smin + wa0s + qf + wq + g2r`  OR  `g1fq <= g2r`. Arc part `2*o6 + d6`: 248 SLOW_MAX / 90 FAST_MIN / -18 box | **E** with a min-response server: N `rt1_counter`, `rt1_counter_minserver`. Structural at FAST_MIN (`rt1_fast_structural`) | UNCHECKED | arc-only (routes 0): 496 SLOW_MAX / 180 FAST_MIN / 72 box (`slow_arc_only`, `fast_arc_only`, `box_arc_only`). Plausible routing ~1.5 ns (arithmetic). Flip window (Bc) at k = 0.55: 84 ps |
| A3 | RT2 ack exclusion (`pulse`, `g1`, `forkA`, `forkG`) — ArbHeldTimed:`rt2_exclusion_arcs`, `A1_low_after`; ArbHeldTimed2:`A1_band`, `A1_band_overlap_matched` | **pulse**: `c1f + wfa1 <= wa0s + qf + wfb + Rrq + smin` (A0's low pulse at ua1 outlasts ua1's fall loop; same shape as H_MUX_RTZ). Reduced at 1C: `wfa1 <= smin + 150 + wa0s + wfb` (SLOW_MAX), `+42` (FAST_MIN); box `wfa1 + 37 <= smin + wa0s + wfb`. g1/forkA/forkG: see 7h table | S; N: `rt2_counter`, `A1_stuck`; pulse is also NECESSARY in the matched-fork case (`A1_band_overlap_matched`: every pulse shorter than `c1f + wfa1` overlaps) | UNCHECKED | arc-only: pulse 398 SLOW_MAX / 132 FAST_MIN / 53 box. Plausible ~0.62 ns (arithmetic, smin ≈ 980). Flip windows 37-216 ps (Bc table) |
| A4 | mirror RT1b, RT2b (`pulse2`, `g2`, `forkA2`, `forkG2`), `A0Fork2` — ArbHeldTimed2:`rt1_exclusion2`, `rt2_exclusion2_arcs`; ArbCorners:`RT1b_iff`, `RT2b_iff`, `rt1b_slow_structural`, `rt1b_fast_race`, `pulse2_zero_routing` | pulse2: `wfa2 <= smin + 150 + wa0s + wfb` (SLOW_MAX), `+42` (FAST_MIN), box `wfa2 + 37 <= smin + wa0s + wfb`. 7j's "wfa2 + 16" tightest margin is a corner-mix artefact (`pulse2_zero_routing`) | S; N `rt1_counter2_minserver`, `rt2_counter2`, `A2_stuck2`. RT1b structural at SLOW_MAX but can fail at FAST_MIN (`rt1b_fast_race`): **a SLOW_MAX-only check of RT1b says nothing** | UNCHECKED (A0Fork2 = rule J client 1) | arc-only pulse2 398 / 132 / 53; plausible ~0.55 ns. Non-vacuity at both corners: `nonvacuous_corners` |
| A5 | server and clients `H_SERVER_MIN`, `Scn.H_SETTLED`, `H_REQ_STEADY` (7g prose) | `smin` = min R0-edge -> A0-edge; A0↑ reached ustate/ua1 before r1↓ (client's 3-LUT chain) | hypotheses | UNCHECKED | — |
| A6 | alternation `H_Q_BEFORE_REREQ` (h2) — ArbBinary:`arbiter_alternates`, N `need_h2`; untimed h1/h3 = RT1/RT2 (`need_h1`, `need_h3`) | a client does not re-raise its request while q is excited | S, N (untimed) | UNCHECKED (fairness, not safety) | — |
| A7 | ack C-elements `ua1`, `ua2` | rows C1-C3 | — | UNCHECKED | Bp box E_need: ua1 +332 [+167, +600], ua2 +351 [+103, +598] |

---

## 7. `bd_merge` (bdc does not emit it: merges go through `bdc_amerge` = `bd_arbiter`)

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| M1 | `H_MERGE_SEQ` — MergeMuxSI:`merge_ok`; N `merge_needs_seq`; LibCtlMergeMux:`merge_early_y_spurious_ack` | protocol: a client raises req only when the other's req and ack are low | S, N | UNCHECKED (GLS assertion suggested) | — |
| M2 | `H_BUNDLED_Z` (z_req after `usel` and both its inputs settled) — `merge_ok` | matched DELAY covers the select cone | S | **rule A** | per-design |
| M3 | isochronic `z_ack -> {uxa, uya}`; `x_ack -> {usel, client}` (broad window) — N `merge_needs_iso_za`, `merge_broad_needs_iso_xa` | weak isochrony: branch skew < one environment round trip | S (`merge_ok`, `merge_ok_early`), N | UNCHECKED | — |
| M4 | uxa/uya feedback — MuxRtzTimed:`merge_rtz_of_latency` | generic C2 (no mux-like race) | S | UNCHECKED (C2) | — |

## 8. `bd_mux`, `bdc_muxn`, `bd_steer`

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| X1 | return-to-zero race `H_RTZ` / `H_MUX_RTZ` — MuxRtzTimed:`rtz_safe`, env form `mux_rtz_env_safe`; untimed N `MergeMuxSI.mux_needs_rtz` | cell: `te + dlmax + dwmax <= tr` (z_ack low pulse at uxa's pins >= uxa O6 arc max + uxa feedback wire max [+ SP[fb]]). Env: `Wux - wux + dlmax + dwmax <= sum of (N+4) min arcs + (N+4) min hops` of the control token loop (za->ctl, ctl, ctl->uj1, uj1, ->uor, uor, DELAY N, server, ->uxa). 1C at each corner: loop at the corner's MIN column, uxa at the same corner's MAX column | **E** for fixed delays: `rtz_counter`/`rtz_counter_loop` (perpetual runt train, spurious ack), `rtz_exact_safe`, `rtz_inertial_lost` (wrong latch). Env bound tightness argued, not proved | UNCHECKED (grep: no uxa/RTZ rule in tighten.py) | `slow_N0` +1067 raw / +414 guarded; `fast_med_N0` +560 / +212; **`fast_adv_N0_fails` -7 raw; `fast_adv_N` N = 2: +405 raw / -6 guarded (fail), N = 3 +154**. Reachable in bdc (loop-header mux, select from control_merge via bd_link); DELAY placeholder 12 is cut post-route |
| X2 | `H_BUNDLED_S`, sender form (s held until ctl_ack falls) — `mux_ok`; N `mux_weak_broad_fails`, `mux_needs_bundled_s`, `mux_needs_bundled_s_hazard` | protocol of the control sender | S, N | UNCHECKED (structural for a bd_link sender) | — |
| X3 | `H_BUNDLED_S_PIN` (s settled at each join pin before ctl_req rises there; moves only while ctl_req low there); steer: LibCtlMergeMux `steer_s_x_while_req` | setup: `t_req,min >= t_sel,max` from a common launch; hold: s may not move at the pin while ctl_req is high at the pin | S, N (untimed) | setup: **rule E** (skew.py, common launch, 0.772/1.155) and rule D (screen, one-sided); hold half: UNCHECKED. Neither adds SP terms | rule E history: 2/118 gcd, 2/24 ipow on one route, 0 on re-routes (skew.py) |
| X4 | isochronic `z_ack -> {uxa, uya, ctl}`, `ctl_req -> {uj0, uj1}` — N `mux_needs_iso_za`, `mux_needs_iso_cr` | weak isochrony (skew < half handshake) | S, N | UNCHECKED | — |
| X5 | `H_BUNDLED_Z` (z_req after the datamux select settled) | matched DELAY | S | rule A | — |
| X6 | join feedback `uj0/uj1` (O -> I3) | C2/C3 for the join loop | not formalised timed (Lib1 "not done"); uj1 used as an `FLoop` in `mux_rtz_env_safe` | UNCHECKED | — |

## 9. `bd_mlink`, `bd_flink` (MOUSETRAP; not emitted by bdc: no match in `bdc/*.py`)

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status, counter-trace | rule | margin evidence |
|---|---|---|---|---|---|
| ML1 | `H_QFB_FIRST` — LibEndMemMlink:`mlink_req_bit_H`, `flink_req_bit_H` | `done -> uq.I2` wire max [+ I2 arc, SP[fb]] < `done -> ux.I0` wire min + ux arc min + `en -> uq.I1` wire min. Box | S (interleaving schedule); N: `mlink_runt`, `mlink_cycle`, `flink_runt`, `flink_cycle`, `masks_fail_without_H` (untimed) | UNCHECKED | none |
| ML2 | data bits | rows L1-L3 | | | |

## 10. `bd_mem` (BRAM boundary)

| # | obligation (Lean name) — file:theorem | physical inequality, corner | status | rule | margin evidence |
|---|---|---|---|---|---|
| ME1 | setup — LibEndMemMlink:`MemPort.setup_ok` | `tSU <= dsLo` (DSETUP line + ubuf + clock net, MIN) | S | **rule B** (T_SU 566/737/532 ps, prjxray BRAM_L max corner; only when clock and payload share a source, else "caller's to meet") | per-design |
| ME2 | hold — `MemPort.hold_ok` | `tHD <= dcLo + dsLoF + dcLoF` (ack round trip) | S (structural with any non-zero lines) | not a separate gate (tighten.py l.177-180: HOLD arcs reported; tb_bdc_mem measures in sim) | — |
| ME3 | read data before ack — `MemPort.rdata_before_ack` | `tCO <= dcLo`, PLUS the consumer's rdata-vs-ack route skew (H_RDATA_ROUTE, named in the Lean doc, NOT in the theorem) | S without H_RDATA_ROUTE | **rule C** (T_CO 2454), MISSING the consumer route skew term | — |
| ME4 | clock high width — `MemPort.clk_high_width`; port serialised `rtz_serialised` | width `>= dsLo + dcLo + dsLoF - dsHi`; compare with BRAM tPWH | S | UNCHECKED against tPWH | — |
| ME5 | `H_NO_INFERRED_BUF`, `H_SETUP_LINE`, `H_CO_LINE` | ram_clk has exactly one driver (the ubuf LUT); ack timed from the same net | hypotheses | netlist/FASM inspection | — |

## 11. Cross-cutting hypotheses (not margins)

- `H_KLEENE_LUT` (one 2:1 mux; MuxTree:`muxTree_eq_lutK`, `Tree.evalK_order_indep`): grade B. Fails plausibly only for a mid-rail select while equal legs rise (NMOS-only tree).
- `H_TERNARY_SIM`: PROVED sound (TernarySound) and exact (TernaryExact) under GMW delays with `H_WIRE_CAUSAL`, `H_GMW_GATE`, `H_WIRE_BOUND`, `H_GATE_BOUND`.
- `H_RF_ASYM`: unmeasured; only `d >= 0` expressible in the 7e/7h OR channel.
- `H_WIRE_RATIO` (one fast/slow ratio per margin): per-wire scatter p10 0.37 .. p90 0.82 not modelled.
- `H_DW`/`H_DL` (C's `pinDelay` = fast-min intrinsic .. slow-max + Elmore): not cross-checked against prjxray `timing.py` or the board (Bt limit 1).

---

## 12. Ranked: the unchecked (or under-checked) obligations most likely to bite

1. **C2/C3: C-element feedback before the environment's answer, at the selects
   (`H_ENV_LATENCY` / `H_LAT i` / `H_FB_FAST` / `H_SEL_ORDER`).**
   Why: it is the one obligation for which a routed model already shows
   failures: C-10d muller64 RT_FB fails 12/64 at the slow corner (prjxray,
   routed neighbours) and 1/64 even on nextpnr's own SDF (-7 ps); Bp shows
   all 12 failures carry a positive site-pin term and the feedback lands on
   pin 1 in about a third of instances. It is on EVERY handshake LUT (link
   controllers, ctree nodes, ua_k, uxa/uya), no rule looks at it, the SDF
   cannot see the site-pin half, and the GLS satisfies it by construction
   (`gls_lut_fifo`). Failure mode: runt / oscillation (`ce_not_fifo`), a
   lost or duplicated handshake event.
   Cheapest check: a tighten.py rule per state node whose LUT is a C-element:
   `max INTERCONNECT(O -> own fb pin) + SP_hi[fb pin] + (124 - 45)
   <= min over neighbours (shortest O -> neighbour state node + its IOPATH +
   shortest back to one of this LUT's non-feedback pins) + SP_lo[that pin]`,
   guarded. Data: SDF INTERCONNECT + IOPATH (already parsed); physical pins
   from the routed JSON's `X_ORIG_PORT_A<k>` (tighten.py already reads it in
   `orig_ports`) or FASM; a 6-row × 4-corner site-pin table per tile type
   from prjxray `tile_type_CLBL{L,M}_{L,R}.json`. C's `routed2lean/rt_all.py`
   already computes RT_FB and could be ported. ~0.5 d (Bp estimate).

2. **L1: latch setup, the feedback-pin term rule I (and K, L) omits.**
   Why: rule I adds `loop_wire` but not the I2 (feedback-pin) IOPATH, and no
   rule adds `SP[fb pin]`; together up to ~150 + ~490 ps against a guard of
   max(0.2t, 200). The latch-pair O6 feedback sat on pin 1 in 3/4 seeds
   (Bp). `counter_rule_I` is the corrupting trace; Bh P5b shows the GLS
   threshold is one arc short of the true one, so no GLS pass can confirm
   it. Failure mode: silent wrong token, or X circulating.
   Cheapest check: in rules I, K and L add `max IOPATH(fb pin -> O)` (SDF,
   available) and `SP_hi[fb pin] - 25` (pin from `X_ORIG_PORT`, site-pin
   table) to `t_data` / `t_follow`. A few lines.

3. **L2: latch enable pulse width `H_PW i` (`ehi + fhi <= Won + elo`).**
   Why: checked by no rule, and on the only routed instances it is the
   BINDING environment constraint (Bt2: E >= 1101-1953 ps, vs 524-915 for
   C2). A wide link's enable fanout spread (~1.1 ns per `bd_link.v`) plus a
   latch loop (up to ~1 ns) is the same order as one neighbour round trip,
   and RFAST / short DACK shrink `Won`.
   Cheapest check: SDF only. Per controller and latch bit: enable route max
   + en arc + loop_wire + fb arc - (enable route min + en arc min) against
   the round trip rule I already computes (`t_ack + t_fall` pieces). No new
   data.

4. **L3: rule H's missing site-pin term `SP[en pin] - SP[d pin]`.**
   Why: Bp §4 measures it at +258 [+123, +421] (pair) and +324 [+172, +509]
   (odd) in the box, invisible to the SDF; rule H margins already move
   150-200 ps per seed (tighten.py l.148) and Bt2's q2 hold requirement
   reaches 929 ps raw, 1167 guarded. Failure mode: silent wrong token
   (`ct1_hold_violation`).
   Cheapest check: add `SP_hi[en pin] - SP_lo[d pin]` (pins from
   `X_ORIG_PORT`, site-pin table) to rule H's `t_en - t_d`.

5. **X1 + A3/A4 pulse: return-to-zero races `H_MUX_RTZ` and the arbiter's
   RT2 `pulse`/`pulse2`.**
   Why: exact obligations (perpetual runt train or wrong latch), reachable in
   bdc's emitted loop-header mux, and the corner-consistent adversarial fast
   estimate is negative once tighten.py cuts the mux's DELAY to 0-2 (-7 raw
   at N = 0, -6 guarded at N = 2). The arbiter pulses are ~0.55-0.62 ns
   (arithmetic only) and only within 37-216 ps flip windows of a corner.
   Cheapest check: SDF only: `z_ack -> uxa` INTERCONNECT (both sides) + uxa
   IOPATH + `loop_wire(uxa)` against the shortest token loop
   (za -> ctl -> uj -> uor -> DELAY -> server -> za), evaluated at both
   corners or with `As - Af/k`; the same walker gives RT2 pulse/pulse2 from
   `wfa_k`, `wa0s`, `wfb`, `smin`.

6. **A1: rule J's missing site pins (rule J').**
   Why: rule J exists and is exact in its arcs, but the site-pin correction
   is negative in the box on 8/8 client-seeds (-13..-388) and can reach
   -0.5 ns; at the survey's tightest raw margin (+618) the worst assignment
   leaves ~0. The fixtures are pad-driven; in-design A0 branches are
   shorter. Already a real deadlock mechanism (gcd_hw GLS).
   Cheapest check: arb_fork.py's `path_to` already resolves the physical
   sink `SITEWIRE/<site>/<LUT>[1-6]`; add the 6-entry site-pin table and
   7g's J' formula. Quick screen with no table: flag A0 on ua_k pin 1/2
   with raw margin < 600 ps.

7. **D2: rule F's in-flight hop `hop_hi(i -> i+1) - tap_lo(i+1)`.**
   Why: `ff_counter_ruleF` passes rule F and still skips the chain; FASTFALL
   is used by every dc DACK and every RFAST link (BDC_LINK_FASTFALL). Covered
   while the difference stays under the guard.
   Cheapest check: SDF only: compare each stage's latest fall plus the max
   INTERCONNECT to stage i+1 against `t_reuse` plus the min tap INTERCONNECT
   into stage i+1.

8. **Lower risk, unchecked:** A2/A4 RT1/RT1b (arc parts 248/90, plausible
   ~1.5 ns; RT1b needs a FAST_MIN check, `rt1b_fast_race`); P3
   `H_ACK_FLUSH`; C5/P4 reset width and line flush; C7 ctree depth latency
   [untracked]; M3/X4 weak isochronic forks (skew < a round trip); X3 hold
   half of `H_BUNDLED_S_PIN`; P6 dctl `H_LT_FIRST`; ML1 `H_QFB_FIRST` (not
   emitted by bdc); ME3 rdata route skew in rule C; ME4 clock high width vs
   tPWH. All SDF-only checks except the site-pin ones.

**Not checkable by any static rule** (need the board or an analog model):
R2 `H_REQ_SEP`, R3 `tau_r`/`T0` (MTBF), R4 `H_BBM`, `H_RF_ASYM`, C4
`H_TREE_FIFO`/`H_KLEENE_LUT` (single-mux static hazard).

## What I could not confirm

- The three untracked Lean files (`CTreeTimed`, `PipePerPin`,
  `TernaryOnBits`): read headers only; not in the journal or a note; not
  checked.
- Rules K and L omitting the feedback-pin arc is my reading of tighten.py
  (l.2009-2012, 2096-2099), not a B theorem: B has not formalised K/L.
- C-10d's RT_FB counts are quoted from `formal/notes/C-10d-routed.md`
  (shard C), one route.
- `bd_mlink`/`bd_flink` "not emitted by bdc" rests on a grep of
  `bdc/*.py` finding no reference.
- The "plausible routing" arbiter margins (7h/7j/Bc) are arithmetic on
  assumed hop ranges, not routed measurements.
