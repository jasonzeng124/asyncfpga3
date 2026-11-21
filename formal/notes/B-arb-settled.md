# B-arb-settled (probe Bset): the sharp H_SETTLED, its latency table, and its discharge for link clients

Shard B, 2026-10-29. Follows `notes/B-arb-no-withdraw.md` (Bbare).

Files:
- `formal/lean/Formal/Cells/ArbSettled.lean` (Mathlib closure through `ArbNoWithdraw` →
  `OnGcdArbKappaSrv`). It checks (`bcheck.py`: OK; `formal/scan.py`: clean).
- Scratch in `/tmp/claude-0/probes/Bset/`: `tbl2.py` (the table, `tbl2.json`, `tbl2.lean`),
  `link.py` (link clients with the controller's O6 arc credited).

## Question

Bbare derived 7h/7j's H_SETTLED (`ta + wa0s + qf ≤ t0 ∧ ta + wa0k + ckf ≤ t0`) from causality
plus a client latency `L` (A_k's rise at ua_k's output → r_k's fall at its driver), and found
that gcd_hw's routed arcs need `L` up to 1.59 ns. A script said that comparing at ustate's
pins (crediting the r_k route, dropping `qf`) lowers this to ≤ 502 ps. This probe proves that
sharper condition, recomputes the table in Lean, and discharges the condition for the clients
whose cell has a model (the link controller).

## Answer

1. **The sharp condition is H_PIN: `ta + wa0s ≤ t0 + wr_ks`.** A0's rise must reach ustate's
   hold pin I4 no later than r_k's fall reaches ustate's request pin. It replaces H_SETTLED in
   every exclusion theorem of 7h and 7j, it is implied by H_SETTLED, it is strictly weaker,
   and it is exact for the q trace (exactly for 7j, and for 7h whenever `qr = qf`, i.e. on
   every `Real7` record). The second conjunct of H_SETTLED is not used by any exclusion theorem
   (only by the `*_stuck` counter-traces), so it is dropped.
2. **The latency it needs on gcd_hw**: at most **502.361 ps** (was 1590.934), positive on
   **21 of 72** clients (was 65). The table is proved safe at κ ≤ κS2 and exact to 10 fs.
3. **Link clients: discharged on 18 of 20 instances**, from LinkExact's controller model and
   the controller's O6 arc, with no latency hypothesis. The other 2 (merge2.uarb1 client 2,
   seeds 3 and 4) need the ack wire into the controller, which is not extracted.
4. **Steer and R0 clients (18 of the 21 positive entries are among them, 16 steer + 2 R0): not
   discharged.** Their release loops have no cell model with arcs here.

### 1. The sharp condition (Lean, real INITs)

- **Why `qf` drops out.** In 7h, q stays 1 at `t ≥ t0` iff some ustate view (rise `qr` or
  fall `qf`) returns 1. In the slow view, either r1 is still high at I0 (`t − wr1s − qf < t0`),
  and then `FS true r2 true a0 = true` whatever r2 and A0 are (`FS_r1q`, decided on INIT
  0xFFF0FFB2ACACACAC); or r1 has fallen there, and by H_PIN A0's rise is already at I4, so
  `FS_hold`. Both pins go through the same flat O6 arc, so the arc cancels. 7j is the mirror,
  with `FS r1 true false a0 = false` (`FS_r2q`), and both views are needed because q RISES.
- **Re-proved chain.** `H.ScnP` / `J.Scn2P` are 7h's `Scn` / 7j's `Scn2` with H_SETTLED
  replaced by H_PIN. On them the whole exclusion chain is re-proved verbatim except for the
  new `H.q_hi` / `J.q_lo2`: server bounds, exact q/g traces, `H.rt1_exclusion`,
  `H.rt2_exclusion_arcs`, `J.rt1_exclusion2`, `J.rt2_exclusion2_arcs`.
- **Generalization.** `H.ofScn`, `J.ofScn2`: H_SETTLED ⇒ H_PIN (`qf ≥ 0`, `wr_ks ≥ 0`).
- **Strictly weaker, non-vacuous** (`strict_witness`). `W1p`/`W2p` are 7j's `W1`/`W2` with A0
  rising at −50 instead of −1000. They are runs of the gate relations on 7j's `D0` for all `t`,
  server included. They satisfy `ScnP`/`Scn2P` for every horizon past the second server edge.
  Both conjuncts of H_SETTLED fail for them: −50 + 124 > 0. The exclusion theorems give
  grant and ack exclusion on them below the horizon. `D0` is corner-mixed (audit row 24), so
  this is satisfiability only.
- **Exact (counter-traces).**
  - `J.q_glitch2`, every record: if `t0 + wr2s < ta + wa0s` and A0 is low at that view
    instant, then in every run q rises at `t0 + wr2s + qr`, which is before `QBb`. The arbiter
    grants client 1 while the server still serves client 2.
  - `H.q_glitch`: if `t0 + wr1s + qf < ta + wa0s + qr` and A0 is low on
    `[t0 + wr1s − wa0s, ta)`, then q falls at `t0 + wr1s + qf`, which is before `QB`. With
    `qr = qf` this condition is exactly ¬H_PIN.
  - What is not shown: that the early q edge goes on to break exclusion.

### 2. From causality, and the table (Lean)

- **`settledP1_of_causal` / `settledP2_of_causal`.** With Bbare's `Caus_k` (`A1_rise_after`:
  A_k rises at `T ≥ ta + wa0k + ckr`; the release is at `t0 ≥ T + L`), H_PIN holds as soon as
  H_ARC_P: `wa0s ≤ wa0k + ckr + L + wr_ks`. Non-vacuous on `W1c` at `L = 0`
  (`settledP1_nonvacuous`).
- **On the routed data** (`Real7`, lit reading).
  - Forms: `fsh1 L`: `dS2 + es + ps ≤ d12 + e1 + p1 + ac1 + rs1 + L`; `fsh2` is the mirror.
    The prefix `ac + dS_k` cancels. `rs_k` enters through H_RK_ROUTE (`rs_k ≤ wr_ks`: the r_k
    route to ustate is at least its extracted suffix; the common prefix from the driver is ≥ 0
    and is not carried by Bar's extraction).
  - `set2_cert` (kernel) and `settledP_safe`: every realization at κ ≤ κS2, all 72 clients.
  - `setTbl2_max`: 502361 fs. `setTbl2_pos`: 21 positive entries.
  - `settledP_tight`: for each positive entry `L` and every κ ≥ κS2, a realization violates the
    form at `L − 10 fs`. The rows are generated from `setTbl2` itself (`tightRows`), so the
    link between the two is by construction.
  - `settledP_L0_fails`: so `L = 0` fails on exactly those 21.
- **`design_gate_held_sharp`**: OnGcdArbKappaSrv's four handover conclusions (A1/A2 and g1/g2,
  both releases) on `ScnP`/`Scn2P`.
- **`design_gate_held_sharp_causal`**: the same with H_PIN derived from a causal run `sr` at
  latency ≥ setTbl2's entry plus H_RK_ROUTE. It is the sharp twin of Bbare's
  `design_gate_held_causal` and uses the same idealized/causal split (`Scn` excludes its own
  cause; the windowed `Scn` is Barb2's).

**Required latency** (ps, κS2, certified; exact to 10 fs), seeds 2 / 3 / 4 / d:

| arbiter | client 1 | L1 | client 2 | L2 |
|---|---|---|---|---|
| merge2 | steer | 64 / 61 / 94 / 0 | link | 0 / **135** / **125** / 0 |
| merge3 | steer | 0 / 0 / 0 / 0 | steer | 0 / 0 / 0 / 0 |
| merge4 | R0 (merge3) | 0 / 0 / 0 / 214 | link | 0 / 24 / 0 / 0 |
| merge6 | steer (forked) | 87 / 0 / 0 / 0 | link | 0 / 0 / 0 / 0 |
| merge9 | steer | 7 / 0 / 248 / 0 | steer | 0 / 490 / 0 / 436 |
| merge10 | link | 0 / 0 / 0 / 0 | link | 0 / 0 / 0 / 0 |
| merge11 | steer | 195 / 58 / 0 / 0 | steer | 223 / 70 / 0 / 371 |
| merge12.uarb1 | steer | 0 / 51 / 0 / 223 | steer | 0 / 0 / 0 / 14 |
| merge12.uarb2 | R0 (uarb1) | 0 / 0 / 0 / 0 | R0 (merge11) | **502** / 0 / 0 / 0 |

The 21 positive entries are 3 link, 16 steer and 2 R0 clients. The script claim (≤ 502 ps,
21/72, link ≤ 135 ps) is confirmed in Lean.

### 3. Link-driven clients: discharged from the controller's own model

The client cell is `bd_link_ctl` = `bd_c2n`: one `LUT6`, INIT 00B2…, with I0 = req_in,
I1 = ack_out = the arbiter's A_k, and output c = the arbiter's r_k. Bbare's `drv2.py` re-run:
in all four synth netlists the amerge's `in*_ack` net is read only by the controller's I1, and
`in*_req` is driven by the controller's O directly.

- **`LinkRel.release`** (LinkExact verbatim, through Bbare's `link_no_withdraw`). Under
  LinkExact's scope `Wf` and exact conjunction `Conj`, for every behaviour in its box, the node
  is definitely high on `[U1, Rb + Blo)`. So with H_ACK_RB (`Rb = T`, the A_k rise) and
  H_ACK_READ (`x ≤ Blo`), a node that is not high at `t0 ≥ U1` gives `T + x ≤ t0`. The
  controller cannot release before its C-element has read the ack, and the read delay is at
  least the O6 arc.
- **`link_caus1` / `link_caus2`**: Bbare's `Caus_k` at latency `x`.
- **Extended corner model.** `litL` is the arbiter's lit model plus one arc (`none`), the
  controller's O6 arc. It uses prjxray A6LUT O6 FAST_MIN 45 / SLOW_MAX 124 ps, flat over pins,
  in SLICEL and SLICEM (`B-arb-corners-pin.md`), under H_LUT6_O6. `realizes_ext`: a realization
  of the arbiter at corner `c` plus `x` within κ of the O6 arc AT THE SAME CORNER
  (H_SAME_CORNER) realizes `litL`. `certL_safe`: the cleared κS2 endpoint check is sound.
- **`link_pin1` / `link_pin2`.** On `linkTbl1` (merge10 client 1, 4 seeds) and `linkTbl2`
  (client 2 of merge2 seeds 2/d, merge4 ×4, merge6 ×4, merge10 ×4), H_PIN holds for every
  κ ≤ κS2, every realization and every such `x`, with no latency hypothesis.
  `design_link_discharged1/2` give the A-exclusion and g-exclusion handover conclusions for
  these 18 instances. 17 of them have table entry `L = 0` (LinkRel still supplies the causal
  order `T ≤ t0`); the O6 arc is what discharges seed 3 merge4 client 2 (24 ps).
- **`link_short`: the 2 instances not discharged.** These are seed 3 and seed 4 merge2.uarb1,
  client 2.
  - At κS2, ConstraintsKappa's `worst` realization of `litL` at the FAST endpoint violates the
    form when the latency is the O6 arc alone (zero ack route).
  - Residual need after the O6 arc (`link.py`): seed 3 19.9 ps fast / 37.6 ps slow; seed 4
    89.7 ps fast / −11.1 ps slow.
- **Non-vacuity** (`link_caus1_nonvacuous`). LinkExact's witness behaviour at `P0`
  (`Rb = 4300`, `Blo = 380`, `U1 = 3521`, node low from `V1 = 5021`) is composed with `W1s`,
  Bbare's `W1c` shifted by +5244 ps (a run of `D0`, A1 rising at 4300, r1 falling at 5244).
  All of `link_caus1`'s hypotheses hold together, and the latency is 45. Two limits:
  - LinkRel does not equate the controller's node with `sr`'s r1 (it is not needed, and the
    witness's two traces are separate);
  - joint satisfiability of the gcd data part (`Real7` of a realization together with a run)
    is not exhibited. The data side is Bsrv's `design_nonvacuous`.

**Exactly which arcs are missing.**
- For every link client:
  - (a) the routed INTERCONNECT from ua_k's O6 (the A_k driver) to the controller's
    physical I1 pin;
  - (b) the site-pin delay SP of that physical pin (prjxray's per-pin lower bound is 2 ps,
    A6, which changes no verdict);
  - (c) the placement fact H_LUT6_O6;
  - (d) the r_k prefix from the controller's O to the r_k net's branch point (credited as ≥ 0).
- (a) is what the 2 short instances need: ≥ 37.6 ps (seed 3) and ≥ 89.7 ps (seed 4), at the
  same corner.
- **Steer clients**: the arcs of the `cond_br` LUT (request pin → O5/O6), the join C-element
  and the `uack` OR in the release loop. Also H_SRC_HOLD, which is named only.
- **R0 clients**: the downstream A0 C-join (H_A0_CJOIN), not modelled.
- No routed SDF/FASM of gcd_hw is on this machine, and there is no toolchain
  (`~/dev2/lib/fpgatoolchain` is absent), so none of these could be extracted here.

### 4. The rule, in `cell_constraints.json` form (proposal; the JSON is NOT edited)

This is the rise-side twin of rule J. Rule J (H_A0_FORK) races A0's FALL to ua_k against
A0 → ustate → q → ugrant → g_k → ua_k. Rule J+ races A0's RISE to ustate's hold pin against
A0 → ua_k → A_k → client release loop → r_k → ustate's request pin. Each client of each
`bd_arbiter` gets one linear row, checked like rule J (one column at FAST_MIN and SLOW_MAX,
or GenOK with κ at both endpoints). Names follow the file's conventions (`<lut>.<logical
pin>`, `@pip` = site-pin input).

```json
{
 "id": "bd_arbiter.a0_rise_settled_client2",
 "cell": "bd_arbiter",
 "obligation": "H_PIN (client 2, sharp H_SETTLED): A0's rise reaches ustate.I4 no later than client 2's release of r2 reaches ustate.I1",
 "inequality": "early <= late; early = wS + SP[ustate.I4] (A0 rise, after the A0 net's ustate/ua2 divergence); late = w2 + SP[ua2.I1] + a_ua2 + LOOP_2 + wR2 + SP[ustate.I1]; LOOP_2 = A2 driver -> client 2 ack pin -> ... -> r2 driver (client cell); shared A0 prefix cancels; the r2 prefix before the ustate/ugrant branch is >= 0 and may be dropped (sound)",
 "forms": [{
   "launch": "A0 rise at the divergence point of ustate's and ua2's branches of the A0 net",
   "data_paths": [[
     {"kind": "wire", "from": "A0@div", "to": "ustate.I4", "lean_sym": "dS1 + es"},
     {"kind": "site_pin", "from": "ustate.I4@pip", "to": "ustate.I4", "pin_role": "A0", "lean_sym": "ps"}
   ]],
   "request_paths": [[
     {"kind": "wire", "from": "A0@div", "to": "ua2.I1", "lean_sym": "d12 + e2"},
     {"kind": "site_pin", "from": "ua2.I1@pip", "to": "ua2.I1", "pin_role": "A0", "lean_sym": "p2"},
     {"kind": "lut_arc", "from": "ua2.I1", "to": "ua2.O6", "lean_sym": "ac2", "note": "A2 rise"},
     {"kind": "wire", "from": "ua2.O6", "to": "<client2>.ack_pin", "lean_sym": "(missing)", "note": "link client: <link>.ctl.u.u.I1"},
     {"kind": "site_pin", "from": "<client2>.ack_pin@pip", "to": "<client2>.ack_pin", "lean_sym": "(missing)"},
     {"kind": "env", "from": "<client2>.ack_pin", "to": "r2 driver", "lean_sym": "L2 (H_CLIENT_LAT)", "note": "link client: lut_arc ctl.I1 -> ctl.O6 (x, H_ACK_READ, H_LUT6_O6), LinkExact.Conj required; steer client: join C-element + uack OR + cond_br arcs (no model with arcs); R0 client: the downstream arbiter's A0 C-join"},
     {"kind": "wire", "from": "r2 driver", "to": "ustate.I1", "lean_sym": "crk (>= 0, dropped) + rs2", "note": "rs2 includes the site pin of ustate.I1"}
   ]],
   "margin_ps": 0
 }],
 "lean": [
   {"file": "formal/lean/Formal/Cells/ArbSettled.lean", "name": "J.q_lo2", "role": "sufficient (q trace)"},
   {"file": "formal/lean/Formal/Cells/ArbSettled.lean", "name": "J.q_glitch2", "role": "necessary (q trace, every record)"},
   {"file": "formal/lean/Formal/Cells/ArbSettled.lean", "name": "J.rt1_exclusion2 / J.rt2_exclusion2_arcs", "role": "sufficient (exclusion)"},
   {"file": "formal/lean/Formal/Cells/ArbSettled.lean", "name": "settledP2_of_causal", "role": "sufficient (latency form)"},
   {"file": "formal/lean/Formal/Cells/ArbSettled.lean", "name": "settledP_safe / settledP_tight", "role": "gcd_hw table, exact to 10 fs"},
   {"file": "formal/lean/Formal/Cells/ArbSettled.lean", "name": "link_pin2 / design_link_discharged2", "role": "discharged for link clients (14 of 16 client-2 link instances)"}
 ],
 "exactness": "sufficient+necessary (q trace); exclusion side sufficient only",
 "site_pins": {"needed": true, "roles": ["ustate.I4 (A0) hi", "ua2.I1 (A0) lo", "<client2>.ack_pin lo", "ustate.I1 (r2) lo"]},
 "rule": {"rule": "J+ (proposed, rise-side twin of J)", "source": "none (cells/verify/arb_fork.py checks the fall side only)", "verdict": "proposed",
          "missing": "LOOP_k arcs: wire + site pin into the client's ack pin, and the client cell's arcs (link: one O6 arc; steer: join + uack + cond_br; R0: the downstream C-join)"},
 "corner": {"mode": "1C", "kappa": {"check": "GenOK at the FAST and SLOW endpoints with every arc, LOOP_k's included, at the SAME corner (H_SHARED_CORNER)"}},
 "check_scope": "static_route (walks from A_k into the client cell)",
 "status": "proved (with LOOP_k as the named latency); discharged for link clients where the arcs suffice",
 "combine": "all",
 "hypotheses": ["H_RK_ROUTE", "H_A0_LOW_BEFORE", "H_SAME_CORNER (link)", "H_LUT6_O6 (link)", "H_ACK_RB, H_ACK_READ (link)", "H_SPREAD_CORRELATED (lit reading)"]
}
```

Client 1 is the mirror: `dS2` for `dS1`, `ua1`, `p1`, `ac1`, `ustate.I0`, `rs1`. In 7h's
direction the q edge is a fall, so the exact form there is
`wS + SP[I4] + qr ≤ late + qf` (`H.q_glitch`). It equals the row above when `qr = qf`, which
holds for prjxray's flat O6.

Proposed checker logic:
1. For each `bd_arbiter` client, find the client cell that drives r_k and reads A_k.
2. Sum LOOP_k's arcs along the path A_k → that cell's ack pin → its output, with each arc at
   its lower bound.
3. If the client is not a known cell (steer, R0), fall back to `setTbl2`'s `L_k` as a required
   latency and report the row as unverified.

## Problem statement

**Assumed.**
- 7h `Run` / `Server` (H_SERVER_MIN).
- The idealized scenario fields of `Scn`/`Scn2` except H_SETTLED.
- Either H_PIN, or Bbare's `Caus_k` (H_A0_LOW_BEFORE, H_CLIENT_LAT) together with H_RK_ROUTE.
- A's corner model (H_SHARED_CORNER, H_SCATTER κ, lit reading) on Bar's UNTRUSTED extraction;
  `Real7`/`Real1`/`Real2`; H_SERVER_GRAPH.
- For links:
  - LinkExact's `Wf`/`Conj`/`Beh`;
  - H_ACK_RB, H_ACK_READ, H_SAME_CORNER, H_LUT6_O6;
  - the netlist reading of r_k's driver (`drv2.py`).

**Proved (Lean, checks).**
- The sharp scenarios and the exclusion chain:
  - `H.ScnP`, `H.q_hi`, `H.rt1_exclusion`, `H.rt2_exclusion_arcs`, `H.ofScn`, `H.q_glitch`;
  - `J.Scn2P`, `J.q_lo2`, `J.rt1_exclusion2`, `J.rt2_exclusion2_arcs`, `J.ofScn2`,
    `J.q_glitch2`;
  - `strict_witness`.
- Causality and the table:
  - `settledP1_of_causal`, `settledP2_of_causal`, `settledP1_nonvacuous`;
  - `set2_cert`, `settledP_safe`, `setTbl2_max`, `setTbl2_pos`, `tightRows_ok`,
    `settledP_tight`, `settledP_L0_fails`.
- The design statements: `design_gate_held_sharp`, `design_gate_held_sharp_causal`.
- Links:
  - `LinkRel.release`, `link_caus1/2`, `realizes_ext`, `certL_safe`, `link_cert1/2`;
  - `link_pin1/2`, `design_link_discharged1/2`, `link_short`, `link_caus1_nonvacuous`.

**NOT covered.**
- The windowed `Scn` (Barb2).
- The routed ack wire and site pin of every client, so 2 of the 20 link instances stay
  conditional.
- Steer clients (16 positive entries) and R0 clients (2).
- Whether a violated H_PIN breaks exclusion: the counter-traces stop at q's early edge.
- 7h with `qr < qf`: the gap between H_PIN and the necessary condition is not decided.
- Kleene X, metastability, κ itself.

## Check status

- `/tmp/claude-0/btools/bcheck.py Formal/Cells/ArbSettled.lean`: **OK**. `formal/scan.py` is
  clean.
- `#print axioms` (companion file, since removed):
  - every headline theorem: ⊆ `[propext, Classical.choice, Quot.sound]`;
  - `[propext]`: `set2_cert`, `setTbl2_max`, `setTbl2_pos`, `tightRows_ok`, `link_cert1/2`;
  - `[propext, Quot.sound]`: `H.q_hi`, `J.q_lo2`, `H.ofScn`, `J.ofScn2`, `H.q_glitch`,
    `J.q_glitch2`.
