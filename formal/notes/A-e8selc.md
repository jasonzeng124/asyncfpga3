# A-e8selc (probe E8SelC): the select wires of the routed verdict — C's H_BUNDLE, setup, hold (shard A)

STATUS (2026-10-29 ~10:30 UTC): Lean done (5 files elaborate against an overlay, no sorry);
16-row run in progress; check.sh pending (see §6).

## 0. Summary

- **(1) `Events9Sel.design_verdict9_sel`**: E8Hyp's `design_verdict8_sel`, ported to the Events9
  verdict. SelOK at every REAL filtered pin is replaced by B's H_S_STABLE (open-ended hold) and
  H_SETUP_PIN on the select wires, and HDsub stays proved (`verdict9`). The SelOK derivation is
  now a lemma, `selOK_real`.
- **(2) `Events9SelC.design_verdict9_selC`**: the select-wire stability premise is derived from
  C's **H_BUNDLE** (`Formal.Net.Ops.Held`) of ONE C channel per select literal. The map from C's
  channel to A's wires is **`chanOf x rq ak ws`**: C's `Handshake.Chan` whose request,
  acknowledge and bus are A's wires. It is given as data (`SelEnt`, one per real filtered pin and
  literal) together with a decidable consistency predicate **`entOK`**, which `xselhold` checks on
  the parsed netlist.
- **(3) the hold half**: `Events9SelHold` (source-anchored) and `Events9SelSplit`
  (junction-anchored, which removes common-path pessimism) state it as a decidable band row
  (`holdBand` / `holdBandS`), proved sound against B's hold condition (`hold_pin_of_band`,
  `tx_of_lag`). The row needs one named trace hypothesis, **H_ACK_LAG**, which is not proved.
  `xselhold` (`Events9SelMain`) evaluates the rows on the corrected bands (E8Mux) for all
  16 rows; results are in §4.

## 1. Task 1: design_verdict9_sel

`Formal/Core/XAudit/Events9Sel.lean`.

**Assumed:** everything `design_verdict9` assumes except SelOK, i.e. Recog6, OK7, the accepted
log, the per-item checks (guards against `hl.map (san J)`), SatPin, the constants, reset and
H_ARB. Plus:
- SelOK at the virtual pins (part of H_ARB);
- at each real filtered pin and literal: R (the lower bound of the transaction start); B's
  setup `S0 + selHi ≤ R + loC` for every copy; stability of the select gate's input wire at
  `vb k` from `S0 k` for every `t` with `t + selLo ≤ u + hiC`, where `u` is any time the source
  shows transaction `k`; and `sel = selFn vb`.

**Proved:** the conclusion of `design_verdict9`, with no HDsub premise.

**Not covered:** the same as E8Hyp. The premises are statements about the wires; nothing here
says why they hold.

## 2. Task 2: C's H_BUNDLE gives A's select stability

`Formal/Core/XAudit/Events9SelC.lean`.

### 2.1 Which C hypothesis, on which channel, on which A wire

The hypothesis is C's `Ops.Held c` (H_BUNDLE, `Formal/Net/Ops.lean:81`, an argument of
`Capstone.latched_const` / `CapNet.Gcd.gcd_hw_circuit_safe''`): the bus does not change across a
step that starts and ends mid-transaction (`req ∨ ack`). Its time base is the ps tick
(`Formal/Net/Prelim.lean:6`), the same as A's 1-ps steps.

It is applied to one channel per select literal, chosen as follows:

| pin kind (A's certificate) | C channel (B's `ResetCapstoneMapData` row) | request wire | acknowledge wire | bus wire |
|---|---|---|---|---|
| steer `ucond_brN` (st) | the **condition input of the cond_br's join**: the row with acknowledge driver `ucond_brN.uack` whose request driver belongs to the select's producer (`ucmpiK` or `ulink_X`) | the producer's request delay line (end of the routed chain) | `ucond_brN.uack` (the steer's ack, broadcast by the join to both inputs) | the select net (`sel_<bit>` port of the skeleton) |
| mux join / 3-way decode `umuxN` | the **select link's output channel** `X` (row with request net `X_req`, `ulink_X` latching the select) | `ulink_X` request delay-line end | the consumer's ack (from the row) | the latch output |

On all 4 seeds, all 126 real select literals map, with 0 unresolved. 6 of them are the 2-bit
index `n_index_97` of `umux21`, channel `g249.2`, whose consumer is the rig's `uenv0`.

### 2.2 What is checked and what is trusted

- **`entOK` (decidable; `xselhold` evaluates it on the parsed skeleton):** gate `rg` exists; it
  is a 1-input BUFFER (`k = 1`, `InitSpec (fun v => v 0)`); it reads `dw` and drives exactly
  input `i` of the pin's select gate (`selGate`, the wire `design_verdict9_sel` talks about);
  `dw` is one of the bus wires; all wires exist. `xselhold` finds `rg` and `dw` itself, so the
  map supplies only the channel name, request, acknowledge and bus.
- **Trusted:**
  - that the entry's channel NAME (C's `chanNames` string, e.g. `g167.0`) is the bdc channel
    whose request, acknowledge and bus nets these wires are. The untrusted `mkmap.py` matches
    B's table (RTL instance and net names) against the routed cell names. Delay lines are
    resized by the flow, so a B driver `X.udly.g[29].u` is matched to the END of the routed
    chain `X.udly.chain.g[*]`.
  - Lean never relies on the name: H_BUNDLE is assumed of the channel `chanOf x rq ak ws` of
    A's own trace. The claim "this is C's H_BUNDLE of channel g167.0" is therefore only as good
    as the name match.
- The bus in `chanOf` may be a SUB-list of C's bus (here only the select bit or bits). C's
  H_BUNDLE on the full bus implies it for the sub-bus, because constant bits stay constant.
  The lemma for this, `held_wire`, is stated for the listed wires.

### 2.3 Lean

- `busVal`, `busVal_inj`;
- `chanOf`;
- `held_const`: Held keeps the bus constant on any interval that is mid-transaction at every
  step;
- `held_wire`: every listed bus wire is constant on such an interval;
- `isBuf`, `buf_read`, `route_hold`: a routed arc of band `[lo, hi]` turns a constant on
  `[a, e]` into a constant on `[a + hi, e + lo]`;
- `SelEnt`, `SelEnt.ch`, `entOK`, `entOK_spec`;
- `stab_of_held`: H_BUNDLE plus H_SEL_TX give `design_verdict9_sel`'s stability premise, with
  `S0 = O k + hi(rg)` and `vb = dw` at `O k`;
- **`design_verdict9_selC`**.

**Plain statement of `design_verdict9_selC`.**

Assumed: everything `design_verdict9_sel` assumes except its four select premises. Plus:
- a map `m` with `entOK` at every real filtered literal;
- **H_BUNDLE** (`Held`) of each mapped channel on A's trace;
- **H_SEL_TX**: the channel is mid-transaction at every `s ≥ O k` with
  `s + selLo + lo(rg) ≤ u + hiC`, for every copy and every `u` at which the source shows
  transaction `k`;
- **H_SEL_SETUP**: `O k + hi(rg) + selHi ≤ R k + loC`;
- the transaction-start bound R;
- `sel` = `selFn` of the bus values at `O k`.

Proved: the verdict.

Not covered:
- H_BUNDLE itself. It is a hypothesis in C too: a ps-level bundling contract on the routed wires
  that C's tick model does not derive.
- H_SEL_SETUP. C's tcheck rule E is its band analogue, but no Lean link is made here.
- H_SEL_TX, which §3 reduces further.

## 3. Task 3: the hold half

### 3.1 Source-anchored row (`Formal/Core/XAudit/Events9SelHold.lean`)

- `chainOK d top bot π`: π is a non-empty connected path of existing gate inputs from wire `top`
  (the output of its head gate) down to wire `bot`.
- `holdBand`: for every copy `c`, `hiC c + 1 ≤ D + selLo + lo(rg)`, with `D = plo π` and π
  running from the channel's ACK wire down to the source node's output.
- `holdMargin`: `D + selLo + lo(rg) − hiC − 1` ps.
- `hold_pin_of_band`: `holdBand` IS B's `H_HOLD_PIN` (`LibGapSteer.steer_pin_ok`,
  `F + pr.hi ≤ S1 + ps.lo`) for every source time `u`, with `F = u + 1`, `S1 = u + D`,
  `pr.hi = hiC` and `ps.lo = selLo + lo(rg)`.
- `tx_of_lag`: `holdBand` plus **H_ACK_LAG(D)** give H_SEL_TX. H_ACK_LAG(D): the channel stays
  mid-transaction from `O k` until `D` after every time the source shows transaction `k`.
- **`design_verdict9_selH`**: `design_verdict9_selC` with H_SEL_TX replaced by the checked rows
  plus H_ACK_LAG.

### 3.2 Junction-anchored row (`Formal/Core/XAudit/Events9SelSplit.lean`)

The source-anchored row is pessimistic when the copy path and the ack path share a stretch.
That happens on the mux joins: `umuxN.ujK` reads the select link's controller through the
link's own ~10 ns request delay line, and that line is also on the way to the select channel's
acknowledge. The shared stretch counts at its high end on the copy side and at its low end on
the lag side, and gb (33 % widening) and indep turn that into −0.1 to −5.6 ns. The split row
cuts each copy path after `n + 1` elements.

- `design_beh8_svG` exposes the realisation's copy warp: `G s = tau full (s + 1)`.
- With `top = full.take (n + 1)` and `bot = full.drop (n + 1)`, `G s = tau bot (tau top (s + 1))`.
- `sel_read_split`: one read under a factored warp.
- `selOK_real_split`.
- `junW`: the junction wire.
- `holdBandS`: `phi top − 1 + 1 ≤ plo π + selLo + lo(rg)`, with π running from the ACK down to
  the junction.
- **`design_verdict9_selS`**: the verdict with **H_ACK_LAG_w**. The channel stays
  mid-transaction from `O k` until `plo π` after every `r` with `M (tau bot r) src = 2k+1`,
  i.e. after every time the junction wire shows transaction `k`.

When `n + 1 = full.length` this is the source-anchored row. `xselhold` picks, per copy, the cut
with the best margin among those whose `bot` is a chain of 1-input buffers, so the junction
carries the source's value delayed. Any cut is sound; the choice is search.

### 3.3 What is NOT proved

**H_ACK_LAG / H_ACK_LAG_w** is not proved. It is a causality claim: the acknowledge's fall for
token `k` comes through some netlist path from the junction's fall, so it is no earlier than
the shortest such path. Proving it from SatPin needs the protocol, namely that the other inputs
along the path do not fall early. That is the verdict's own count/wire link at earlier times.
`design_verdict9` obtains that link only from SelOK at all times, so a direct proof is circular.
It needs a time-inductive (causal) version of safe8; suggested next probe.

**Finding (NEGack, §5): `chainOK` does not authenticate the acknowledge wire.** Replacing a
literal's ack by the request wire of an unrelated channel still finds a path, and the row passes
with a margin of 19079 ps. So the identity of the ack wire is TRUSTED map data, exactly like the
channel name. `xselhold` takes the SHORTEST path from the given ack (Bellman-Ford; minimality is
not proved), so the lag it assumes is the smallest that any path from that ack gives.

## 4. Results (E8Mux-corrected bands; `tools-A/xaudit/selhold/run.sh`)

PENDING — table filled from `results/xs_<seed>_<corner>.txt`.

Untrusted Python recomputation (`crosscheck.py`, independent band rebuild and Dijkstra), min
margins in ps, source-anchored / split:

| seed | slow | fast | gb | indep |
|---|---|---|---|---|
| d | 927 / 1125 | 419 / 481 | 296 / 741 | −4246 / −56 |
| 3 | 699 / 982 | 294 / 411 | −139 / 630 | −5635 / −124 |
| 4 | 648 / 1055 | 301 / 476 | −701 / 744 | −5224 / 73 |
| 5 | 788 / 1077 | 357 / 475 | 103 / 733 | −5268 / 26 |

## 5. Negative controls (seed d slow)

- NEGhold: the stage-pin arc `ulink_n_falseResult_77.ctl.u.u/I3` has its hi raised by 5000 ps.
  Python predicts margin −4073 / split −2149, so that row must FAIL.
- NEGmap: entry (node 6, pin 0, lit 4) has its bus port swapped (`sel_72861` → `sel_62896`), so
  `entOK` must be false.
- NEGack: a literal's ack is replaced by an unrelated request wire. Expected to PASS; this is the
  finding of §3.3, not a control.

## 6. Check

PENDING.
