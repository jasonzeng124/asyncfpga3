# B-ipow-cells-t (probe Bfc): timed feedback contracts `FbCelT` for ipow

Lean: `formal/lean/Formal/Cells/IpowCellsT.lean`. It is core only: it imports
`Formal.Cells.ContractBridge` and `Formal.Cells.LutFbBridge`, and neither file is edited.
It checked OK with `/tmp/claude-0/btools/bcheck.py` (autoImplicit=false). There is no
sorry, axiom or native_decide in it. `#print axioms` (run from a scratch companion file,
since removed) on the 12 headline theorems gives `[propext, Classical.choice, Quot.sound]`.

## The finding being fixed

`ContractBridge.fbCel_iff_si` proves that IpowCells' `FbCel F p o` is equivalent to the
bare SI step. The reason is that `FbCel` quantifies existentially over three things:

- the feedback trace `qp`;
- the bounds `lo hi`;
- the H_RT_FB field.

The ideal route `qp = o`, `lo = hi = 0` always satisfies them. So the feedback contracts
in IpowCells / ContractBridge carry no timing content. The same goes for the notes
`B-ipow-cells.md` and `B-contract-bridge.md`, and for `ipow_safe_of_contracts`.

## The repair

`FbCelT F p o r` makes the route `r = ⟨qp, lo, hi⟩` a **parameter** (`FbRoute`). It is
pinned per feedback LUT, either to routed values or to symbolic per-cell constants. Its
fields are:

| field | statement |
|---|---|
| H_LUT_FB | `LutFb F p r.qp o` |
| H_FB_POS | `1 ≤ r.lo` (new: excludes the ideal route) |
| H_FB_ROUTE | `BoundedDelay r.lo r.hi o r.qp` |
| H_FB_RST | `r.qp 0 = o 0` |
| H_RT_FB | `RespAfter r.hi p o` |

`ContractT` is IpowCells' `Contract` with each `FbCel` field replaced by `FbCelT` on the
operator's routes `rt o i`. The route slots are:

- slot 0: fork ack, join req, link ctl, `ua1`, `uj0`;
- mux slots 1/2/3: `uj1`, `uxa`, `uya`;
- amerge slot 1: `ua2`.

All other fields are unchanged.

## Results

**What `FbCelT` gives C.**

- `FbCelT.si`: the SI step.
- `FbCelT.fbFirst`: H_FB_FIRST on the *routed* pin, which is what OpsGen's bindings
  consume, via C-10k's `fbFirst_of_resp`.
- `FbCelT.toFbCel`: the old `FbCel`.
- `contract_of_contractT` and `ipow_safe_of_contractsT`: C-8y's ipow safety follows from
  the 83 timed contracts, for every route assignment `rt`.

**The timing content is real.**

- `Gap.gap_exact` is exact. Take a 2-input C-element whose environment answers the output
  edge `g` ticks later (`Gap.x/o`), and a transport feedback route of delay `d ≥ 1`. Then
  `FbCelT` holds **iff `d ≤ g`**: this is tcheck Rc's `fb_hi ≤ resp_lo`. The SI step and
  `FbCel` hold for every `g`.
- `Gap.gap_reject`: no route with `hi > g` meets `FbCelT`.
- `Gap.si_not_fbCelT` (g = 0): the SI step and `FbCel` hold and the node switches, but
  **no route at all** meets `FbCelT`. So even the existential closure of `FbCelT` is
  strictly stronger than SI. The ingredients are `FbCelT.hi_pos` (H_FB_POS forces
  `hi ≥ 1` on a switching node) and the rejection above.

**`FbCelT` from B's physical model.** This uses LutFbBridge's lemmas `c2_lutFb`,
`link_lutFb`, `node_steps`, `cc_*` and `s_*`, plus the new `respAfter_of_steps`.

- `c2_fbCelT` (`bd_c2`) and `link_fbCelT` (`bd_link` ctl, `bd_c2n`) derive `FbCelT` with
  the *physical* feedback wire `⟨qp, wl, wh⟩` as the pinned route.
- The physical model is: Win LUT band `[lo, hi]`, H_NO_REVERT, `WinDelay wl wh` wire, the
  four-phase `EnvC`/`Env1`, and `Timing1` (H_RST_LONG, H_LAT).
- H_RT_FB is **derived**, not assumed. H_LAT gives `wh ≤ min Es Ea`, so every input
  departs at least `wh` after the node's last edge. H_RST_LONG covers the first
  departures.
- New named hypotheses:
  - H_WIRE_POS: `1 ≤ wl`.
  - H_FB_PWR: the feedback pin is 0 for `t < wh`, where `WinDelay` says nothing.
  - H_IN_RST: the input pins are 0 during reset. `EnvC`/`Env1` leave them free there,
    and `RespAfter` speaks about every `t`.
- Instances in IpowCells' encodings:
  - `cgate2_fbCelT` and `fork2_ack_fbCelT` (lands on `ForkCT.ack` for N = 2; join N = 2
    is the same cell);
  - `ack_fbCelT`: arbiter `ua1`/`ua2` and mux `uxa`/`uya`.

**Non-vacuity.**

- `ipow_contractsT_satisfiable`: for **every** pinned bound assignment with `L o i ≥ 1`
  (any `H`), one run with b = 3, e = 7 meets all 83 `ContractT`s on routes with exactly
  those bounds, together with H_BUNDLE and H_START_ONCE. It is the all-quiet run; network
  liveness is still open.
- `c2_fbCelT_witness`: the real switching `bd_c2` loop of `LutFbBridge.c2_witness` (LUT
  `[1, 2]`, wire 1) meets `FbCelT` on route `⟨sq 7, 1, 1⟩`, and the node toggles.

## NOT covered (open)

- **No routed numbers.** No ipow route exists, so the routes are symbolic. gcd_hw's routed
  RT_FB data (C's RtFbGcd*) is not wired in.
- **No physical derivation of `FbCelT`** for:
  - `bd_c3`/`bd_c4` (fork/join arity 3–4);
  - the 5-input C-tree;
  - mux `uj0`/`uj1` (5-pin LUTs with the select).

  These stay `FbCelT` hypotheses with pinned routes. LutFbBridge2 is uncommitted work by
  another probe and was not used.
- **No network-level derivation of `EnvC`/`Env1`.** So there is no switching run meeting
  `ContractT` at all 83 operators.
- **Not derived:** H_IN_RST and H_FB_PWR.
- **Non-feedback fields** (H_SEL_PIN, H_DELAY_LUMPED, H_CTREE_ATOMIC, arbiter grants) are
  exactly as in IpowCells/ContractBridge.
