# 05 — Timing signoff without STA

## Why STA doesn't apply

- `icetime` and nextpnr STA report Fmax/criticality for a design with no
  clock.
- nextpnr will not build a timing graph at all without `--ignore-loops`.
- `--timing-allow-fail` (needed when a clockless cone sits between
  registers) **silences real failures elsewhere in the same design**.

Ignore P&R timing numbers; gate on the two tiers below.

## Tier 1 — structural audit (pre-route)

Count LUT levels on the post-synthesis netlist: for every data-consuming
element, is the request path structurally deeper than every datapath it
covers? Cheap enough for every build. Reference: `ref/audit_bundling.py`.

Requirements for any equivalent tool:

- **Audit RAM request boundaries, not just latches.** Classify the RAM
  clock pin as request, address/write-data/enables as bundled data; same
  depth-slack rule. On xc7: check delay-chain-clocked capture FFs, skip
  genuine BUFG/PS7-clocked FFs, and treat `BUFG` as a **transparent
  zero-weight** cell rather than a source — as a source it truncates the
  strobe cone and the check passes vacuously.
- **Warn loudly on anything unclassifiable.** A primitive with no config
  entry must not be silently passed.

Hierarchical instance names survive `synth_ice40`'s flatten with `.`
separators, so per-element probe points stay addressable
(`<latch>.mem.bitcell[k].u0.u0`).

## Tier 2 — routed-delay signoff (the gate)

Per data-consuming element, from the same fork event:

```
min routed request arrival  >=  max routed data arrival  +  guardband
```

Reference: `ref/xc7/timing_signoff.py` (docstring carries the soundness
argument).

| Aspect | Rule |
|---|---|
| Guardband | `need = max(0.2 × data_arrival, 200 ps)`, i.e. `req >= max(1.2 × data, data + 200 ps)` — the conjunction. Ratio covers proportional PVT/model mismatch between the racing paths; the flat floor covers additive skew on short paths. Delay data is single-corner. |
| Same-chain differences | flat floor **only** — proportional scaling cannot flip the sign of a difference between two taps on one chain, and the ratio would gate on a shared prefix that cancels exactly |
| Loops | no global timing graph; each check is a bounded forward traversal stopping at the next handshake element's cells. Soundness is inductive per hop. |
| Failure modes | fail on tracing inconsistency and on any consumer never compared — "nothing to report" must be unreachable by accident |

## Delay sources

| Target | Source |
|---|---|
| iCE40 | `nextpnr-ice40 --sdf X.sdf` — full IOPATH + INTERCONNECT keyed by yosys names, hierarchical paths preserved |
| xc7 | `nextpnr-xilinx --sdf`, **or** `--post-route timing_dump.py` via the local Python bindings |

`--sdf` works on nextpnr-xilinx (confirmed 2026-07-28); notes claiming
otherwise are stale. The pybinding route (`ctx.getCellDelay` /
`ctx.getRouteDelayPs`, `01`) remains available and is what
`ref/xc7/timing_dump.py` uses.

Any post-route delay extraction **must** resolve LUT inputs back to
logical pins via the pre-place JSON (`04` §5b). Delays are single-corner
ps.

## Calibration (empirical, per target)

Per-hop routed delay, measured from real delay-chain `chain_ps / T`:

| Target | ps/hop |
|---|---|
| iCE40 HX8K | ~1090 |
| xc7z010 | ~478 (median) |

**Do not derive these from raw LUT-arc delays.** xc7 arcs are ~117–152 ps;
routing is ~74% of a hop ⇒ arc-only figures are ~3× wrong.

Validated depth-scale / margin settings:

| Target | Setting |
|---|---|
| iCE40 | depth-scale 6/5, margin 3 |
| xc7 | depth-scale 12/5, margin 8 |

An ice40 chain hop routes at ~3 ns ≈ 1 data level; an xc7 chain hop is
~450 ps against ~750 ps+ per routed wide-bus level, so hop-for-level
request chains are structurally short on xc7 — and xc7 placement scatter
(±1 ns per net **between builds**) needs extra constant margin. Calibration
points against measured scatter, not derived laws.

Make hardware build scripts **refuse** designs below the target's margin.
A design at an ice40-calibrated margin can pass golden vectors on xc7
hardware by routing luck; that is not signoff.

## Anti-patterns

| Anti-pattern | Detail |
|---|---|
| Vacuous passes | a BUFG treated as a depth-0 source truncated a strobe cone ⇒ the boundary reported `req 0.00` and passed; a SAT checker that dropped INIT proved constant-0 ≡ constant-0. Both emitted green output. Assert structural preconditions: proof counts, non-zero cone depths, zero unresolved probes. |
| Jitter sims as signoff | randomized-delay sims explore a spread around an idealized model whose margins over-compensate by several factors ⇒ they cannot violate bundling. Retain only for 4-phase *protocol* stress (RTZ tails, capture windows, merge guards) after a handshake-primitive change. |
| Margin without diagnosis | a constant that doesn't fix a race is evidence the mechanism is misunderstood. Scaling two guard delays never fixed a memory-port corruption whose cause was pipelined RTZ overlap between adjacent accesses. |
| Single placement seed | xc7 scatter ±1 ns net-to-net between builds; ice40 Fmax spread ~6 MHz across seeds. Passing 7/8 seeds = thin margin, not an unlucky seed. Keep a `NEXTPNR_SEED` env hook. |

## Expected STA noise

- A design with exactly one real clock (e.g. a RAM strobe) wakes STA up,
  which then reports **false hold violations** latch→WDATA/RADDR: it
  assumes the strobe launched the latch, when address/data are held for
  the whole transaction. Use `--timing-allow-fail` **plus** a checker that
  tolerates only strobe-domain hold errors.
- "No clocks found in design" ×2 from nextpnr-xilinx.
