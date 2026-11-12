# B-arb-amerge: early re-request, z_req and C's AMerge fields for the held bd_arbiter (probe Barb3)

File: `formal/lean/Formal/Cells/ArbAMerge.lean` (1300 lines). It is core Lean and imports
`Formal.Cells.ArbMultiToken`, which brings in 7h and 7j. Check command:
`/tmp/claude-0/btools/bcheck.py Formal/Cells/ArbAMerge.lean`, result **OK**.
It has no sorry, admit, axiom or native_decide. The lead must add
`Formal.Cells.ArbAMerge` to `Formal.lean`.

`#print axioms` was run from a scratch companion, since deleted. Every headline theorem
gives propext, Classical.choice, Quot.sound. The headline theorems are `e_exclusion`,
`e_fields`, `f_exclusion`, `f_fields`, `cex_Q`, `cex_G`, `cex_R`, `cex_Q2`, `cex_G2`,
`cex_R2`, `races_of_arc1/2`, `early_nonvacuous` and `cexG_run`.

## What changed relative to Barb2

* **Windows instead of a full past.** `E1` and `E2` assume their settled state only on
  `[L, t0)`. The only other assumptions are A0's last rise `a ≤ L` and R0 high on
  `[a, L+M)`. So no splicing is needed, and the analysis applies inside any run,
  including a run that starts from reset.
* **The re-request time `u` is free.** It can be any `u > t0`, including before A0's
  re-rise. H_SLOW_REREQ is gone.
* **`z_req` is modelled.** `ZLine s z dz` sets `z t = R0 (t - dz)`, one pure delay with
  rise = fall. H_DZ is `0 ≤ dz ≤ smin`. The server is still 7h's relation on R0 with
  `smin`.

## Results

| theorem | assumed | proved |
|---|---|---|
| `e_exclusion` / `f_exclusion` | `Run`, H_M, `E1`/`E2`, RT1/RT1b (7h/7j arc form), races Q, R, G (or mirrors) | `g1 ∧ g2` never both high on `[L, Hz)`, for every server meeting H_SERVER_MIN |
| `e_fields` / `f_fields` | the same, plus RT2a and the A0 fork (run form), the four-phase client (`T1 < u`), `ZLine`, and the tick rows `Rows1`/`Rows2` | C's **H_ARB1, H_ARB2, zr, H_AMERGE_RTZ, xa, ya** (`CF`, the shapes of `OpsCM.AMerge` verbatim) at every 1 ps tick of `[L+M+dz, Hz-1)` |
| `races_of_arc1/2` | four-phase client, `Arc1`/`Arc2` | the races, from A0-fork-type arc inequalities |
| `early_nonvacuous` | — | one run from reset (all signals low before 0, all delays nonzero: `Dw`, dz = 2, server = pure 3 ps delay) meets every hypothesis of all four window theorems for two consecutive handovers (g2↑ at 39, g1↑ at 63). Both releasers re-request before A0 re-rises (38 < 42, 62 < 66) |

**The races, exact per arc view.** Client 1 releases at `t0` and re-requests at `u`,
with `QB = TA + wa0s + qf`. Each race is a necessary condition for its exact trace;
the counter lemmas below make it tight.

* **Q** (ustate): `QB + wfb ≤ u + wr1s`.
  Mirror: `QBb + wfb ≤ u + wr2s`.
* **R** (R0): `RR ≤ u + wr1s + Rr1`. The fall-arc view is implied, so the note's form
  `QB+wfb+Rfq ≤ u+wr1s+Rr1` is stronger than needed.
  Mirror: `RRb ≤ u + wr2s + Rr2`.
* **G** (g1, per-pin arcs, one inequality per view):
  - `QB + wq + g1rq ≤ u + wr1g + g1r1`;
  - `QB + wq + g1fq ≤ u + wr1g + g1f1`.

  Mirror (g2, flat arcs): `QBb + wq ≤ u + wr2g`.

What race R actually protects is **H_HOLDQ** (`HQ`): A0's re-rise reaches ustate only
after q's reset has come round its own loop (`QB + wfb ≤ TA2 + wa0s`). The q and grant
lemmas take `HQ` directly; `e_HQ` derives it from race R plus the server.

**Arc form.** Assume C's SendStep for the client: it re-requests only when its ack is
low, which gives `T1 < u`, with `T1 ≥ TA + wa01 + c1f`. Then the races follow from
`Arc1`:
- `wa0s+qf+wfb ≤ wa01+c1f+1+wr1s`;
- `…+Rrq ≤ …+wr1s+Rr1`;
- `wa0s+qf+wq+g1rq ≤ wa01+c1f+1+wr1g+g1r1`, and the same for the fall view.

These are A0-fork races: A0↓ → ustate → q → ugrant against A0↓ → ua1 → A1↓ →
client → r1↑ → ugrant. `Arc2` gives the mirror.

**Rows (run form, each named in `Rows1`).**
- `rt1s`: RT1 strict.
- `g1p`: tick causality.
- `a1`: H_GRANT_IN_A0_LOW.
- `zf`, `zrise`: H_ZR. z falls after g1 fell, and z rises after g2 rose (`G2 < RR + dz`).
- `rtz`: the H_AMERGE_RTZ row. A1 has fallen before z re-rises (`T1 < RR + dz`). A2 is
  low then, by H_DZ.
- `x1`, `y1`: H_ACK_IN_PHASE.
- `dz`: H_DZ.

## Counter-runs at slack −1

Each counter lemma keeps every other hypothesis and misses one race by exactly 1 ps.
It then proves, for every such run, that one of C's fields fails.

| lemma | race missed | consequence | side conditions |
|---|---|---|---|
| `cex_Q` | Q | q's reset is undone: g2 rises and falls while r2 = 1, so **H_ARB2 fails** | `qr+wfb ≥ 2`, `g2r = g2f` |
| `cex_G` | G (either view) | g1 makes a runt after q flipped and falls while r1 = 1, so **H_ARB1 fails** | none |
| `cex_R` | R | R0, hence z, rises 1 ps early while neither grant is high, so **zr fails** | z-rise row tight (`G2+1 = RR+dz`); `smin+wa0s+qf+wfb+Rrq ≥ 2` |
| `cex_Q2` | Q2 | **H_ARB1 fails** | `qr = qf`, `g1rq = g1fq`, `qr+wfb ≥ 2` |
| `cex_G2` | G2 | **H_ARB2 fails** | none |
| `cex_R2` | R2 | **zr fails** | z-rise row tight |

**Concrete counter-run, race G only (`cexG_run`).** It runs from reset with `Dg` (`Dw`
with `wq = 3`). The client re-requests at the earliest four-phase instant, `T1 + 1 = 38`.
Race G and `Arc1.gr` both miss by 1 ps. Everything else holds: races Q and R, H_HOLDQ,
RT1, RT2a, the fork and the client. g1 makes a 1 ps runt at 40 with r1 high.

The other five lemmas have no concrete run, so their joint satisfiability is not shown.

Race R alone is NOT tight for exclusion. At slack −1, R0 just rises 1 ps early and
merges with the legitimate rise. Its failure is visible only through C's `zr` field,
and only when the z-rise row is also tight. Exclusion needs H_HOLDQ, which race R
implies with slack `Rrq + smin`.

## Goals vs this probe

1. **Exclusion with early re-request:** done, both directions, on windows. Every race has
   a slack −1 counter lemma. Only race G has a concrete run.
2. **Arbitrary schedules:** only partly done.
   - The windows work inside any run, and `early_nonvacuous` starts from reset.
   - There is NO window theorem for a solo client, a release with no waiter (idle), a
     grant from idle, or the same client winning twice.
   - The windows are not chained into an all-time theorem. The only chain is
     ArbMultiToken's, which still assumes H_SLOW_REREQ.
   - Requests racing at an idle arbiter are the metastable case. They would need a named
     separation hypothesis, and none is modelled.
3. **`z_req` and H_AMERGE_RTZ:** derived on the windows (`CF`'s third clause), from the
   row `T1 < RR + dz` plus H_DZ and the fork.
4. **C's AMerge:** **NOT instantiated.**
   - `e_fields`/`f_fields` give H_ARB1, H_ARB2, zr, RTZ, xa and ya, which is everything
     `amerge_inv` reads at a step except H_ARB_EXCL, and that comes from
     `e_exclusion`/`f_exclusion`.
   - They hold only on the handover windows, not at every tick of a whole run.
   - Missing: the reset and grant-from-idle epochs, the hold periods between windows
     (Barb2's `persist`, not yet re-done with the z line and acks), the stitching, and
     the fields `i1`, `i2`, `iz`, `ix`, `iy` (true in `early_nonvacuous`'s run, but not a
     theorem over a schedule class) and `dat`, which has no data model.
   - Estimated cost: one window theorem per remaining epoch type (about 300 lines each, in
     the style used here), plus a chain like ArbMultiToken's.

Scratch: `/tmp/claude-0/probes/Barb3/sim.py`, the simulator that produced the witness
traces. Lean re-checks those traces against every gate relation for all t ∈ ℤ.
