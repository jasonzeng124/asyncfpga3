# B-arb-amerge-run: every epoch, stitching, and C's AMerge instantiated (probe Barb4)

Three core Lean files (no Mathlib):

| file | lines | contents | check |
|---|---|---|---|
| `formal/lean/Formal/Cells/ArbAMergeRun.lean` | ~920 | the epoch windows WG, WR, WX, hold; H_SEP; `cex_RA1`, `cex_SEP` | OK |
| `formal/lean/Formal/Cells/ArbAMergeRunStitch.lean` | ~490 | `stitch_run`, the schedule class `Plan`, `win_step`, `run_fields`, **`amerge_of_plan`** | OK |
| `formal/lean/Formal/Cells/ArbAMergeRunWit.lean` | ~470 | `amerge_witness` (non-vacuity), `sep_cex_run` (H_SEP is needed) | OK (about 2 min) |

Check command: `/tmp/claude-0/btools/bcheck.py Formal/Cells/ArbAMergeRunWit.lean`. It
compiles all three files.

The files contain no sorry, admit, axiom or native_decide. Bounded trace checks use kernel
`decide +kernel`. `#print axioms` was run from a scratch companion, since deleted. Every
headline theorem gives propext, Quot.sound and Classical.choice, or a subset of them.

The lead must add three imports to `Formal.lean`: `Formal.Cells.ArbAMergeRun`, `...Stitch`
and `...Wit`.

## 1. Epoch windows (`ArbAMergeRun`)

All windows use the form of `e_fields` / `f_fields`:
- the window is `[L, Hz)`;
- nothing is assumed before `L` except the anchor `Anc`: A0's last edge, or the reset past;
- the conclusion is the exact traces and C's six step fields `CF` at every 1 ps tick of
  `[L+M+dz, Hz-1)`, plus grant exclusion.

`srv_lb` is the single H_SERVER_MIN lemma that all windows use.

| epoch | window theorem | assumed (beyond `Run`, H_M, `ZLine`, the input pattern) | new race / counter |
|---|---|---|---|
| grant from idle, client 1; a waiter may arrive at `v` once client 1 is ahead at ustate (`u+wr1s ≤ v+wr2s`) | `wg_fields`, `wg_excl` | `RowsG`: tick-causal, H_GRANT_IN_A0_LOW `GU ≤ RU+smin`, H_ZR, H_ACK_IN_PHASE, H_DZ | none (q never moves) |
| client 1 releases with nobody waiting; it may re-request at any `u` after its ack fell (`TF < u`): the solo client and the same client winning twice; with `u ≥ Hz` it is a release to idle | `wr_fields`, `wr_excl` | `RowsR`, four-phase `TF < u`, RT2a, **RA1** | **RA1** (H_CEL_LOOP): `TF + wfa1 ≤ GU + wg1`. `cex_RA1`: at slack −1, ua1 sees (g1=1, fb=1) and re-raises A1 while A0 is low, so **C's `xa` fails**. Side condition `GU+wg1+c1r ≤ TA2` |
| grant from idle to client 2 (q flips), client 1 may follow at `u` | `wx_fields`, `wx_excl`, `wx_all` | `RowsX`, **H_SEP** (`SepX`) | `cex_SEP` (below) |
| idle race (both requests at an idle arbiter) | `race_fields` | **H_SEP** = `HSep u v`: `u+wr1s ≤ v+wr2s` (client 1 ahead: epoch WG) ∨ `SepX v u` (client 2 first by more than the loop: epoch WX) | the metastable middle is excluded |
| hold (mode `I`/`H1`/`H2`, constant inputs) | `hold_st`, `hold_fields` | `Fix m c1 c2` (by `decide`) | none |

`SepX` (H_SEP, client 2 first, with `QX = v+wr2s+qf`) has three clauses:
- **q** (ustate's loop): `QX + wfb ≤ u + wr1s`;
- **r** (R0): `RX ≤ u + wr1s + Rr1`, where `RX = max(v+wr2s+Rr2, QX+wfb+Rrq)`;
- **g** (g1, two arc views): `QX + wq + g1rq ≤ u + wr1g + g1r1` and `QX + wq + g1fq ≤ u + wr1g + g1f1`.

The r clause is sufficient, not exact, when `Rr2 > qf + wfb + Rrq`.

**`cex_SEP`** (universal). Assumptions:
- client 1 overtakes at ustate: `v+wr2s ≤ u+wr1s`;
- H_SEP's loop clause is missed by exactly 1 ps;
- side conditions as for `cex_Q`: `qr+wfb ≥ 2`, `g2r = g2f`, `QX < TA2`, and `v+wr2g ≤ QX+wq`
  (r2 reaches ugrant before q's fall does).

Then g2 rises and falls while r2 is high, so **C's H_ARB2 fails**.

## 2. Stitching (`ArbAMergeRunStitch`)

**`stitch_run`** is abstract. Its hypotheses:
- the start condition holds for window 0;
- each window, given its start condition, yields `F` on its range and the next window's start
  condition;
- consecutive ranges overlap;
- the windows reach every time.

It concludes that `F` holds at every tick.

The concrete form:
- **`StartC`**: the start mode is settled on `[L, first)`, R0 holds the mode value since the
  anchor `a`, and `Anc` holds.
- **`EndC`**: the end mode is settled on `[Lend, Hz)`, R0 holds since `aEnd`, and `Anc(aEnd)`
  holds.
- **`Link`**: the start mode equals the end mode, the next `a` equals `aEnd`, `Lend ≤ L'`,
  `first' ≤ Hz`, and `L'+M+dz+1 ≤ Hz`.
- **`win_step`**: discharges "start ⇒ fields ∧ end" for all seven kinds, the E1/E2 handovers
  of `ArbAMerge` included.
- **`run_fields`**: `CF` and exclusion hold at every `t ≥ 0` of any run scheduled by a `Plan`.

## 3. C's AMerge (`amerge_of_plan`)

**Assumed:**
- `Run D s`, `MB D M`, `ZLine s z dz`;
- a `Plan D M s dz`: an infinite epoch sequence from reset, where epoch 0 is hold-idle from
  the reset past (`rst`: every internal signal at its idle value for `t < 0`), every epoch
  satisfies `EpOK`, consecutive epochs satisfy `Link`, and the windows reach every time;
- **H_DAT**: `z.dat = 2·(won ? y.dat : x.dat) + won`.

**Proved:**
- `AMerge ⟨r1, A1, xd⟩ ⟨r2, A2, yd⟩ ⟨z, A0, zd⟩ g1 g2` at C's tick = 1 ps;
- all 13 fields. H_ARB1, H_ARB2, H_ARB_EXCL, zr, H_AMERGE_RTZ, xa and ya come from
  `run_fields`. The init fields `i1 i2 iz ix iy` come from the reset epoch. `dat` comes from
  H_DAT.

**Non-vacuity (`amerge_witness`).**
- One run from reset, with `Dw` (1 ps per route and arc), a 3 ps pure-delay server and
  dz = 2.
- `Wt_run` checks the run against every gate relation and the server relation at all `t ∈ ℤ`:
  tables on `[0,300)` by kernel `decide`, and the rest by the reset and idle constants.
- Its schedule `Wplan` has these epochs:
  1. reset;
  2. grant from idle at 20, client 2 arriving at 30;
  3. handover 1→2 with an early re-request at 58 (A0 re-rises at 62);
  4. handover 2→1;
  5. a solo re-request (release 120, re-request 128: the same client wins twice);
  6. release to idle;
  7. the idle race with client 2 first (v = 200, u = 205, slack 3 on H_SEP), where q flips;
  8. handover 2→1;
  9. release to idle;
  10. idle for ever (hold epochs).
- `AMerge` holds on this run. The grants and q really move.

**`sep_cex_run`** shows that H_SEP is needed.
- Delays: `Ds` = `Dw` with ustate's fall arc set to 2 ps.
- From reset, r2 rises at 10 and r1 at 12. Every structural hypothesis of `WX` holds, and
  H_SEP's loop clause is missed by exactly 1 ps.
- q makes a 1 ps runt at 13, g1 one at 14 and g2 one at 15. Client 1 then wins.
- Lean proves `¬ CArb s 15` (H_ARB2 fails) and `¬ CArb s 14` (H_ARB1 fails).
- With rise = fall on ustate, the runt would circulate for ever. That is the pure-transport
  artefact of `ArbBinary`; the rise-fast arc kills the runt after one loop.

## 4. Not covered / open

- **The schedule class is one-sided.** These are not covered:
  - client 2 releasing with nobody waiting (mode H2 → idle with q = 0);
  - every epoch starting from idle with q = 0;
  - client 1 granted from q = 0.

  These would need mirrors of WG, WR and WX, mechanical in the style of E2. In the class,
  client 2 releases only while client 1 waits, or never.
- **A waiter arriving while the holder releases is excluded.** In WR, client 2 may arrive only
  after client 1's re-request is ahead of it at ustate. Arrival at any other time is a
  handover race with no window theorem.
- **Two counter lemmas are missing.** SepX's R and G clauses have no counter lemma here; they
  are analogous to `cex_R`/`cex_G` but not proved. The tick rows (`RowsG/R/X`) have none
  either.
- **`cex_RA1` has no concrete run.** It is universal only.
- **The data path is a hypothesis.** `dat` is H_DAT, because B has no timing model of the data
  mux (`won ? in1 : in0`).
- **The server reads R0.** As in `ArbAMerge`, the server reads R0 with `dz ≤ smin`, not z.
- **`Link` and `EpOK` use coarse bounds.** They use the coarse M, and the window overlaps
  (`L'+M+dz+1 ≤ Hz`) are sufficient, not tight.
- **The epoch hypotheses are numeric and per epoch.** They are satisfiable (`amerge_witness`),
  but they are not yet derived from arc inequalities plus C's SendStep, as `races_of_arc1/2`
  did for the handovers.

Scratch: `/tmp/claude-0/probes/Barb4/` holds `sim.py`, `gen.py` and `gen_sep.py`, the
simulators that produced the witness tables. Lean re-checks the tables, so the simulators are
not trusted.
