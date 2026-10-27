# A-kapres: the indep residuals of gcd_hw under the settled corner model (shard A)

## Verdict

**Under the corner model (shared corner c plus local scatter κ), the indep residual items are
almost all artefacts of the indep band.**

- Seeds d, 3 and 4: every timing residual item of A-events6's indep run is discharged on the
  whole corner interval c ∈ [0, 1] at κ = 0.10, the largest κ asked for. By containment (§2) they
  are then discharged at every κ ≤ 0.10. These are 9, 13 and 10 items, Back pins and lines.
- Seed 5: 7 of its 8 indep timing items are discharged at κ = 0.10.
- **The one exception is `urig.uenv1.u` pin1 on seed 5**, the rig environment
  `uenv1 ← uenv0`, a Back pin. It is the same item that fails gb by −61 ps.
  - **Discharged at κ = 0.05** on the whole interval, and so at κ = 0.02 and κ = 0.
  - **Not discharged at κ = 0.0906 or at κ = 0.10.** It fails at real point corners, not only on
    cells:
    - at κ = 0.10, at every point corner tried, from c = 0 (margin −5 ps) to c = 1 (−48 ps);
    - at κ = 0.0906, at every point corner with c ≥ 3/16 (margin 0 at 3/16, down to −29 ps at
      c = 1). The corners c ≤ 1/8 pass.
  - At the slow corner c = 1 the margin is 186 ps at κ = 0 (A-events6's slow run), 44 at 0.06,
    21 at 0.07 and **−2 at 0.08**. So the checker's κ limit for this pin at the slow corner lies
    in (0.07, 0.08).
- **No residual item survives at every corner at κ = 0.** At κ = 0, every cover cell of every
  seed has exactly A-events6's 45 structural residual items and no timing item.
- **So there is no timing finding under the model at κ = 0.** The one finding for κ ≥ 0.08 is
  `uenv1` pin1 on seed 5. That is the rig environment, not the gcd kernel. It sits at about the
  median ring scatter (8.5 %, CLAUDE.md) and below rule A's 1/11.

The checker is **xevents5** (A-events6: `Events6.design_verdict`, the committed
`Formal/Core/XAudit/Events5Main.lean`). Events7 is being rebuilt by another probe, so it was not
used. Consequently:
- every row still carries A-events6's 45 structural residual items (U3, W-E4x, cascade, the 6
  guarded delay lines);
- the 6 guarded delay lines enter as a `PinOK` obligation that is false in general (A-events6 §3).

This probe is about the timing items only. In every cell of every cover, the structural set was
exactly the slow-corner 45 ("structural items beyond the slow-corner 45: none" in `table.txt`).

## 1. The band (`kapres/cornerband.py`)

**The model is exactly Corner.lean / CornerNat.lean:**
- **H-affine**: the nominal delay is `lerp F S c = (1-c)F + cS`.
- **SharedCorner**: one `c ∈ [0, 1]` for all arcs.
- **Scat κ**: `(1-κ)·nom ≤ d ≤ (1+κ)·nom`.

**One point the model leaves open: what F and S are for an arc.** prjxray gives
`(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`; `CArc` wants one fast and one slow number.
- I take the union over every admissible choice, `F ∈ [FAST_MIN, FAST_MAX]` and
  `S ∈ [SLOW_MIN, SLOW_MAX]`.
- `lerp` is nondecreasing in F and in S for `c ∈ [0, 1]`.
- So for a corner cell `[ca, cb]`, the band of arc e is
  `[⌊(1-κ)·min_{c∈{ca,cb}} lerp(Fmin, Smin, c)⌋, ⌈(1+κ)·max_{c∈{ca,cb}} lerp(Fmax, Smax, c)⌉]`,
  computed in exact rationals and rounded outward.
- The inputs are the committed one-corner band files (`fast` = [FAST_MIN, FAST_MAX], `slow` =
  [SLOW_MIN, SLOW_MAX]; `routed2x.py`, ps, already rounded outward). Gate bands there are
  min-lo / max-hi over IOPATH rows. The same lerp bound holds row by row, so it holds for the
  aggregate.

**Checks of the band file:**
- At `ca = cb = 1`, κ = 0, the band file equals `slow` arc for arc.
- `xevents5` on it reproduces A-events6's `xe5_3_slow.txt` byte for byte.
- At `ca = cb = 0`, κ = 0, it equals `fast` except on the data quirk below.

**Data quirk.** On 2 to 20 arcs per seed (d 20, 3 7, 4 8, 5 2; all LUT5/LUT6 pins inside delay
lines), the committed FAST bands have lo > hi (prjxray FAST_MIN > FAST_MAX).
- `Parse.toSteps` reads such a band as [lo, lo].
- cornerband takes the hull [min, max] instead, which contains both readings.
- Nothing here depends on these arcs. The fast runs of A-events6 should be read with this in mind.

## 2. Why a finite grid covers the continuum (soundness of the sweep)

**Lemma (cell cover; argued here, not in Lean).** Let `0 ≤ ca ≤ c ≤ cb ≤ 1` and let `F, S` be
any admissible endpoints. Then
`(1-κ)·min(lerp(Fmin,Smin,ca), lerp(Fmin,Smin,cb)) ≤ (1-κ)·lerp(F,S,c)` and
`(1+κ)·lerp(F,S,c) ≤ (1+κ)·max(lerp(Fmax,Smax,ca), lerp(Fmax,Smax,cb))`.

So every delay the model allows at corner c lies in the cell band.

Proof:
1. Write `c = lerp ca cb t` with `t ∈ [0, 1]`.
2. Then `lerp F S c = lerp (lerp F S ca) (lerp F S cb) t`, a ring identity.
3. `Corner.lerp_ge_of_ends` (an affine function that is ≥ m at both ends is ≥ m on [0, 1]) gives
   the lo side. The hi side is the same lemma applied to the negated function.
4. `(1-c)` and `c` are ≥ 0, so lerp is monotone in F and S.
5. `0 ≤ κ ≤ 1` makes both factors ≥ 0.
6. Rounding is outward, as in `CornerNat.scat_band`.

**Consequences:**
- xevents5's verdict (`design_verdict`, sound for every per-pin behaviour with delays in the
  bands) for the cell band covers every shared corner in the cell.
- A list of cells whose union is [0, 1] covers the continuum. `table.py` checks that every cover
  is contiguous from 0 to 1.

**Lemma (containment).** If `κ' ≥ κ` and `[ca', cb'] ⊇ [ca, cb]`, the band of every arc at
`(κ', ca', cb')` contains the band at `(κ, ca, cb)`. A verdict for the wider bands applies to
every behaviour in the narrower ones, with the same residual set. So:
- κ is swept in descending order;
- a cell that is clean at κ' is not re-run at a smaller κ (`implied_clean`; `summary.json` names
  the run that covers each cell).

**No CornerDiff lemma covers this.** CornerDiff is about difference scatter. The closest
statements are `Corner.lerp_ge_of_ends`, `corner_refines_band` and `CornerNat.scat_band` /
`band_sub_ind`.

**Proposed Lean statement for the lead** (about 20 lines, Mathlib `linarith` / `nlinarith`;
not written, because Mathlib was not built during this probe):

    theorem Corner.cell_band {F S ca cb c κ : ℝ} (hca : 0 ≤ ca) (hcab : ca ≤ c) (hcb : c ≤ cb)
      (hcb1 : cb ≤ 1) (hκ0 : 0 ≤ κ) (hκ1 : κ ≤ 1) :
      (1-κ) * min (lerp F S ca) (lerp F S cb) ≤ (1-κ) * lerp F S c ∧
      (1+κ) * lerp F S c ≤ (1+κ) * max (lerp F S ca) (lerp F S cb)

**Corners vs cells.**
- A point cell `[c, c]` that fails shows the checker cannot discharge the item **at that
  corner**.
- A failing cell of width > 0 may be an artefact of the cell's own spread: the lo of an arc is
  taken at `ca` and the hi at `cb`.
- **The refinement rule:**
  1. Start from 8 cells.
  2. When a cell has a timing item, run its two end corners as point cells.
  3. Bisect the cell (down to 1/32) only if some item passes at both ends.
  4. Leave the cell unrefined if every item fails at an end corner: that item fails at that
     corner, and no refinement can discharge it.

## 3. Results (`kapres/table.txt`, `runs/<seed>/summary.json`)

**Grid used per seed** (leaf cells of the final cover):
- d: 8 cells of 1/8;
- 3: 20 cells of 1/16 and 1/32. The H_ARB virtual line `control_merge12` grant needs narrow
  cells near both ends; it fails at −207 to −270 ps on 1/8 cells but passes at every point
  corner;
- 4: 8 cells of 1/8;
- 5: 16 to 18 cells of 1/16 and 1/32.

| seed | indep timing items (A-events6) | largest κ in {0, .02, .05, .0906, .10} discharged on all of c ∈ [0,1] | fails at point corners |
|---|---|---|---|
| d | 6 Back (`ulink_n_falseResult_41` s2 p1 −269, `ulink_n_trueResult_28` s2 p0 −72 / p1 −59, `umux15.uya` p1 −26, `control_merge2.uarb1.ua2` p1 −53, `control_merge4.uarb1.ua2` p0 −88), 3 Line (`ulink_n168` s0 p0 −444, arb `control_merge12` grant −2812, arb `control_merge4` grant −283) | **all 0.10** | none |
| 3 | 6 Back (`ulink_n_falseResult_77` p1 −344, `ulink_n143` s0 p1 −242, `umux4.uya` p1 −217, `ulink_n_trueResult_28` s1 p1 −201 / p0 −35, `umux9.uj0` p1 −30), 7 Line (`ulink_n139` −805, `ulink_n_falseResult_37` s1 −172, `ulink_n_index_97` s0 −119, `control_merge12_f` p1 −119, `ulink_n_falseResult_39` s0 −2, arb merge12 −2750, arb merge4 −2422) | **all 0.10** | none |
| 4 | 8 Back (`control_merge10.uarb1.ua1` p0 −246, `umux9.uj1` p1 −222, `umux3.uya` p1 −146, `ulink_n143` s0 p1 −132, `umux3.uj1` p0 −103, `ulink_n_trueResult_72` s1 p1 −95, `ulink_n_trueResult_24` s1 p1 −93, `ulink_n_falseResult_55` s0 p1 −36), 2 Line (arb merge12 −2204, arb merge4 −760) | **all 0.10** | none |
| 5 | 6 Back (`uenv1` p1 −474, `ulink_n_trueResult_28` s0 p1 −387, `ulink_n_falseResult_55` s2 p1 −252, `control_merge4.uarb1.ua2` p1 −99, `ulink_n_falseResult_91` s1 p0 −31, `control_merge12_f` p0 −29), 2 Line (arb merge12 −2991, arb merge4 −1299) | **0.10 for all but `uenv1`; `urig.uenv1.u` pin1: 0.05** | `uenv1` p1: κ = 0.10 at every point corner tried (c = 0 to 1 in steps of 1/16: −5 to −48 ps); κ = 0.0906 at c ≥ 3/16 (0 to −29 ps) |

All names have the prefix `urig.udut.` (except `urig.uenv1`); "s1 p0" means `.many.stage[1].u.ctl.u.u pin0`.

**Surviving at every corner at κ = 0: none.** The only item not discharged at some κ in the set is
seed 5's `urig.uenv1.u` pin1 (Back):
- κ = 0.10: it fails at every corner tried, by −5 ps (c = 0) to −48 ps (c = 1);
- κ = 0.0906: it fails at every corner c ≥ 3/16, by 0 to −29 ps.

**Beyond κ = 0.10** (`kapres/beyond.txt`; point corners c = 0 and c = 1 only, a necessary
condition, not a cover):
- Seeds d and 4 have no timing item at κ = 0.15 at c = 0 or c = 1. At κ = 0.1988 (rule E's
  `kappaE`), only the arb `control_merge12` grant line fails at c = 1 (d −679, 4 −417).
- Seed 3 already fails at κ = 0.15 on the two arb grant lines (merge12 −46 at c = 0, −531 at
  c = 1; merge4 −159 at c = 1).
- Every Back pin of d, 3 and 4 still passes at κ = 0.1988, at c = 0 and c = 1; the Back minima
  there are 52 to 266 ps.
- Those arb lines are the H_ARB virtual pins whose window A-events6 already flags as an artefact
  of the conservative virtual band. So these are not route findings.

## 4. What this does NOT cover

- **The checker is xevents5, not Events7.** The 45 structural residual items stay hypotheses.
  Among them is the false `PinOK` for the 6 guarded delay lines (A-events6). GuardOK, SelOK and
  H_ARB are hypotheses as before.
- **"Discharged" means** that the item is not a residual hypothesis of `design_verdict` for the
  cell bands. It is no stronger than A-events6's verdict.
- **"Fails at a corner" means** that the checker cannot discharge the item there. Because the
  checker is conservative (min-plus walks, per-pin warps anywhere in the band, `dw` of virtual
  lines), it is **not** a counterexample trace. `uenv1` at κ ≥ 0.08 is a finding of the checker,
  not a demonstrated failure.
- **The model's own hypotheses:**
  - H-affine in c;
  - one shared corner for the whole run (Corner.lean only needs one per handshake);
  - symmetric relative scatter κ with no additive θ;
  - endpoints only as known as prjxray's per-corner [MIN, MAX].
  - The ring data say per-path κ can reach 0.31 (`guard_refuted_by_7link_rings`). At such κ, the
    present per-arc κ check is not a sign-off.
- **Inherited from the checker's band reading:** sub-ps lo = 0 arcs are raised to 1 ps, and the
  hi of a lo > hi fast arc is raised to lo (§1).
- **The cell-cover lemma (§2) is argued, not proved in Lean.** The statement is given above.

## Files

| file | what |
|---|---|
| `formal/tools-A/xaudit/kapres/cornerband.py` | corner-model band file for a cell `[ca, cb]` and κ (exact rationals, outward rounding) |
| `…/kapres/kapres.py` | sweep driver: descending κ, adaptive cell cover, end-corner point runs, `implied_clean` reuse; writes `runs/<seed>/k<κ>_<ca>_<cb>.txt` (xevents5 stdout) and `runs/<seed>/summary.json` |
| `…/kapres/table.py` → `table.txt` | per item: indep / gb margin, largest κ discharged, failing point corners |
| `…/kapres/run.sh` | restores the inputs from the committed `.xz` files and runs all 4 seeds |
| `…/kapres/mk.sh`, `mkexe.sh`, `xe5.sh` | private olean overlay of the committed module chain (`/tmp/kapres/olean`), and a native build of the same `Events5Main` (`/tmp/kapres/exe/xevents5`). Every lean / leanc step goes through `slot.sh` |
| `…/kapres/runs/{d,3,4,5}/` | 200 xevents5 outputs plus the summaries |

**Runs.**
- About 200 xevents5 runs, each through `slot.sh`.
- The first runs (`k0_*` for d and 3) used `lean --run`; later runs used the native build. Its
  output on seed 3 slow is byte-identical to A-events6's committed `xe5_3_slow.txt`.
- Failed launches: 2 runs early on printed nothing under load; they were re-run.
  `/tmp/kapres/work/failed.log` is empty for the final sweep.

**Reproduce:**

    tools-A/xaudit/kapres/mk.sh
    tools-A/xaudit/kapres/mkexe.sh   # optional
    tools-A/xaudit/kapres/run.sh
    python3 tools-A/xaudit/kapres/table.py

**Lean.** Nothing new is claimed. No file under `formal/lean` was written, and no lakefile or
root-import change is needed: the `xevents5` stanza already exists.
