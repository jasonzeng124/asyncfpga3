# B-kappa-cppr (probe Bshp): shared path prefixes in the arbiter race conditions vs the κ threshold

Shard B, 2026-10-29. File: `formal/lean/Formal/Cells/KappaCPPR.lean` (530 lines, imports
OnGcdArbKappa, so Mathlib through CornerNat). Scratch: `/tmp/claude-0/probes/Bshp/ana.py`
(the arithmetic below that is marked "not Lean").

## Answer

**The 0.0443 threshold does not move.** OnGcdArbKappa (Bk3) had already cancelled every arc
that the data shows to be shared by both sides of a condition: the A0 stem (`ac`, `dS_k`) and
the r_k net prefix. Its 18 forms are exactly the CPPR forms of the un-netted conditions. That is
proved here (`fulls_net`, `design_cppr_safe`, `design_cppr_tight`): on the FULL conditions, with
the r prefixes as arcs of any endpoints, every condition holds for κ ≤ 16587/374773 ≈ 0.04426,
and the binding one fails from 33181/749546 ≈ 0.04427 on. The server-credited 0.0802 does not
move either.

What CPPR is worth, where the data has the prefix delays (not Lean, from the same formula):
without cancellation the A0 fork's design κ\* would be 0.0934 (fork1, seed d merge9.uarb1), not
0.3276; `naive_pessimistic` proves one such row.

Going the other way, two of Bk3's cancellations rest on equal numbers or on rise = fall, not on
one physical event. Undoing them moves the mA/nA rows of 4 arbiters each and every fork row; the design minimum stays at 0.0443
(`split_design_safe`). The lowest moved row is fork2 on seed 4 merge12.uarb2, from 0.2165 to
121144/604431 = 0.2004 (`split_fork2_safe/_unsafe`).

The only sharing that is physically possible and not expressible in the data is inside one LUT,
between two input-pin arcs to the SAME output. It cannot touch the binding rows. RT1b and h21 pair
ugrant's O6 with its O5, and with `I5 = 1` (bd_arb.v:92) these come from the two disjoint LUT5
halves. Bracketed by arithmetic (not Lean), it moves only o1x/o2x: o1x's design κ\* goes from
0.0828 to at most 0.0967.

## Problem statement (assumed / proved / not covered)

**Assumed.** A's corner model (`CornerNat`: one shared corner, affine nominal, each arc id within
`1 ± κ`) with one delay per arc id per realization (H_ONE_DELAY). The data is Bar's UNTRUSTED
extraction as transcribed in OnGcdArbKappa (lit reading: FAST_MIN / SLOW_MAX, fs). The source
files' path accounting is taken as their definitions say: OnGcdArbA0 `late/early`, `Rsrv`, `As`,
`A1r`, `A2r`, `mP..nGG`; OnGcdArbFix `m1/m2` with the r prefix `cr`; ArbPin2 `a_k, b_k, c5, c6`
with H_R_SPLIT.

**Proved (generic).**
- `allOK_net`: for any two arc-id lists, the form `ΣP + a ≤ ΣQ + b` holds on every realization
  iff it holds after removing the common multiset one-for-one. `net` gives the intersection C and
  the symmetric difference split by side. `net_disj`: after netting, no id is on both sides.
- `allOK_iff_gen_net` (H_DIV on the net lists): the form holds iff `GenOK` holds on the symmetric
  difference, so that is the exact check. `sandwich_net` is the version without H_DIV:
  sufficient, and necessary within one fs per net arc.
- `genOK_full_iff`: `GenOK` on the full lists ⟺ `GenOK` on the net lists with `2·κ·C_s` added
  to the data side at each endpoint s. That is exactly how pessimistic the uncancelled check is.
  It is sound (`genOK_net_of_full`) and strictly pessimistic (`naive_pessimistic`). In threshold
  terms (arithmetic): κ\* goes from `(R'−D'+b−a)/(R'+D')` to `(R'−D'+b−a)/(R'+D'+2C)`.

**Proved (data).**
- `fulls_common` (decided): the common ids of the 18 un-netted conditions; see the table below.
- `fulls_net` (decided): netting the full conditions gives OnGcdArbKappa's `F_*` forms, up to
  order. `full_iff`: so the full and netted conditions are equivalent in every corner model on
  these ids.
- `design_cppr_safe`: every arbiter in `arbs` (36), every full condition, every r-prefix arc and
  every κ ≤ 16587/374773 gives the form on every realization.
- `design_cppr_tight`: for κ ≥ 33181/749546, the full RT1b of seed 3 merge12.uarb1 fails on some
  realization, for every r2-prefix arc.
- `design_cppr_nonvacuous`: the κ bound can be met, and every model is realised (fast endpoint).
- `splits_common`, `splits_cert`, `split_design_safe`: the per-edge / per-pin variant (below).
  `split_fork2_safe/_unsafe` are its lowest row, with `split_nonvacuous`.

**NOT covered.**
- Sharing inside a LUT (the note's bracket is arithmetic only).
- The `cons` reading. Its endpoints depend on the side, so an arc on both sides is not one
  `CArc`; that reading only makes sense after netting, which is what Bk3 did.
- Per-traversal scatter of one arc at different times.
- The value of κ, and the r-prefix delays: they are not in the extraction, and the theorems hold
  for any value.
- Gate-level consequences beyond Bk3's bridges, which are unchanged.

## Which conditions share arcs, by identity

**Identity information that exists.**
- **Route segments.** Bar splits each routed net's RC tree at its branch points: the A0 tree
  (`ac`, `dS1`, `dS2`, `d12`, `es/e1/e2`, site pins `ps/p1/p2`), the q tree (`cq`, `qs`,
  `qgw`, `pqg`), and the r_k suffixes `rs_k`/`rg_k`. Distinct segments are disjoint pip sets by
  construction, and a common prefix is literally the same wire.
- **r_k prefixes.** The r_k prefix before the ustate/ugrant branch is identified as one wire
  (H_R_SHARED / H_R_SPLIT), but its delay was NOT extracted (`cr` in OnGcdArbFix is "any common
  value").
- **LUT arcs.** These are named by (cell, output, pin). Pin identity is real: ugrant's r2-pin O6
  arc `ag2r` and q-pin O6 arc `ag2` have the same prjxray numbers and are kept as different arcs
  (Bk3 did this right).

**Where identity is missing, or replaced by equal numbers.**
- `aq` is one id for ustate's O6 arc from the A0, q, r1 and r2 pins (H_FLAT_O6, equal numbers
  checked).
- `ac_k` is one id for ua_k's O6 arc from its A0, grant and feedback pins (7g's H_ARC_C).
- `Real7`'s single O6 arc of ugrant has rise = fall.
- prjxray has no rise/fall split, so one id covers both edges of a wire (H_ONE_DELAY).
- prjxray has no decomposition of a pin-to-output arc into input buffer, mux stages and output
  driver.

**Common ids per condition** (`fulls_common`, decided; each is one physical event unless marked):

| condition | common ids cancelled | edge / identity |
|---|---|---|
| fork1, fork2 | `ac`, `dS1` (`dS2`) | the A0 stem; one A0-fall event on both sides. Also, inside 7g: ua_k's `aC` (**H_ARC_C, equal numbers**) |
| mP, nP | none | |
| mG, mGG, nG, nGG | `cr_k` | r_k prefix, one r_k edge |
| mA, nA | `ac`, `dS1` (`dS2`), **`d12`** | `ac` and `dS_k` pair the P-side A0 fall with Rsrv's A0 fall (same event). **`d12` pairs the A0 fall (P) with the A0 RISE in `A2r` (`A1r`)**: rise = fall, H_ONE_DELAY |
| rt1, rt1b, rt1s, rt1bs, h12, h21, o1x, o2x | `cr_k` | r_k prefix, one r_k edge (the release) |

No LUT-arc id is common to both sides of any condition. In particular `aq`'s and `ac_k`'s
collapsed pins never meet across a form, so no cancellation in Bk3's forms rests on H_FLAT_O6.
In ArbPin2's own rows, `cq + qgw + pqg` (the q route into ugrant) is shared by the c5 and c6
reads. No κ form contains both, so this matters only to ArbPin2's q-window ordering (FR/SR/BOX
rows), not to any κ threshold.

## Thresholds

### With every identity-backed cancellation (Lean): unchanged

| | Bk3 (netted forms) | full conditions, CPPR (this file) |
|---|---|---|
| all conditions | 16587/374773 = 0.0443 (s3 merge12.uarb1 RT1b) | **same**: `design_cppr_safe` + `design_cppr_tight` |
| server credited | 138217/1724217 = 0.0802 (s2 merge3.uarb1 h21) | same (the forms are the same, `full_iff`) |

### Without CPPR (arithmetic; κ\* of `GenOK` on the full lists, design minimum)

| form | CPPR κ\* | uncancelled κ\* | row (uncancelled) |
|---|---|---|---|
| fork1 | 0.3276 | 0.0934 | d merge9.uarb1 (`naive_pessimistic` proves this row at κ = 1/5) |
| fork2 | 0.2165 | 0.2076 | d merge9.uarb1 |
| mA | 0.6360 | 0.5194 | d merge9.uarb1 |
| nA | 0.5929 | 0.5686 | 2 merge12.uarb1 |
| r-prefix forms | – | not computable | `cr_k` not extracted; lower for any `cr_k > 0` (`genOK_full_iff`) |

### The two number-based identifications undone (Lean: `splits_*`)

| variant | rows moved | lowest κ\* | design min |
|---|---|---|---|
| mA/nA with `d12` per edge (`Y.s` = rise copy) | 4 + 4 | nA 1392235/2358809 = 0.5902 (s4 merge12.uarb2; was 0.6468) | ≥ 0.0443 (`split_design_safe`) |
| forks without H_ARC_C (A0-pin arc late side, g-pin arc early side) | all 72; design min fork1 0.3276 → 0.3022, fork2 0.2165 → **0.2004** (s4 merge12.uarb2) | `split_fork2_safe` ≤ 121144/604431, `split_fork2_unsafe` ≥ 242303/1208862 | ≥ 0.0443 |

### Sharing inside a LUT (arithmetic only, an upper bracket)

On opposite sides of a form, pairs of arcs of the same LUT occur only on ugrant:
- rt1, rt1s, h12: `ag1r` vs `ag2`;
- rt1b, rt1bs, h21: `ag2r` vs `ag1q`;
- o1x: `ag2r` vs `ag2`;
- o2x: `ag1r` vs `ag1q`.

Suppose the two arcs of a pair shared a component s ≤ min of the pair at each endpoint. The exact
check is then `GenOK` with relief `2κ·s` (`genOK_full_iff` with C = [s]), and κ\* rises at most to
`(R−D+b−a)/(R+D−2·min)`.
- **Same output** (o1x: both O6 from the upper LUT5; o2x: both O5 from the lower): the two pins
  can share the later mux stages and the output driver. The design minimum stays **0.0443** and
  the srv one 0.0802. o1x goes 0.0828 → ≤ 0.0967 and o2x 0.1483 → ≤ 0.1657.
- **Opposite outputs** (rt1*, h12, h21): with `I5 = 1`, O5 is the lower LUT5 and O6 the upper.
  The two arcs come from different pins through disjoint halves, so nothing is shared beyond the
  die corner. Ignoring that structure entirely, the bracket would be 0.0443 → ≤ 0.0503
  (rt1b) and 0.0802 → ≤ 0.0930 (h21). That is an upper bound, not a claim.

## Check

    /tmp/claude-0/probes/Bshp/bcheck.py Formal/Cells/KappaCPPR.lean   (from formal/lean)
    == Formal/Cells/KappaCPPR.lean: OK      (~45 s once OnGcdArbKappa's olean exists; no warnings)

`bcheck.py` here is `/tmp/claude-0/btools/bcheck.py` with one fix. Its package path
`.lake/packages/proofwidget` does not exist (the package is `proofwidgets`), so every Mathlib
closure failed with "unknown module prefix 'ProofWidgets'". The copy goes through the same
slot.sh and private olean dir. ConstraintsKappa and OnGcdArbKappa compiled under it (real
Mathlib).

- `#print axioms` (scratch, removed): every headline theorem uses only
  `[propext, Classical.choice, Quot.sound]` or `[propext]`.
- No sorry, admit, axiom or native_decide. The data checks are `decide +kernel`.
- Mutations, all killed: fork2 split κ\* 121144 → 121145; tight κu 33181 → 33180.
