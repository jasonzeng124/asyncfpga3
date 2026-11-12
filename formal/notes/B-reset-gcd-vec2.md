# B-reset-gcd-vec2: the per-cell reset model derived from the network run, and the 21 first-wave cells

Probe Bfw (shard B), 2026-10-27. Follows `B-reset-gcd-vec.md` (Brst:
`CellRun`, `gcd_reset_vec`), `B-reset-gcd.md` (Rst2: `gNet`, GMW reset and
release) and `B-reset-gcd-wave.md` (Rst3: first wave).

No route, no board, no toolchain run. The network is Rst2's elaborated RTL
import (default matched-delay sizes, plus `gcd_rig`). It is not a routed
netlist. Every time below is a GMW model step.

## File and check

- `formal/lean/Formal/Cells/ResetGcdVec2.lean` (core Lean, about 1100 lines).
  It imports `ResetGcdVec` and `LibEndMemMlink` (for `lutK_ofBool`), both
  read-only.
- Check: `scratchpad/bchk.sh formal/lean/Formal/Cells/ResetGcdVec2.lean`
  prints `[bchk] OK` with no warnings. The whole file takes about 60 s wall
  and 1.79 GB peak RSS. That covers 9 node chunks of 400 (`ca0..ca8`), the
  census, and the two counter-run certificates.
- `formal/scan.py` passes. There is no sorry, admit, axiom, native_decide,
  opaque or extern. Every certificate is checked with `decide +kernel`.
- `#print axioms` (scratch file, not in the repo):
  - `vec2_census`: propext.
  - `counter_uori2`, `counter_br9`, `nonvac_net`: propext, Quot.sound.
  - Everything else: propext, Classical.choice, Quot.sound.
- The lead still has to add the file to `Formal.lean`.

## Part 1: `CellRun` from the network `Run`

`CellRun` is Brst's per-cell model. Its `H_TREE` says that the root EQUALS
the Kleene LUT of the pins at every tick. A GMW gate output does not satisfy
this, because it may hold a stale value for up to `D + 1` steps. So the
derived model takes as its root **the LUT value the cell sees**
(`GG = Run.exc`), not the output wire. With that choice every field is
derived.

- **`H_TREE`** is exact: `tree_eq`. It is `lutK` of the definite reads,
  through `lutK_ofBool`, and uses one decided fact: each pin node of the cell
  appears once (`pinsOK`, checked for all 414 cells in `vecA`).
- **`H_FB_WIN`**, with `Dhi = W + D + 1`, is `exc_lag`. In any bounded run,
  a gate's output at step `m ≥ D + 1` equals its LUT value at some step of
  `[m - D - 1, m - 1]`.
  - The proof uses Bounded's gate bound and Run's hold-or-update rule
    (`switch_back`).
  - The feedback pin reads the output at most `W` steps old, which gives
    `W + D + 1`.
- **`H_RST_HIGH`** and **`H_DATA_STATIC`** follow from facts about the reads
  (`cellRun_of_run`; `cellRunW_of_run` adds the first-wave phase).

**`cellRunW_clean`.** Assume Rst3's `gcd_clean_release` hypotheses:
- any power-up state;
- rst is 1 on `(0, F]` with `F ≥ 23(D+W+1) + W` (H_RST_CLEAN, H_HOLD_LONG),
  and 0 on `(F, E]` (H_RST_LOW);
- data is arbitrary;
- the steers are 0 on `(F+34, E]` (H_STEER_HOLD).

Then every rst-reading loop has its two-phase model with `T1 = W + 1`,
`s = F + 1`, `Tz = E + 1`, `Dhi = W + D + 1` and `Tw = twOf` (`E + 1`, or
`F + 1 + dminP` for the 21 cells). The facts come from:
- `gcd_reset_binary`;
- `gcd_clean_release` (the `sA` cover);
- `wave_early` (below).

**`gcd_reset_vec_of_net`.** Brst's `gcd_reset_vec` holds with every
`H_CELL` and every `H_RST_LONG` discharged:
`T1 + Dhi = 2W + D + 2 ≤ F + 1` follows from `H_HOLD_LONG`. In the network
model the per-cell width condition is therefore implied by the global rst
hold. **No per-cell timing assumption remains.**

**`gcd_reset_vec_net`.** This is the stronger form. Under the same
hypotheses, the LUT value each loop sees is its reset value:
- on `[W + 1, E]` (the whole first-wave segment) for the 397 cells that are
  neither frontier nor moving;
- on `[W + 1, min E (F + dminP)]` for the 7 moving cells;
- for the 10 frontier controllers: their reset value up to `F`, and the
  other value at every step of `(F, E]` at which their rst pin reads 0.

**Non-vacuity (`nonvac_net`).** The unit-delay simulation of `gNet`, with
rst 1 on `(0, 23]` and 0 on `(23, 57]`, `D = W = 0`, `F = 23`, `E = 57`,
meets every hypothesis.

**What this does NOT say.**
- The root is the LUT value seen, not the output wire. Rst2's
  `gcd_release_quiet` / Rst3's `gcd_wave_only` already state the output
  form for non-wave nodes.
- `Dhi = W + D + 1` is a model bound, not a routed number.

## Part 2: the 21 first-wave cells

### The class at the first-wave vector (`vec2_census`, decided)

The first-wave vector `rhoA` is `rho` with every Rst3 wave node at `x`
(`wR ≠ 0`). The 414 loops split as follows:

| class at `rhoA` | count | class at `rho` |
|---|---|---|
| hold | 203 | 192 hold (Brst's 195 minus the 3 steer joins) + **11 forced** |
| forced | 194 | forced |
| leave | 10 | the frontier, as before |
| moving (none) | 7 | 3 hold (`ucond_br9/10/11_j`), 4 forced (`ufork11/19/24/39`) |

- The 21 loops with a first-wave data pin are exactly `wcL`.
- 14 of them do not move in the first wave.
  - 3 are hold at both vectors: `uori2/3/4.ujoin`. Their c4 never has all
    inputs equal during the wave.
  - 11 are `newHoldL`: `ufork1`, `ufork10`, `ushrsi0..4.ujoin`,
    `uaddi0.ujoin`, `ufork18`, `ufork23`, `ufork38`. These are forced
    while their wave pin is 0 and HOLD once it rises: a bd_c2 at (0, 1).
- The other 7 are themselves wave nodes.

### Theorems

**`forcedA_clean`, `holdA_clean`, `gcd_reset_vec2` (per-cell model).**

Each cell has a `CellRunW`: Brst's `CellRun` (data ≤ `rho` on `[s, Tw)`),
plus H_DATA_WAVE (data ≤ `rhoA` on `[s, Tz)`). Then every non-moving,
non-frontier cell is at its reset value on `[T1, Tz)`, through the WHOLE
first wave, not only up to `Tw`. The width conditions are:
- 194 forced: none;
- 192 old hold: `T1 + Dhi ≤ s` (H_RST_LONG);
- 11 new hold: `T1 + Dhi ≤ s`, OR `T1 + Dhi ≤ Tw` (H_RST_LONG2). The first
  data move may itself come late enough;
- 7 moving: reset value on `[T1, Tw)`, with H_RST_LONG at the 3 hold
  joins. After `Tw` they leave, which Rst3's `sB` certificate covers at
  network level.

**`newHold_exact`.** At the moved vector `rhoA1` (control nets at their
end-of-wave value), `CElemStrict2.reset_width_iff` holds for each of the 11
real LUTs, from `q = ¬reset` and from `q = x`. So if the data pin has risen
before release, `Dhi + wa ≤ P` is exact there. Exactness of the "or `Tw`"
branch is NOT proved.

**`wave_early` (network, GMW).** Assume:
- wires at most `W` old;
- control at reset on `[S - W, S]`;
- the rst source 1 on `[S - W, F]`;
- non-wave control quiet up to `T`.

Then every wave node `w` is at its reset value at every step
`k ≤ min T (F + wR w - 1)`. This needs one decided check, per wave node, of
the LUT at an "early" state (`earlyOK`, 108 nodes). It generalises Rst3's
`chain_hold`: the frontier is held until `F + 1`, `ucmpi0.udly.g[29]` until
`F + 32`, each `uack.g[5]` until `F + 2`.

**`wave_cells_order`.** Take Rst3's first-wave hypotheses with a clean rst
(1 on `[S-W, F]`, 0 on `(F, E]`). For every loop `n`:
- every control data pin reads its reset value at every step
  `t ∈ [S, min E (F + dminP n)]`;
- the rst pin reads 0 at every step of `(F + W, E]`.

`dminP` is the least `wR - 1` over the first-wave data pins:

| cells | dminP |
|---|---|
| `ucond_br9/10/11_j` (read `ucmpi0.udly.g[29]`) | 32 |
| `ufork10`, `ufork18`, `ufork23`, `ufork38` (read a moving fork) | 3 |
| `ufork1` and the 4 moving forks (read `uack.g[5]` elements) | 2 |
| `uori2/3/4.ujoin`, `ushrsi0..4.ujoin`, `uaddi0.ujoin` (read a frontier controller) | 1 |

**Condition:** `W < dminP n` (rst wire skew, in model steps, below
`dminP n`) means the cell is released for good before any of its data pins
can read a moved value.

**Exactness (`counter_uori2`, `counter_br9`).** These are bounded runs that
meet every hypothesis of `wave_cells_order` with `W = dminP`:
- `uori2.ujoin`: `W = 1`, `D = 4`;
- `ucond_br9_j`: `W = 32`, `D = 65`.

In each, the cell's rst pin reads 1 at every step before the first step at
which its first-wave data pin reads the moved value 1. Construction:
- a prefix in which only the chain moves, one step per LUT, and every other
  gate holds (allowed because `D = T0`);
- then the unit-delay simulation;
- the cell's rst pin is read `W` steps late.

The chain step is decided (`updOK`). Exactness is shown for these two
cells only; for the other 19 the condition is sufficient only.

## What this answers, for the owner

- **The open point of Brst is closed in the network model.** Whether `Tw`
  comes before or after a cell's release, the cell is clean.
  - Non-moving cells stay at reset through the whole wave (class at `rhoA`).
  - The moving ones stay at reset until their own data moves.
  - In the GMW network with Rst2's global hold, no width condition is left
    at any cell (`gcd_reset_vec_net`).
- **Finding (per-cell model only).** 11 cells forced at the reset vector
  (`newHoldL`, every one a fork or compute-unit join fed by a frontier link,
  its ack delay, or a moving fork) become hold vectors when that input rises. With rst
  skew `W ≥ dminP` (1 to 3 steps for these cells), the input can rise
  before the cell's own rst pin falls.
  - The width condition then binds there too, and it is exact at the moved
    vector.
  - So the JSON's `reset_width` matters at up to 206 cells (195 + 11), not
    195. The exception is when per-pin rst skew is below `dminP` (1 step
    for the ushrsi/uaddi joins).
  - Gate: routed SDF. For each of the 11, check either rst high width at
    that pin > LUT + feedback route (slow max), or that the rst skew
    between the frontier link's pin and this cell's pin is below
    `dminP` × min LUT delay.
- For `uori2/3/4.ujoin`, Brst's "reads a frontier link" concern needs
  nothing new: they are hold at both vectors, so H_RST_LONG alone covers
  them.
- For the three steer joins: released before `g[29]` can read 1 iff the rst
  skew is below 32 GMW steps (exact). Either way they cannot fire before
  `F + 33`.

## Not covered

- **The moving cells after `Tw` in the per-cell model.** This is Rst3's
  `sB` at network level only. An intermediate vector of a moving fork (some
  inputs up) is a hold vector, and the per-cell theorem does not cover it.
- **Exactness of the `T1 + Dhi ≤ Tw` branch** for the 11 cells, and of
  `W < dminP` for 19 of the 21 cells.
- **Counter-run gate delays.** The counter-runs use slow gates
  (`D = T0`). A counter-run with `D` small would need a full-network
  simulation in the kernel; it was not attempted.
- **The arbiter's cross-coupled pin and the LUT6_2 shared input buffer.**
  These are as in Brst/Rst2.
- **Physical numbers.** There are none: no route, and `W`, `D` and `dminP`
  are model steps.
