# B-reset-gcd-vec: which data vector each gcd_hw reset cell sees at release

Probe Brst (shard B), 2026-10-27. Follows `B-celem-strict2.md` (Bc4: exact
reset-width condition per cell, needed only at hold vectors) and
`B-reset-gcd.md` / `B-reset-gcd-wave.md` (Rst2/Rst3: gcd_hw's control
network, 3322 nodes, real INITs and pin lists, reset state `gR`).

No route, no board, no toolchain run. The network is Rst2's elaborated RTL
import (default matched-delay sizes, plus `gcd_rig`). It is not a routed
netlist.

## File and check

- `formal/lean/Formal/Cells/ResetGcdVec.lean` (core Lean). It imports
  `ResetGcdWave` (and through it `ResetGcd`, `ResetGcdNet`) and
  `CElemStrict2`, all read-only.
- Check: `scratchpad/bchk.sh formal/lean/Formal/Cells/ResetGcdVec.lean`
  prints `[bchk] OK` with no warnings. The file alone takes about 130 s wall
  and 1.96 GB peak RSS: 9 node chunks of 400 at about 13 s each, plus the
  census.
- No sorry, admit, axiom, native_decide, opaque or extern. All certificates
  are checked with `decide +kernel`.
- `#print axioms` (scratch file, not in the repo):
  - `gcd_vec_census`: propext.
  - `link_boundary_x`, `cellRun_of_loopK`: propext, Quot.sound.
  - `gcd_reset_vec`, `gcd_hold_exact`, `hold_clean`, `forced_clean'`,
    `leave_clean`, `nonvac_hold`: propext, Classical.choice, Quot.sound.
- The lead still has to add the file to `Formal.lean`.

## Method

Each rst-reading LUT `n` is a single loop: the root is `cellF init pins n e r q`.
This is `lutK` of the real INIT on the real pin list, where:
- the rst pin (node 0) reads `r`;
- the cell's own output pin reads the feedback `q`;
- every other pin reads `e`.

The reset vector is `rho`: every control net at its reset value `gR`, every
data net `x`. Per node, the kernel decides:
- `followB`: rst = 1 gives the reset value for EVERY data value (all-`x`
  data, by monotonicity) and every feedback value.
- `forcB` (forced): at `rho`, the root is the reset value for every rst and
  every feedback value.
- `holdB` (hold): at `rho`, with the feedback at the reset value, the root
  is the reset value for every rst value.
- `leaveB` (leave): at `rho` with rst = 0, the root is the other value for
  every feedback value.
- `exactB`: Bc4's `rstB` race facts at the cell's real LUT and vector
  (data nets at 1), from `q = ¬reset` and from `q = x`.

The class is the first of forced, hold, leave that holds. A cell that is
none of them would fail the check; none does.

## Results

### `gcd_vec_census`

There are 423 rst readers. 9 of them, the arbiter `ustate` O5, are
combinational: their own output is not one of their pins. The other 414 are
loops:

| cell | hold | forced | leave |
|---|---|---|---|
| bd_c2 (153) | 8 | 145 | 0 |
| bd_c2n (185) | 174 | 1 (`urig.uenv0`, (0,1)) | 10 (the frontier) |
| bd_c2n_set (1, `uenv1`) | 1 | 0 | 0 |
| bd_c3 (10) | 0 | 10 | 0 |
| bd_c4 (14) | 3 | 11 | 0 |
| bd_mux uj0 / uj1 (21 + 21) | 0 | 42 | 0 |
| arbiter ustate O6 (9) | 9 | 0 | 0 |
| **total 414** | **195** | **209** | **10** |

- The leave set is exactly `ResetGcd.frontierL`.
- The hold set is exactly the 195-entry certificate `holdL`.
- Rst-reading loops with a data pin that is a first-wave node of
  `ResetGcdWave` (so the pin moves after release): 6 hold, 15 forced.

### Generic theorems (any LUT loop, a model wider than Bc4's)

The model is `CellRun`. It assumes:
- H_TREE;
- H_FB_WIN: from the release on, the feedback reads the root `d` ticks
  ago, with `1 ≤ d ≤ Dhi`, and `d` may vary with time;
- H_RST_HIGH: rst reads 1 on `[T1, s)`;
- H_DATA_STATIC: every data pin is Kleene-below `rho` on `[s, Tw)`.

Nothing is assumed about:
- the data before `s`;
- rst from `s` on (skew, glitches, re-assertion);
- the start value of the loop (power-up `x` included).

The theorems:
- `hold_clean`: assume `followB`, `holdB` and H_RST_LONG (`T1 + Dhi ≤ s`,
  which is Bc4's `Dhi + wa ≤ P`). Then the root is the reset value on
  `[T1, Tw)`.
- `forced_clean'`: assume `followB` and `forcB`. Then the same conclusion
  holds with no width condition.
- `leave_clean`: assume `followB` and `leaveB`. Then the root is the reset
  value on `[T1, s)` and the other value at every tick of `[s, Tw)` where
  rst reads 0.
- `cellRun_of_loopK`: Bc4's loop (pure delay `D`, static data, rst phases)
  is a `CellRun`.

### `gcd_reset_vec` (the composition)

Assume:
- every rst-reading loop `n` of `gNet` has a `CellRun` with its own `T1 n`,
  `s n`, `Tw n` and `Dhi n`. This covers per-pin rst timing and per-cell
  loop delay.
- H_RST_LONG (`T1 n + Dhi n ≤ s n`) holds for the cells in `holdL` ONLY.

Then every one of the 414 cells:
- is at its reset value while rst is high;
- if it is not a frontier cell, stays at its reset value until a data pin
  leaves the reset vector;
- if it is a frontier cell, is at 1 at every released tick before that.

No width condition is assumed for the 209 forced cells or the 10 frontier
cells.

### `gcd_hold_exact`

At each of the 195 hold cells, `CElemStrict2.reset_width_iff` holds for
that cell's real LUT at its real vector, from `q = ¬reset` and from
`q = x`: every behaviour is safe iff `Dhi + wa ≤ P`. So the width condition
cannot be dropped at any of them.

### Non-vacuity and the counter-trace

- `nonvac_hold`: a run of the real link controller
  `ulink_n106__1.many.stage[0].u.ctl.u` (node 1703) meets every hypothesis
  of `hold_clean`, including H_RST_LONG (D = 420, rst settled from tick 1,
  release at 421, feedback 1 before reset). Its root is 0 from tick 1 on.
- `link_boundary_x`: at `P = D` the same cell's root is `x` at the release
  tick. This goes through `node1703_c2n` (the cell is exactly Bc4's
  `c2nR false false`) and `rst_boundary_x_c2n`.

## Where the reset width binds (the 195 hold cells)

- **174 bd_c2n link and pipe stage controllers.** These are every
  `ulink_*` controller except the 10 frontier ones. All of them sit at
  req = ack = 0, which is a hold vector of C(a, ¬b). This confirms Bc4's
  open point.
- **`urig.uenv1`** (bd_c2n_set, the token), at (0, 0).
- **9 arbiter ustate O6:**
  - `ucontrol_merge2/3/4/6/9/10/11/12.uarb1.ustate`;
  - `ucontrol_merge12.uarb2.ustate`.

  All requests are 0 at reset and the reset value is 1, so this is a hold.
  Caveat: pin I4 of these cells (the grant side) is another loop node. The
  single-loop model holds it at its reset value from `s` on.
- **5 bd_c2 at a hold vector because one input is a reset-1 token:**
  - `ufork0.u.u` (reads node 3257, an element of `urig.upsnk`, reset value 1);
  - `ucond_br9_j`, `ucond_br10_j`, `ucond_br11_j` (read `uenv1`);
  - `ucmpi3.ujoin` (reads `usource3`).
- **3 bd_c4 joins** `uori2.ujoin`, `uori3.ujoin`, `uori4.ujoin` (read a
  source token).
- **3 bd_c2 `umux21.uj0`, `uj1`, `uj2`** (muxn3). One of their pins is the
  free muxn3 decode output. With that pin at 1 the vector is a hold, so they
  are counted as binding. Under H_GUARD_MAP (the decode keeps `ctl_req`, so
  it is 0 during reset) they would be forced.

Every other cell needs no width condition in this model:
- every bd_c2 fork, join and ack tree at all-0;
- every c3 and the remaining c4;
- `uenv0` at (0, 1);
- all 42 bd_mux joins, whatever their select does.

## For the owner

- The JSON's per-cell `reset_width` (`dlmax + dwmax + 1 ≤ width`) is needed
  at 195 of the 414 reset loops. These are listed above, chiefly every link
  controller. It is not needed at the other 209. A board-level rst pulse of
  `23(D+W+1)+W` steps (Rst2's H_HOLD_LONG) already exceeds every per-cell
  `Dhi + 1` by a wide margin. The per-cell condition matters only if a
  per-pin rst skew made some cell's own high width shorter than its loop.
- Gate: routed SDF. For each of the 195 cells, check that the rst high width
  at that cell's pin is greater than that cell's own LUT + feedback-route
  delay (slow max).

## Not covered

- **First-wave data pins.**
  - 6 hold cells read a first-wave node:
    - `ucond_br9_j`, `ucond_br10_j`, `ucond_br11_j` read
      `ucmpi0.udly.g[29]`;
    - `uori2.ujoin`, `uori3.ujoin`, `uori4.ujoin` read a frontier link.
  - So does 15 forced cells.
  - For these, `gcd_reset_vec` speaks only up to `Tw`, the first time that
    pin moves. Whether `Tw` comes after the cell's own release is not proved
    here.
  - Rst3's GMW `gcd_first_wave` covers that window at network level, for
    every rst waveform.
- **Not linked to GMW.** `CellRun` is a per-cell model and is not derived
  from Rst2's GMW `Run`. H_FB_WIN (feedback delay ≤ Dhi) and H_DATA_STATIC
  are per-cell hypotheses. Rst2's `gcd_release_quiet` is the network-level
  reason that data pins of cells off the first wave stay at `rho`.
- **The arbiter's cross-coupled pin.** Its I4, and the shared LUT6_2 input
  buffer, are treated as static data.
- **The 9 combinational arbiter O5.** They have no loop, so there is no
  race of this kind.
- **Physical numbers.** There are no routed numbers. `wa`, `D` and `P` are
  model ticks.
