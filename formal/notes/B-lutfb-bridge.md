# B-lutfb-bridge (probe Bfb): C's `LutFb` / `FbFirst` from B's physical cell model

Lean: `formal/lean/Formal/Cells/LutFbBridge.lean` (core only; it imports
`Formal.Net.OpsGen` and `Formal.Cells.WinFifoCausal`). Checked OK with
`/tmp/claude-0/btools/bcheck.py` (autoImplicit=false). It has no warnings and no sorry, axiom
or native_decide. `#print axioms` on all 12 headline theorems gives
`[propext, Classical.choice, Quot.sound]`.

## The question

The bridge Br1 (C's O4, `B-hypotheses.md`): C's operator bindings in `OpsGen.lean` assume,
for each LUT with feedback, the step relation `LutFb F p qp o` (`o` changes only to
`F (p t) (qp t)` one tick earlier) and `FbFirst qp o` (at each change the feedback pin
already shows `o`). Before this probe no B file derived either one. This probe derives both
from B's physical model, using C's definitions as they stand (imported, not restated):

- the LUT output is shard A's window channel `Win lo hi` of the real-INIT excitation, plus
  the intrinsic H_NO_REVERT (`NoRevertI`);
- the feedback wire is `WinDelay wl wh`.

## Answer

**C's premise is derivable. It is not a property of the cell alone: it is cell plus
environment timing.**

- **What `LutFb` needs.** `LutFb` builds in a one-tick delay, but the LUT delay is
  `lo..hi` ticks (about 100 ps at 1 tick = 1 ps). `LutFb` still holds on the real traces,
  for this reason: under the four-phase environment and H_LAT, the pins and the feedback
  hold their phase values from the phase start until the node's edge. So the excitation one
  tick before the edge already equals the new output value. No time abstraction is needed.
- **Cells covered:**

| theorem | cell (real INIT) | C premise delivered | B hypotheses |
|---|---|---|---|
| `link_lutFb` | bd_link `ctl.u.u` = `bd_c2n` `0x00B2…` | `LutFb linkF (req, ack) qp O`, `FbFirst qp O` (`link_bound`'s premises); `link_cel_si` = `Link.H_CEL_SI` | `WinFifoCausal.Stage`, `Env1`, `Timing1` (unchanged), plus H_LUT_POS `1 ≤ lo`, H_PWR |
| `c2_lutFb` | `bd_c2` `0x00E8…` | `LutFb F (a, b) qp O`, `FbFirst` for any `F = cel2` | `CelC` (= Stage with the bd_c2 INIT), `EnvC` (new: two inputs, each 0 from reset until its first rise), `Timing1`, H_PWR |
| `fork2_lutFb`, `fork2_cel_phys` | bd_fork N=2 ack C-element | `fork2_cel`'s premises; `Fork.cel` | as `c2_lutFb` |
| `join2_lutFb`, `muxn_c2_lutFb`, `arb_ack_lutFb`, `mux_ack_lutFb` | bd_join N=2; bdc_muxn's bd_c2; bd_arbiter `ua1`/`ua2`; bd_mux `uxa`/`uya` | the matching `OpsGen` premises | as `c2_lutFb` |
| `lutFb_of_phases`, `fbFirst_of_phases` | any LUT function | `LutFb`, `FbFirst` | Win + NoRevertI, H_LUT_POS, H_PWR, plus H_EX_CLEAN in phase form (`Phases`) and the spacings `c j + hi ≤ c (j+1)`, `c j + hi + wh < c (j+1) + lo`, `hi + wh ≤ c 0` (named, NOT derived) |

- **How the proof works.**
  - Reduction: `bd_c2` is `bd_c2n` with the `b` pin inverted (`c2_eq_c2n_inv`). That lets
    the C-element proof reuse WinFifoCausal's `exc_phase_w`. Only the pre-phase lemma
    `cc_pre` is new; it is needed because both inputs start at 0.
  - Edges: `node_win` gives one edge per phase. Every output change is such an edge
    (`change_at`). The excitation one tick before the edge is the phase value
    (`lutFb_of_phases`). The feedback pin reads the previous segment's value, because H_LAT
    gives `c j + hi + wh < c (j+1) + lo` (`fbFirst_of_phases`).
- **Non-vacuity, with nonzero delays:**
  - `link_witness`: B's `Wx.witness1` run. The LUT band is `[1, 3]`, two ticks wide, so
    there `Win` is not FIFO. The wire delay is 1 and the pins carry junk before reset. The
    node toggles.
  - `c2_witness`: the real `bd_c2` loop. The LUT band is `[1, 2]` and the wire delay is 1.
    The inputs are `sq 4` and `sq 5`, so on `[4, 5)` and `[8, 9)` they disagree and the cell
    holds through its feedback pin. The node toggles, and the fork's generated-LUT
    `LutFb`/`FbFirst` hold.
- **Counter-runs:**
  - `no_revert_needed_lutFb`: B's one-glitch run. Every hypothesis except H_NO_REVERT holds
    (Win, wire, Env1, Timing1, H_LUT_POS, H_PWR). **Both** `LutFb` (at t = 5) and `FbFirst`
    (at t = 6) fail. `Win` alone never gives C's premise.
  - `env_needed_lutFb`: a fixed transport loop, LUT delay 2 and wire delay 1, on the real
    `bd_c2n` INIT. It satisfies `Stage`, H_LUT_POS and H_PWR. The request is a one-tick runt
    (which `Env1`'s H_SND forbids), and `LutFb` fails at t = 6. So no channel model, even an
    ideal transport one, yields `LutFb` without an environment timing hypothesis.
- **Weakest form.** The weakest form proved here is `lutFb_of_phases`: excitation phases
  clean and at least `hi` long. `FbFirst` additionally needs the gap of `hi + wh` against
  `lo`.
- **Not proved:** that these hypotheses are the weakest. H_PWR and H_LUT_POS are argued
  needed but have no counter-run in Lean:
  - H_PWR, because `Win` is unconstrained for `t < hi` while `LutFb` constrains all `t`;
  - H_LUT_POS, because with `lo = 0` the node can change in the same tick as its pins.

## NOT covered (open)

- **Not derived:**
  - `bd_mux` `uj0`/`uj1`: 5-pin LUTs with the select. The generic theorem applies, but
    their phases are not derived.
  - `bd_join` N=3 (`bd_c3`), and C-trees.
  - The `LutSI` premises of steer and src.
- **No such premise in C's bindings:** bd_latch (it enters as the `H_LATCH_*` data fields)
  and bd_arbiter's `ustate` (lumped into `AMerge.zr` under H_DELAY_LUMPED).
- **Environment not derived:** `Env1` and `EnvC` are not derived from the neighbouring
  cells. That needs the network-level causal induction, done in Lean only for the
  two-stage pipe (`WinFifoCausal.pipe_fifo`), not for gcd_hw.
- **Not instantiated on `CapstoneNet`:** the bridge is per cell kind.
- **Relation to C-10k:** C-10k's `fbFirst_of_resp` (via `RespAfter`) is a different route to
  `FbFirst`, and it assumes `LutFb`. This file assumes neither.
