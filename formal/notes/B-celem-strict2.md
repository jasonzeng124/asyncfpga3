# B-celem-strict2: the strict own-feedback race on every C-element, the latch pair, and reset release

File: `formal/lean/Formal/Cells/CElemStrict2.lean` (core Lean, imports
`CElemStrict`). Check:
`scratchpad/bchk.sh formal/lean/Formal/Cells/CElemStrict2.lean` gives
`[bchk] OK` (autoImplicit=false, no warnings). Axioms: `propext` for the
`decide +kernel` facts; `propext`, `Classical.choice`, `Quot.sound` for the
generic iff theorems. No sorry, axiom or native_decide.

## Verdict

**Works, with no failures.** Every `Facts` field holds on every real INIT
for every four-phase cycle. The model is Bs's: H_TREE, H_MUX_KLEENE,
H_FB_PURE and H_IN_PHASES (notes/B-celem-strict.md).

## 1. Generalisation: the feedback can start at a Kleene value

`FactsK`, `LoopK`, `SpecK` and `edgeK` take the start value `v : K3`, so
they cover `v = x`, the power-up state of a LUT loop.

Proved: `prefix_okK`, `cleanK`, `hazardK`, `clean_iffK`, `box_iffK`,
`loop_existsK` and `sim_loopK` (non-vacuity). Bs's results are the special
case `v = ofBool b` (`factsK_of_facts`, `facts_of_factsK`, `loopK_of_loop`,
`specK_iff`).

`forced_clean`: if the function is the constant `n` in phases I1, RX and R1
for every feedback value, then `G = n` from `tb + wb` on, for every `D` and
every release time.

## 2. Every cycle of every C-element variant (`decide +kernel`)

`AllCycles F pol` means: for each direction `v`, each follow pin `f` and
each release pin `r` (`f = r` allowed), the facts hold. The other inputs sit
at the logical value `u = !v`, and a bubble on a pin is modelled by `pol`.
Each result is a `Facts`, so all of Bs's results apply to it: `clean_iff`,
`box_iff`, `env_latency_iff` and `env_latency_strict`. `c4_clean_iff` is the
usage form.

| cell | INIT | cycles | theorem |
|---|---|---|---|
| bd_c2 | 00E8.. | 8 | `c2_all8` (re-checks Bs's `c2_all`) |
| bd_c2_set | FFE8.. | 8 | `c2set_all` |
| bd_c2n | 00B2.. | 8 | `c2n_all` (Bs had 1 of these) |
| bd_c2n_set | FFB2.. | 8 | `c2nset_all` |
| bd_c3 | 0000_FE80_0000_FE80 | 18 | `c3_all` |
| bd_c4 | 0000_0000_FFFE_8000 | 32 | `c4_all` |
| bd_c2_norst | E8E8.. | 8 | `c2norst_all` |
| bd_c3_norst | FE80.. | 18 | `c3norst_all` |

bd_ctree nodes are instances of bd_c2, bd_c3 or bd_c4 (cells/rtl/bd_ce.v).
The N = 1 case is a wire and has no loop.

**Mutants.** Clearing INIT bit 7 of c3 (`0x..FE00`) makes `AllCycles` false
by decide. So does removing one hold bit of c4 (`0x..FFFC8000`).

## 3. Latch pair (LUT6_2, INIT FF33_CC00_B8B8_B8B8)

`pair_o5_eq` and `pair_o6_eq`: each output's root is exactly `latF` of its
own pins (d, en, q), whatever the other bit's two pins carry.

`pair_o5_loop` and `pair_o6_loop` let the other bit's pins be arbitrary
time-varying Kleene traces, and the loop is still a `Loop latF`.

`pair_o5_clean_iff` and `pair_o6_clean_iff`: the setup race against the
enable fall is exact and strict, `Spec ↔ tb + D + wb ≤ s`, for both data
directions. This uses Bs's `latch_facts`.

## 4. rst as the release pin

The rst pin moves through `0 → x → 1` (the follow phase: the cell must go to
its reset value `n`) and then `1 → x → 0` (the release: the cell must hold
`n`). The data pins sit static at a binary vector `w`.

Exhaustive over `w` and over every Kleene start `v ≠ n`, from the binary
spec alone. These are proved for c2, c2_set, c2n, c2n_set, c3, c4 and
latch_rst RST0/RST1 (`*_rst_dec`):

- **hold `w`** (`∀q, cell(w,q) = q`): the race facts hold, both for `v = ¬n`
  and for `v = x`;
- **forced `w`** (`∀q, cell(w,q) = n`): race-free. The Kleene function is
  `n` for every rst value and every feedback value (`forcedB`,
  `c2_rst_forced_clean`).

The remaining `w`, all inputs at the non-reset value, makes the cell leave
reset by design. `c2_rst_classes` and `c2n_rst_classes` list the vectors by
name.

| cell | race-free (forced) vector | leaves-reset vector |
|---|---|---|
| bd_c2 | a = b = 0 | a = b = 1 |
| bd_c2n | (a, b) = (0, 1) | (a, b) = (1, 0) |
| c3, c4 | all inputs 0 | all inputs 1 |
| latch_rst | en = 1 with d = reset value | en = 1 with d ≠ reset value |

For bd_c2n, a = b = 0 is a **hold** vector and therefore races.

**Exact condition (`reset_width_iff`).** Let `P` be rst's binary high width:
from its assert edge settled (`tb + wb`) to its release edge settled
(`s + wa`). Over `D ∈ [Dlo, Dhi]`, the cell is safe for every behaviour iff
`Dhi + wa ≤ P`.

- `reset_width_strict` (`wa = 1`): the condition becomes `Dhi < P`.
- `reset_width_atomic` (`wa = 0`): it becomes `Dhi ≤ P`.

At power-up use `v = x` and `tb = wb = 0`.

**Traces** (real INIT, D = 420):

| theorem | cell and vector | setup | result |
|---|---|---|---|
| `rst_boundary_x` | bd_c2, w = (1, 0), q = 1 | P = D | root is 0 at 419 and x at 420 |
| `rst_strict_clean` | same | one tick longer | clean forever |
| `rst_glitch` | same | binary release at 300 | root is back to 1 (reset lost) |
| `rst_powerup_x` | same, power-up x | P = D | x at release |
| `rst_powerup_strict_clean` | same, power-up x | P = D + 1 | clean |
| `rst_boundary_x_c2n` | bd_c2n, a = b = 0 | P = D | x |

## For the owner

- `bd_c2.reset_width` and `design.rst_hold` already carry `+ 1`
  (`dlmax + dwmax + 1 ≤ width`). `reset_width_strict` now backs them on every
  rst-carrying C-element and on latch_rst, including the all-X power-up
  start.
- The JSON is sufficient but not tight. The condition is needed only where
  the cell's data pins sit at a hold vector at release. At a forced vector
  (bd_c2 inputs 0; bd_c2n at (0, 1)) any width works in this model.
  gcd_hw's 185 bd_c2n link controllers are released with req = ack = 0, if
  that is the idle state. That vector is a hold vector, so the race is real
  there.
- The c3 and c4 entries for `env_latency`, `sel_order` and `pulse_width`,
  and `bd_ctree.node_fork`, are now backed by `c3_all` and `c4_all`. All of
  bd_c2n's and bd_c2_set's are backed by `c2n_all` and `c2set_all`.
- `[pair.O5]` and `[pair.O6]` `setup_*` are backed by `pair_o*_clean_iff`,
  independently of the sibling bit.

## Not covered

- Data inputs moving during the reset pulse or at its release.
- A follow and a release that overlap other moving pins (one moving pin per
  phase).
- Inertial filtering.
- A feedback X width other than G's own.
- The physical width of `wa`: one tick is the model's minimum, not a
  measured slew.
- Whether gcd_hw's reset network meets `Dhi < P` (no routed numbers here).
- The power-up trace after an under-width release: in Kleene it does not
  settle (an x pulse circulates with period D). Only `G s = x` is proved.
