# B-rig-idx: `gcd_rig.idx_setup`, sufficient and necessary (probe Bri)

File: `formal/lean/Formal/Cells/RigIdx.lean`. It is Core Lean and imports
`Formal.Cells.RigContract`. I edited nothing else.

Check (core-only closure, `-DautoImplicit=false`):

    /tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/RigIdx.lean
    [bchk] lean Formal.Cells.RigIdx
    [bchk] OK: formal/lean/Formal/Cells/RigIdx.lean

- No `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `extern` or `unsafe`.
- `#print axioms` (scratch file): every theorem uses only `propext`,
  `Classical.choice` and `Quot.sound`. `pathOK_band` uses only `propext`
  and `Quot.sound`.
- `RigContract.lean` itself checks with bchk (it prints only deprecation
  warnings).

## 1. The obligation

`gcd_rig.idx_setup`: the hk edge that loads `idx` (the load edge `n0`) also
raises `rig_rst`. The operand word `vector(idx)` must settle at the frontier
latch's `d` pins at least `su` before the frontier controller `F`
(`ulink_n1__1`, whose request is `uenv1`) opens the latch. The same holds at
any direct `a_data`/`b_data` reader whose request is a delayed copy of F,
such as `ucmpi0`.

`SetupOK` is that statement. Take any instant `t` of window `n0` such that:
- the reset has already forced the enable low (`t ≥ e n0 + rhi + dlmax + enhi`);
- `t` is before the next window's operands can move (`t < e(n0+65536) + vlo`);
- the latch enable `En` is high at `t`.

Then the `d` pins carry the window's vector on all of `[t − su, t]`.

## 2. Hypotheses (`Rig`, all named)

| name | meaning |
|---|---|
| `H_HK_PERIOD` | `e n + Tlo ≤ e (n+1)`: every hk period is at least `Tlo` |
| `H_LOOP` | F is the real `bd_c2n` INIT in a window-channel loop: LUT `[dlmin, dlmax]`, feedback wire `[dwmin, dwmax]` |
| `H_PATH_RST` | from `rig_rst` to F's rst pin, `PathOK` band `[rlo, rhi]` (tCO + OR + route + site pin) |
| `H_PATH_IDX` | from `idx` to the latch `d` pins, `PathOK` band `[vlo, vhi]` (tCO + vector decode + route) |
| `H_RST_ONE_FALL` | rst at F falls once, at `r`, inside its band |
| `H_EN` | from F's output to the latch enable pin (or to the reader's request), window channel `[enlo, enhi]` |

These are used as separate hypotheses, outside `Rig`:
- `Load n0` (steady state, `n0 ≥ 65537`);
- `H_RST_LONG : rhi + dlmax + dwmax ≤ 16·Tlo + rlo`;
- `H_IDX_SETUP : vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`.

**No token hypothesis is needed for the setup half.** The reset alone holds F
low until `r + dlmin`.

## 3. Results

| theorem | statement |
|---|---|
| `F_low` | Assume `Rig` and `H_RST_LONG`. Then F is 0 on `[e n0 + rhi + dlmax, r + dlmin)`, whatever its request, acknowledge or power-up state. |
| `idx_setup_suff` | Assume `Rig`, `H_RST_LONG` and `H_IDX_SETUP`. Then (1) `SetupOK` holds; (2) the operands are the window's vector on `[e n0 + vhi, e(n0+65536) + vlo)`; (3) `F_low` holds. |
| `idx_fire` | Add `H_HK_POS` and `H_TOKEN_FIRST`: `aF = 1, bF = 0` on `[e n0 + rhi, r + dlmax + dwmax]`, i.e. only until F's first rise plus its loop bound, which is the form of `gcd_rig.token_static`. Then F is 1 on `[r + dlmax, r + dlmax + dwmax + dlmin]`, so the opening exists. |
| `pathOK_band` | A transport delay `d` from edges `e n = T·n` is a `PathOK` for any band `[lo, hi]` that contains `d`, provided `d ≤ lo + T` and `hi ≤ d + T`. |
| `cex_rig` | An explicit run satisfies every field of `Rig`. Its parts: `e n = T·n`, `n0 = 131073`, unpinned; rst is a transport of `rlo`, operands a transport of `vhi`; F is a `bd_c2n` with a pure `dlmin` LUT delay, `aF` = token from `T·n0` on, `bF = 0`; `En` = F delayed by `enlo`. No setup inequality is assumed. |
| `cex_open` | In that run, the enable is high at exactly `T·n0 + 16·T + rlo + dlmin + enlo`, which lies inside `SetupOK`'s domain. |
| `idx_setup_iff` | **Exactness.** Assume the side conditions below. Then `SetupOK` holds for every run satisfying `Rig` (every edge timing `e`, every window, pinned or not, all traces) iff `vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`. |
| `idx_nonvacuous` | The 7.6 ns instance, below. |

**Side conditions of `idx_setup_iff`:**
- `Tlo > 0`;
- each band is ordered, `lo ≤ hi`;
- `rhi ≤ rlo + Tlo` and `vhi ≤ vlo + Tlo` (each band is at most one hk
  period wide; a `PathOK` wider than that is close to unsatisfiable anyway);
- `enlo ≤ enhi`, `dlmin ≤ dlmax`, `dwmin ≤ dwmax`, `0 < dlmin + dwmin`;
- `H_RST_LONG_EN : rhi + dlmax + dwmax + enhi ≤ 16·Tlo + rlo`;
- `H_SHORT : rlo + dlmin + enlo < 65520·Tlo + vlo` (the earliest opening is
  inside the window).

**The counter-run** (the → direction). Suppose `H_IDX_SETUP` fails. In the
explicit run:
- the operands show the previous window's vector up to `T·n0 + vhi`;
- the enable rises at `T·n0 + 16T + rlo + dlmin + enlo`, which is earlier
  than `T·n0 + vhi + su`.

So `d` at `t − su` is vector 0 or 1, not 2 (`idx_before`, `idx_n0C`).

**Non-vacuity at 7.6 ns.**
- hk period `Tlo = 7600` ps, `gcd_hw.v`'s own figure of 27.5 hops at about
  275 ps.
- The bands are illustrative, NOT routed:

  | path | band (ps) |
  |---|---|
  | rst | `[1200, 4800]` |
  | idx | `[900, 4200]` |
  | enable net | `[150, 1125]` (the bd_link header's measured enable-net spread on a routed 32-bit link) |
  | F's LUT | `[100, 500]` |
  | feedback wire | `[50, 400]` |

  The setup time is 300 ps.
- What holds in that instance:
  - every `Rig` field;
  - `H_RST_LONG`;
  - `H_IDX_SETUP`, with margin `121600 + 1200 + 100 + 150 − 4200 − 300 =
    118550` ps;
  - the enable is high at an instant inside the window;
  - the operands are vector 2 on the whole setup interval;
  - F fires (it is 1 at `r + 500`).
- The margin is set by the 16-cycle reset (121.6 ns) against a few ns of
  decode and route. A routed check cannot plausibly fail it. Still, NO routed
  number has been evaluated.

**Not covered:**
- **Hold side.** `idx_setup_suff` (2) gives stability up to
  `e(n0+65536) + vlo`. Closing the latch after that is the next window's
  business, and `RigContract.verdict_current` handles it.
- **Whether a late operand actually corrupts the kernel.** A transparent latch
  passes a late change. Whether downstream then misreads it is link bundling.
  So the necessity is necessity of this obligation, not of correct
  computation.
- **The first window after configuration.**
- **Routes.** None was used.
- **Direct readers.** These are covered only if the reader's request is a
  window-delayed copy of F (`H_EN`). For `ucmpi0`, `[enlo, enhi]` is F →
  `uor` → `udly` (30 elements), which only enlarges the margin.

## 4. Re-check of RigContract's headline claims

Sources: `B-rig-contract.md`, `RigContract.lean`, and audit row 48, which
quotes commit 3e00ce4.

1. **`RigContract.idx_setup` is proved under a hypothesis the running ring
   violates.**
   - Its `H_TOKEN_STATIC` requires `aF = 1 ∧ bF = 0` on all of
     `[e n0 + rhi, e(n0+65536) + rlo)`, the whole window.
   - In `gcd_rig.v`, F = `ulink_n1__1` has request `env_c` (`uenv1`). After F
     fires:
     - the next stage (`ucmpi0`'s join) takes the token, so `bF` rises;
     - `uenv1 = C(env_c0, ~in_ack)` falls when `in_ack` rises, so `aF` falls.
   - So any window in which the kernel completes one input handshake falsifies
     the hypothesis. The theorem's conclusion (c), "F high from `r + dlmax` to
     the end of the window", is false for the real ring.
   - The constraint `gcd_rig.token_static` asks for the token only until F's
     first rise plus its loop bound. The note's table equates the two, which
     is wrong.
   - There is no non-vacuity witness for `idx_setup`.
   - The note's "the entry's form, made exact" has no necessity theorem behind
     it.
   - RigIdx repairs all three points:
     - `idx_setup_suff` uses no token;
     - `idx_fire` uses the token only until the first fire;
     - `idx_setup_iff` proves exactness;
     - `idx_nonvacuous` is the witness.
2. **"The comment's explanation is refuted"** (note §2d; commit "refuted").
   - Checked:
     - `armedOld_iff`: without `settled`, the arm is closed on
       `p ∈ [2, 32]` and open at `p = 1`;
     - `stale_cycle` / `stale_window`: the old arm is 1 while the readers show
       the new idx;
     - `stale_err_vectors`: a steady-value detector, ASSUMING the stale result
       is the previous vector's CORRECT gcd.
   - Not checked: that no pre-reset result survives to `p ≥ 33`. That is
     exactly the comment's mechanism, and excluding it is `H_RESULT_FRESH`, a
     hypothesis of `verdict_attrib`. It is cited from ResetGcd's GMW-model
     result and not composed.
   - So what is proved is this: the `p = 1` mechanism exists in the old RTL,
     and the comment's mechanism is excluded *given* `H_RESULT_FRESH`.
     "Refuted" and "the 2048-cycle drain buys nothing more" are conditional on
     `H_RESULT_FRESH`.
   - "Explained to the cycle" (commit) is a model consistency argument. The
     timed filter part `C_STALE` is unproved, and there is no measurement.
3. **"`verdict_current` proves no verdict can be stale"** (note §2d, "Current
   RTL").
   - `verdict_current` proves only two things: the arm pin is a definite 0
     whenever the instant is less than 2047 periods after the load edge, and
     the readers show the window's idx.
   - "No stale verdict" needs `verdict_attrib` plus `H_RESULT_FRESH` (and
     `H_RES_BUNDLED`).
4. **Proposed json "`stale_window` (necessary)" for `gcd_rig.arm_before_idx`**
   (note §5).
   - `stale_window` is about a different RTL (no `settled`). It is not a
     counter-run for `H_ARM_BEFORE_IDX : ahi ≤ Tlo + vlo` in the current RTL.
     That necessity is unproved.
5. **"Bit-exact"** (commit).
   - `arm_sr` is abstracted to a constant `armG`; the RTL shifts it on
     `win_edge_d && por_done`.
   - `hold_pin` and `hold_vec` are constants.
   - The note says both, but the commit headline overstates.
6. **Wrong theorem name.** The module docstring item 4 names `stale_counter`,
   which does not exist. The theorems are `stale_cycle`, `stale_window` and
   `stale_err_vectors`.

## 5. Suggested updates (not applied)

**`cell_constraints.json` `gcd_rig.idx_setup`:**
- status `proved`, exactness `exact`;
- lean entries:
  - `RigIdx.idx_setup_suff` (sufficient);
  - `RigIdx.idx_setup_iff` (exact, with the side conditions);
  - `RigIdx.cex_rig` / `cex_open` (counter-run);
  - `RigIdx.idx_nonvacuous` (witness);
  - `RigIdx.idx_fire` (context, token until the first fire);
- inequality `vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`, with `enlo` = F →
  latch enable (or reader request) minimum;
- drop `RigContract.idx_setup` as evidence, or mark it as "under a whole-window
  token hypothesis".

**`B-rig-contract.md`:**
- §2b: replace "made exact" and the whole-window `H_TOKEN_STATIC` with a
  pointer to RigIdx;
- §2d: "refuted" → "excluded given `H_RESULT_FRESH`";
- §2d current-RTL bullet: "`verdict_current` proves no stale verdict" →
  "`verdict_attrib` does, given `H_RESULT_FRESH` / `H_RES_BUNDLED`";
- §5: drop "`stale_window` (necessary)" for `arm_before_idx`;
- module doc: `stale_counter` → `stale_cycle` / `stale_window`.

## 6. Fidelity

Same as RigContract §7:
- the hk sequencer is the cycle model (`H_HK_STA`);
- the paths are `PathOK` bands;
- F is the real `bd_c2n` INIT, binary, in a window-channel loop.

The enable net is one window channel. It is not per-latch: the 32-bit enable
fans out to 16 or more latch pairs, so use `enlo` = the minimum over the
latches.

Effort: about 1.5 h.
