# B-rig-contract: the rig's own obligations for the gcd_hw capstone (probe Rig)

> **Corrections (2026-10-27, probes Bri and Bsa: notes/B-rig-idx.md, notes/B-self-audit.md).**
> 1. `RigContract.idx_setup` assumes `H_TOKEN_STATIC` (aF=1, bF=0) for the whole
>    window, which the running ring breaks after its first input handshake; its
>    conclusion (c) "F high to the end of the window" is false in the real ring.
>    The constraint `gcd_rig.idx_setup` is now proved, sufficient AND exact, in
>    `RigIdx.lean` (`idx_setup_suff`, `idx_setup_iff`, `cex_rig`, `idx_nonvacuous`),
>    with `token_static` needed only until F's first rise (`idx_fire`).
> 2. "The gcd_hw.v comment's mechanism is refuted" and "explained exactly" are
>    OVERSTATED: what is proved is the open arm at p=1 while idx has moved
>    (`armedOld_iff`, `stale_cycle`, `stale_window`) and steady detector values
>    (`stale_err_vectors`). Excluding an old result surviving to p>=33 is the
>    hypothesis `H_RESULT_FRESH` (not composed with ResetGcd in Lean), and the
>    timed part `C_STALE` (a stale result passing the width filter) is unproved.
>    Read "refuted" below as "excluded given H_RESULT_FRESH".
> 3. `verdict_current` alone does not prove "no verdict can be stale": it needs
>    `verdict_attrib` + `H_RESULT_FRESH` + `H_RES_BUNDLED`.
> 4. §5's "`stale_window` (necessary)" for `arm_before_idx` is withdrawn:
>    `stale_window` is about the RTL without `settled`; no counter-run exists
>    for the current RTL.
> 5. "Bit-exact": `arm_sr`, `hold_pin` and `hold_vec` are modelled as constants.

File: `formal/lean/Formal/Cells/RigContract.lean`. It is Core Lean and imports
`Formal.Cells.ResetContract`, which brings in `CElemTiming` and `CTreeTimed`.
I edited nothing else.

Check command (it takes about 4 s):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/RigContract.lean

- Result: clean. The only output is deprecation warnings for `if_pos`/`if_neg`.
- The file contains no `sorry`, `admit`, `axiom` or `native_decide`.
- I ran `#print axioms` on every theorem below in a scratch copy:
  - all of them use only `propext`, `Classical.choice` and `Quot.sound`;
  - `table_ok`, `stale_err_vectors` and the sticky lemmas use only `propext`.

Sources read:
- `cells/hw/gcd_hw.v`, `cells/hw/gcd_rig.v`;
- `B-reset-contract.md` (section 7.3), `B-reset-gcd.md`;
- `formal/out/cell_constraints.json`, entries `gcd_rig.idx_setup` and
  `gcd_rig.token_static`.

## 0. What the RTL actually does (facts the task statement got slightly wrong)

- **The verdict path has no synchronizer, and it needs none.**
  - The chain is `err_flt`/`ok_flt` (async) -> `uerr_g`/`uok_g` (AND with
    `sel = (idx == vi)`) -> a LUT4 sticky latch, `INIT 16'hEC00`.
  - The sticky's pins are `[raw, q, armed, sticky_keep]`, and it computes
    `q = keep & (q | armed & raw)`.
  - This is an asynchronous latch, not a clocked FSM. So the CLAUDE.md rule
    ("an async signal entering a clocked FSM needs a synchronizer") does not
    apply to it.
  - The race that does matter is the one at the LUT's pins between `armed`
    (hk domain) and `raw` (async plus hk-derived `sel`/`g_v`). That race is
    what is proved here.
- **Places where a clocked element does sample an asynchronous signal.** None of
  them is on the verdict path; all are listed in section 3:
  - `rs0/rs1` (TCK, a proper 2-flop synchronizer);
  - `hk_run`, `lap_run` (2-flop);
  - the JTAG `sr` capture of `mux_d`;
  - `hold_*` into the hk domain;
  - the `errv`/`absv`/`cmpv` captures, which sample hk-domain `armed` and `idx`
    on the asynchronous `lap_ck`/`abs_ck`/`cmp_ck`.

## 1. Model

**Clocked part, cycle level** (`St`, `step`, `run`):
- Every register of the window sequencer is modelled bit for bit as written:
  - `win_cnt` (16 bit), `win_edge_d`;
  - `rst_sr` (load `16'hFFFF` / shift in 0);
  - `idx` (with `hold_pin`/`hold_vec` as constants);
  - `settle_sr` (clear on `rig_rst` / shift in 1);
  - `por_sr` (shift in 1);
  - `settled = |win_cnt[15:11]`;
  - `armed = arm_sr[31] & settle_sr[15] & settled`.
- `arm_sr[31]` is the constant `armG`. It is 1 from the 32nd window edge on and
  never falls.
- `run n` is the state after `n` hk edges from configuration.
- Flops are ideal edge-triggered elements. Hk-to-hk setup/hold is `H_HK_STA`:
  one BUFG clock domain, closed by static timing. The cycle model *is* that
  assumption.

**Timed boundary** (`PathOK e lo hi v s`):
- `e n` is the time of hk edge `n`, with `H_HK_PERIOD: e n + Tlo ≤ e (n+1)`.
- A path from hk flops to a pin in the asynchronous part (clock-to-out, LUTs,
  route) shows the cycle value on `[e n + hi, e(n+1) + lo)`.
- If the value holds across edge `n+1`, it also shows it through the transition
  band. This is `H_NOGLITCH_STEADY`.

**Frontier controller**: `ResetContract.c2n_frontier`, used unchanged. It is a
window-channel feedback loop of the real `bd_c2n` INIT.

**Sticky and gates**: the real INITs `0xEC00`, `8` and `4`, through
`lutB`/`lutK`.

**Vector table**:
- Transcribed from `gcd_rig.v`.
- The expected values are checked against Stein's algorithm, transcribed from
  `bdc/simcheck.py:ref_gcd`, which is itself a transcription of Dynamatic's
  `gcd.c`. They are also checked against `Nat.gcd` (`table_ok`).
- `dynamatic/` is not checked out in this tree, so the C itself was not read.

## 2. Theorems

Throughout, phase `p = n mod 65536`. A **load edge** `n0` is the edge that sets
`win_cnt := 1`, which is where `win_edge_d = 1` is sampled
(`Load n0 := 65537 ≤ n0 ∧ n0 % 65536 = 1`).

### 2a. Sequencer closed forms (all from configuration, no timing)

| theorem | statement |
|---|---|
| `wc_run`, `wed_run`, `por_run`, `rst_run`, `settle_run`, `idx_run` | exact closed forms of every register after `n` edges |
| `rr_steady`, `rr_window` | `rig_rst` is high exactly at `p ∈ [1,16]`: 16 hk cycles, rising on the load edge itself |
| `idx_const`, `idx_moves` | `idx` is constant on edges `[n0, n0+65535]`. Unpinned, it moves at every load edge. |
| `armed_phase` | **current RTL:** `armed → p ≥ 2048`, for every `n` and any `arm_sr`/`settle_sr` |
| `armed_iff` (n ≥ 2^17) | non-vacuity: `armed ↔ p ≥ 2048`, i.e. open 63488 of 65536 cycles |
| `armedOld_iff` (n ≥ 2^17) | **without `settled`:** `arm_sr[31] & settle_sr[15] ↔ p ∈ {0,1} ∪ [33, 65535]` |

### 2b. (1) `idx_setup`: the constraint `gcd_rig.idx_setup`, now a composed theorem

**Setting.**
- `F` is a frontier link controller:
  - for example `ulink_n1__1.ctl.u`, which carries the rig token (ResetGcd node 1696);
  - it has the real `bd_c2n` INIT and a window-channel loop
    `[dlmin,dlmax] / [dwmin,dwmax]`.
- `rstP` is rst at F's pin.
  - Its path from `rig_rst` is `PathOK [rlo, rhi]`.
  - It falls once in its band at `r` (`H_RST_ONE_FALL`).
- `idxP` is the operand word at F's latch d-pins and at the direct
  `a_data`/`b_data` readers. Its path is `PathOK [vlo, vhi]`.
- `enlo` is the minimum delay from F's output to the latch enable. `su` is the
  setup time of the latch or reader.

**Inequality (the entry's form, made exact):**

    vhi + su  ≤  16·Tlo + rlo + dlmin + enlo          (H_IDX_SETUP)

with these terms:
- `vhi` = tCO(idx) + vector decode LUTs + route, maximum;
- `16·Tlo` = rst width;
- `rlo` = tCO(rst_sr) + rst route to F.I3, including the site pin, minimum;
- `dlmin` = F's I3 -> O6 arc, minimum.

These are also needed:
- `H_RST_LONG: rhi + dlmax + dwmax ≤ 16·Tlo + rlo` (F's loop settles within the
  reset);
- `H_TOKEN_STATIC` (the constraint `gcd_rig.token_static`);
- `H_HK_PERIOD` with `Tlo > 0`.

**Conclusions.**
- (a) The operands are the window's vector on `[e n0 + vhi, e(n0+65536) + vlo)`.
- (b) Every instant in the window after F's reset hold at which F is high
  satisfies `e n0 + vhi + su ≤ t + enlo`. No latch enable derived from F comes
  sooner than `su` after the operands settle.
- (c) F fires: it is high from `r + dlmax` to the end of the window.

**The hold side is handled differently.**
- The operands change at the next load edge, while the ring is running. The
  input handshake under way at that instant can latch a mixture.
- That is not prevented. It is made harmless by (2): the arm has been closed
  since `e(n0+65535) + ahi < e(n0+65536) + vlo`, and the next window's 16 hk
  cycles of reset flush the ring.
- So "held until consumed" is true only for laps whose verdicts can count. That
  is the right statement, and it is proved, as `verdict_current` plus (a).

The setup margin is huge: about 16 hk cycles, or 120 ns, against a few ns of
decode.

### 2c. (2) The result-capture path

**`verdict_current` (current RTL).**

Assume:
- the arm path is `PathOK [alo, ahi]`;
- the idx readers (operands, `g_v` at the compare, `sel`) are `PathOK [vlo, vhi]`;
- `H_ARM_BEFORE_IDX: ahi ≤ Tlo + vlo`;
- `H_VEC_EARLY: vhi ≤ 2047·Tlo + alo` (trivial).

Then:
- Take any instant `t` in window `n0`'s tile `[e(n0-1) + ahi, e(n0+65535) + ahi)`
  at which a sticky's arm pin is **not a definite 0**: either 1 or intermediate,
  so that the sticky could set.
- Then `t ≥ e(n0+2047) + alo`, and the idx readers show the window's idx.
- The tiles partition time after the first window.

**`verdict_attrib`.**
- It adds the kernel-side fact as the named hypothesis `H_RESULT_FRESH`: a result
  present on the padded `res_req` at such a `t` was computed from operands read
  at some `s ∈ [e(n0+16) + rlo, t]`.
- `H_RESULT_FRESH` is the reset contract (ResetGcd `gcd_reset_binary`,
  `gcd_release_quiet`) plus the one-token ring. It is cited, not derived here.
- With `H_IDX_BEFORE_RELEASE: vhi ≤ 16·Tlo + rlo`, it concludes
  `out t = K(idxP t)`. In words, the compare judges the kernel's answer to the
  same vector whose expected value and `sel` it uses.

**Gate lemmas.**
- `sticky_sets_only` (Kleene, all 27 cases): a sticky leaves 0 only if
  raw, arm and keep are all non-0.
- `sticky_holds_K`: with `armed = 0` and `keep = 1`, the excitation is `q`,
  even when raw is X.
- `gate_needs_req`: `res_req = 0` forces `err_raw = ok_raw = 0`, so the result
  is sampled only while the completion (padded) is present.
- `sticky_eq`: `INIT EC00 = keep & (q | armed & raw)`.

### 2d. The "stale result after reset" claim: checked, and the gcd_hw.v comment's mechanism is refuted

`stale_cycle`, `stale_window`, `stale_err_vectors` and `stale_nonvacuous` give
the counter-run **for the RTL without `settled`**. That is the design the
comment above `settled` describes as having been measured.

**Which cycles.**
- On the load edge (`win_cnt 0000 -> 0001`):
  - `idx` moves;
  - `rst_sr` loads, so `rig_rst` rises on the same edge;
  - `settle_sr` still shifts in a 1, because it saw `rig_rst = 0` before the
    edge.
- So `arm_sr[31] & settle_sr[15]` stays 1 for the whole hk cycle `p = 1`.
- It closes only at the next edge (`p = 2`). It reopens at `p = 33`.
- In the timed window `[e n0 + max(ahi,vhi), e(n0+1) + min(alo,vlo))`, the old
  arm pin is 1 while the idx readers already show the new vector.

**What sets.**
- Suppose the result on `res_req` in that window is the previous vector's.
  It can be still high, or arrive before rst reaches the output link plus
  `urdly`'s 16 elements.
- `mism` is then computed against the NEW `g_v`, and `sel` selects the NEW
  vector.
- With the real INITs, err sets on every vector of the sweep except 3, 5 and 13.
  Their predecessors (2, 4, 12) have the same expected gcd, so on those three
  `ok` sets instead.
- The pair seen on the board is a stale `err` plus the vector's own legitimate
  `ok`, which matches "every one of those five had ok set as well".

**Prediction (falsifiable).**
- With `settled` removed, the stale mechanism can never set err on vectors 3,
  5 or 13.
- The `errv` capture (addr 18/19) should then read the previous vector's
  expected gcd, with `errv_idx` equal to the new vector.

**Current RTL.**
- `armed = 0` at `p = 0` and `p = 1`: `settled` fell at the `FFFF -> 0000` edge,
  one hk cycle *before* idx moves.
- `verdict_current` proves no verdict can be stale, given
  `H_ARM_BEFORE_IDX` (a margin of about one hk period, roughly 7.6 ns).
- **So with the current RTL, an ok+err pair from this mechanism is impossible.**

**The comment's explanation is refuted.**
- The comment says the old result is "still in flight" after release plus
  `settle_sr`.
- `armedOld_iff` shows the old arm was CLOSED on all of `p ∈ [2, 32]` and
  reopened at `p = 33`, 16 cycles after `rig_rst` fell (`p = 17`).
- `gcd_reset_binary` says 16 hk cycles of rst leave no request in flight.
- What the 2048-cycle `settled` actually cured is the one open cycle at `p = 1`,
  by closing the arm one cycle before idx moves. Any `settled` that falls at the
  `FFFF -> 0000` edge would do; the 2048-cycle drain buys nothing more.
- This confirms the hypothesis in B-reset-contract §7.3, now with the exact
  cycle.
- Still a model result, not a measurement. A board test is in §5.

**What the counter-run does not prove.**
- That `res_req` actually carries an old result in that cycle, for longer than
  the width filter. This is condition C_STALE: the old `res_req` must be high on
  an interval of length > WFILT·(element) + 2 LUT after `g_v` and `sel` have
  settled, inside the open-arm band.
- How often that happens: one lap is in flight and its result is high briefly,
  so it is a race per window.
- `stale_err_vectors` evaluates the detector at its steady values, not as a
  timed trace through the filter.

### 2e. Non-vacuity

- `pathOK_transport`: a fixed transport delay is a `PathOK`.
- `verdict_nonvacuous`:
  - setting: hk period 7600 ps (27.5 hops × about 275 ps, from gcd_hw.v's own
    figures), arm path 600 ps, idx path 1500 ps;
  - all hypotheses of `verdict_current` hold;
  - at phase 3000 of window `2·65536+1` the arm pin is 1.
- `stale_nonvacuous`: with the same numbers, 1500 ps after the load edge:
  - the old arm is 1;
  - the current arm is 0;
  - the readers show the new idx.
- That pair is the negative control: the same trace, and the two arms differ
  only in `settled`.

## 3. The rig's hypotheses (complete list)

| name | what it stands for | how to test |
|---|---|---|
| `H_HK_STA` | hk-to-hk setup/hold met: one BUFG domain, the cycle model is exact | nextpnr STA with `--freq` set to the hk ring's slow-corner frequency; ro_measure.py period |
| `H_HK_PERIOD` (`Tlo`) | min hk period | `hw/ro_measure.py` at the slow and fast corner, take the min |
| `H_PATH[lo,hi]` for arm, idx/operands/`g_v`/`sel`, rst | flop-to-pin path delay band (tCO + LUTs + route, prjxray FAST_MIN / SLOW_MAX) | routed SDF / prjxray per path, ≥ 4 seeds |
| `H_NOGLITCH_STEADY` | a path whose logical value holds does not glitch. For `armed`: `settled` is constant 0 on `p ∈ [0,2047]` and the OR is monotone at its two real transitions. A low glitch mid-window (`0FFF -> 1000` inside the OR) is harmless (`sticky_holds_K` with q = 1) | X/edge scan of the arm LUTs; GLS |
| `H_RST_ONE_FALL` | rst at F falls once inside its band (one flop edge through a passive route) | GLS of the routed rst net |
| `H_ARM_BEFORE_IDX: ahi ≤ Tlo + vlo` | **new rig obligation**: the arm reaches every sticky's I2 low before any idx-derived change reaches its I0 (via `sel` or via `g_v`/`mism`) | EndpointOK with launch = the hk edge `FFFF -> 0000`: data = `win_cnt` tCO + settled + armed LUTs + route to `u*_s.I2` (hi); request = one hk period (lo) + `idx` tCO + decode + `sel`/`mism` path to `u*_s.I0` (lo). Margin ≈ one period |
| `H_IDX_SETUP` | the `gcd_rig.idx_setup` inequality above | EndpointOK as in the entry |
| `H_RST_LONG` | F's reset hold sets in within the 16-cycle reset | trivially met: one LUT loop vs 16 hk cycles |
| `H_TOKEN_STATIC` | constraint `gcd_rig.token_static` (structural) | — |
| `H_RESULT_FRESH` | after the window's reset and before the arm opens, no pre-reset result survives; the one token makes `res_req` belong to operands read after release | ResetGcd `gcd_reset_binary` / `gcd_release_quiet`; H_NO_RETURN still argued (B-reset-contract §6) |
| `H_RES_BUNDLED` (`CMPD`) | `out0_data` is stable while the padded `res_req` is high (the compare's own bundling) | separate rig obligation; not in cell_constraints yet |
| `H_HOLD_STATIC` | `hold_pin`/`hold_vec` do not change during a measurement (they enter the hk domain from TCK with no synchronizer) | procedure: `gcd_measure.py` writes hold, then clears |
| **`H_SYNC_RESOLVES`** | every flop that samples a signal asynchronous to its clock resolves within its next cycle (MTBF excluded per the digital-only north star) | — (excluded) |

`H_SYNC_RESOLVES` is used at these points:
- (i) `rs0/rs1` and `hk_run`/`lap_run` (2-flop, fine).
- (ii) The JTAG `sr <= cap_word` capture of `mux_d`. The stickies are
  asynchronous to TCK; they are read after the run, and the counters are
  poisoned while `hold_run` is set.
- (iii) `hold_*` into `idx`'s load. If `hold_vec` changes at a load edge, `idx`
  can resolve to a third vector. That is harmless, because sel, g_v and the
  operands all read the same resolved register, and the arm is closed.
- (iv) **`errv`/`absv`/`cmpv`**:
  - These sample hk-domain `armed` and `idx` on `lap_ck`/`abs_ck`/`cmp_ck`, with
    no synchronizer.
  - A metastable `armed` drives the CE of 37 flops, so `errv_valid` can set
    while `errv`/`errv_idx` do not load: a multi-bit-enable hazard.
  - `errv_idx` itself is safe: idx is constant for at least one hk cycle on
    either side of every `armed` transition (`idx_const` + `armed_iff`).

### Unproved rig obligation found (not in cell_constraints)

- **`errv` capture race.**
  - `errv` loads on `lap_ck = BUFG(res_req)`, gated by `rig_err`.
  - `rig_err` is the WIDTH-FILTERED `err_flt`. It rises about 1 LUT + WFILT
    elements + 1 LUT after `res_req`.
  - `lap_ck` arrives after a BUFG plus the clock tree.
- This is the same shape `gcd_hw.v` documents as a *measured* failure for
  `cmpv`: "captured nothing at all".
- The obligation is `err_flt` rise + setup ≤ BUFG + clock-tree insertion (min).
  It is unverified and may fail.
- It affects only the diagnostic word at addr 18/19, not the verdict stickies.

## 4. What did not work, and what is unproved

- **Kernel recursion trap (fixed).** If omega has to identify `e (n0+65535+1)`
  with `e (n0+65536)` up to defeq, the kernel unfolds 65536 successors and stops
  with "deep recursion".
  - Fix: all index arithmetic goes through propositional equalities (`e_le`,
    `path_const` with an explicit end index `N`).
  - Worth knowing for anyone modelling the hk windows.
- `H_RESULT_FRESH` is a hypothesis, not a theorem. Composing ResetGcd's
  GMW-model network result with these ps-time bands is the same model gap
  B-reset-contract §6 records (shard A's Bridge).
- The counter-run is at steady values for the detector. Its timed part, through
  the `a & delay(a)` filter (C_STALE), is stated and not proved. Its probability
  is not modelled.
- No route was used, so no inequality is evaluated:
  - `H_IDX_SETUP` has a margin of about 16 hk cycles;
  - `H_ARM_BEFORE_IDX` has a margin of about one hk period.
  - Both are very likely to hold, but neither has been checked.
- The first window (configuration to edge 65537) is excluded from the steady-state
  theorems. There `rst_sr` starts at `FFFF` and shifts from edge 1, so it is off
  by one relative to later windows. `armed` is closed there anyway: `arm_sr` is
  0 until 32 window edges have passed.

## 5. Suggested updates (not applied; this probe writes only its own files)

**`cell_constraints.json` `gcd_rig.idx_setup`:**
- status `proved` (sufficient);
- lean `RigContract.idx_setup` (role sufficient) and `RigContract.verdict_current`
  (hold side);
- inequality `vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`, with `rlo` including
  tCO(rst_sr), so it appears on the request side as well;
- replace the exactness_note's §7.3 sentence with a pointer to
  `RigContract.stale_*`.

**New entry `gcd_rig.arm_before_idx`:**
- form `H_ARM_BEFORE_IDX`;
- launch = the hk edge at which `win_cnt` goes `FFFF -> 0000`;
- data = arm path to each `u*_s.I2` (hi);
- request = `Tlo` + idx path to each `u*_s.I0` via `uerr_g`/`sel` and via
  `g_v -> mism -> uerr_d -> filter` (lo);
- margin 0;
- `RigContract.verdict_current` (sufficient), `stale_window` (necessary: drop
  the `settled` closing and it fails).

**Possible new entries:**
- `gcd_rig.res_bundled` (CMPD);
- `gcd_hw.errv_capture` (above).

**gcd_hw.v comment above `settled`:** the stated mechanism is wrong. A board
test of the corrected mechanism:
- Replace `settled` by a term that falls at the `FFFF -> 0000` edge and rises at
  `p = 33`, e.g. `~(win_cnt == 0 || win_cnt == 1)` combined with
  `settle_sr[15]`.
- Expected: no ok+err pairs. That separates "closing before idx moves" from
  "2048-cycle drain".
- Conversely, delaying the `idx` load by one hk cycle with `settled` removed
  should also remove them. This is B-reset-contract's test.

## 6. Verdict

**Works.** Effort was about 2.5 h.

Proved, given the named hypotheses:
- `gcd_rig.idx_setup` is now a composed theorem: the clocked sequencer plus
  `c2n_frontier`, with an exact inequality.
- The verdict cannot be stale in the current RTL, given one new rig obligation
  `H_ARM_BEFORE_IDX` (a margin of about one hk period).
- The "stale result after reset" ok+err pairs are explained exactly. They come
  from the one hk cycle `p = 1` in the pre-`settled` RTL, on every vector except
  3/5/13. The comment's drain mechanism is refuted.

To finish (about 1 day):
- evaluate `H_IDX_SETUP` and `H_ARM_BEFORE_IDX` on the 4 routed gcd_hw seeds
  (static_route forms);
- write the timed filter part of the counter-run (C_STALE);
- bridge `H_RESULT_FRESH` to ResetGcd.

What it buys: the capstone's top-level claim ("ok=FFFF, err=0000 means the
kernel computed gcd on every vector") now has its rig half stated and proved.
What remains is the kernel half plus routed numbers for two inequalities.

## 7. Fidelity per primitive

- **hk flops:** ideal edge-triggered (H_HK_STA). Metastability is excluded
  (H_SYNC_RESOLVES) and is used only on the CDC points listed in §3, none on the
  verdict path.
- **Sequencer registers:** bit-exact to the RTL, including the load and shift-in
  values, the initialisers, and `settled` as `wc / 2048 % 32 ≠ 0`, i.e.
  `|win_cnt[15:11]` for a 16-bit value.
- **Combinational hk-to-async paths:** one delay band `[lo, hi]` per path with
  no glitch while the value holds (`PathOK`). This is coarser than per-arc
  EndpointOK. The checker should expand each band into arcs.
- **`bd_c2n` frontier:** `ResetContract.c2n_frontier`:
  - real INIT via `lutB`;
  - a window-channel LUT plus a feedback wire, one routed wire with a delay
    interval;
  - binary values (not Kleene).
- **Sticky LUT4 `EC00`, LUT2 `8`/`4`:**
  - real INITs via `lutB`;
  - via `lutK` (H_KLEENE_LUT: pass-transistor mux tree) for the hold and forcing
    lemmas;
  - the sticky's feedback (O -> I1) is not timed here. Its loop timing is the
    same as any bd_c* cell (CElemTiming).
- **Vector table:** verbatim. `stein` is a transcription of `ref_gcd` (simcheck),
  not of `gcd.c`, because `dynamatic/` is absent from this tree.
