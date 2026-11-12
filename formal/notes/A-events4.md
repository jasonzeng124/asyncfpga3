# A-events4: the event-count domain on the routed gcd_hw R5 control, at real prjxray bands (shard A)

## Verdict

**Works with effort, in two parts.**

1. **The analysis runs on the real route at real prjxray band widths.** This part is measured.
   The domain no longer loses precision the way the window domain did (A-xaudit-gcd: about 11
   ns after reset).
   - At the one-corner bands, every rule holds on **402 of the 405 C-element stages, for all
     time and for every select sequence**:
     - slow `[SLOW_MIN, SLOW_MAX]`, Back margin ≥ 961 ps;
     - fast `[FAST_MIN, FAST_MAX]`, Back margin ≥ 434 ps.
   - The 3 remaining stages are the acknowledge C-elements of the single 3-input
     `control_merge12`, a cascade of two arbiters (§4).
   - At the mixed bands `[FAST_MIN, SLOW_MAX]` the domain finds the **same two own-feedback races
     that fbrace found on seed d, with the same margins**:
     - `ulink_n_falseResult_41` stage 2: **−190 ps**;
     - `ucontrol_merge4.uarb1.ua2`: **−9 ps** (the runt reproduced concretely in
       A-xaudit-gcd).
   - At the mixed bands it also finds **three classes of violation that fbrace cannot see**,
     because they need token/branch reasoning: guarded-pin entry/exit races, delay-line
     contiguity, and arbiter re-arm (§3).
2. **The proof chain is not closed.**
   - Every new rule has its counter-arithmetic core proved in Lean (`Events4.lean`).
   - The Lean recogniser `xevents4` re-derives the stage classification from the real INITs and
     agrees with the analysis: 405 cel + 9 arb, all 1,747 LUTs recognised.
   - Open: the integration into one behaviour-level soundness theorem (`Beh4.safe`), the netlist
     link (`design_beh4`) and the guard-timing discharge. These are `Wip/Events4.lean`, about 3.5
     days.
   - **Until those check, the gcd verdicts below are "the domain's rules hold on the routed
     netlist", not a kernel-checked certificate.**

All numbers are for **one route (seed d)**, nextpnr sha256 9c732bc6303458df (9/9 patch
fingerprints, A-xaudit-gcd §1), with prjxray bands from `xray_delay.py` (md5 99b10a6d).

**This is a single sample.** Only seed d's netlist is in `gcd/inputs/`. fbrace found 7, 10 and 9
mixed-corner candidates on seeds 3, 4 and 5. Rerunning this analysis on them needs their
`net_*.json`; `routed2x.py` regenerates them in about 1 min per seed from the routed JSONs.

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Events4.lean` | **proved** (check OK): `or_sum`, `orL_sum`, `filt_not_both_odd`, `excl_step`, **`merge_excl`**, `sub_step`, `sub_step'`, `reconv`, `filt_add_le`, `filt_le`, **`cel_guard_ph`**, `andCnt`/`orCnt`, `Contig`, **`and_val`**, **`or_val'`**, `andCnt_mono`, `orCnt_mono`, `andCnt_mem`, `orCnt_mem`, **`contig_union`**; negative controls `or_sum_neg`, `excl_step_neg`, `and_val_neg`, `guard_neg` |
| `formal/lean/Formal/Core/XAudit/Events4Main.lean` | compiles, audited. Executable `xevents4`: the TRUSTED recogniser (no theorem) |
| `formal/lean/Wip/Events4.lean` | open shapes (`sorry`): W-E4i integration `Beh4.safe`, W-E4g guard timing, W-E4n `design_beh4`, H_ARB (stated hypothesis), W-E4x n-ary exclusivity |
| `formal/tools-A/xaudit/events4/run.sh` | reproduces everything below (scratch in `/tmp/events4`) |
| `…/events4/skel.py` | cuts the control skeleton (copy-only) |
| `…/events4/classify.py`, `model.py`, `ana.py`, `report.py`, `negctl.py`, `netlib.py`, `shapes.py` | the UNTRUSTED analysis |
| `…/events4/ana_{slow,fast,indep}.txt`, `ana_slow_NEG_fb.txt`, `report.txt`, `recog_skel_d.txt` | results |

### Check

From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Events4.lean                      # [audit] 443 declarations, [check] OK
    ../check.sh Formal/Core/XAudit/Events3.lean Formal/Core/XAudit/Events4.lean \
                Formal/Core/XAudit/Events4Main.lean                  # + executable audit 1145, [check] OK

- There is no sorry, admit, axiom, native_decide or bv_decide.
- Only `propext`, `Classical.choice` and `Quot.sound` are used.
- The negative controls use `decide`.

### Lakefile stanza (for the lead; I did not edit the lakefile)

```toml
[[lean_exe]]
name = "xevents4"
root = "Formal.Core.XAudit.Events4Main"
```

Usage: `xevents4 SKELETON.json [--bands B.json]`. On the gcd skeleton it takes 13 s in the
interpreter. Until the stanza exists, `run.sh` runs it with `lean --run` on private oleans.

## 1. What the domain now covers, and why each step is sound

A wire with reset 0 that has fired `m` times reads `ph false m`. As in Events2/3, the domain
computes min-plus counts over the behaviour's own warps. It adds the following, each a lemma in
`Events4`:

| shape in gcd_hw | rule | Lean |
|---|---|---|
| **merge of different sources**: cond_br ack OR, mux `z = Δ(j0+j1)`, nested ORs (W-E5a) | count = **sum**; exclusivity is **proved by induction**, with no timing condition, from two facts: (1) each arm fires only in its own branch of one steer source S (`x_b ≤ filt_b m`); (2) S cannot start again before the merge has seen the previous transaction (a ≤ 1-token walk S → merge). The arm skew cancels because S's acknowledge *is* the merge. This is why Events3's `Skew` was conservative (W-E5b is subsumed) | `merge_excl`, `excl_step`, `or_sum`, `orL_sum` |
| **steer arm consumed downstream; loop exit and entry** (W-E5c/d) | a Back walk may (R3) cross a merge whose arms are distinct branches of S by jumping to S, and (SUB) pass from a steer arm *through* that steer's acknowledge merge by subtracting the other branch (conservation `filt_add`) | `reconv`, `sub_step`, `sub_step'`, `filt_add_le`, `filt_le` |
| **filtered pins**: bd_steer's AND halves, the mux join's folded `ctl·[s=b]`, the 3-way mux decode | `filt sel b` of the source count, under SelOK (bundling: the select is stable while the request is high; E6) | `Events3.steer_val` |
| **guarded pins**: `x_ack = C(j0, z_ack)`, arbiter `A_b = C(g_b, A0)` | the guarded pin fires in every transaction, the stage only in branch b. It is not a counter pin. While the guard has not advanced, the C-element holds whatever the guarded pin does; otherwise it needs `hguard` | **`cel_guard_ph`** (the reduction). Discharging `hguard` from the ENTRY/EXIT timing conditions is open: W-E4g |
| **delay lines**: FASTFALL AND / FASTRISE OR chains of copies of one source (bdc's request delays) | if the copies' counts are contiguous, AND reads `ph(min hi (lo + lo%2))` and OR reads `ph(max lo (hi − 1 + hi%2))`. Both counts are monotone and lie in `[lo, hi]`, so walks cross a line with band `[min lo, max hi]`. Contiguity is checked per gate: the inputs' representatives are within one event, i.e. a window ≤ W(src) | **`and_val`**, **`or_val'`**, `contig_union`, `*_mono`, `*_mem` |
| **arbiter** (out of domain, no SI) | **H_ARB** (below) | stated in Wip |

### Negative controls (Lean, `decide`)

- `or_sum_neg`: two arms high together lose a token.
- `excl_step_neg`: without the walk fact `m ≤ y0 + y1 + 1`, both arms can be odd.
- `and_val_neg`: copies with a gap (counts 1 and 3) read AND = 1, but `andCnt 1 3` is even. This
  is the failing delay-line condition of §3.
- `guard_neg`: a guarded pin that still shows the previous transaction fires the stage.

### H_ARB: the arbiter is environment choice under mutual exclusion (an explicit hypothesis)

`bd_arbiter`'s state and grant LUTs are **not** analysed: there is no SI and there is
metastability. Each arbiter core is replaced by a **virtual mux core**:

- `g_b = C(r_b, ctl·[σ = b])`, where **σ, who wins each transaction, is an environment choice
  sequence**;
- `ctl = ¬A0`, delayed by `[lo(A0→state arc) + lo(state LUT) + lo(q→grant arc), ∞)`: no new
  grant before A0 has fallen and the state LUT has re-armed, and contention may wait for ever;
- `R0 = g1 + g2`, a merge.

This encodes three things:
- **mutual exclusion** of the grants: at most one `g_b` per `ctl` transaction;
- grants that copy their request once granted;
- no re-grant before A0 falls. The state LUT's INIT shows that `q` holds while `A0 = 1`.

The real arcs r_b → grant LUT → `A_b` are used unchanged, so the Back margins at the arbiter's
C-elements are real-route numbers. R0's tap band is the real (r_b → R0) path minus (r_b → g_b).

A test that could falsify H_ARB (GLS or board): under contention, the grant order must be
explainable by some σ, with no double grant and no grant before A0 falls.

## 2. The run

**Skeleton** (`skel.py`).
- Kept: every reset-carrying storage LUT and every stateless LUT on a control path between them.
  That is **1,747 LUTs**: 414 storage (405 C-elements + 9 arbiter states), 79 steer halves,
  358 AND2 and 177 OR (delay lines and acknowledge ORs), 688 buffers, 4 inverters and 27
  arbiter outputs.
- Cut: the **32 select nets** (data-latch outputs that feed steers and mux joins) become free
  inputs.
- The verdicts quantify over every waveform of the cut nets **and** every select sequence σ.
- The data path is the separate bundling question E6 (SelOK).
- The analysis gives the same output on the skeleton and on the full 9,959-LUT netlist. The
  one exception is the cascade's pins (§4), where the heuristic walk search depends on cell
  order.

**Recognition.**
- `xevents4` (Lean) and `classify.py` agree. The C-elements, read from the INIT over physical
  pins in any order, split as:
  - 338 `n=2 v=0`;
  - 42 `n=2 v=0` with a folded steer (the mux joins);
  - 1 `n=2 v=1` (`uenv1`, a `_set` cell);
  - 10 `n=3`;
  - 14 `n=4`;
  - plus 9 arbiter states (`arb`).
- 0 LUTs are unrecognised.

### Per-stage verdicts (real stages; a stage is clean if every rule on every pin holds)

| family | slow | fast | mixed `[FAST_MIN, SLOW_MAX]` |
|---|---|---|---|
| link stage | 184/184 | 184/184 | 162/184 |
| mux join / ack | 90/90 | 90/90 | 87/90 |
| fork | 44/44 | 44/44 | 42/44 |
| cond_br join | 38/38 | 38/38 | **4/38** |
| arbiter ack C (A1/A2, under H_ARB) | 15/18 | 15/18 | 7/18 |
| compute-unit join | 16/16 | 16/16 | 16/16 |
| control_merge fork | 8/8 | 8/8 | 7/8 |
| control_merge (1-input = fork) | 5/5 | 5/5 | 5/5 |
| rig env | 2/2 | 2/2 | 1/2 |
| **total** | **402/405** | **402/405** | **331/405** |

The 3 at slow and fast are the cascaded arbiter of §4. Merge exclusivity is certified for
68 of 69 merges at every corner; the exception is the cascade's inner R0.

### Margins (ps)

| | slow | fast | mixed |
|---|---|---|---|
| Back pins (784 real) | min **961**, median 6048 | min **434**, median 2829 | min **−190**, median 2594 |
| guarded pins (63): ENTRY | min 439 | min 215 | min **−1278** (10 negative) |
| guarded pins: EXIT | min 3734 | min 1666 | min **−187** (3 negative) |
| delay-line contiguity (164 lines) | min 207 | min 282 | **64 fail**, worst −11,422 |
| per-window bound W | min 2100 (`ucontrol_merge10.uarb1.ua1`), median 9474 | min 934, median 4327 | (lo = fast) min 934 |

**Every negative item at the mixed corner** (`report.txt`):

- **Back (own feedback against the token-correct neighbour response):**
  - `ulink_n_falseResult_41` stage 2: **−190**. Pin I4 ← `ucontrol_merge4.uarb1.ua2`; lo 252 +
    d 648 − hiQ 1090.
  - `ucontrol_merge4.uarb1.ua2`: **−9**. Pin ← grant g2; lo 178 + d 722 − hiQ 909.
  - **These are exactly fbrace's two seed-d control candidates, with the same margins.** The
    other two fbrace candidates are data-latch bits, which are cut here (E6).
  - The cascade's 3 pins have no certificate (§4).
- **Guard ENTRY** (a guarded C-element sees the new branch's guard before the old acknowledge has
  fallen):
  - 9 arbiter acknowledges under H_ARB, from −18 to −1278 (one of them is the cascade's −118). The re-arm path A0 → state LUT →
    q → grant → `A_b` is faster at fast-min than the direct A0 → `A_b` arc at slow-max.
  - `umux3.uya`: −51.
- **Guard EXIT** (the acknowledge falls, and then sees the next transaction's `z_ack` before its
  own feedback has settled):
  - `umux3.uya`: −187;
  - `umux4.uxa`: −56;
  - `umux4.uya`: −77.

  fbrace listed `umux3.uya`, −67, on seed 4 only. These are **new candidates**: the mux
  acknowledge's guard race.
- **Delay-line contiguity**:
  - **What fails.** 64 FASTFALL lines, e.g. `uselect1`'s 26-tap line into `ulink_n139`: local
    window 14,534 against W 3,112.
  - **What it means.** With every element independently at fast-min or slow-max, the line's
    slow copy can still show the previous transaction's HIGH while the fast copy shows the next
    one. The AND then rises without the matched delay: a request that **skips its bundling
    delay**.
  - **Where it holds.** Contiguity holds with ≥ 207 ps at slow and ≥ 282 ps at fast.
  - **Scale.** This is the largest mixed-corner effect: 34 of the 38 cond_br joins are flagged
    through the compute-unit lines that feed them.

### Comparison with A-xaudit-gcd

**Window domain against counter domain.**
- The window domain lost every control node about 11 ns after reset at slow, and about 4 ns
  after at fast. It needed bands ≤ 2% wide to certify one transaction.
- The counter domain holds at the real 17% slow and fast widths, **for all time and for every
  select sequence**. It is not limited to one transaction of one vector.

**fbrace against the counter domain.**
- fbrace is untimed by token: its local check is "own feedback against the fastest structural
  response". The counter domain's Back checks the same inequality with token-correct walks. On
  seed d the two agree exactly at all three corners:
  - 0 negatives at slow;
  - 0 negatives at fast;
  - the same two at mixed.
- The domain adds the guard, contiguity and arbiter-re-arm obligations, which need branch counts.

**Period bounds.**
- They are per-window upper rates only: every stage fires at most once per W
  (`Events2/3.cycle_le` from a closed walk with one token).
- The fastest stage, `ucontrol_merge10.uarb1.ua1`, needs ≥ 2W per 4-phase handshake: ≥ 4.2 ns
  at slow and ≥ 1.87 ns at fast.
- **No lower rate bound (latency) is claimed under choice.** It depends on σ, on the select
  data and on the environment, and Events2Time's `LoCert` is for marked graphs.

### Negative controls of the analysis

- `ana_slow_NEG_fb.txt`: adding 1500 ps to `ucontrol_merge4.uarb1.ua2`'s own-feedback arc gives
  exactly one new negative, that stage at −358 ps, with verdict NOT MET.
- The mixed-corner run is itself a control that can fail: 74 stages fail there.

## 3. Fidelity (gate-fidelity rule)

| item | model | status | test |
|---|---|---|---|
| C-element stages | real INIT over physical pins, any order and arity (n = 2/3/4, folded steer), recognised twice (Python, Lean `xevents4`) | exact functionally (UG474) | GLS with the unisim LUT6 |
| routes and LUTs | per-arc prjxray bands, transport (monotone warp), ps (no 25 ps rounding) | the FIFO hypothesis of Events2 | GLS: SDF transport; board TDC |
| steer / filtered pins | the select is an environment sequence; **SelOK** (select stable while the request is high at that LUT) | hypothesis (bundling, E6) | GLS at both corners: the select route against the request route |
| merges | sum; exclusivity derived, no timing | proved lemma (`merge_excl`); integration open | GLS with a long arm on one branch |
| guarded pins | ENTRY/EXIT timing inequalities | **rule not yet proved** (W-E4g); the reduction is proved | GLS of `bd_mux` with the z_ack fan-out skewed |
| delay lines | contiguity by local windows ≤ W(src) | value lemma proved; the per-gate certificate's soundness is `contig_union` + `cycle_le`, integration open | GLS / board: a short low phase on a FASTFALL line must not skip the delay |
| arbiters | **H_ARB** (virtual mux core, σ free, mutual exclusion) | hypothesis, out of domain | contention GLS; ARBITER.md's MTBF data |
| one corner / mixed | slow and fast assume H_ONE_CORNER; mixed lets each element sit anywhere in sign-off range | as A-xaudit-gcd: the mixed negatives are real only if one die can be fast on some arcs and slow on others | own-feedback against neighbour on one die (TDC) |
| walk search | heuristic DFS (depth 24, two pin orders): a found walk is a valid certificate; a missing one is not a disproof | untrusted | — |

## 4. What remains unrecognised, and why

- **`control_merge12`**, the only 3-input control_merge: two cascaded arbiters, where the inner
  stage's A0 is the outer stage's A1.
  - H_ARB's single-arbiter virtual core does not compose there. The inner R0 is a virtual merge
    read by the outer arbiter's virtual grant, so no single steer source dominates both merges.
  - Consequence: 3 acknowledge pins (`uarb1.ua1/ua2 ← uarb2.ua1`, `uarb2.ua1 ← g`) and 1 merge
    have no certificate at any corner.
  - Fix: a 3-way virtual core (one σ over 3 inputs), or an arbiter model from shard B. About
    0.5 day.
- **Nothing else.** Every LUT is recognised. The open items are proofs, not recognition:
  - W-E4i, integration: 1.5 days;
  - W-E4g, guard timing, which needs a LOWER-bound walk judgement: 1 day;
  - W-E4n, netlist link: 1 day;
  - W-E4x, n-ary exclusivity for the 3-way mux merge (certified by the analysis, proved only
    for binary merges): 0.5 day.
- **Data path** (E6, out of scope): the 32 select nets and every latch. SelOK is where they
  enter the control verdict.

## 5. Effort and what it buys

**Effort.** About 5.5 h:
- reading: 1 h;
- the zoo of real shapes (multi-tap lines, absorbed steers, nested ORs, guarded acknowledges,
  arbiter outputs), and the analysis that covers them: 2.5 h;
- Lean (lemmas, recogniser, Wip): 1.5 h;
- runs and notes: 0.5 h.

**To finish:** about 4 days for a kernel-checked gcd control certificate (W-E4i/g/n/x and the
cascade), plus seeds 3/4/5 at about 5 min each once their netlists are regenerated.

**What it buys:**
- **The first all-time, all-select-sequence analysis of the real routed gcd control at
  real one-corner prjxray widths.** 402/405 stages clean at slow and at fast, with explicit
  margins.
- At mixed corners, the domain separates the C-element own-feedback race (fbrace's class,
  reproduced exactly) from three new classes. Each is a candidate bdc/route gate:
  1. mux and arbiter **guarded-acknowledge** entry/exit;
  2. **FASTFALL delay-line contiguity** (a request can skip its bundling delay when the
     source's low phase is shorter than the line's spread);
  3. **arbiter re-arm** entry.
- The rules, the Lean recogniser and the proved arithmetic are the base of the remaining
  ~4 days to a kernel-checked certificate.
