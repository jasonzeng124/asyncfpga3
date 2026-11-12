# A-events5: the integrated counter domain `Beh4`, four gcd_hw seeds, and the FASTFALL finding (shard A)

## Verdict

**Works, with two named hypotheses left open.**

1. **Integration (W-E4i) is proved.** `Beh4.verdictW` checks with no sorry and no axioms beyond
   `propext`, `Classical.choice` and `Quot.sound`. It covers every behaviour in the bands, for
   every select sequence, with every node equal to its reset value flipped `M t j` times at
   every time. It covers:
   - C-elements with guarded pins;
   - binary merges, with exclusivity derived and no timing condition;
   - FASTFALL / FASTRISE delay lines;
   - steer (filtered) pins;
   - branch-aware Back walks (R1, R3, SUB).

   It holds from decidable-shape certificates (`BackW`, `LineCert`, `ExclCert`, `Net4.OK`)
   plus two named hypotheses:
   - **SelOK** (bundling, E6, as in Events3);
   - **GuardOK** (the guarded-pin timing).

   Two items are **not done**:
   - **W-E4g**, discharging GuardOK from the ENTRY/EXIT inequalities;
   - **W-E4n** (`design_beh4`), the link from the parsed netlist to `Beh4`.

   Both are stated precisely in `Wip/Events5.lean`, with the reason each is open. So xevents4's
   verdict on gcd is a theorem **about the model `Beh4`**: every unguarded stage, every merge and
   every delay line, under SelOK + GuardOK + H_ARB. It is **not yet a theorem about the parsed
   netlist**: that step is W-E4n.
2. **Seeds 3, 4 and 5 are regenerated and analysed** (with seed d) at slow, fast, mixed and the
   project guardband, with strict margins (a margin of 0 is a FAIL).
   - The four routes are **byte-identical** to A-xaudit-gcd's: same SDF and routed-JSON md5s,
     same routed2x nets.
   - Toolchain: nextpnr sha256 **9c732bc6303458df**, 9/9 fingerprints ok before every build.
   - At one corner, every seed has 402/405 stages clean. The 3 that fail are the cascaded
     arbiter, as before.
3. **FASTFALL contiguity: the −11.4 ns is a modelling artefact; a residual is real, under
   mixed corners only.**
   - **The artefact.** `events4/model.py` gave each tap of a line its whole path band, all the
     way to the stage pin. In the pair window it therefore counted the band width of the
     **shared chain suffix**, about 26 × 560 ps. The corrected per-gate window (`contig5`)
     cancels that suffix.
     - Mixed-corner contiguity failures drop from **64 → 1** on seed d. The cited line
       `uselect1 → ulink_n139` goes from −11,422 to **+895 ps**.
     - On seeds 3, 4 and 5 the failures drop from 59/63/59 → **4/0/0**.
     - At the guardband corner, 4–6 failures per seed drop to **0**.
     - At one corner there are **0** failures, including seed 3 slow, where the old window
       failed at −359.
   - **The residual.** What remains is exactly rule F's missing in-flight term at the head hop
     of a `bd_delay_gated` line:
     - seed d: `ushli0`, **−365 ps**;
     - seed 3: `uselect1`, **−726 ps**, plus 3 at −85 to −93 ps.
   - **It reproduces concretely** in a fixed-delay transport trace of the routed line, run at the
     analysis's own bound on the source's low phase (`linetrace.py`, §3). The request rises
     **2602 ps early**, and a 365 ps runt reaches the C-element.
   - **It needs one die to be fast-min on the ring and slow-max on the line head at the same
     time.** At the project guardband ([0.668·SLOW_MAX, SLOW_MAX]) the margin is +1,572 ps on
     seed d. In the rig's actual operation, the source's low phase is about 260 ns, not 2.2 ns.

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Events5Line.lean` | **proved** (check OK). Delay lines in the warp model. |
| `formal/lean/Formal/Core/XAudit/Events5.lean` | **proved** (check OK). `Net4`, `Bands4`, `Beh4`, `safe`, the certificates, `verdict`, `verdictW`. |
| `formal/lean/Wip/Events5.lean` | open shapes (`sorry`): W-E4g, W-E4n, W-E4x (n-ary merges), U3, the cascade. Compiles. |
| `formal/tools-A/xaudit/events5/ana5.py` | events4's analysis, plus strict margins and `contig5`, the corrected contiguity check. UNTRUSTED. |
| `…/events5/run5.sh`, `table.py`, `table.txt`, `ana5_<seed>_<corner>.txt` (16) | per-seed runs and tables |
| `…/events5/linetrace.py`, `witness.py`, `trace_*.txt` | concrete line traces (§3) |
| `…/events5/builds.txt`, `inputs/` | build fingerprints and md5s; xz nets for seeds 3/4/5 and bands (seed d's net and one-corner bands are in `gcd/inputs/`) |

### Check

From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Events3.lean Formal/Core/XAudit/Events4.lean \
                Formal/Core/XAudit/Events5Line.lean Formal/Core/XAudit/Events5.lean
    # [audit] 761 declarations checked, [check] OK

- Events3 and Events4 are listed because lake has not built their oleans.
- There is no sorry, admit, axiom, native_decide or bv_decide.
- The negative controls use `decide`.

**No new executable, so there is no lakefile stanza.** `Events5Main` was not written. An
executable that prints `verdictW`'s conclusion would have to check `BackW` / `LineCert` /
`ExclCert` derivations emitted by `ana5.py`, against a `Net4` built by the recogniser. That is
W-E4n.

## 1. What is proved (theorem names)

### `Events5Line` (namespace `Formal.Core.XAudit.Events5`)

- **Per-gate certificate.** `LTree`, `LTree.Cert` (the per-gate contiguity certificate), and
  `tree_contig`: with `OneEvent` (at most one source event per `W`), the certificate gives
  contiguous tap counts.
- **Line values.** `line_and` (FASTFALL value `ph (andCnt lo hi)`) and `line_or` (FASTRISE).
- **Where the window comes from:**
  - `hop_skew`: two tap paths that meet at a gate are within `max(hiQ−loP, hiP−loQ)`. Only the
    paths up to that gate's pins count. The suffix is the same warp for both, and the gate is
    one warp (H_ATOMIC_LUT).
  - `prefix_skew` and `prefix_skew_tight`: a **shared prefix does not cancel** in the warp
    model. It adds its band width, and the bound is attained.
  - `warp_comp` and `gate_cert_of_hop`.
- **Negative control.** `line_gap_neg`: a low phase shorter than the hop window gives tap counts
  1 and 3, the AND reads 1 while `andCnt` says 0, and `OneEvent` fails.

### `Events5`

- **Indexed families and lines.** `fsum`, `fany`, `fall`, `fodd`, `fmax` and their lemmas;
  `fany_sum` (an n-ary merge with ≤ 1 arm high reads the sum); `andF_val` / `orF_val` (indexed
  lines); `contigF_chain`.
- **The network and its behaviours.**
  - `Net4`: node kinds stage / merge; pin kinds `plain | filt | multi | guard`, copies `nc`,
    `op`, group `grp`, branch `br`, guard pin `gp`.
  - `Net4.OK`: the decidable structural side conditions.
  - `Bands4`: per-copy bands, plus the hop windows `dw`.
  - `Beh4`: warps per LUT, per copy and per feedback; `hskew` (copies of a line are sampled
    within `dw`); `mg0` (a merge is low at time 0); `gcmono`.
  - `Beh4.M`: the count recursion. A stage counts `fmin` of its pins, a merge the `fsum`. A pin
    counts `filt` / `andCnt` / `orCnt` / `gc` of its copies.
- **Soundness.** `M_mono`, `E_mono`, `q_le_P`, `cel_guards` (any number of guarded pins),
  `pin_val`, and **`Beh4.safe`**: under `Net4.OK`, `SelOK`, `LineOK`, `PinOK`, `ExclOK` and
  `GuardOK`, `c j t = ph (v j) (M t j)` for all `t` and `j`.
- **Certificates ⇒ count facts.**
  - `P_le`, `M_le_pin`, `walk_le`, `cycle_le`, `oneEvent`, `Back4` ⇒ `pinOK_of_back`.
  - `LineCert` ⇒ `lineOK_of_cert`.
  - `UArm`/`UArmD` ⇒ `ubound`/`ubound_d` (the U-bounds).
  - `ExclCert` ⇒ **`exclOK_of_cert`**: `Events4.merge_excl` instantiated on the behaviour, for
    binary merges. There is no timing condition on the arms.
- **Branch-aware walks.** `WD` is the inductive walk derivation with steps `refl`, `r1`, `fpin`,
  `r3` (`Events4.reconv`), `lift` and `sub` (`Events4.sub_step` via `filt_add`). **`wd_sound`**
  proves it sound. `BackW` ⇒ `pinOK_of_backW`.
- **`Beh4.verdict` / `Beh4.verdictW`.** From the certificates and `SelOK` + `GuardOK`, every
  node of every behaviour reads its count.
- **Negative controls:** `andF_neg` (gap: AND = 1, count says 0, `ContigF` false), `fany_neg`
  (two arms high lose a token) and `cel_guards_neg`.

### Coverage of the analysis by the Lean judgement (seed d)

- **Back walks.** Of the 784 Back walks, 323 use R1 only, 300 use R3, 73 use SUB and 88 use
  both. All four kinds are steps of `WD`.
- **Merges.** Of the 69 merges, 68 are binary (`ExclCert`) and 1 is ternary (W-E4x).
- **Guards.** 63 guarded pins are covered by `cel_guards`, under GuardOK.
- **U through merges.** `UArmD` certifies an arm's branch through stage pins only. `ana.py`'s
  `compute_U` also passes through reconverging merges (U3). Whether any certified gcd merge
  needs U3 was not measured: that needs the derivations emitted (W-E4n).

## 2. Seeds d, 3, 4, 5 (strict margins; a margin ≤ 0 is a FAIL)

**Build.**
- Worktree: `/tmp/gcdwt2`, a detached HEAD 520a43f, removed at the end.
- Command: the BOARD-QUEUE #2 command, as in A-xaudit-gcd, with no `--freq`.
- `toolchain.sh` ran before each build: 9/9 ok, nextpnr sha256 9c732bc6303458df.
- SDF md5s: d a9c4e265, 3 e0d4202b, 4 b1b4b951, 5 030c36bd. They are identical to A-xaudit-gcd's
  four builds (worktree cbe4a52), and so are the routed-JSON md5s and the routed2x nets
  (`events5/builds.txt`).
- The prjxray arcs come from `xray_delay.py` (md5 99b10a6d).

**Corners.**
- `slow` [SLOW_MIN, SLOW_MAX], `fast` [FAST_MIN, FAST_MAX], `mixed` [FAST_MIN, SLOW_MAX].
- `gb` [0.668·SLOW_MAX, SLOW_MAX], where 0.668 = GUARD_LO/GUARD_HI of `skew.py`. This is one die
  with the project's guardbanded spread.

**Run details.**
- `PYTHONHASHSEED=0` is pinned. With an unpinned hash seed, one seed-d slow run found walks for
  the cascade (405/405). events4's walk search iterates Python sets, so its certificate set
  depends on the order. I count the cascade as uncertified in every case: H_ARB does not
  compose there.
- Every row is one route of one placer seed. The 4 seeds give the spread.

| seed corner | stages clean | non-cascade bad | Back min / ≤0 | guard ENTRY min / ≤0 | guard EXIT min / ≤0 | contiguity events4 min / fail | **contig5** min / fail | merges | W min |
|---|---|---|---|---|---|---|---|---|---|
| d slow | 402/405 | 0 | 961 / 0 | 439 / 0 | 3734 / 0 | 207 / 0 | 2669 / 0 | 68/69 | 2100 |
| d fast | 402/405 | 0 | 434 / 0 | 215 / 0 | 1666 / 0 | 282 / 0 | 1260 / 0 | 68/69 | 934 |
| d mixed | 389/405 | 13 | −190 / 2 | −1278 / 10 | −187 / 3 | −11422 / 64 | **−365 / 1** | 68/69 | 934 |
| d gb | 399/405 | 3 | 568 / 0 | −52 / 3 | 2339 / 0 | −3027 / 6 | 1572 / 0 | 68/69 | 1692 |
| 3 slow | 402/405 | 0 | 772 / 0 | 446 / 0 | 3559 / 0 | −359 / 1 | 2060 / 0 | 68/69 | 1472 |
| 3 fast | 402/405 | 0 | 343 / 0 | 195 / 0 | 1569 / 0 | 183 / 0 | 997 / 0 | 68/69 | 623 |
| 3 mixed | 380/405 | 21 | −265 / 4 | −819 / 17 | −217 / 1 | −12553 / 59 | **−726 / 4** | 68/69 | 623 |
| 3 gb | 402/405 | 0 | 458 / 0 | 130 / 0 | 2664 / 0 | −4256 / 5 | 1486 / 0 | 68/69 | 1194 |
| 4 slow | 402/405 | 0 | 779 / 0 | 826 / 0 | 2937 / 0 | 1376 / 0 | 2953 / 0 | 68/69 | 1767 |
| 4 fast | 402/405 | 0 | 345 / 0 | 366 / 0 | 1452 / 0 | 1097 / 0 | 1367 / 0 | 68/69 | 766 |
| 4 mixed | 385/405 | 17 | −167 / 7 | −869 / 7 | −373 / 5 | −11553 / 63 | **259 / 0** | 68/69 | 766 |
| 4 gb | 402/405 | 0 | 459 / 0 | 227 / 0 | 1750 / 0 | −2910 / 6 | 2025 / 0 | 68/69 | 1429 |
| 5 slow | 402/405 | 0 | 210 / 0 | 715 / 0 | 2739 / 0 | 668 / 0 | 2478 / 0 | 68/69 | 1731 |
| 5 fast | 402/405 | 0 | 118 / 0 | 292 / 0 | 1213 / 0 | 762 / 0 | 1107 / 0 | 68/69 | 778 |
| 5 mixed | 389/405 | 13 | −395 / 4 | −503 / 11 | −50 / 1 | −11938 / 59 | **67 / 0** | 68/69 | 778 |
| 5 gb | 401/405 | 1 | −19 / 1 | 296 / 0 | 1871 / 0 | −3685 / 4 | 1691 / 0 | 68/69 | 1393 |

How to read the table:
- "stages clean" uses contig5 and counts the 3 cascade stages as bad.
- "non-cascade bad" lists stages outside `control_merge12`.
- **Every failing item** (non-cascade, mixed and gb) is in `events5/table.txt`.

### One corner: 402/405 on all four seeds, for all time and every select sequence

- The 3 failures are the cascaded arbiter.
- **Min Back margin across seeds:**
  - slow: 210 ps (seed 5);
  - fast: 118 ps (seed 5).

### Mixed corners

- **Back negatives (C-element own feedback).** 2 / 4 / 7 / 4 on seeds d / 3 / 4 / 5. They
  are the C-element and arbiter subset of fbrace's candidates (A-xaudit-gcd: 4 / 7 / 10 / 9,
  which include latch bits) and have the same names and margins:
  - seed 3: `ulink_n_falseResult_77`, −265;
  - seed 4: `ucontrol_merge10.uarb1.ua1`, −167, and `umux9.uj1`, −143;
  - seed 5: `uenv1`, −395.
- **Guard ENTRY / EXIT.** 10–17 / 1–5 per seed.
  - The ENTRY failures are mostly arbiter re-arm (H_ARB acknowledges).
  - The EXIT failures are the `bd_mux` acknowledges `umux3/4/5/19.u{x,y}a`.

### The guardband corner (new): a single die with skew.py's spread

The mixed corner lets each element sit anywhere in [FAST_MIN, SLOW_MAX]. The gb corner is
narrower: one die, with skew.py's 0.772/1.155 spread. Every item it flags is also flagged at the
mixed corner, with a larger margin there:
- 3 arbiter re-arm ENTRY failures on seed d: `ucontrol_merge3.uarb1.ua1` −52,
  `ucontrol_merge2.uarb1.ua2` −26, `ucontrol_merge3.uarb1.ua2` −9;
- 1 Back failure on seed 5: the rig's `uenv1 ← uenv0`, −19 ps. This is the rig environment, not
  bdc output.

These are the candidates that survive the project's own guardband model. They are the ones worth
a GLS or board test first.

## 3. FASTFALL delay-line contiguity: mechanism, the artefact, and what is real

### The RTL

`cells/rtl/bd_latch.v`:
- **`bd_delay #(.FASTFALL(1))`.** `s[1] = LUT1(a)`; `s[i+1] = LUT2 8'h8 (s[i], a)` for
  1 ≤ i < N; `z = s[N]`.
- **`bd_delay_gated`, the gcd shape (29 lines, B-gcd-cells).** The same, with the side taps
  from `gate` (the anchor's input), while `a` is the `uor` anchor's output.

So `z(t) = AND_i c(τ_i(t))`: one sample of the source per tap.
- The rise must pass every tap. Its effective delay is the longest path (the matched chain).
- The fall is flushed by the nearest tap (one LUT).

### The mechanism (the Lean form is `line_gap_neg`)

**Skip condition.** Suppose the source's low phase `L` is shorter than the difference between
two adjacent taps' sample times. Then the slow path still shows the OLD high while the fast tap
shows the NEW high. The gate ANDs two highs from different transactions: the count set has a gap
(1 and 3).

**What the gate does then.** It passes a runt, the request rises a tap hop after the source
instead of after the matched delay, and the data it bundles may not be ready.

**Exact per-gate condition** (`hop_skew` + `tree_contig`). With `W` = the source's minimum event
spacing (a closed walk with one token, `cycle_le`), the condition is

    window(gate) = max(hi(P∖Q) − lo(Q∖P), hi(Q∖P) − lo(P∖Q)) + width(P∩Q) ≤ W,

where `P` and `Q` are the two tap paths to that gate's pins only.

**This is B's per-stage flush condition.** It is H_FLUSH_STAGE in B-bundling and
B-constraints-more (`fall_i + hop_hi(i→i+1) ≤ T + tap_lo(i+1)`), including **the in-flight term
that tighten.py's rule F omits** (B-bundling: rule F checks "latest stage-output fall ≤ earliest
re-rise", without `hop_hi(i→i+1) − tap_lo(i+1)`).

**Where it is worst: the head hop of a gated line.** `g[0]` is a plain buffer of `a`, not ANDed
with `gate`. So the fall of `s[1]` is not flushed by a tap. It travels
`gate → uor → g[0] → g[1].I0`, five elements, against one tap arc `gate → g[1].I1`.

### Why −11.4 ns was an artefact

**Where it came from.** In `events4/model.py`, `leaf()` adds the downstream band to every
sub-expression's band. Each tap's band therefore runs from the source to the stage pin. The pair
window `max(hi) − min(lo)` between consecutive taps then contains the full width of the shared
chain suffix after the gate where they meet, and of the line's output wire.

**Why that is wrong in the model.**
- In the warp model the suffix is one warp per element, shared by both taps. The gate samples
  both pins at one instant (H_ATOMIC_LUT, `Beh.hc`), so the suffix cancels from the difference
  of the sample times. `model.py`'s own comment says "shared downstream path cancels". The code
  did not do it.
- At mixed bands the width is about 560 ps per element. Over a 26-tap line that is
  `14,534 − 2,217 ≈ 12.3 ns` of spurious window.

**What the correction does.** `contig5` computes the window on the symmetric difference of the
two paths, plus the shared prefix's width (`prefix_skew`: a shared prefix does NOT cancel in the
warp model, because a time-varying delay can differ by its band width at the two sample times).
It gives:

| line (mixed corner) | events4 window / margin | contig5 window / margin |
|---|---|---|
| d `uselect1 → ulink_n139` (26 taps) | 14,534 / **−11,422** | 2,217 (at g[8]) / **+895** |
| d `ushli0 → ulink_n168` (22 taps) | — / fail | 2,602 (at g[1], head) / **−365** |
| 3 `uselect1 → ulink_n139` | — / fail | 3,522 (at g[1], head) / **−726** |

**Totals.** The fail counts per seed (d/3/4/5) go from 64/59/63/59 to 1/4/0/0 at mixed, from
6/5/6/4 to 0 at gb, and from 0/1/0/0 to 0 at slow.

**Per-pin IOPATH.** `contig5 --lutpin` adds the gate LUT's band width, for the per-pin IOPATH
case without H_ATOMIC_LUT (A-contradictions X2). It was not used for the table.

### The residual is real under the bands: concrete trace (`linetrace.py`)

**Setup.**
- The routed line of seed d is cut out: `ushli0.uor` + `udly.chain.g[0..21]`, 23 LUTs, real
  INITs, real nets.
- Every element gets ONE fixed delay: FAST_MIN everywhere, except the five head elements on the
  slow side of the failing pair, which get SLOW_MAX: `uor/I0` 1235, `uor` 124, `g[0]/I0` 441,
  `g[0]` 124, `g[1]/I0` 1012.
- The source `ushli0.joined` rises at 10 ns, falls at 40 ns and rises again `L` later.
- Simulation: pure transport (`csim.py` semantics).

**Results** (`trace_d_LW.txt`, `trace_d_Lwindow-1.txt`, `trace_d_Lwindow.txt`):

| L | result |
|---|---|
| **2237 ps** (= W) | `g[1]` pulses high 42,616–42,981 (365 ps = −margin); `z` rises at 46,847 ps, **+4,610 ps** after the source instead of the matched 7,212 (2,602 ps early = the window), then a 365 ps runt and the true rise: **3 rises of z for 2 of the source** |
| 2601 ps | still early by 2,602 ps, with a 1 ps runt |
| 2602 ps (= window) | matched: the equal-time events annihilate under transport |

The strict check (margin 0 = FAIL) stays on the safe side of that boundary.

**Seed 3** (`trace_3_*.txt`): at L = W = 2796 ps the request rises **3,522 ps early** with a
runt. It is matched at L = 3522.

### Is it physical? Three conditions, all needed

1. **A mixed die.** The five head elements must be at SLOW_MAX while the source's return ring is
   at FAST_MIN. That is a within-die ratio of about 2.6. The ring is
   `ushli0.ujoin → ulink_n164.stage[1] → ulink_n168.stage[0] →` (fast tap) `→ ujoin`.
   - At one corner the margin is +2669 (slow) and +1260 (fast).
   - At the guardband corner it is **+1572 ps**.
2. **A low phase at the structural minimum.** `W` is a lower bound on the spacing of the
   source's events. The rig does not get near it: in a full-netlist csim of vector 2 with the
   same forced delays, `ushli0.joined` is low for **260 ns** (301 → 561 ns). The kernel calls
   `shli` once per invocation, and the rig waits a whole lap between invocations. The answer is
   right (0x6 both laps, derived from C in A-xaudit-gcd).
   - The hazard needs an environment that offers the next token as soon as the handshake ring
     allows. The domain quantifies over such environments; this rig is not one.
3. **Seed dependence.** Seeds 4 and 5 have no failure. Their minimum margins are +259 and +67
   ps, which are thin.

**Conclusion.** It is the rule-F in-flight gap, now measured on the real route.
- The worst margins are −365 / −726 ps at the mixed corner, against −11.4 ns before.
- It is positive at every one-corner and guardband band.
- It is not reachable in the shipped rig's operation.

**The fix is in bdc, not here.** Either:
- add the in-flight term to rule F; or
- make `g[0]` of `bd_delay_gated` an AND with `gate`, so that the head's fall is also flushed.

The second changes `cells/rtl` (frozen) and needs a routed-GLS result first.

## 4. Fidelity (gate-fidelity rule)

| item | model | status | test |
|---|---|---|---|
| stage LUT | `cel` over bubbled pins, one sample instant per LUT (H_ATOMIC_LUT, `Beh4.hc`) | exact functionally. H_ATOMIC_LUT is the A-contradictions X2 assumption; strict margins cover a 1-step pin skew | GLS with the unisim LUT6 and per-pin IOPATH |
| merge | stateless OR (`fany`); `mg0`: low at time 0 (acyclic OR gates) | exact; `mg0` is a stated field (W-E4n derives it) | — |
| filtered pin | steer AND with select `sv`; **SelOK** | hypothesis (E6) | GLS: select route against request route |
| delay line | AND/OR of copies with per-copy warps; **`hskew`**: copies within `dw` | `hskew` is a field of the behaviour, justified by `hop_skew`/`prefix_skew`. Deriving it from the netlist is W-E4n | the concrete trace of §3; a board TDC on one line |
| guarded pin | count `gc` supplied by the behaviour; **GuardOK** | **named hypothesis (W-E4g open)**. ENTRY/EXIT are checked by the analysis but not yet proved sufficient | GLS of `bd_mux` with `z_ack` fanout skewed |
| arbiter | H_ARB virtual mux core (A-events4) | hypothesis, out of domain | contention GLS |
| corners | one-corner, mixed, gb as in §2 | mixed = each element anywhere in [FAST_MIN, SLOW_MAX]; gb = one die with skew.py's spread | own-feedback against neighbour on one die (TDC) |

## 5. Effort and what it buys

**Effort.** About 5.5 h:
- reading: 0.5 h;
- builds, prjxray and runs: 0.5 h wall, run in the background;
- contig5 and the traces: 1 h;
- Lean: 2.5 h, of which Events5Line took 0.3 h;
- notes: 0.5 h.

**To finish.** About 4 days for a netlist-level certificate:
- W-E4n, `design_beh4`, plus an executable `Events5Main` that checks the emitted derivations by
  `decide`: 1.5 days;
- W-E4g: 1.5 days. It needs a definition of `gc` through the merge order and a lower-bound walk
  judgement (see Wip);
- W-E4x (n-ary merges), U3 and the cascade: 1 day.

**What it buys.**
- The integration step is closed. The counter domain's rules (R1/R3/SUB walks, merge
  exclusivity, delay-line contiguity, guarded C-elements) are one theorem, `verdictW`, about
  every behaviour and every select sequence.
- The delay-line rule is now correct. Its proved form is exactly B's per-stage flush with the
  in-flight term. The −11.4 ns headline is retracted as an artefact. The real residual is
  −365 / −726 ps, mixed-only, and reproduced concretely.
- Across 4 seeds the gcd control is clean at one corner, apart from the cascade.
- Under the project guardband, 4 candidate items remain: 3 arbiter re-arm, 1 rig env. They are
  the first things to test.
