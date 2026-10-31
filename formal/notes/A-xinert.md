# A-xinert: an inertial option for xaudit (probe XInert, shard A)

STATUS: done (11:25 UTC). Lean checks (see Check); all planned runs done except the two gcd ρ=delay-everywhere simulations (killed, see below).

## The problem

XSound2 proved that xaudit's timed verdicts hold in continuous time for two kinds of gate:
- transport gates;
- bounded-inertial gates (`DelayInertial.BoundedInertial ρ L H`) whose reject window satisfies
  ρ ≤ (hi+1−lo)·unit (`XSimChanReal.boundedInertial_chanCells`).

The side condition is necessary (`inertial_wide_not_chanCells`). So a run that is clean with
transport bands says nothing about a gate whose reject window is wider. This probe adds:
- a way to state ρ;
- a mode that widens the band to restore the side condition;
- a mode that refuses to run instead;
- the soundness theorem connecting both to the executable.

## What was added

**Band format (optional `inertial` key; absent means all 0):**

    "inertial": 50            -- every LUT output and routed arc, ps
    "inertial": "delay"       -- Verilog/iverilog default: reject = the delay, taken as the band's hi (ps)
    "inertial": {"lut": R, "route": R, "feedback": R, "cells": {"cell": R}, "arcs": {"cell/I3": R}}

The keys are the same as `cells` / `arcs` of the band file. Pads are always transport.

**CLI (additive):**

    --inertial widen|check  [--rho R] [--rho-lut R] [--rho-route R] [--rho-feedback R]   (R = ps | delay)

- **Without `--inertial`:** the old code path runs, and the output is byte-identical (diffed below).
- **`widen`:** every gate with window ρ gets `hi' = max(hi, lo + ⌈ρ/unit⌉ − 1)`. That is the least
  hi' ≥ hi with ρ ≤ (hi'+1−lo)·unit. The run prints how many gates were widened and by how much.
- **`check`:** if any gate would be widened, the run is refused before simulation (exit 4) and
  the offenders are listed. Otherwise it runs the unchanged design.

**Code.**
- `Parse.lean`, additive:
  - `RhoSpec`, `Inert`, `parseInert`;
  - `widenHi`, `widenGate`, `widenD`;
  - `applyInertial`, which reconstructs each gate's ps band and window from the band file
    (TRUSTED). It re-rounds every reconstructed band and throws on any mismatch with the parsed
    step band.
- `Main.lean`: the `--inertial` branch and two header lines, printed only under `--inertial`.

**Inverted bands (lead's extra item, from E8Mux).**
- `Parse.checkedSteps` rejects a ps band with lo > hi ("NOT RECOGNISED" error) instead of letting
  `toSteps` narrow it to [lo, lo].
- `bandFor` now uses it. This is the one non-additive edit, and it changes behaviour only on
  inverted bands.

## Check

    cd formal/lean && ../check.sh Formal/Core/XAudit/Design.lean Formal/Core/XAudit/Parse.lean \
      Formal/Core/XSimChan.lean Formal/Core/XSimChanReal.lean Formal/Core/XAudit/Fast.lean \
      Formal/Core/XAudit/SoundCells.lean Formal/Core/XAudit/SoundPhys.lean \
      Formal/Core/XAudit/SoundSteps.lean Formal/Core/XAudit/SoundInertial.lean \
      Formal/Core/XAudit/Untimed.lean Formal/Core/XAudit/Main.lean
    # -> [audit] 1273 declarations checked; [check] audit (executable) Formal.Core.XAudit.Main
    #    [audit] 1116 declarations checked; [check] OK

The other files are listed only because their oleans are not in `.lake/build` yet. Of these,
only Parse and Main changed. No new executable, so no lakefile stanza.

Binary: `tools-A/xaudit/build.sh`, run from a mirror tree. **`build.sh` has an order bug.** Its
MINE list compiles `Parse` before `Design`, and Parse imports Design, so a fresh `$XAUDIT_OLEAN`
fails with "Design.olean: No such file". The fix is to put Design first. I fixed it only in my
scratch copy, because build.sh is not mine.

## Lean: `Formal/Core/XAudit/SoundInertial.lean` (Mathlib, ℝ)

(see the file header for the full list)
- `checkedSteps_ok`: an accepted band has lo ≤ hi and is rounded by `toSteps`.
  `checkedSteps_inverted`: an inverted band is rejected.
- `toSteps_hi_ceil`: for an accepted band, step hi = max 1 ⌈H/u⌉, so there is no narrowing.
- `checkedSteps_inside`: if also u ≤ L, then lo·u ≤ L ≤ H ≤ hi·u and 1 ≤ lo ≤ hi.
- `widenHi_window`: ρ ≤ (widenHi+1−lo)·u. `widenHi_ge`: hi ≤ widenHi.
- `widenHi_eq_of_window`, `widened_wide`: a gate is widened iff (hi+1−lo)·u < ρ, which is exactly
  the case where `inertial_wide_not_chanCells` gives a counterexample for the unwidened band.
  So `check`'s refusals are necessary. `widenHi_eq_of_le_unit`: ρ ≤ unit never widens.
- `widenD_zero`, `widenD_eq_of_window`: with all ρ = 0, or when `check` passes, the simulated
  design is the parsed design.
- `GateOK q lo hi ρ e o`: there is a ps band [L,H] with lo·q ≤ L and H ≤ hi·q (the ORIGINAL step
  band), and the channel is transport in [L,H], or BoundedInertial ρ' L H with ρ' ≤ ρ.
  - `gateOK_of_toSteps`: the parser's rounding gives `GateOK` when the arc is not raised.
  - `gateOK_verilog`: a Verilog-default inertial gate (`Inertial Δ`, Δ ∈ [L,H]) is `GateOK` with
    ρ = H. This is the executable's `"delay"`.
- `physChan_widen`, `satPhys_widenD`: if every gate is `GateOK`, then `SatPhys (widenD …)`.
- `valF_sound_inertial`, `noXF_sound_inertial`, `constF_sound_inertial`, `settledF_inertial`:
  the printed verdicts on the widened design hold at every real instant, in every behaviour.

## Results

### Byte-identity (ρ = 0)

- `base` is a binary built from the pre-XInert `Main.lean`/`Parse.lean`, copied to scratch and
  built through a mirror tree. `new` is the binary built from the current files.
- For all 5 small cases:
  - `new` with no flag is **cmp-identical** to `base`;
  - `new` with no flag is also identical to the committed `xaudit/results/*.txt`;
  - `new --inertial widen --rho 0`, minus its 2 header lines, is **identical** to both.
  (`inert/results/summary.txt`)
- gcd seed d, slow, `--inertial widen --rho 0` reports "widened 0 of 47887 gates".

### Inverted bands (negative control)

- `inert/designs/inverted.bands.json` is the pipe3 slow corner with one arc [450, 380].
  - `base` accepts it silently: exit 0, the arc narrowed to [45, 45] steps.
  - `new` exits 1: `band of stage[1].u.ctl.u/I0: inverted band [450, 380] ps (lo > hi): NOT RECOGNISED`.
- The committed pre-E8Mux `gcd/inputs/bands_d_fast.json`, which has 20 inverted arcs, is now
  rejected at its first one (`results/gcd_old_fast_inverted.txt`).

### pipe3 / ring3 (`inert/run_small.sh`; `inert/results/`)

Window sizes are hand-derived from the bands, not read from a run. pipe3 slow corner,
unit 10 ps:
- LUT [99,121] → [9,13] steps, window (13+1−9)·10 = 50 ps;
- route [360,440] → [36,44], window 90 ps;
- own feedback [270,330] → [27,33], window 70 ps.

So ρ = 15 or 50 widens nothing, which the runs confirm. ρ = delay:
- LUT hi becomes 9+13−1 = 21, so [90,210] ps;
- route hi becomes 79, so [360,790];
- feedback hi becomes 59, so [270,590].

The runs print exactly these values. "dlut" is ρ = delay on LUTs, with routes transport. That is
the baked GLS (`-DGLS_TRANSPORT_IC`: inertial LUT specify paths, transport interconnect).
"dall" is ρ = delay everywhere, which is the annotated GLS.

| case | ρ=0 | ρ=15 ps | ρ=50 ps | ρ=delay, LUT only | ρ=delay, all |
|---|---|---|---|---|---|
| pipe3 slow corner (clean) | 0 flagged | same (0 widened) | same (0 widened) | check REFUSED (11 LUTs); widen: **0 flagged, still clean** | check REFUSED (40); widen: **9 flagged, all 9 storage nodes UNRESOLVED from 4.35-8.45 ns** |
| pipe3 hold-violation control | 10 flagged | same | same | REFUSED; widen: still flagged (4 windows, longer STORED X: stage 0 latch X [5900, 13290]) | REFUSED; widen: 9 flagged |
| pipe3 slow own-feedback | 22 | same | same | REFUSED; widen: 16 | REFUSED; widen: 12 |
| pipe3 default bands (unit 25) | 9 | same | same | **check passes** (LUT [45,124] → [1,5], window 125 ≥ 124) | REFUSED (29 routes: 700 > 625); widen: 9 |
| ring3 slow corner | 5 (UNRESOLVED, the W2 imprecision) | same | same | REFUSED; widen: 4 | REFUSED; widen: 3 |

How to read the flag counts:
- A flagged run stays flagged. The count can drop because widened X windows merge, for example
  several GLITCH windows become one STORED/UNRESOLVED window.
- The one verdict that changes is **pipe3's clean slow-corner run, which is lost under ρ = delay
  on every gate.** The cause was not classified here. The widened own feedback (hi 590 ps) is
  still below the fastest neighbour response (3·360+2·99 = 1278 ps), so it is not the known
  own-feedback race. The likely cause is the window-domain imprecision of A-xaudit ring3 / gcd §4
  (handshake windows overlap), but this was not checked.
- Under ρ = delay on LUTs only, the clean verdict survives with the widened bands. So it is sound
  for an inertial-LUT GLS of these bands.

### gcd_hw seed d (`inert/run_gcd.sh`; `inert/results/gcd/`)

**Inputs.**
- The netlist is md5 5c0830d5, the same as the committed `gcd/inputs/net_d`.
- The bands are the **E8Mux-corrected** ones (OUTMUX hop, `--inverted hull`):
  `scratchpad/e8mux/w/d/new/{slow,fast,gb}.bands.json`.
  - `smax_w0` / `smax_w0.02` were regenerated here with `routed2x.py --corner slowmax --widen w
    --inverted hull` from E8Mux's `arcs_new.tsv` and route. `checkbands.py`: 47887 bands, 0 bad.
  - `gb` is `--corner slowmax --widen 0.332`.
- Unit 25 ps; vector 1 (answer 7, from C); `--timed-only --all`.
- The ρ = 0 rows are the new baselines on the corrected bands. They are not the old A-xaudit-gcd
  numbers: smax w0 now certifies with rig_lap 1 from 83.80 ns, against 83.15 ns before.

**Check mode** (`check_summary.txt`; 1-step stimulus, refusal counts only):

| corner | ρ=15 ps | ρ=50 ps | ρ=delay, LUT only | ρ=delay, all |
|---|---|---|---|---|
| slow | passes | REFUSED: 1996 gates, widen ≤ 1 step | REFUSED: 9807 (every LUT output), ≤ 6 steps | REFUSED: 45553, ≤ 245 steps |
| fast | passes | 1996, ≤ 1 | 923, ≤ 1 | 36669, ≤ 137 |
| gb (slowmax −33.2%) | passes | 1996, ≤ 1 | 9807, ≤ 5 | 45553, ≤ 190 |
| smax w0 | passes | 3408, ≤ 1 | 9807, ≤ 8 | 45553, ≤ 285 |
| smax w0.02 | passes | 1996, ≤ 1 | 9807, ≤ 8 | 45553, ≤ 279 |

Notes on the check table:
- ρ = 15 ps passes everywhere because ρ ≤ unit never widens (`widenHi_eq_of_le_unit`). So the
  ρ = 15 verdicts ARE the ρ = 0 verdicts, with the inertial gates covered.
- The 1996 gates refused at ρ = 50 are 1-step arcs ([1,1]: MUXF dedicated inputs, CARRY4
  internals, mostly raised ones).

**Widen mode** (simulations):

| corner / ρ | widened | control storage clean / STORED / UNRESOLVED | rig_lap = 1 with res = 7? | wall s |
|---|---|---|---|---|
| slow, 0 | 0 | 307 / 4 / 103 | no (X from 69.9 ns) | 1303 |
| slow, delay LUT | 9807 | 307 / 3 / 104 | no (X from 69.9) | 1353 |
| fast (70 ns), 0 | 0 | 190 / 3 / 221 | no (X from 39.3) | 484 |
| fast, delay LUT | 923 | 190 / 3 / 221 (observables identical to ρ=0) | no | 402 |
| gb, 0 | 0 | 243 / 11 / 160 | no (X from 60.4) | 1029 |
| gb, delay LUT | 9807 | 241 / 13 / 160 | no | 1335 |
| **smax w0, 0** | 0 | 387 / 27 / 0 | **yes, 83.80 ns, res = 7**; ok = 1 [87.2, 95.1]; err = 0 [15.3, 96.0] | 535 |
| **smax w0, 50 ps** | 3408 (+1 step) | 387 / 27 / 0 | **yes, 83.83 ns, res = 7**; ok = 1 [87.25, 95.1]; err = 0 [15.3, 96.0] | 649 |
| smax w0, 75 ps | 43997 (≤ +2) | 386 / 9 / 19 | **no** (X from 79.7; first flag `ulink_n8__1` stage 1 at 37.2 ns) | 641 |
| smax w0, 100 ps | 44615 (≤ +3) | 386 / 10 / 18 | **no** (first flag `ucond_br11_j` at 32.7 ns) | 757 |
| smax w0, delay LUT | 9807 (≤ +8) | 386 / 7 / 21 | **no** (first flag `ulink_n8__1` stage 0 at 35.2 ns) | 1016 |
| **smax w0.02, 0** | 0 | 386 / 26 / 2 (after the lap) | **yes, 83.80 ns, res = 7** | 490 |
| **smax w0.02, 50 ps** | 1996 | identical observables to ρ=0 | **yes, 83.80 ns, res = 7** | 495 |
| slow / smax w0, delay all | — | KILLED by hand after 40 / 24 min | — | — |

The two "delay all" runs were killed because windows of up to 285 steps make each step about 5×
dearer. Their outcome is not a result. Since "delay LUT only" already loses the smax
certificate, and slow / gb / fast flag at ρ = 0, the expected outcome is "flagged". That is NOT
proved: XSim's monotonicity in the band was not used or proved here.

**Which verdicts change.**
- **ρ ≤ 50 ps (the physically plausible range, A-fidelity R1): no verdict changes.**
  - The smax w0 / w0.02 transaction certificate holds with every gate inertial at ρ = 50. Only
    windows move, by ≤ 25 ps.
  - The flagged corners stay flagged.
- **ρ = 75 / 100 ps on every gate, and ρ = delay on LUTs (the baked-GLS inertial semantics),
  lose the smax w0 certificate.** The first flags are the same nodes as the A-xaudit-gcd §4
  mechanism (`ucond_br11_j`, `ulink_n8__1` stage 0), so this is most likely the window-domain
  imprecision getting worse with wider windows (W2), not a found race. That was not checked by
  sampling.
- **Consequence for the GLS:** a transport-band xaudit certificate does NOT imply a clean
  inertial-LUT GLS (`dlut` refuses on every LUT). With the widened bands, xaudit at the narrow
  smax bands cannot certify the inertial-LUT GLS's behaviour set.

**Caveat on every gcd row (pre-existing, not inertial).**
- The gcd runs have **2334 raised arcs**, with lo < 25 ps raised to 1 step: MUXF dedicated
  inputs and CARRY4 internals (A-xaudit-gcd §5).
- For those arcs `GateOK` fails (`SoundSteps.toSteps_raised_lo`). So **none of the gcd verdicts,
  at any ρ, is covered by the continuous-time theorems** (`SoundPhys`, `SoundInertial`). They are
  theorems of the discrete model only.
- A finer unit (5-10 ps) removes this. With it, the ρ ≤ unit rule also changes: ρ = 15 would then
  need checking.

## What is NOT covered

- Pads (always transport).
- Raised arcs.
- Involution channels.
- Per-pin skew inside a LUT.
- Analog runts.
- The parser and `applyInertial` (TRUSTED). `applyInertial`'s reconstruction self-check guards
  the ps band and its rounding, but not the window lookup itself.
- `"delay"` uses the band's hi as ρ. For a gate whose reject limit is its actual delay Δ ≤ H that
  is `gateOK_verilog`. A reject limit larger than H is not covered.
- Whether the widened-band flags (pipe3 dall, smax w0 at ρ ≥ 75) are real races or imprecision.

## Files

- `formal/lean/Formal/Core/XAudit/SoundInertial.lean`: new, proved.
- `formal/lean/Formal/Core/XAudit/Parse.lean`:
  - additive: `RhoSpec`, `Inert`, `parseInert`, `widenHi`, `widenGate`, `widenD`, `tbl`,
    `applyInertial`;
  - `checkedSteps`, used by `bandFor` (rejects lo > hi);
  - `import Std.Data.HashMap`.
- `formal/lean/Formal/Core/XAudit/Main.lean`: additive (`--inertial`, `--rho*`, usage line).
- `formal/tools-A/xaudit/inert/`:
  - `run_small.sh`, `run_gcd.sh`;
  - `designs/inverted.bands.json` (negative control), `designs/gcd_1step.stim.json`;
  - `results/`, which holds the small runs, `summary.txt` and `gcd/`: summaries, headers, times,
    `.out.xz`, `check_summary.txt`. The ρ=15 check outputs are trimmed.
- `formal/notes/A-xaudit.md`: the LUT-delay fidelity row is corrected.
