# B probe Bex: the causal induction behind `ctl_of_win`

Shard B, 2026-10-27. Lean: `formal/lean/Formal/Cells/WinFifoCausal.lean`, core Lean only.
Check: `scratchpad/bchk.sh formal/lean/Formal/Cells/WinFifoCausal.lean` prints `[bchk] OK`.
`#print axioms` for every theorem below gives a subset of `[propext, Classical.choice, Quot.sound]`.
There is no sorry, admit, axiom or native_decide.

This follows Bw (`notes/B-win-fifo.md`). Bw's `ctl_of_win` took two inputs:
- H_EX_CLEAN: the excitation has clean edges `c`;
- H_LOOP: `e j + D ≤ c (j+1)`.

This probe derives both, for one `bd_link_ctl` stage and for PipeTimed's 2-stage pipe.

## Idea

The node's edge times are defined from the node trace itself, with no read map:
`nt O lo hi c v` is the first `t ≥ c + lo` at which `O t = v`. So every event time exists
before anything is known about the run, as in `PipeTimed.P2.cc`. The induction is then
PipeTimed's, with two lemmas replaced:
- `exc_phase` is replaced by `exc_phase_w`. Its proof never used FIFO: `Win` for the LUT and
  the feedback is enough.
- `node_phase` is replaced by `node_win`. It uses `Win` plus H_NO_REVERT plus the phase spacing,
  and it gives `nt ∈ [c+lo, c+hi]`, the node at `v` on `[nt, c'+lo)` and the node at `!v` on
  `[c+lo, nt)`.

**H_NO_REVERT** is now stated intrinsically, without edge indices (`NoRevertI`): if the input
holds `v` on `[a,b)` and the output shows `v` at some `t1 ≥ a+lo`, the output keeps `v` until
`b+lo`.
- `noRevertI_of_ret`: on a clean input with H_SPREAD_PULSE, every FIFO read of band `[lo,hi]`
  satisfies it. So it asks nothing that FIFO did not already give.
- `noRevert_of_I`: it implies Bw's zone form.

## Results

| theorem | assumed | proved |
|---|---|---|
| `stage_fifo` | `Stage`: H_LUT_WIN (`Win lo hi` of the real `bd_c2n` excitation), H_NO_REVERT, H_FB (`Win`), H_LOOP_POS. `Env1`: H_RST; req and ack clean four-phase **from `R` on** (junk before `R`); H_SND / H_RCV measured from the node edges `τs = nt`. `Timing1`: H_R_POS, H_RST_LONG, H_LAT. | (1) The excitation is `Clean` from time 0 (edges `0, cph 0, cph 1, …`) and satisfies H_SPREAD_PULSE. (2) H_LOOP holds for every edge, with `D = min Es Ea`. (3) There is a `Ret L` of band `[lo,hi]` with `PipeTimed.Ctl … L wl wh`, which is H_LUT_FIFO **derived**. Its `L.fst (cph j) = τs j`. |
| `pipe_ctl_w` | `Gates2W` (both LUTs are a `Stage`; request and ack lines are FIFO as in `PipeTimed.Gates2`), `Env2W`, `Timing2W` (the fields of PipeTimed's `Env2`/`Timing2`, with the LUT bands) | Both excitations equal `Vph j` on every phase. This is the interleaved causal induction: stage 0's phase `j+1` needs stage 1's phase `j` through the ack line and stage 1's H_NO_REVERT, and stage 1's phase `j` needs stage 0's phase `j` through the request line. |
| `pipe_fifo` | same | There are `L0`, `L1` (bands `[lo0,hi0]`, `[lo1,hi1]`) such that `P := W.sk L0 L1` (same lines, reset and environment times) satisfies `PipeTimed.Gates2`, `Env2` and `Timing2`. Also `P.τ0 j = W.τ0 j` and `P.τ1 j = W.τ1 j`. **So every PipeTimed theorem (`pipe_ctl`, `nodes_clean`, `pins_clean`, `live`, `token0/1`, `pipe_forward`) holds on Win LUTs.** `nodes_clean_w` is an example. |
| `Wx.witness`, `Wx.witness_fifo` | — | Non-vacuity for the pipe. PipeTimed's square-wave run satisfies every field, with the LUT bands widened to `[1,3]`. That band is 2 ticks wide, so `Win ⊄ FIFO` there (`win_glitch_not_fifo`). |
| `Wx.witness1` | — | Non-vacuity for the single stage. Request and ack are HIGH (junk) on `[0,4)`, before reset release `R = 4`. |
| `Wx.no_revert_needed` | — | **H_NO_REVERT cannot be dropped.** Take the single-stage run with ONE node glitch: `O 6 = 0`, inside its zone `[5,7)`. The feedback carries it to I2 at 7, where req=1 and ack=0 force the excitation. Every other hypothesis of `stage_fifo` holds: `Win`, `H_FB`, `H_LOOP_POS`, `Env1`, `Timing1`. `NoRevertI` fails, and **no** `Ret` with `hi ≤ 5` gives `Ctl`. |

## Findings

1. **H_BAND is not a separate hypothesis.** The spacing `c j + hi < c(j+1) + lo` follows from
   the existing H_LAT (5b `H_ENV_LATENCY`: `hi + wh ≤ lo + min Es Ea`) and H_LOOP_POS
   (`s_spread`, `spread0/1`). The reason: the next phase starts `≥ lo + min(Es, Ea)` after this
   one, and that is `≥ hi + wh > hi - lo`. So Bw's `uenv1_band` arithmetic is subsumed by H_LAT,
   and no counter-run for H_BAND is meaningful on its own. (Dropping H_LAT breaks
   `exc_phase`. That is 5b/6d territory and is not redone here.)
2. **In a single stage, H_EX_CLEAN needs no glitch freedom at all.** `s_phase` and `s_pre` use
   only `Win` for the LUT and the feedback.
   - H_NO_REVERT is needed only so that the node, the stage's OUTPUT, is clean.
   - In the pipe, that node is the neighbour's input, so H_NO_REVERT enters the excitation
     induction there.
3. **Reset at `Tr = R > 0` costs nothing.** Reset forces the excitation to 0 on `[0,R)`, so the
   excitation is clean from time 0 even with junk pins, as `witness1` shows. Bw's "clean from 0"
   premise is met by the excitation, not by the pins.

## Not covered / caveats

- **The pipe's lines are still FIFO.** These are the request line `Rq` and the OR-of-two-FIFO
  ack line (`H_REQ_LINE`, `H_ACK_LINE`), unchanged from PipeTimed.
  - Their inputs (the nodes) are proved clean, so Bw's bridge applies to each of them as a
    `Win` + H_NO_REVERT line.
  - But the event-time recursion uses their `fst`. Making them `Win` needs `nt`-style times for
    the lines too. Not done.
  - So "H_NO_REVERT is the only extra assumption" holds for the two LUTs, not yet for the lines.
- General `N` (PipeTimedN) is not done. The recursion would be the same, on `2j + i`.
- The witnesses' LUTs are a transport delay equal to `lo`, for which `NoRevertI` holds trivially
  (`noRevertI_shift`). They show the hypotheses are satisfiable with a wide band. They do not
  exercise a delay in the interior of the band.
- The LUT reads the lumped excitation at one instant, as in PipeTimed. Per-pin arcs (FifoFidelity
  H_SEL_ORDER) are outside this file.
