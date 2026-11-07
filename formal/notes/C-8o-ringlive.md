# C-8o: ring liveness with a linear bound, per-token period of the pipeline

Shard C, probe 8o, 2026-10-27. About 2.5 h. Core Lean only, no sorry/axiom/native_decide.

## Verdict

- **Goal 2 (ring, linear bound): works.** Every stage of a ring of `N ≥ 3` `bd_link`
  controllers holding one loop token toggles in **every window of `N·H`**, `H` bounding every
  stage's upper delay (8d had `(N(N-1)+1)·H`). Parametric in `N`, from the timed (inertial)
  model, no fairness and no SI-run counting.
- **Goal 1 (pipeline period): works for n = 1, 2, 3, open for general n.** A generic
  marked-graph progress theorem (`mg_fire_within`) gives a steady-state period bound that does
  NOT need the pipeline to empty. It does not empty, see below. For 8n's `pipe n` with
  n = 1, 2, 3, every node (in particular the sink acknowledge) toggles in **every window of
  `(2n+3)·H`** of every timed trace from reset. So the sink accepts a token at least every
  `2(2n+3)·H`. A kernel-checked reachable-set certificate supplies the per-net facts. For
  general `n` the same depth `2n+3` holds for n = 1..4 (`#eval`), but the parametric proof is
  open.
- **Goal 3 (ring of op cells): not done.** It is scoped below. Fork/join/link loops are
  covered by the same certificate method with no new theory. Mux/steer need one extension.
- **Goal 4 (gcd_hw liveness): what remains is stated below.**

## Run

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/OpsRingLive.olean Formal/Net/OpsRingLive.lean  # ~3 s
    ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/OpsPeriod.olean Formal/Net/OpsPeriod.lean      # ~75 s, 1.1 GB peak
    ../slot.sh lean Wip/C8o/Axioms.lean
    cd .. && ./check.sh Formal/Net/OpsRingLive.lean Formal/Net/OpsPeriod.lean
    # -> [audit] 2764 declarations checked, [check] OK  (73 s)

Dependencies: the existing oleans of BridgeRing, Ring, Bridge, OpsTimedLive (8n), OpsGen.
The lead must add `Formal.Net.OpsRingLive` and `Formal.Net.OpsPeriod` to `Formal.lean`. I do
not own that file.

Axioms (`Wip/C8o/Axioms.lean`): every theorem uses {propext, Classical.choice, Quot.sound},
from `byContradiction` and core `simp`. `pipe_mg` uses propext only.

## Files

| file | contents |
|---|---|
| `formal/lean/Formal/Net/OpsRingLive.lean` | `ring_f`, `frozen`, `blocked`, `first_change`, **`fire_local`**, offsets `off`/`off_prv`/`off_nxt`/`off_surj`, `three_distinct`, `cnt_three`, `no_third`, **`near`**, **`ring_every_window`**, **`ring_every_window_reset`**, **`ring_unit_live`** |
| `formal/lean/Formal/Net/OpsPeriod.lean` | `marked`, `MG`, `safeB`, `readyB`, `safe_at`, `mark_stays`, `marked_flip`, **`mg_fire_within`**, **`mg_window`**; certificates `ofL`, `flipL`, `certC`, `certB`, `certB_reach`, `certB_persistent`, **`cert_window`**; pipeline `pins`, **`pipe_mg`**, `pipe_src`, `pipeS1..3`, `pipe_cert1..3` (decide +kernel), **`pipe_period_n1`**, **`pipe_period_n2`**, **`pipe_period_n3`**, **`pipe_period_unit`** |
| `formal/lean/Wip/C8o/Axioms.lean` | `#print axioms` (proves nothing) |

## Goal 2: the ring, `N·H`

**Model.** This is `BridgeRing.ringNet n K`: stage `i` is the real `bd_c2n`/`bd_c2n_set` LUT
in run mode, `c_i = C(c_{i-1}, ¬c_{i+1})`. It runs as a `Bridge.Timed` trace: every stage is an
inertial channel `[lo i, hi i]` with `lo ≥ 1`, and `hi i ≤ H`.

**Theorem `ring_every_window`.**
- Hypotheses: `N ≥ 3`, and `D = 2` wavefronts at every time (one loop token).
- Conclusion: every stage `j` changes at some `u ∈ [t, t + N·H)`, for every `t`.
- `ring_every_window_reset` gets `D = 2` from a clean reset (`0 < K < N`) through 8d's
  `timed_ring_safe`.
- `ring_unit_live`: non-vacuity at unit delay.

**Proof.**
- Take the wavefront nearest behind `j`, at offset `m ≤ N-2`.
- Every stage strictly between it and `j` has no wavefront, so it cannot move (`frozen`: the LUT
  holds on a tie).
- The wavefront's successor has no wavefront, so the wavefront is excited. It moves within its
  `hi`, and both its neighbours hold until it does (`fire_local`, from `settle` and `cause1`
  only). So `m` drops by one per `H` (`near`).
- At `m = 0` the wavefront is at `j`. Either `j` is excited and moves within `H`, or the other
  wavefront is at `j+1`. In that case `D = 2` and `N ≥ 3` leave `j+2` free (`no_third`), so
  `j+1` moves within `H`. That frees `j`, which moves within another `H`.
- Total `(m+2)·H ≤ N·H`.

**Tightness.** Not proved. The informal worst case is both wavefronts adjacent just behind `j`,
with slow stages, which gives about `(N-1)·H`. At uniform unit delay the real gap is much
smaller (3 ticks for N = 5, from `#eval` of `unitTrace`).

## Goal 1: per-token period of the pipeline

**The pipeline does not return to empty.**
- 8n's source is the generated `bd_src` LUT, `req = ¬ack`.
- As soon as stage 0 acknowledges and its acknowledge falls, `r0` rises again. The next token
  then waits in stage 0 while the previous one drains.
- The BFS from reset finds 18·4^(n-1) reachable states. The all-zero state is visited only at
  reset.
- So I chose a steady-state argument, not "return to empty + first-token latency".

**Generic theorem (`mg_fire_within`, any network).**
- Each gate is a marked-graph transition (`MG`). `bd_link`'s `C(r, ¬a)`, the source inverter,
  each buffer route and the sink wire all are (`pipe_mg`, proved for every `n` against 8n's
  `pf`, i.e. the generated LUT functions).
- Hypothesis `SafeInv` at every time: a marked place disables its source. This is 1-safeness,
  one token per elementary cycle.
- Then `readyB (x t) d g` implies that `g` toggles within `d·H`. Here `readyB d g` means every
  backward path of unmarked places from `g` has fewer than `d` places.
- Proof:
  - An unmarked input place is filled when its source first fires, within `(d-1)·H` (induction
    on `d`).
  - A marked place stays marked until `g` fires (`mark_stays`, from SafeInv).
  - After that, `g` fires within `H` (`reach_step`, upper bound only).
- `mg_window`: if `readyB · d g` holds at every time, `g` toggles in every window of `d·H`.
  That is a period bound that holds in any steady state.

**Certificates (`cert_window`).**
- A list `S` of states (bit lists) is checked in the kernel by `certB`. It must:
  - contain reset;
  - be closed under firing excited gates;
  - be persistent;
  - satisfy `SafeInv`;
  - satisfy `readyB d` for the targets.
- Bridge's `timed_reach` maps every timed state into `S`. It needs persistence, which the
  certificate provides.
- Nothing about `S` is trusted: a BFS outside the kernel produced it, and only `certB` matters.

**Results.**

| theorem | net | states | window |
|---|---|---|---|
| `pipe_period_n1` | `pipe 1` (6 nodes) | 18 | `5·H` |
| `pipe_period_n2` | `pipe 2` (9 nodes) | 72 | `7·H` |
| `pipe_period_n3` | `pipe 3` (12 nodes) | 288 | `9·H` |
| `pipe_period_unit` | unit-delay run of `pipe 3` | | 9 ticks (non-vacuity) |

- Each row applies to every node except the unused id `3n+1`, in particular the sink
  acknowledge `a n` (id `3n+2`).
- The depth `2n+3` is the minimum for the sink and the source. The `#eval` sweep gives
  [5,3,4,4,–,5], [7,5,6,6,5,6,6,–,7], …
- n = 4 also gives 11 by `#eval` (1152 states, not kernel-checked).
- **Per-token period**: the sink sees a rise and a fall per token, so it gets one token per
  `2(2n+3)·H`, in steady state, from reset.

**What the bound is not.**
- It is linear in `n`. Marked-graph theory says the real cycle time is constant: the maximum
  cycle mean, about `4H` from the local cycle `c_k → r_{k+1} → c_{k+1} → a_{k+1} → c_k`, which
  has 1 token.
- Proving that needs a max-plus (k-th firing time) argument. It is not attempted here.

## Goal 3: ring of op cells (not done; scoped)

- **Fork/join/link loops are marked graphs.**
  - Fork's ack C-tree and join's req C-element are `C(...)` transitions. Links are `C(r, ¬a)`.
    Wires are buffers.
  - So a fixed loop of them is a direct instance of `cert_window`. Needed: write its `Net`, bind
    each gate to the generated cell as 8n's `pipe_ctl_gen` does, give `ins`, and run BFS +
    `certB`.
  - Estimate: 2-3 h per loop shape, ≤ ~20 nodes, if it fits the kernel. The pipeline of 12 nodes
    and 288 states takes 75 s and 1.1 GB.
- **Mux/steer (choice) are not marked graphs.**
  - Extension: let the place list depend on the latched select, `ins : State → Nat → List`.
    A steer is then a buffer to the selected branch, and a mux a C-element with the selected
    input.
  - Add a hypothesis that the select is stable while the gate waits. This is the bundled-data
    condition H_STEER_SEL / H_MUX_SEL of 8f/8n, plus H_SEL_PIN.
  - `mg_fire_within`'s proof carries over if the list is constant on the waiting interval.
  - Estimate: 0.5-1 day for the generic part.

## Goal 4: what remains for gcd_hw liveness

The bound would compose as `T ≤ T_fill + (#laps)·L + T_drain`, with these pieces:

1. **Number of laps.** It comes from 8k's loop lemmas, under H_ONE_INVOCATION and
   `a, b < 2^31`:
   - main loop ≤ `log2(a·b) + 1` iterations (`main_eq`);
   - each strip ≤ 32 (`strip_eq`);
   - bb3 ≤ 31 (`shared_bound`).
   - That gives `#laps ≤ 31 + 2·32 + (log2(a·b)+1)·(1 + 32)`, at most about 2200 for 31-bit
     inputs. 8k's `log2(a·b)+34` is a fuel bound on the main loop, not a lap count.
2. **Lap time `L`.** It is `d·H` per loop ring, from `cert_window` on each loop's controller
   ring. This needs the choice extension of goal 3, and each loop ring with its op cells
   written as a `Net` from bdc's emission. 8l's `gcdhw_ring_ge3` (≥ 3 links per cycle) is the
   `N ≥ 3` condition that makes `D = 2` live.
3. **Coupling to the token run.** This is O1 of 8l: the selects the circuit latches follow the
   Kahn token run, so the lap count of (1) is the circuit's. Not started anywhere.
4. **Arbiters.** gcd_hw has 8 multi-input control_merges with `bd_arbiter`.
   - A bound needs either a bounded arbitration time (B's H_ARB* plus a resolution-time
     hypothesis; the fabric gives none, metastability is unbounded in principle), or a proof that
     under H_ONE_INVOCATION the merges are never contended. 8l's capacity argument points
     that way.
   - This is the real blocker for an unconditional number.
5. **Parametric pipeline/ring lemmas** for chains between loops. `ring_every_window` already
   holds for any N. For pipelines of any n, the parametric SafeInv (one token per local 4-cycle,
   by SI induction) and the depth `2n+3` are open: about 1 day.

Overall: about 3-5 days after O1, dominated by (3) and (4).

## Hypotheses (named), fidelity, test

| hypothesis | where | fidelity / test |
|---|---|---|
| H_BOUNDED_DELAY, inertial `[lo, hi]`, `lo ≥ 1` (`Bridge.Timed`) | both files | as C-8d/8n. Only `settle` (upper bound) and `cause1` are used. Test: GLS step response per LUT arc and route at the slow corner gives `H` |
| H_ISO (ring) | `ringNet` reads neighbour nodes directly | as 8d. The pipeline instance does NOT assume it: each route is its own gate |
| H_FB_SETTLED | gate reads its own node | = 8n's `FbFirst` = B's C2. Unchecked by any rule; should become tcheck RT_FB (C-10d measured failures) |
| one loop token, `D = 2` | `ring_every_window` | derived from H_RESET_CLEAN (`ring_every_window_reset`) |
| reset state all-zero | `pipe_period_n*` | B's C5 reset width / H_RESET_CLEAN |
| `SafeInv` | `mg_fire_within` | hypothesis of the generic theorem, DISCHARGED for the pipeline instances by the certificate |
| H_SEL_PIN, H_DATA_COMB | not used | control-only theorems; no data path is modelled here |

## Surprises

- The ring bound comes out at `N·H`, slightly better than 8n's `(N+1)·H` plan, because the
  nearest wavefront is never further back than `N-2`.
- With the free-running source the pipeline never returns to the all-zero state. 8n's open
  item 3 ("RTZ wave clears") is therefore the wrong shape; a steady-state invariant is needed,
  and the 1-safe marked-graph invariant is that invariant.
- Kernel certificates are cheap here: 288 states × 12 gates, with persistence (O(n²) per
  state), take about 75 s and 1.1 GB. (My first memory reading of about 6 GB summed other
  agents' lean processes; the per-process VmHWM is 1.1 GB.)
