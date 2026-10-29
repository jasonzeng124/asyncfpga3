# B-arb-multi-token: multi-token exclusion of the held bd_arbiter (probe Barb2)

File: `formal/lean/Formal/Cells/ArbMultiToken.lean`. It is core Lean and imports only
`Formal.Cells.ArbHeldTimed2` (7j), which imports 7h. Check command:
`/tmp/claude-0/btools/bcheck.py Formal/Cells/ArbMultiToken.lean`, result **OK** (about 25 s).
It has no sorry, admit, axiom or native_decide. The lead must add
`Formal.Cells.ArbMultiToken` to `Formal.lean`.

`#print axioms` was run from a scratch companion file, since deleted. `mt_exclusion`,
`H_ARB_EXCL_of_mt`, `H_ARB12_of_mt`, `mt_nonvacuous`, `win1` and `win2` give
propext, Classical.choice, Quot.sound. `splice_run` and `persist` give propext, Quot.sound.

## 1. Why 7h/7j cannot be chained as stated, and how this file chains them anyway

7h's `Scn` and 7j's `Scn2` assert their settled state over the WHOLE past:
- `H_q_init`, `H_A1_init` and `H_A2_init` for all t < t0;
- the waiting request high for all t < Hz;
- A0 low just before `ta`.

No segment of a multi-token run meets these. An earlier handover gives A1 low at some
time before t0. This agrees with the lead's `ArbNoWithdraw.scn_excludes_caus`.

The fix is **splicing**, and it leaves 7h/7j unchanged:
- `splice s P B` is the run from `B` on. Before `B` it is the stylised settled state `P`,
  with A0 low.
- `splice_run`: the spliced traces satisfy every gate relation and the server relation
  for **all t**, under three conditions:
  - the run is quiet in `P` on `[B, B+M)`;
  - `P` is a fixed point of every gate for either value of A0 (`FixA`, by `decide` on the
    real INITs);
  - A0's last rise `a ≤ B` was followed by R0 high on `[a, B)`.
  **H_M** (`MB`) says that `M` bounds every single read offset (route + fall arc).
- `win1` (client 1 releases) and `win2` (client 2 releases) are the **windowed
  one-handover theorems**. Their settled state is assumed only on `[B - M, t0)` and their
  requests only on `[B - M, Hz)`. The proof builds the spliced run and shows that it
  satisfies `Scn` / `Scn2`. H_SETTLED comes from `B + M ≤ t0`; the lead's
  `settled*_of_causal` is not needed. The proof then applies the ORIGINAL `rt1_exclusion`,
  `q_eq`, `g1_eq`, `g2_eq`, `A1_low_after` (RT2a from the RT2 arcs), `TA_ge` and `TA2_ge`,
  and 7j's mirrors, and transports the results back to `s` on `[B, Hz)`. Four new
  end-state lemmas are added: `R0_after`, `A2_after`, `R0_after2` and `A1_after2`.
- `persist`: a settled state `P1`/`P2` persists while the holder's request stays up,
  whatever A0 and the LOSING request do (`Ins`, by `decide`).

## 2. Headline results (namespace `Formal.Cells.ArbMultiToken`)

| theorem | assumed | proved |
|---|---|---|
| `mt_exclusion` | `Run D s` (7h's gate model: real INITs, rise-fast OR channel, a routed delay per pin, server H_SERVER_MIN); H_M; RT1, RT2 (7h) and RT1b, RT2b (7j) in arc form; `MTRun` | `(g1 t && g2 t) = false` for EVERY t ≥ B0, over infinitely many handovers (induction over handovers: `inv_all`, `step1`, `step2`) |
| `H_ARB_EXCL_of_mt` | same | C's **H_ARB_EXCL** verbatim on Nat traces `n ↦ g(σ n)`, for any sampling σ ≥ B0 |
| `H_ARB12_of_mt` | same + `CX` | C's **H_ARB1, H_ARB2, H_ARB_EXCL** verbatim at C's tick = 1 ps (`n ↦ B0 + n`), with x.req = r1, y.req = r2, z.ack = A0 |
| `mt_nonvacuous` | — | the hypotheses are jointly satisfiable, including `CX` |

**`MTRun`** (the environment, all named). The schedule `Sched` lists the observed edge
times `t0 k`, `TA k`, `TA2 k` and `u k`. Client 1 releases at even k and client 2 at
odd k.
- **H_ORD**: `t0 < TA < TA2`.
- **H_SLOW_REREQ**: `TA2 + 4M ≤ u`. The releasing client re-requests only after the
  handover has settled.
- **H_HOLD**: `u + 2M ≤ t0 (k+1)`. The new holder keeps its request until the loser's
  re-request has settled. This is sustained contention.
- **H_A0**: the server's phases. Its timing is otherwise constrained only by `Run`.
- **H_REQ1, H_REQ2**: four-phase clients with no withdrawal. The releaser is high from its
  previous re-request until `t0 k`, and low on `[t0 k, u k)`.
- **H_INIT, H_R0_INIT**: the initial state is settled with client 1 holding the grant.

**`CX`** is needed only for C's tick form. Every inequality in it is an arc inequality.
- `pos1`, `pos2`: a request edge reaches its grant no sooner than 1 tick.
- **RT1 / RT1b strict**: margin of at least 1 tick. C's rise clause reads the other grant
  one tick earlier.
- **H_GRANT_IN_A0_LOW**: the new grant rises after A0's fall plus 1 tick, and no later
  than the earliest possible A0 re-rise:
  - client 1 releasing: `wq + g2r ≤ wfb + Rrq + smin`;
  - client 2 releasing: `wq + g1rq ≤ wfb + Rrq + smin`.

  C's clause "a grant rises only while z.ack is low" fails without it.

**Non-vacuity (`mt_nonvacuous`).** `Dw` sets every route to 1 ps and every arc to 1 ps
(rise = fall, one consistent corner), with smin = 3 ps. `Ww` is a periodic run over all
of ℤ: period 48 ps, two handovers per period. The gate relations and `Server` are checked
for every t. `Sw` has t0 = 24k, TA = 24k+5, TA2 = 24k+12, u = 24k+20, B0 = -2, a0 = -12
and M = 2. The witness shows the grants really alternate: g2 rises at 9 and 57, g1 at 33
and 81. All values were derived by hand and cross-checked by a scratch discrete
simulation, `/tmp/claude-0/probes/Barb2/sim.py`.

## 3. Item (3): C's fields vs what is derivable

* **H_ARB_EXCL is derivable as C states it, for the held arbiter.** This needs the
  multi-token hypotheses above. It does not contradict `ContractBridge.arb_excl_not_derivable`,
  which concerns the BARE cell (no hold), in B's per-pin box. So the field is correct for
  `bd_arbiter`, which is what gcd_hw instantiates. It is not correct for `bd_arbcell` alone.
* **H_ARB1 and H_ARB2** are derivable verbatim at 1 ps ticks under `CX`. Under plain
  RT1 (non-strict), the rise clause can fail at a tie, `G1 = G2`.
* **H_AMERGE_RTZ is NOT derived.** It speaks of `z.req = delta(uor(R0))`, and B's held
  model has no z_req: its server reads R0 with `smin` included. What it would need, by
  hand and not proved:
  - z_req modelled as R0 delayed by `dz ≤ smin`;
  - A1's fall `T1` before `RR + dz` (an arc inequality);
  - 7h's `A2_low_before`, which needs A0Fork;
  - the mirrors of these three.
* **Does C's amerge proof go through?** C's `OpsCM.amerge_inv`, and `amerge_proto`/
  `amerge_op` on top of it, read H_ARB1, H_ARB2 and H_ARB_EXCL at every tick, which
  `H_ARB12_of_mt` supplies. But `AMerge` also needs:
  - **(a)** H_AMERGE_RTZ, still open;
  - **(b)** the initial fields `i1`/`i2` (grants low at tick 0) and `ix`/`iy`, while this
    run starts mid-contention with g1 high (P1);
  - the remaining fields (`zr`, `xa`, `ya`, `dat`), which are C's own and not touched here.

  So the arbiter half of `AMerge` is now derived on contention runs, but `AMerge` as a
  whole is not instantiated. A start from reset or idle (both requests low) is not in the
  schedule.

## 4. What it does not show (open)

* **Fast re-request.** Four-phase lets the releasing client re-raise as soon as its ack
  falls (`T1`), which can be before `TA2`. H_SLOW_REREQ excludes that. By hand, the extra
  races are:
  - r1↑ must reach ustate after q's reset has latched: `QB + wfb ≤ u + wr1s`;
  - r1↑ must reach R0 after R0's view of q has fallen: `QB + wfb + Rfq ≤ u + wr1s + Rr1`;
  - r1↑ must reach g1 after g1's view of q has fallen: `QB + wq + g1fq ≤ u + wr1g + g1r1`;
  - the mirrors of these three.

  With `u = T1 ≥ TA + wa01 + c1f`, each race becomes an A0-fork-type arc inequality, for
  example `wa0s + qf + wq + g1fq ≤ wa01 + c1f + wr1g + g1r1`. Without them g1 or R0 can
  glitch while g2 is high. None of this is formalized, and no counter-run is built.
* **Schedules other than alternating contention.** A solo client, idle periods, a start
  from reset, or the same client winning twice are not covered.
* `H_SLOW_REREQ` and `H_HOLD` use the coarse `M` (one bound on every read offset), so
  they are sufficient, not tight.
* Ack exclusion (RT2) on multi-token runs is used internally: A1 low after T1 gives the
  next settled state. It is not packaged as a theorem. A0Fork is not needed for the grant
  results.
* Metastability and the bare-cell overlap are out of scope. Every race here is decided by
  RT1/RT1b.
