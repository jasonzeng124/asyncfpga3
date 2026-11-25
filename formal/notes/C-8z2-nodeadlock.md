# C-8z2: H_NO_DEADLOCK' is false as stated (counterexample); repaired theorem; joint witnesses

Shard C, probe 8z2, 2026-10-29. About 2.5 h, mostly waiting for builds. Core Lean only (no
Mathlib), no sorry/axiom/native_decide.

**Status: PARTIAL.**
- (1) H_NO_DEADLOCK' **refuted** as a network obligation (kernel-checked counterexample run).
  The repaired obligation H_NO_DEADLOCK'' is **still open** for general runs.
- (2) Joint witness: **done**, for 8z's `gcd_hw_live_final` and for the repaired
  `gcd_hw_live_final2`.

## Verdict

1. **8z's open obligation H_NO_DEADLOCK' is not a network property.** It is false on a run that
   meets all six other hypotheses of `gcd_hw_live_final` (`nd_counterexample`, kernel-checked).
   - **The run:** the unit-delay run of the concrete 465-channel network on a = 12, b = 18, in
     which `start`'s `bd_src` LUT never releases its request after its one offer.
   - **Why that is allowed:** 8z exempted that LUT from every delay bound once it has offered.
     H_BOUNDED_DELAY' skips it, and H_START_ENV only covers the time before the first offer. So
     holding the request for ever breaks no hypothesis.
   - **What happens:** the start token is never released. The return-to-zero wave that the
     link stages need before they take the next token never starts. The network comes to rest
     at tick 126, before out0 is even requested. out0's acknowledge never falls.
   - **Consequence:** no proof of H_NO_DEADLOCK' from the network structure can exist. The
     obligation hid an environment assumption: "the start token is released".
   - Why 8z's simulations missed it: `ndsim.py` (8z) gives the start LUT's release an ordinary
     gate delay. That is the repaired hypothesis below, not the one 8z stated.
2. **Repair: `gcd_hw_live_final2`** (`CapstoneLiveNd2`). Same conclusion, with two changes.
   - **H_START_REL `H`** (new, environment). While `start`'s request and acknowledge are both
     high on a whole window `[t, t + H]`, the request falls somewhere in it. This is the release
     half of the LUT's bounded delay. H_START_ONCE still forbids a second offer.
   - **H_NO_DEADLOCK''** replaces H_NO_DEADLOCK'. Quiescence now also requires that `start`'s
     LUT is not excited to release (`¬ (req ∧ ack)`).
     - It is weaker than 8z's obligation (`nd2_of_nd'`).
     - The counterexample run violates H_START_REL (`x_not_rel`), as it must.
   - H_NO_DEADLOCK'' is **OPEN** for general runs. Evidence and a route are below.
3. **Non-vacuity: one run satisfies ALL hypotheses of both theorems together**
   (`gcd_hw_live_joint_witness`, `gcd_hw_live2_joint_witness`, kernel-checked).
   - The run: a = 12, b = 18, `H = 1`. The a/b sources are free-running. `start` is offered
     once and released.
   - It meets H_CELLS (internal traces explicit), H_BUNDLE, H_START_ONCE,
     H_BOUNDED_DELAY' 1 (every gate but `start`'s LUT), H_START_ENV 1, H_START_REL 1,
     H_ARB_UNCONTESTED_BOUNDED 1 and H_NO_DEADLOCK' (hence H_NO_DEADLOCK'').
   - Its first out0 token closes at tick 473, carrying 6 = gcd 12 18.
   - Applying either theorem to the run gives the same value (`gcd_hw_live_witness_consistent`,
     `gcd_hw_live2_witness_consistent`).
   - This answers 8z's "no consistency witness for H_BOUNDED_DELAY' + H_START_ENV + H_CELLS"
     and 8u's vacuity worry, for the repaired and the original statement.
4. **H_NO_DEADLOCK'' in general: evidence only.**
   - 320 random bounded-delay runs (one input pair each), 79 of them with an operand ≥ 2^16 and
     some up to 2^31 - 1. In every run: no deadlock, no persistence violation, no contested
     arbiter, and out0 = gcd.
   - Two negative controls show the harness can fail.

## The theorems

```
-- CapstoneLiveNd2 (namespace Formal.Net.CapNet.Live.Nd2)
def StartRel (H : Nat) (c : Chan) : Prop :=
  ∀ t, Win H t (fun u => c.req u = true ∧ c.ack u = true) → Ev H t (fun u => c.req u = false)
def NoDeadlock2 (ch) (itr) : Prop :=
  ∀ t, cnt (fallB (ch out0).ack) t = 0 →
    ¬ (Quiet2 (gsAt ch itr t) ∧
       (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true) ∧
       ¬ ((ch start).req t = true ∧ (ch start).ack t = true))
theorem gcd_hw_live_final2 (a b H) (ha : a < 2^31) (hb : b < 2^31) (ch) (itr)
    (H_CELLS) (H_BUNDLE) (H_START_ONCE) (H_BOUNDED_DELAY' H) (H_START_ENV H)
    (H_START_REL : StartRel H (ch start)) (H_ARB_UNCONTESTED_BOUNDED H)
    (H_NO_DEADLOCK'' : NoDeadlock2 ch itr) :
    ∃ y, Good a b y ∧ ∃ e, e < (1168 * (8 * Lrun y + 23) + 1) * (H + 1) ∧
      TokAt (ch out0) 0 e ∧ (ch out0).dat e = Nat.gcd a b

-- CapstoneLiveWitCex (namespace Formal.Net.CapNet.LiveWit)
theorem nd_counterexample : ∃ ch itr,
    H_CELLS(12,18) ∧ H_BUNDLE ∧ H_START_ONCE ∧ H_BOUNDED_DELAY' 1 ∧ H_START_ENV 1 ∧
    H_ARB_UNCONTESTED_BOUNDED 1 ∧ (∀ t, cnt (fallB (ch out0).ack) t = 0) ∧ ¬ H_NO_DEADLOCK'

-- CapstoneLiveWit
theorem gcd_hw_live_joint_witness : ∃ ch itr,
    [all 7 hypotheses of gcd_hw_live_final at a = 12, b = 18, H = 1] ∧
    ∃ e, TokAt (ch out0) 0 e ∧ (ch out0).dat e = 6
theorem gcd_hw_live2_joint_witness : ∃ ch itr,
    [all 8 hypotheses of gcd_hw_live_final2 at a = 12, b = 18, H = 1] ∧ ∃ e, ... = 6
```

The hypotheses in the witness theorems are written out literally, in the same form as in
`gcd_hw_live_final` / `gcd_hw_live_final2`. They are instantiated by applying both theorems
in `*_witness_consistent`, so a mismatch would not typecheck.

How `nd_counterexample` refutes H_NO_DEADLOCK':
- If it held on the run, `gcd_hw_live_final` would give an out0 close.
- But the run's out0 acknowledge list is empty (`x_never`).

The negative-control file also checks directly that the run is quiescent at tick 130. No gate of
any operator except `start`'s LUT is excited there (`Wip/C8z2/Neg.lean`, last claim).

## How the checks work (`CapstoneLiveWitLib`)

The run is given in 8t's event-list format (`CD`). The four timing and progress hypotheses are
reduced to Boolean checks that the kernel evaluates.

- **Gates as syntax.**
  - `gatesE k` lists each operator kind's gates as data: an output atom, plus excitation toward
    true and toward false as Boolean expressions over atoms (req, ack, internal node, `sel2`/`selD`
    of a bus).
  - **`gates_eq`**: `gatesK p k ++ grantsK p k = (gatesE k).map (toG p)`. The syntax denotes
    exactly 8u's gate list, in order, arbiter grants included. Nothing about the gates is
    re-modelled.
- **Step property ⇒ `BndG 1`, `ArbUnc 1`.**
  - `spChk` checks "excited toward `v` at `t` ⇒ output `v` at `t+1`" for one gate. It checks
    only at tick 0, after each change point of the gate's inputs, and before each change point
    of its output (`pw_of`). Between those points neither side can change.
  - `spChk_sound` lifts it to all `t`. With `H = 1` this gives `BndG 1` (`bnd_of_step`) and,
    for the grants, `ArbUnc 1` (`arb_all`), indeed the full bounded law.
  - `start`'s producer is skipped. The negative control shows that its LUT does fail the check:
    it is excited to re-offer for ever.
- **No deadlock from a certificate.**
  - `certL` names, for each tick `0..473`, one gate (operator, index, target) that is excited
    and not yet at its target. That operator is not `start`'s producer.
  - `ndChk` checks every entry. **`nd_of`** turns that into H_NO_DEADLOCK' for every tick before
    out0's first close.
- **H_CELLS with the internal traces explicit.**
  - `cellI_of` reuses 8t's `kChk` soundness.
  - The internal traces are `itrW cd p k`, read from the producer's output-channel record.
- **H_START_ENV, H_START_REL, H_START_ONCE.** These are proved by hand from the start
  channel's toggle lists: `start_env`, `start_rel`, 8t's `once_of`, and `once_of1`.

The run comes from `Wip/C8z2/livesim.py`, which imports 8t's `sim.py` unmodified.
- **Gate semantics:** every gate fires one tick after it is excited. C-elements hold while their
  inputs disagree.
- **Environment:** the a/b sources are free-running (each offers 2 tokens, then backpressure
  stops them). `start` is offered at tick 0, acknowledged at 98 and released at 99. The sinks
  acknowledge after one tick.
- **Size:** 2299 request/acknowledge toggles. Every gate but `start`'s LUT is quiescent from
  tick 476.
- `--hold` makes the counterexample run instead (413 toggles, at rest from tick 126).

## Hypotheses and their status

| hypothesis | in | status | non-vacuity |
|---|---|---|---|
| H_CELLS, H_BUNDLE, H_START_ONCE | both | as 8r/8s; H_START_ONCE false for the rig's full trace (8s) | witness (this probe) |
| H_BOUNDED_DELAY' `H` | both | B (as 8u) | witness, `H = 1` |
| H_START_ENV `H` | both | environment (8z) | witness |
| **H_START_REL `H`** (new) | final2 | environment: the rig's start ring releases start after the acknowledge | witness; the counterexample run shows it is needed |
| H_ARB_UNCONTESTED_BOUNDED `H` | both | B (8u) | witness (no stage is contested in the run) |
| H_NO_DEADLOCK' | final (8z) | **FALSE on a run meeting all the others** (`nd_counterexample`) | witness: holds on one run |
| **H_NO_DEADLOCK''** | final2 | **OPEN** network obligation; evidence below | witness: holds on one run |

## Evidence for H_NO_DEADLOCK'' (not a proof): `Wip/C8z2/persim.py`

The harness runs random bounded-delay schedules over the same gate lists, in the same order as
`gatesE`.
- **Delays:** each gate, once excited, draws a delay in `[1, D]`. It fires if it is still
  excited after that delay.
- **Persistence violation:** an excited gate that loses its excitation before firing. That is
  a hazard, and the one way a confluence argument (below) could fail.
- **Environment:** the a/b sources are free-running. `start` is offered once. Its release is an
  ordinary bounded gate, which is H_START_REL.

| run set | runs | failures | persistence violations | contests |
|---|---|---|---|---|
| D = 4: 10 fixed vectors (incl. 0/0, a = 0, b = 0, 2^31-1 / 2^31-2) + 190 random of 4..31 bits | 200 | 0 | 0 | 0 |
| D = 9: same scheme, other seeds | 120 | 0 | 0 | 0 |
| negative control `--mutant`: start never offered (must deadlock) | 10 | 10 deadlocks | 0 | 0 |
| negative control `--mutant2`: source a's bus random every tick (H_BUNDLE broken) | 5 | 4 wrong results | 738 | 3 |

In total, 79 of the 320 good runs have an operand ≥ 2^16. Outputs: `Wip/C8z2/persim_*.out`.

### A route to a proof (not done)

- **Persistence and confluence.** If every reachable state is persistent (an excited gate stays
  excited until it fires), the gate system is a persistent transition system. Each firing writes
  only its own output bit.
- **Keller's theorem.** Then all maximal runs from reset reach the same final state (Keller
  1975). So for each input, one schedule decides deadlock. The unit-delay run above is such a
  schedule, and it ends with out0 closed.
- **What it would take:**
  - persistence as an invariant of all reachable states. For speed-independent circuits that is
    hazard-freedom (semi-modularity). It is a design property, but it still has to be proved;
  - a symbolic argument over the data, to cover all a, b at once.
- **Alternative.** The 8u plan: simulate the token run by the circuit along 8s's walk, with
  data-arrival and capacity invariants. 8u estimated it at 2-3 days. With the counterexample
  here, that plan must also use H_START_REL.

## Files

| file | contents |
|---|---|
| `formal/lean/Formal/Net/CapstoneLiveWitLib.lean` | `Sg`/`BE`/`GE`, `gatesE`, **`gates_eq`**, `evF`, `spChk`, `spChk_sound`, `step_of`, `bnd_of_step`, `opStep`, `stepR`, `bnd_all`, **`arb_all`**, `ndOne`, `ndChk`, **`nd_of`**, `start_env`, `start_rel`, `once_of1`, `never_close`, **`cellI_of`** |
| `formal/lean/Formal/Net/CapstoneLiveWitData.lean` | GENERATED: the witness run (`cdsL`) and certificate (`certL`) |
| `formal/lean/Formal/Net/CapstoneLiveWitCells.lean` | `l_cells`, `l_held`, `l_start_once`, `l_start_env`, `l_out0` (kernel) |
| `formal/lean/Formal/Net/CapstoneLiveWitStep{A..F}.lean` | `lstepA..F`: step property, operators in chunks of about 60 (kernel) |
| `formal/lean/Formal/Net/CapstoneLiveWitNd.lean` | `lnd`, `lcert_len` (kernel) |
| `formal/lean/Formal/Net/CapstoneLiveNd2.lean` | `StartRel`, `QuietR`, `NoDeadlock2`, `nd2_of_nd'`, `frozen_quietR`, **`gcd_hw_live_final2`** |
| `formal/lean/Formal/Net/CapstoneLiveWit.lean` | **`gcd_hw_live_joint_witness`**, **`gcd_hw_live2_joint_witness`**, both `*_witness_consistent` |
| `formal/lean/Formal/Net/CapstoneLiveWitCexData.lean` | GENERATED: the counterexample run (`cdsX`) |
| `formal/lean/Formal/Net/CapstoneLiveWitCexCells.lean`, `CapstoneLiveWitCexStep{A,B}.lean` | its kernel checks |
| `formal/lean/Formal/Net/CapstoneLiveWitCex.lean` | **`nd_counterexample`**, `x_not_rel` |
| `formal/lean/Wip/C8z2/livesim.py`, `emit.py`, `check_drift.sh` | run generator (untrusted), emitter, drift check |
| `formal/lean/Wip/C8z2/persim.py`, `persim_*.out` | random bounded-delay evidence and its negative controls |
| `formal/lean/Wip/C8z2/Neg.lean`, `Axioms.lean` | kernel negative controls; `#print axioms` |

No existing file was edited. The lead must add the 17 modules to `Formal.lean`.

## Commands

    cd /home/user/asyncfpga3/formal
    for m in CapstoneLiveWitLib CapstoneLiveWitData CapstoneLiveWitCexData CapstoneLiveWitStepA \
      CapstoneLiveWitStepB CapstoneLiveWitStepC CapstoneLiveWitStepD CapstoneLiveWitStepE \
      CapstoneLiveWitStepF CapstoneLiveWitNd CapstoneLiveWitCells CapstoneLiveWitCexStepA \
      CapstoneLiveWitCexStepB CapstoneLiveWitCexCells CapstoneLiveNd2 CapstoneLiveWit CapstoneLiveWitCex; do
      ./slot.sh lake build Formal.Net.$m; done
    ./check.sh Formal/Net/CapstoneLiveWitLib.lean Formal/Net/CapstoneLiveWitData.lean \
      Formal/Net/CapstoneLiveWitCells.lean Formal/Net/CapstoneLiveWitStep{A,B,C,D,E,F}.lean \
      Formal/Net/CapstoneLiveWitNd.lean Formal/Net/CapstoneLiveNd2.lean Formal/Net/CapstoneLiveWit.lean \
      Formal/Net/CapstoneLiveWitCexData.lean Formal/Net/CapstoneLiveWitCexCells.lean \
      Formal/Net/CapstoneLiveWitCexStep{A,B}.lean Formal/Net/CapstoneLiveWitCex.lean
    ./slot.sh lake env lean -DautoImplicit=false Wip/C8z2/Neg.lean   # silent = all 6 controls hold
    ./slot.sh lake env lean Wip/C8z2/Axioms.lean
    lean/Wip/C8z2/check_drift.sh                                       # check_drift: ok
    python3 -I lean/Wip/C8z2/livesim.py 12 18          # untrusted mirror: OK
    python3 -I lean/Wip/C8z2/livesim.py 12 18 --hold   # counterexample run: OK
    python3 -I lean/Wip/C8z2/persim.py 200 4           # evidence (~30 min); also 120 9, --mutant, --mutant2

Results (2026-10-29):
- `check.sh` on the 17 files: `[audit] 4328 declarations checked`, `[check] OK`.
- Axioms: every main theorem uses {propext, Classical.choice, Quot.sound}. `gates_eq` uses only
  {propext, Quot.sound}.
- Kernel cost: every chunk is under 45 s and 1.8 GB peak. The heaviest are `CapstoneLiveWitCells`
  (38 s) and `CapstoneLiveWitCexStepB` (37 s, 1.7 GB).

## What it does NOT show

- **H_NO_DEADLOCK'' is not proved**, so `gcd_hw_live_final2` is still a reduction, not a
  liveness theorem for every run. The witness shows only that its hypotheses can all hold at
  once, on one run (a = 12, b = 18, unit delays).
- The counterexample refutes only the derivability of 8z's H_NO_DEADLOCK'. It says nothing
  against the circuit: on the board, start's environment ring does release start.
- One invocation only (H_START_ONCE). H_START_REL and H_START_ENV are environment assumptions,
  not facts about the circuit. The rig re-offers start, which H_START_ONCE excludes (8s).
- The random runs are finitely many schedules. They prove nothing.

## Surprises

- The same flaw hit 8u and 8z, at the same LUT. 8u gave `start`'s LUT a delay bound and
  forbade a second offer. That forces the token never to close. 8z removed the bound entirely.
  That lets the token never close. The right exemption is narrow: the second rise only.
- The change-point check (excited ⇒ fires one tick later, tested only where something changes)
  made every timing hypothesis cheap. The whole step property of a 2299-toggle run costs under
  2 minutes of kernel time.
