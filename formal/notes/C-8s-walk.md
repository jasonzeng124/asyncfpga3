# C-8s: H_WALK proved (capstone O1, last token-level hypothesis)

Shard C, probe 8s, 2026-10-27. About 3 h.

**Status: DONE** for the main task (H_WALK). The second task (H_START_ONCE from the rig) is
PARTIAL: analysed and stated precisely below, nothing proved.

## Verdict

H_WALK is now a theorem. For every `a, b < 2^31` there is a complete traced token run `y`
with `Good a b y ∧ WalkOK (σY a b y) (omOf a b y)`. With that, C-8r's circuit theorem can be
stated with only H_CELLS, H_BUNDLE and H_START_ONCE:

```
theorem gcd_hw_circuit_safe3 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b))
```

`gcd_hw_circuit_safe3` is `gcd_hw_circuit_safe''` (8r, unchanged) applied to `gcd_hw_walk`.

**About the range hypothesis.** `a, b < 2^31` is now an explicit hypothesis. It replaces
H_WALK and does not weaken the result. The old theorem was vacuous outside that range,
because no `Good` run exists there. The new one simply says so.

Also proved, by the same route:
- `gcd_hw_forced3`: H_CM_FORCED.
- `gcd_hw_arbiters_uncontended3`: no free contention at any arbiter stage.

Both assume only H_CELLS, H_BUNDLE, H_START_ONCE and the range.

**What remains in the circuit theorem's hypotheses:**
- the gate models (H_CELLS);
- bundling (H_BUNDLE);
- one start offer (H_START_ONCE).

No token-level hypothesis is left. The fidelity of those hypotheses is unchanged from 8m and 8r.

## How the proof works (`Formal/Net/CapstoneWalk.lean`)

**The run.** `good_run` is 8m's `good_exists`, but it keeps the schedule. It gives a traced
run `texec (x0 a b) ls = some y` from `init a b` to `final (gcd a b)`.

**The simulation (`walk_sim`).** For every circuit walk step `p` there is a state `x` on that
run's path, with the run invariants `RI` and a continuation to `y`, such that
`Rel x (walk σY p)` holds. `Rel` has four parts:
- **Token.** The walk's current channel `c` carries the group `grp c` of the run's spine
  token. Here `x.s (grp c) ≠ []`. If the walk has ended, every spine channel of `x` is empty.
- **Counts.** For every spine channel `c'`:
  `W c' + [cur = c'] = Σ_{h ∈ al c'} |x.cn h| + Bo(cur, c')`.
  - `al c' = [grp c']`, except `acc251`, where it is `[13, 27]`.
  - `Bo = 1` iff `c'` is `adj`, lies in the current group, and does not come after `cur` in it.
- **acc251.** At `acc251`, label `|x.cn 251|` of control_merge12 is not 2.

**The steps.**
- **A step inside a group** (link, bjoin, a fork behind an arbiter, the cascade's stage 2
  from acc251) keeps `x`.
- **A step out of a group** takes the run to its next spine-moving firing (`next_fire`).
  - The firings in between touch no spine channel (`quiet`). That uses only
    `pop_le`/`pop_ins`, `cnt_apply` and one-token closure: no per-rule cases.
  - That firing is the GcdHw rule `lc c`, by input uniqueness.
  - Its effect is matched against the circuit operator: fork, branch, control_merge or sink.
- **The steer select.** `sel2 (σY c (W c))` is the cond history's entry at `W c`. It equals
  the head of the cond channel at the firing, by:
  - `cn_pre`: consumed history plus store is a prefix of the final history;
  - `BrI` lengths;
  - the count relation `W c = |x.cn (grp c)|`.
- **Arbiter arrivals (WalkOK).**
  - The next firing is the control_merge rule of the arrival input. It appends its label at
    index `|x2.pr idx| = |x2.pr res| = |x.cn res| = W z`. This uses
    `RI.cml : |pr idx| = |pr res|`, FIFO, and the count relation.
  - `omOf` reads exactly that entry from `y.pr idx`, which has `x3.pr idx` as a prefix.
  - **lo3 (cascade stage 1)** uses `RI.lab : |filter (≠2 mod 4) (pr 249)| = |cn 13| + |cn 27|`.
  - **hi3 arrival from acc251** uses the acc251 clause of `Rel`.

**Kernel checks (`Formal/Net/CapstoneWalkTab.lean`).** The per-channel conditions are
checked by kernel `decide`, so the tables are not trusted:
- `cOK_chk`, over all 67 spine channels. For each step `c → o` it checks `transOK`: the
  count relation is preserved at every spine channel. It also checks that the circuit
  operator and the GcdHw rule correspond: the fork's spine output; the branch's targets,
  cond channel and `condOK` descriptor; the control_merge's res/idx/label against
  `tab.w w` (`lab2`/`lo3`/`hi3`); the sink.
- `recs_chk` and `spN_chk`: the tables agree with `spL`.
- `recs_glob`: groups and `al` lie on the spine; `adj → al = [grp]`.
- `init_chk`: the relation holds at the start.
- `cmPair_chk`: the producers of a control_merge's res and idx are that control_merge's own
  rules.
- `lab249_chk`: control_merge12's labels.

## Files (all new)

| file | what |
|---|---|
| `formal/lean/Formal/Net/CapstoneWalkTab.lean` | Generated tables (`spN`, `grpL`, `rhoL`, `adjL`, `alL`, `lcL`, `recs`), the checker (`transOK`, `cOK`, …) and the kernel checks. |
| `formal/lean/Formal/Net/CapstoneWalkRun.lean` | Token-run lemmas: `RI` and `ri_pres` (with the new invariants `pres_cml` and `pres_lab`), `quiet`, `next_fire`, `fire_cn`, `texec_pre`, `cn_pre`, `only_tok`, `tok_one`. |
| `formal/lean/Formal/Net/CapstoneWalk.lean` | `Rel`, `trans_step`, `step_main`, `walk_sim`, `walk_ok`, `good_run`, **`gcd_hw_walk`**, **`gcd_hw_circuit_safe3`**, `gcd_hw_forced3`, `gcd_hw_arbiters_uncontended3`. |
| `formal/lean/Wip/C8s/walkgen.py` | Table generator. It replays every transition condition in Python first. `NEG=acc` builds the negative-control tables. |
| `formal/lean/Wip/C8s/check_tab.sh` | Drift check: regenerates the tables and compares them with the Lean file. |
| `formal/lean/Wip/C8s/negctl.sh` | Three mutated checkers, which must be rejected. |
| `formal/lean/Wip/C8s/Axioms.lean` | `#print axioms` only; it proves nothing. |

No pre-existing file was edited. The lead has to add the 3 modules to `Formal.lean`.

## Commands that check (run 2026-10-27)

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    FORMAL_SLOT_CWD=$PWD ../slot.sh lake build Formal.Net.CapstoneWalk
    ../slot.sh lake env lean Wip/C8s/Axioms.lean   # all: [propext, Classical.choice, Quot.sound]
    Wip/C8s/check_tab.sh                           # check_tab: ok
    Wip/C8s/negctl.sh                              # Neg1/Neg2/Neg3: rejected (ok)
    cd .. && ./check.sh Formal/Net/CapstoneWalkTab.lean Formal/Net/CapstoneWalkRun.lean \
      Formal/Net/CapstoneWalk.lean                 # [audit] 3497 declarations checked, [check] OK (2m24s)

- `CapstoneWalkTab` builds in 69 s. The other two take a few seconds each.
- The negative controls must each be rejected by kernel `decide`:
  - **Neg1:** the lab2 oracle expects the other input's label.
  - **Neg2:** the tables are regenerated with acc251 treated as an ordinary channel. The step
    g246.0 → z251 then breaks the count relation at acc251.
  - **Neg3:** the walk's steer targets are swapped relative to the branch.

## What it does NOT show

- **Nothing new at cell or timing level.** H_CELLS, H_BUNDLE and their §2/§3 hypotheses,
  and O4, are untouched.
- **The circuit theorem is still safety only.** Non-vacuity at network level is still open
  (O5): the all-quiet run meets every hypothesis.
- **H_START_ONCE is still a hypothesis, and as stated it is false for the rig's full run.**
  See below.
- **One invocation only.** The token run, the walk and the oracles all cover one invocation.

## H_START_ONCE and the rig (second task, PARTIAL: analysis only)

The rig's environment (`cells/hw/gcd_rig.v`, read-only) is two C-elements with one inverted
input each (`bd_c2n` = C(a, ¬b), from `rtl/bd_ce.v`):
- `uenv0 = C(res_req, ¬env_c)`, starting at 0;
- `uenv1 = C(env_c0, ¬in_ack)`, starting at 1 (SET);
- `env_c` drives `start_req`, `a_req` and `b_req` through a `bd_fork`;
- `res_req` is `out0_req` delayed by CMPD.

So `env_c` can rise again only after `env_c0` has risen, and `env_c0` can rise only while
`res_req` is high. **Rig property: between any two rises of `start_req` there is a rise of
`out0_req`.**

Consequences:
1. **H_START_ONCE as stated is false for the rig's whole trace.** It says at most one rise
   of `start.req` ever. The rig re-offers `start` after every result, forever. So
   `gcd_hw_circuit_safe3` does not apply to the rig trace as it stands.
2. **Route to the rig, not done.** Freeze the circuit trace at the tick before the second
   rise of `start_req`: every signal is held constant from then on.
   - The frozen trace meets H_START_ONCE.
   - Every gate model in `Cell` (Fork, Join, Steer, Mux, MuxN, AMerge, Link, Src, Sink) and
     `Held` *appears* to be a safety property of consecutive ticks: "x(t+1) ≠ x(t) → …",
     constant buses, reset values. If that is so, freezing preserves them.
   - A lemma `freeze_cell` per cell kind (about 1-2 h) would then give: every `out0` value
     latched before the second start offer is `gcd a b`. By the rig property that covers
     the first invocation's result.
   - This was not checked against every structure's fields. A field with a liveness or
     fairness shape would break it.
3. **Caveat on reset.** `Src.iz` asks `start.req = 0` at tick 0. The rig's `uenv1` comes up
   at 1 (SET), so `start_req` is high when reset is released, unless `bd_fork`'s `rst` holds
   its outputs low. The rig reset sequence, and whether the model's tick 0 is "after reset",
   need checking before the Src model is claimed for the rig.
4. **Repeated invocations.** These would need a periodic walk that re-enters `start` after
   the spine token reaches `sink 251`, and a token run per invocation. The vector is fixed
   per window (`idx` may change only under reset), so every invocation computes the same
   `gcd a b`.

## Surprises

- **The proof needs one global relation, not a per-group unrolling.** The relation
  `W c' + [cur=c'] = Σ cn + Bo` is preserved by every step. The whole per-channel case
  analysis became one Bool check per transition (`transOK`) plus one generic arithmetic
  lemma (`trans_step`).
- **The only irregular channel is acc251**, the cascade's stage-1 output. It is skipped by
  arrivals from input 2, so it needs its own count (`al = [13, 27]`, non-`adj`). It also
  needs the extra `Rel` clause for the stage-2 oracle when the walk arrives from acc251.
- **`Good` alone does not fix the control_merge labels' order.** The proof uses a run with
  two extra invariants, `|pr idx| = |pr res|` and control_merge12's label count. H_WALK is
  existential in `y`, so this is allowed. Whether `WalkOK` holds for *every* `Good y` is
  not shown and not needed.
