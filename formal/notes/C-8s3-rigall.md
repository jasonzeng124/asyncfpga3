# C-8s3: every result of gcd_rig (per-invocation safety under the real rig)

Shard C, probe 8s3, 2026-10-29. **Status: DONE (safety, every invocation).** All three files
check (`check.sh` OK, 3718 declarations audited); `gcd_rig_all` uses only
[propext, Classical.choice, Quot.sound].

## Question

8s2 proved that the rig's FIRST `out0` result is `gcd a b` (`gcd_rig_first`). It also proved
that re-arming fails at every re-offer: `out0`'s handshake is still open, so the network is
never back in its reset state. Is EVERY result `gcd a b`? If so, what must the environment
guarantee, and does `gcd_rig.v` guarantee it? If not, what is the trace?

## Answer (proved)

Every result is `gcd a b`. **The overlap is real but harmless**, and no quiescence or reset
between invocations is needed. The rig overlaps invocations in two ways:
- the second `start` offer comes while `out0`'s return-to-zero is still pending (8s2);
- the gate models also let the function-end control channel `g251.0` (417, a fork branch into
  a sink) lag arbitrarily behind its sibling `out0`-select branch.

The circuit induction does not need a re-armed network. It needs only that the control token
of invocation `k` has left the last arbiter stage before invocation `k+1`'s `start` token
enters:

**H_START_GATE**: `riseB start.req t → #rises(start.req) before t ≤ #rises(z251.req) before t`
(`z251` = channel 464, the output of the final arbiter stage).

The rig guarantees H_START_GATE through two facts. The first comes from the gate models of its
two env C-elements; the second from the kernel's own gate models:
1. **Env** (`env_inv`). `RigEnv` is the four C(a, ¬b) gate facts of uenv1 and uenv0:
   - `start.req` rises only while `out0.ack` is high, and falls only while it is low;
   - `out0.ack` rises only while `start.req` is low, and falls only while it is high.

   From these, `#rises(out0.ack) = #rises(start.req) + [¬start.req ∧ out0.ack]`. So at the
   `j`-th re-offer, `out0` has been acknowledged `j` times, hence offered `j` times
   (`ack_le_req`).
2. **Kernel** (`out0_le_zEnd`). `out0` is produced by the 3-way mux. Its select comes from
   `z251` through `forkG 464 [417, 413]` and the links 413→414→415. So `out0` is never offered
   more often than `z251` (MuxN invariant `muxn_inv`, `link_strict`, `fork_strict`).

Counting the reset level as offer 0 (8s2's prepended idle tick), this gives H_START_GATE on the
prepended run (`rig_gate`).

## Method

- **Periodic walk** (`CapstoneRigAllWalk`).
  - `walkR` is 8r's spine walk, except that the token re-enters `start` when it leaves `z251`,
    instead of moving to 417.
  - 417 is dropped from the count invariant. It is a dead end: its consumer is a sink and it
    feeds no operator.
  - `mainR` is 8r's induction on time, with `InvR`, `ForcB` and `Agree` unchanged in shape.
    H_START_ONCE's single use, the `src` case of `rise_cur`, becomes H_START_GATE with
    `tr_startR`: re-entries into `start` are exactly the visits of `z251`.
  - Results: `gcd_hw_forcedR` and `gcd_hw_circuit_safeR`, given `WalkOKR`.
- **Periodic H_WALK** (`CapstoneRigAllPer`, `walk_okR`). There are two cases.
  - If the one-invocation walk never reaches 417, `walkR = walk`.
  - Otherwise, let `P` be the first arrival on 417 and `Wf = W(P)`. Then
    `walkR(mP+q) = walk(q)` with `m·Wf` visits added (`Ag`, `stepA`, `stepB`).

  This needs:
  - **`Wf c = A y c`** (`end_counts`): at the walk's end, 8s's `walk_sim` relation gives the
    consumed counts of the run's spine groups. The spine is empty there, and no later firing
    touches it (`quiet0`). That uses `push_le_pop`, which restates the core of
    `closed_of_check` for the spine check `spine_ok`.
  - **Periodicity of the stream solution with that period.**
    - Steer selects (`sel_period`): the cond history has the same length as the branch's data
      history (`Good.br`).
    - Arbiter oracles (`om_period`): `|idx| = |res|` (`RI.cml`). For the cascade's stage 1,
      `RI.lab`.
    - Both are read from 8s's kernel-checked table `cOK` (`steerR`, `amR`).
- **Rig** (`CapstoneRigAll`, `gcd_rig_all`). It uses the hypotheses of 8s2's `gcd_rig_first`,
  with `H_ENV` strengthened to the full `RigEnv`.

## What it does NOT cover

- Everything 8s2 lists still applies. In particular:
  - safety only (the all-quiet run meets every hypothesis);
  - H_CELLS and H_BUNDLE are unchanged;
  - the CMPD delay line and the ok/err compare logic are not modelled;
  - `out0`'s Sink model abstracts `res_req`'s delay.
- `RigEnv` is a hypothesis: the gate model of two `bd_c2n` LUTs, the same style as every other
  cell model. Non-vacuity: the all-quiet run satisfies it trivially. No multi-invocation
  witness run was built.
- One window only: `idx`, and so `a, b`, are fixed. Window changes go through `rig_rst`.
  Shard B's RigContract (`idx` moves only while `rig_rst` is high, H_RESULT_FRESH) covers the
  clocked side. Composing the two is not done here.

## Theorems (all proved)

- `CapstoneRigAllWalk`: `walkR`, `WalkOKR`, `H_START_GATE`, `mainR`, `gcd_hw_forcedR`,
  `gcd_hw_circuit_safeR` (H_CELLS, H_BUNDLE, H_START_GATE, periodic H_WALK).
- `CapstoneRigAllPer`: `push_le_pop`, `quiet0`, `end_counts`, `sel_period`, `om_period`,
  `walk_okR`, and **`gcd_hw_circuit_safe_all`** (H_CELLS, H_BUNDLE, H_START_GATE, a, b < 2^31).
- `CapstoneRigAll`: `RigEnv`, `env_inv`, `env_at_rise`, `req_ack_cnt`, `out0_le_zEnd`,
  `rig_gate`, and **`gcd_rig_all`**: under `CellR` (H_CELLS without `Src.iz`), H_BUNDLE, `RigEnv`
  and a, b < 2^31, every value `out0` offers (bus right after each request rise) and every value
  it latches (at each acknowledge fall), in every invocation, is `gcd a b`.

## Witness with two or more invocations: not built

8t's single-invocation witness (one explicit 465-channel run) took a full probe. A run with two
invocations would also have to satisfy `RigEnv`, run the out0 return-to-zero concurrently with
the second invocation's entry, and repeat the whole token schedule. That is estimated at about
a day, beyond this probe's time box. So `RigEnv` together with H_CELLS and H_BUNDLE has only the
trivial witness (the all-quiet run), as for every capstone theorem (O5).

## Commands (run 2026-10-29)

    cd /home/user/asyncfpga3/formal && export PATH=$HOME/.elan/bin:$PATH
    ./check.sh Formal/Net/CapstoneRigAllWalk.lean Formal/Net/CapstoneRigAllPer.lean \
      Formal/Net/CapstoneRigAll.lean          # [audit] 3718 declarations checked, [check] OK
    ./slot.sh lake env lean Wip/C8s3/Axioms.lean   # needs the three oleans (lake build)

## Files (all new)

| file | what |
|---|---|
| `formal/lean/Formal/Net/CapstoneRigAllWalk.lean` | Periodic walk, its generic lemmas, the circuit induction `mainR`. |
| `formal/lean/Formal/Net/CapstoneRigAllPer.lean` | `push_le_pop`, spine quiet after the end, periods, `walk_okR`, `gcd_hw_circuit_safe_all`. |
| `formal/lean/Formal/Net/CapstoneRigAll.lean` | Rig environment gates, `out0_le_zEnd`, `rig_gate`, `gcd_rig_all`. |
| `formal/lean/Wip/C8s3/Axioms.lean` | `#print axioms` only. |
