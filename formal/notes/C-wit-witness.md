# C-wit: non-quiet witnesses for `gcd_rig_all`, `xorshift_circuit_safe`, `collatz_circuit_safe`

Shard C, probe wit, 2026-10-29. **Status: DONE (all three).**

## Verdict

**The hypotheses of all three theorems are jointly satisfiable by runs that deliver results.**
Each is proved in Lean and kernel-checked (`decide +kernel` over generated event lists; no
sorry, no extra axiom, no native_decide; axioms propext, Classical.choice, Quot.sound).

1. **`gcd_rig_all` (8s3)**: `gcd_rig_all_witness`. One explicit run of the concrete 465-channel
   gcd_hw network inside gcd_rig's environment, a = 12, b = 18. These are gcd_rig.v's vector
   idx 2, and the rig's own table gives 6 for them. The run meets `CellR` (H_CELLS without
   `Src.iz`), H_BUNDLE and `RigEnv` at once. It has three invocations:
   - start is high at reset release, as the `bd_c2n_set` holds it, and is re-offered at
     ticks 432 and 865;
   - out0 offers 6 at ticks 430, 863 and 1296;
   - out0 latches 6 twice: its acknowledge falls at 474 and at 907.

   The second start offer (432) comes while out0's first handshake is still open: its
   return-to-zero completes only at 474. This is exactly the overlap 8s3 proved harmless.
2. **`xorshift_circuit_safe` (8y2)**: `xorshift_joint_witness`. The 94-channel network on
   seed = 2463534242, rounds = 4, the inputs of `xorshift.c`'s own `main`. It meets H_CELLS,
   H_BUNDLE and H_START_ONCE, and latches 2008045182 at tick 263.
3. **`collatz_circuit_safe` (8y2)**: `collatz_joint_witness`. The 81-channel network on n = 7,
   with fuel 200 (the circuit ignores the fuel). It meets H_CELLS, H_BUNDLE and H_START_ONCE,
   and latches 16 at tick 979.

The expected values 2008045182 and 16 come from the C functions. `formal/tools/capwit2/expected.sh`
extracts each function verbatim from `kernels/<k>/<k>.c`, compiles it with gcc and runs it on
the chosen inputs. They are not read from the runs.

Each witness also has a `*_consistent` theorem, which applies the target theorem to the run:
- `xs_expected`: `xsSpec 2463534242 4 = 2008045182`;
- `c_expected`: `collatzC 200 7 = some 16`, which is the termination hypothesis of
  `collatz_circuit_safe`;
- for gcd, `Nat.gcd 12 18 = 6`.

Before this probe, the only witness for these three theorems was the all-quiet run, which
latches nothing (8s3 §"Witness"; 8y2).

```
theorem gcd_rig_all_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, CellR ch (srcV 12 18) (opAt o)) ∧        -- H_CELLS without Src.iz
      (∀ c, Held (ch c)) ∧                                    -- H_BUNDLE
      RigEnv (ch start).req (ch out0).ack ∧                   -- H_ENV (uenv1/uenv0)
      (ch start).req 0 = true ∧ OffAt (ch start) 0 432 ∧ OffAt (ch start) 1 865 ∧
      (OffAt (ch out0) 0 430 ∧ (ch out0).dat 431 = 6) ∧
      (OffAt (ch out0) 1 863 ∧ (ch out0).dat 864 = 6) ∧
      (OffAt (ch out0) 2 1296 ∧ (ch out0).dat 1297 = 6) ∧
      (TokAt (ch out0) 0 474 ∧ (ch out0).dat 474 = 6) ∧
      (TokAt (ch out0) 1 907 ∧ (ch out0).dat 907 = 6)

theorem xorshift_joint_witness :
    ∃ ch : Fin XorshiftCap.NC → Chan,
      (∀ o : Fin XorshiftCap.NO, Cell ch (CapNet.srcV 2463534242 4) (KCap.opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, Handshake.cnt (riseB (ch XorshiftCap.start).req) t ≤ 1) ∧
      (∃ k e, TokAt (ch XorshiftCap.out0) k e ∧ (ch XorshiftCap.out0).dat e = 2008045182)

theorem collatz_joint_witness :      -- same shape, at srcC 7 200, value 16
```

These are the target theorems' hypotheses, literally instantiated. The `#check` output is in
`Wip/Cwit/Axioms.lean`. The range side conditions `a, b < 2^31` and `rounds < 2^32` are
discharged by `decide` in the consistency theorems.

## How

**Simulator** (`formal/tools/capwit2/sim.py`). It is a copy of C-8t's `capwit/sim.py`, which
I did not edit. It uses the same unit-delay semantics of the `CapNet.Cell` gate models (every
gate has delay 1, C-elements hold, the arbiter wins x on a tie). I generalised it:
- it accepts any CapNet data file (gcd's `CapstoneNet`, `XorshiftCapData`, `CollatzCapData`);
- source values are given per `which`;
- the environment is a parameter (`--rig N`).

The rig environment transcribes `cells/hw/gcd_rig.v`:
- `a.req = b.req = start.req = env_c`: `bd_fork`'s `req_out` is the wire `{N{req}}`;
- `env_c` is high at reset release (`uenv1` is a `bd_c2n_set`);
- `in_ack` = C(a.ack, b.ack, start.ack): `bd_fork`'s C-element;
- `env_c` = C(out0.ack, ¬in_ack): uenv1;
- `out0.ack = env_c0` = C(out0.req, ¬env_c): uenv0, with `res_req`'s CMPD delay line abstracted
  to out0.req itself, as the `Sink` model does;
- every gate has delay 1. After N = 3 offers, `env_c` does not rise again, so the run is
  finite. A C-element's inertial delay is unbounded, so `RigEnv` and `SrcR` allow this.

`sim.py` mirrors every Lean condition in Python, including the reset fields and `RigEnv`. All
three runs show 0 violations. This mirror is untrusted; the kernel re-checks everything.

**Requests that start high** (`RigAllWitLib`).
- The problem: C-8t's event lists start every signal low, but the rig needs `start.req 0 = true`.
  With start low at 0, `RigEnv` forbids it from ever rising: it may rise only while `out0.ack`
  is high, and out0 needs start first. So no non-quiet run of `gcd_rig_all` exists with all
  requests low at tick 0.
- The fix: `RigAllWitLib` copies C-8t's channel layer (C-8t's file is unchanged), with a
  channel record `CD` that carries the request's initial level `r0`
  (`rb x t = r0 xor parity`). Toggle-step reasoning is unchanged (`rb_ne`, `step_ofR`).
- The checker: `kChkR = r0Chk && kChk`. Every non-source operator's output requests must start
  low, because those are the models' reset fields; a source's request may start high, because
  `SrcR` has no reset field.
- `kChkR_sound : kChkR cd sv k = true → CellR (wch cd) sv k` holds for all 12 kinds.
- `envChk`/`env_of` check `RigEnv` at the toggle steps of start.req and out0.ack.

**Kernel checks**:
- `RigAllWitCells`: `rcells1..4` (4 chunks of 92 operators), `held_all`, `env_all`, and the
  start/out0 events (counts and bus values by `decide +kernel`).
- `XorshiftWit` and `CollatzWit` use C-8t's `kChk`/`kChk_sound`/`heldChk`/`once_of` unchanged,
  at `KCap.opAt` (with `xorKD`/`collatzKD` as local instances, as in 8y2's statements).

## Negative controls (`Wip/Cwit/negctl.sh`; files generated by `capwit2/gen_neg2.py`)

Each file must be rejected at exactly its "MUST FAIL" claim, and its "must SUCCEED" claims
must pass.

| file | mutation | passes | rejected |
|---|---|---|---|
| `NegR0` | rig run; the link output `g6.1` (channel 7, operator 192) requests at tick 0 and drops at step 0 | `ops.all kChk` (every moving field) | `ops.all kChkR` (only the new reset check `r0Chk` sees it) |
| `NegEnv` | rig with uenv1 replaced by an inverter of `in_ack` (start re-offered whatever out0 does) | `ops.all kChkR` (CellR), `heldChk` | `envChk` (RigEnv `s_rise`) |
| `NegXStart` | xorshift, start source offers twice (a legal `Src` run) | H_CELLS, H_BUNDLE | `cnt (riseB start.req) T ≤ 1` |
| `NegCStart` | collatz, the same | H_CELLS, H_BUNDLE | H_START_ONCE |

Result: `negctl: ok`. All four were rejected at the required line.

NegEnv is informative: without uenv1's out0.ack input, the unit-delay run still meets every
cell model and H_BUNDLE, and only `RigEnv` fails. So `RigEnv` is not implied by the cell
models; it carries real content, which `rig_gate` uses.

## Commands

    cd /home/user/asyncfpga3/formal && export PATH=$HOME/.elan/bin:$PATH
    ./check.sh Formal/Net/RigAllWitLib.lean Formal/Net/RigAllWitData.lean \
      Formal/Net/RigAllWitCells.lean Formal/Net/RigAllWit.lean \
      Formal/Net/XorshiftWitData.lean Formal/Net/XorshiftWit.lean \
      Formal/Net/CollatzWitData.lean Formal/Net/CollatzWit.lean
    # oleans for the Wip files (one at a time):
    cd lean && for f in RigAllWitLib RigAllWitData RigAllWitCells RigAllWit XorshiftWitData \
        XorshiftWit CollatzWitData CollatzWit; do
      ../slot.sh lake env lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done
    ../slot.sh lake env lean Wip/Cwit/Axioms.lean        # #check / #print axioms
    Wip/Cwit/negctl.sh                                   # must print negctl: ok
    ../tools/capwit2/check_drift.sh                      # generated data == generator output
    ../tools/capwit2/expected.sh                         # C results: 2008045182, 16
    python3 ../tools/capwit2/sim.py gcd 12 18 --rig 3    # untrusted mirror: 0 violations
    python3 ../tools/capwit2/sim.py xorshift 2463534242 4
    python3 ../tools/capwit2/sim.py collatz 7

Result, 2026-10-29:
- `check.sh` on the 8 files: `[audit] 4697 declarations checked`, `[check] OK`.
- `negctl: ok`, `check_drift: ok`.
- `Axioms.lean`: all six theorems depend only on [propext, Classical.choice, Quot.sound].

Dependencies, all already built: CapstoneRigAll (8s3), CapstoneCutSpine, CapstoneNetChk,
KernelCapXorshift and KernelCapCollatz (8y2), CapstoneWitnessLib (8t).

Cost per file (`Wip/Cwit/peak.sh`, slot wait excluded):

| file | time | peak memory |
|---|---|---|
| `RigAllWitCells` | about 70 s | 1.6 GB |
| `CollatzWit` | under 45 s | 1.85 GB |
| `XorshiftWit` | under 10 s | 0.7 GB |
| every other file | under 15 s | 0.65 GB |

All are well under the 3 GB budget.

**The lead has to add the 8 modules to `Formal.lean`; I do not own it.**

## Files

| file | content |
|---|---|
| `formal/lean/Formal/Net/RigAllWitLib.lean` | `CD` with `r0`, `rb`, `kChkR`, `kChkR_sound` (CellR, 12 kinds), `heldChk`/`held_of`, `envChk`/`env_of` (RigEnv) |
| `formal/lean/Formal/Net/RigAllWitData.lean` | GENERATED (`gen_wit.py rig`): 465 channel records, 1341 ticks, 6750 toggles |
| `formal/lean/Formal/Net/RigAllWitCells.lean` | `r_cells`, `r_held`, `r_env`, `r_start`, `r_out0` |
| `formal/lean/Formal/Net/RigAllWit.lean` | **`gcd_rig_all_witness`**, `gcd_rig_all_witness_consistent` |
| `formal/lean/Formal/Net/XorshiftWitData.lean` | GENERATED: 94 channels, 266 ticks, 864 toggles |
| `formal/lean/Formal/Net/XorshiftWit.lean` | `x_cells`, `x_held`, `x_start_once`, `x_out0`, `xs_expected`, **`xorshift_joint_witness`**, `xorshift_witness_consistent` |
| `formal/lean/Formal/Net/CollatzWitData.lean` | GENERATED: 81 channels, 982 ticks, 2844 toggles |
| `formal/lean/Formal/Net/CollatzWit.lean` | `c_cells`, `c_held`, `c_start_once`, `c_out0`, `c_expected`, **`collatz_joint_witness`**, `collatz_witness_consistent` |
| `formal/tools/capwit2/sim.py`, `leanparse.py` | generalised simulator (copy of capwit's, plus the network choice, values and rig environment) |
| `formal/tools/capwit2/gen_wit.py` | emits the three data files (`--check` reports drift) |
| `formal/tools/capwit2/gen_neg2.py` | emits `Wip/Cwit/neg/Neg*.lean` |
| `formal/tools/capwit2/expected.sh` | C results from the kernels' own .c files |
| `formal/tools/capwit2/check_drift.sh` | drift check of the three data files |
| `formal/lean/Wip/Cwit/negctl.sh`, `neg/Neg*.lean` | negative controls |
| `formal/lean/Wip/Cwit/Axioms.lean`, `peak.sh` | axiom print; time/peak-memory wrapper |

No pre-existing file was edited.

## What it does NOT show

- **One input and one schedule per theorem.** This is non-vacuity, not testing and not
  liveness. All delays are 1, the arbiter wins x on a tie, and the sources and sinks are as
  described above.
- **The gate models, not hardware.**
  - H_BUNDLE holds for the models' zero-delay buses. Whether physical buses meet it is the
    tcheck question (8w/8x), and these witnesses say nothing about it.
  - The rig witness abstracts the CMPD delay line `res_req` to out0.req, as 8s3's Sink model
    does. It does not model the ok/err compare logic.
- **The rig run stops after three offers.** The C-element models allow an unbounded hold, but
  gcd_rig.v keeps going forever.
  - The witness has three offered results and two latched ones (the third token's acknowledge
    never falls, because start is not offered a fourth time).
  - It is not an unbounded-invocation run, though `gcd_rig_all` covers every invocation.
- **Arbiter and branch coverage is the same as in 8t's run on the same input.**
  - The rig run exercises 407 of 465 channels; 58 never request. These are the untaken
    branches and the a = 0 / b = 0 paths, including arbiter stage `acc251`.
  - In the xorshift and collatz runs, 6 and 5 channels never request: the untaken steer
    branches.
- **The `g251.0` lag is not reached.** 8s3 also allows the function-end branch `g251.0` to
  lag behind the out0-select branch. With unit delays it does not lag noticeably here, so that
  particular overlap is not exercised. The start/out0 return-to-zero overlap is exercised.

## Hypotheses: non-vacuity status after this probe

| theorem | hypotheses | witness |
|---|---|---|
| `gcd_rig_all` | CellR, H_BUNDLE, RigEnv, a, b < 2^31 | **this probe**: 3 invocations, 2 latched (6, 6) |
| `xorshift_circuit_safe` | H_CELLS, H_BUNDLE, H_START_ONCE, rounds < 2^32 | **this probe**: latches 2008045182 |
| `collatz_circuit_safe` | collatzC fuel n = some r, H_CELLS, H_BUNDLE, H_START_ONCE | **this probe**: latches 16 (n = 7) |
