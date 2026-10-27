# B-rig-src: the rig environment as C's `Capstone.Src`, and the time origin (probe Bsrc)

File: `formal/lean/Formal/Cells/RigSrc.lean`. Core Lean. It imports C's
`Formal.Net.CapstoneRig` (and through it `CapstoneRigTime`, `CapstoneNet*`, `CapstoneO1`),
B's `RigToken` and `CElemFn`. Nothing else was edited; no file of shard C was touched.

Check:

    /tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/RigSrc.lean
    -> [bchk] OK: Formal/Cells/RigSrc.lean

- The first run builds C's whole capstone closure into the private olean dir (about
  25 min, one slot at a time). After that, the file alone takes about 1 min.
- There is no `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `extern` or `unsafe`.
- `#print axioms` on all 13 headline theorems (scratch file `.../scratchpad/Bsrc/Ax.lean`)
  shows at most `propext`, `Classical.choice` and `Quot.sound`.

## What C already had (read before this probe)

C's `CapstoneRig.lean` / `CapstoneRigTime.lean` had already done two of RigToken's four
bridges, on C's side:

- **(3) time origin.** `CellR` is `Cell` with `Src.iz` dropped. `preRun` = `pc` prepends an
  idle tick on every channel, and `preRun_cells` turns `CellR` into `Cell`.
- **(1) prefix.** `gcd_rig_first` (first result) and `gcd_rig_window` (offers made while
  `start` has risen at most once, counting the reset level).

Both theorems still assume two things about the environment:

- the sources' `SrcR` (H_LUT_SI and `dat`), inside `H_CELLS_R`;
- `H_ENV`: `start.req` rises only while `out0.ack` is high.

Those two assumptions are bridge (4). This probe discharges them.

## Results

| theorem | assumed | proved | NOT covered |
|---|---|---|---|
| `shiftC_req`, `shiftC_ack`, `rigC_eq` | (ack: `ack T0 = 0`) | RigToken's `shiftC x T0` is exactly C's `pc (rtC (shf T0) c)`, i.e. `preRun (shiftRun T0 ch)` (`rigC`): one re-timing applied to every channel | — |
| `start_per_result_C` | RigToken's ring hypotheses (M1, M0, read maps, quiet window), rig time | RigToken's counts, stated on C's channels `rigC T0 ch start/out0` | — |
| `RigPrefix` (def), `rig_prefix` | C's `CellR` + `H_BUNDLE` on `shiftRun T0 ch`; RigToken's ring hypotheses | every `out0` offer made before `out0.ack` has risen carries `gcd a b`. This is C's `gcd_rig_window` with its premise discharged by B's counts | only the first result. By the protocol only offer 0 meets the premise, so the content equals `gcd_rig_first`'s first conjunct |
| `c3_move` | the real `bd_c3` INIT (`c3B`); H_LUT_FIFO, H_RST_ONE_FALL, H_FB_FIRST (as `set_move`) | at every move of the fork's c3, all three pins read the new value | per-pin skew inside the LUT |
| `env_lut_si` | quiet window (`e=1, k=0, x=0`); every move reads through a monotone causal map: H_UENV1_B (`e` moves to `¬k(β t)`), H_C3 (`k` moves to `x(γ t)`), H_KER_ACK (`x` moves to `e(δ t)`) | **`Src.H_LUT_SI`** on that channel: at every move of `env_c`, its ack at the previous tick equals `¬env_c` after the move | — |
| `env_lut_si_upto` | as above, H_KER_ACK only at steps `< T` | the same at step `T` (causal form) | — |
| `env_H_ENV` | RigToken's ring hypotheses (read maps φ1, φ0) | **C's `H_ENV`**: `env_c` rises only while `env_c0 = out0.ack` is high | — |
| `rig_cellR` | H_KER (C's cell model for every NON-source operator), H_BUNDLE, H_FORK_WIRE, H_DAT, H_REL, H_UENV1_B and H_C3 through monotone causal maps | **C's `CellR` for every operator of gcd_hw, sources included**. The kernel's ack rule is NOT assumed: it is C's own `gcd_hw_protocol`, applied to the run frozen at each step | Src.iz (false; C's `preRun` supplies it) |
| `gcd_rig_first_env` | `rig_cellR`'s hypotheses plus M1, M0 (the `a` halves, read maps), `out0.ack = env_c0`, `env_c0 = 0` at release | **C's `gcd_rig_first` with `H_ENV` and the sources discharged**: the first value `out0` offers, and the first it latches, are `gcd a b` | later laps (bridge 2) |
| `iz_fails` | H_FORK_WIRE, `env_c = 1` at release | `¬ Capstone.Src (ch start) 0` | — |
| `W.env_nonvacuous` | — | a 6-tick lap meets every hypothesis of `env_lut_si` and `env_H_ENV`, with `start` offered 3 times by tick 20 | — |
| `CX.ker_ack_needed` | — | a run where every other hypothesis of `env_lut_si` holds but the kernel raises an ack while `req` is low; `Src.H_LUT_SI` fails there | — |

## Plain-language statements

**Bridge (3), time origin.**

- Proved: B's `shiftC` (RigToken) and C's `preRun ∘ shiftRun` are the same map. It is
  applied to every channel the same way. So B's count theorems and C's capstone talk about
  the same traces.
- `Src.iz` is the one field of `Src` that does NOT hold for the rig at release
  (`iz_fails`). It holds only on C's prepended tick.
- Assumed, not mechanised: the kernel's cell models hold on `shiftRun T0 rig`, including
  their reset fields at `T0`. That is the kernel's state at release. B's `ResetGcd` gives
  it per cell; joining `ResetGcd` to C's `Cell` reset fields is not done here.

**Bridge (4), `H_ENV_REFINES_SRC`.**

- Assumed:
  - every kernel operator meets C's model;
  - `bd_fork`'s requests are wires from `env_c`;
  - the buses are `vector(idx)`, held, and `start` carries 0;
  - at release `env_c = 1` and `in_ack = 0`;
  - uenv1's `b` half and the fork's c3 move to what their pins read. Each pin read is any
    monotone causal map (FIFO wires, reads before the move). This is `set_move`'s and
    `c3_move`'s conclusion, with no SI assumption on the env.
- Proved: the three sources satisfy C's `Src` without `iz` (`SrcR`), at every tick, and
  C's `H_ENV` holds. So C's `gcd_rig_first` holds for the rig's first result with no
  environment hypothesis beyond the env cells' step forms.
- How the circularity is broken:
  - `Src` at step `T` needs each source ack to move only toward its request (C's
    `RecvStep`) before `T`. C proves `RecvStep` from H_CELLS, which contains `Src`.
  - `rig_cellR` does a strong induction on `T`. At each step it freezes the run at `T`
    (C's `frz` / `cell_rt`). The frozen run meets every cell model, so C's
    `gcd_hw_protocol` gives `RecvStep` before `T`. That gives `Src` at `T`.

**NOT covered.**

- Later laps: C's `rearm_fails_at_reoffer` stands, and bridge (2) is still open.
- The rig's two sinks. H_KER includes C's `Sink` model for `out0` (op `K.sink 416`) and
  for `p_end` (`K.sink 3`). In the rig these are, respectively:
  - uenv0's `a` half behind `urdly`: `out0.ack` moves to `res_req = delay(out0.req)`;
  - `upsnk = bd_delay#2`.
  `Sink.wire` (the ack moves to `req` of the previous tick) is their SI form. Name for this
  gap: **H_SINK_SI**, not proved here.
- RT_FB (H_FB_FIRST) at uenv1. It fails on seeds 2 and 4 (B-rig-token §5), and the step
  forms `set_move` / `c3_move` rest on it.
- `c3_move`'s per-route hypotheses (H_LUT_FIFO, H_FB_FIRST) for the real `ufork` c3 are
  not checked on routes.

## Exactness / non-vacuity

- `W.env_nonvacuous`: all read maps `id`, one lap every 6 ticks, `T0 = Tq = 0`. It satisfies
  every hypothesis of `env_lut_si` and `env_H_ENV`.
- The composed theorems `rig_cellR` / `gcd_rig_first_env` add C's kernel hypotheses. A
  witness for those would be a full gcd_hw run, which is C's responsibility. Its env part
  is `W`.
- `CX.ker_ack_needed`: drop only H_KER_ACK (the kernel acks `a`/`b`/`start` while the
  request is low), and `Src.H_LUT_SI` fails. In `rig_cellR` this is the rule that C's
  protocol supplies.

## Instructions for C (shard C owns `Formal/Net`; nothing there was edited)

1. **Use it.** `Formal.Cells.RigSrc.gcd_rig_first_env` is `gcd_rig_first` with `H_ENV`
   and the sources' `SrcR` discharged. `rig_cellR` gives `∀ o, CellR ch (srcV a b) (opAt o)`
   from the kernel-only hypothesis
   `H_KER : ∀ o, isSrcK (opAt o) = false → Cell ch (srcV a b) (opAt o)` plus the env
   model. `env_H_ENV` gives `H_ENV` from RigToken's ring hypotheses. In C's hypothesis
   table:
   - `Src.H_LUT_SI` (ch 0, 1, 2) and `H_ENV`: proved from the env cells' step forms.
   - `Src.dat`: H_DAT, the idx-under-rst contract.
   - `Src.iz`: false at release, supplied by `preRun`.
2. **No T-bounded capstone is needed for lap 1.** C's `gcd_rig_first` / `gcd_rig_window`
   already avoid H_START_ONCE. `RigPrefix` is the prefix proposition; `rig_prefix` proves
   it from `gcd_rig_window` plus B's `start_per_result`. C may restate it in `Formal/Net`
   if wanted: the proof is the 10 lines of `rig_prefix`.
3. **Still open on C's side:**
   - bridge (2), laps ≥ 2. Re-arming fails (`rearm_fails_at_reoffer`). A multi-lap
     statement needs a re-entrant cut, or "kernel back in its reset token state after
     `out0`'s handshake closes".
   - The two sink models (H_SINK_SI above). If C keeps `K.sink 416`, its `Sink.wire` is a
     hypothesis about uenv0 + urdly and should be listed as such. B can prove it in
     read-map form, the same way as `env_lut_si`, if C wants it (out0's `SendStep` keeps
     `out0.req` constant between uenv0's read and its move).
4. **Do not** re-derive `Src` per source from that source's channel alone. The c3 joins all
   three acks, so a source's `Src` needs the kernel's ack rule on its OWN channel only (the
   per-channel invariant). The c3 enters through H_C3, read per channel.

## Fidelity

- Env LUTs:
  - uenv1 is the real INIT, through `set_move` (RigToken);
  - the fork's c3 is the real INIT, through `c3_move`;
  - both run under H_LUT_FIFO, H_FB_FIRST and H_RST_ONE_FALL.
- Wires: FIFO (monotone causal) read maps.
- Kernel: C's gate models, in C's tick model (1 tick = 1 ps, the same base as B's rig time).
- Values: binary.

Effort: about 2.5 h.
