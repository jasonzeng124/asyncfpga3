# B probe Lt4: exact forms of the operator obligations

Follows Lt3 (`B-ops-counter.md`, `OpsCounter.lean`). It works through the
open items Lt3 listed: `merge_data_ok` under the single node-launched x_ack
condition, `merge_ok` without `H_OR_SKEW`, counter-runs that need new
control runs (`H_SEL_START`, `S_Z_X` with x late, `S_Z_S0` and `S_Z_S1`
separated), and a first look at the C-element env-latency obligations.

## File and check

| file | lines | contents | check time |
|---|---|---|---|
| `formal/lean/Formal/Cells/OpsExact.lean` | ~1230 | §1 `merge_ok_noskew`, `MergeStaticNS`, `merge_timing_ns_of_static`; §2 `MergeDataExact`, `merge_data_ok_exact`, `MergeDataStatic.exact`, `merge_data_ok'`; §3 `MergeCex.*_S_SEL_XA_N`; §4 `MergeY` (y-first merge run, `H_SEL_START`); §5 `MuxA` (asymmetric mux run, x late); §6 `mux_rtz_of_J`, `merge_za_of_R` | ~20 s |

CLAIMED, core Lean (no Mathlib), no `sorry`/`admit`/`axiom`/`native_decide`.
It imports `Formal.Cells.OpsCounter` read-only (that brings in OpsTimed2,
OpsTimedWit, OpsTimedMux, OpsTimed, ConstraintsMux, Bundling, LibCtlMergeMux).
No shared definitions were edited. New names live in `Formal.Cells.OpsTimed`.
New sub-namespaces are `MergeY` and `MuxA`, and `MergeCex` gains
`apply_exact`, `bnd_S_SEL_XA_N` and `cex_S_SEL_XA_N`. `set_option
maxRecDepth 100000` is set only inside `MergeCex`, `MergeY` and `MuxA`.

    cd /home/user/asyncfpga3/formal/lean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsExact.lean
    cd .. && ./check.sh Formal/Cells/OpsExact.lean      # [check] OK (2642 declarations audited)

`#print axioms`, run in a scratch copy on the 16 main theorems, gives
`[propext, Classical.choice, Quot.sound]` or a subset.

## 1. `merge_ok` without `H_OR_SKEW` (item 2)

* `merge_ok_noskew` (G, V, `MergeTimingNoSkew`, `MergeCausal`, `1 ≤ Es`)
  proves `merge_ok`'s whole conclusion: z_req is a clean token trace on `Z`,
  `x_ack`/`y_ack` are clean on `XA`/`YA` with the right gates, and
  `ρ ≤ Z`, `ζ ≤ XA`, `ζ ≤ YA`. `MergeTimingNoSkew` is `MergeTiming` without
  `H_OR_SKEW`. The proof uses Lt3's `or_tok_mono` with `merge_or_step`.
  `merge_S_lt_ρ` supplies unboundedness, from causality alone.
* `MergeStaticNS` is `MergeStatic` without `S_OR`.
  `merge_timing_ns_of_static` derives `MergeTimingNoSkew` from it. Also
  `MergeStatic.ns` and `MergeTiming.ns` (the old structures imply the new
  ones).
* Non-vacuity: `MergeWit.noskew_witness`.

**Verdict.** The merge's `H_OR_SKEW` and `S_OR` are now removed by a theorem,
not only by its key lemma.

## 2. `merge_data_ok` under `S_SEL_XA_N`, without `S_SEL_XR` (item 1)

`merge_data_ok_exact` has the same conclusion as `merge_data_ok`: for every
merged token `k` and every `t ∈ [Z(2k) − Mz, ζ(2k) + Hm]`, `z t` is the
owner's bit. Its hypotheses are:
`MergeGates`, `MergeEnv`, `MergeCausal`, `1 ≤ Es`, `MergeStaticNS` (no
`S_OR`), reset sequencing, the usel/udat window relations (REAL INITs
`4'hE`, `8'hE4`), `MergeDataEnv`, and `MergeDataExact`. `MergeDataExact` is
`MergeDataStatic` with:

* **S_SEL_XA_N** `hq + sh + Mz ≤ Wxa.lo + Eo + Wyo.lo + Lor.lo + Dz.lo` in
  place of `S_SEL_XA_Z` and `S_SEL_XA_R`;
* **no `S_SEL_XR`**.

The key step is that in a y token `k` the launch is the LAST x token
`k0 < k` (`last_x`), not the previous merged token. Every slot in between is
a y slot, so x_req and the uxa node stay low across them (`Tok.low_range`).

* The x_req branch: `ρ(2k0+1) + Wxo.lo + Lor.lo + Dz.lo ≤ Z(2k0+1)`, and
  `Z(2k0+1) < ζ(2k0+1) ≤ XA(2k0+1) < ρ(2k0+2) ≤ ρ(2k)`. So `S_ZM_SEL_X`
  covers the branch, and **`S_SEL_XR` is redundant (proved)**.
* The x_ack branch: the node falls at `N`, then `N + Wxa.lo + Eo ≤ ρ(2k0+2)
  ≤ ρ(2k)` by `H_OWN` (owner x) and the monotonicity of `ρ`, which follows
  from causality alone (`merge_ρ_mono'`). This gives `S_SEL_XA_N`.
* With no x token before `k`, both branches are covered by `H_SEL_START`.

`MergeDataStatic.exact` proves that the old static set implies the new one
(`S_SEL_XA_Z ⇒ S_SEL_XA_N` via `wz ≤ Wzx.lo ≤ Wzx.hi`, etc.), so
`merge_data_ok'` re-derives `merge_data_ok` as a corollary. The new theorem
strictly generalises the old one.

**Tightness** (`MergeCex.bnd_S_SEL_XA_N`, `cex_S_SEL_XA_N`). In Lt's
unit-delay merge run, `hq = 4` is the boundary and the theorem applies. At
`hq = 5` only `S_SEL_XA_N` fails (every other `MergeDataExact` field is
restated and proved), and `z(23) = 1` where `yvC 1 = 0` is expected (y's
token 1). The theorem also proves `¬ MergeDataExact …` for those windows.

## 3. Counter-run for `H_SEL_START` (item 3a): `MergeY`

* The run: Lt's unit merge run moved 3 ticks earlier with the owners swapped.
  `ρ j = 8j+1`, `ζ j = 8j+5`, `Z j = 8j+4`, `XA = YA = 8j+8`, reset high on
  `[0,2)`, token 0 is y's. uxa's output at `t = 0` is a parameter `p`, its
  power-up level. `H_UXA` constrains the output only from `Lxa.hi = 1`.
  `MergeY.gates p`, `env`, `causal`, `static`, `hRE` and `witness p` (the
  whole control side via `merge_ok_noskew`) are proved for both values of
  `p`.
* `H_SEL_START` reads `max hr (1 + hq) + sh + Mz ≤ 1 + 3`. Its boundary is
  `hq = 2`, and `S_SEL_XA_N` allows up to `hq = 4`.
* `bnd_H_SEL_START p`: at `hq = 2` the theorem applies for either `p`.
* `cex_H_SEL_START`: at `hq = 3`, every other field of `MergeDataExact`
  holds, including `S_SEL_XA_N`. With `p = true`, usel still reads uxa's
  power-up level when y's token 0 reaches the server: `z(4) = xvC 0 = 1`,
  expected `yvC 0 = 0`. The theorem also proves
  `¬ MergeDataExact run 1 1 3 …`.
* `surv_H_SEL_START_low`: with `p = false`, the same violation is harmless
  at `t = 4..7`.

**Verdict.** `H_SEL_START` is exact, tight by one tick in this run, but only
against an uxa output that powers up high. It is a start-up condition about
uxa's undefined output before its first evaluation. Its `hr` part (x_req's
pin before `t = hr`) cannot be exercised by a transport run on ℕ, where
`x (t − hr)` saturates to `x 0 = 0`. That part is not shown necessary.

## 4. The asymmetric mux run `MuxA` (items 3b and 4)

The run has unit delays except `Wc0 = 2` (ctl_req → uj0). Control token `k`
(even: x, odd: y) sits on base `20k`. ctl_req rises at `20k+8` (x tokens) or
`20k+10` (y tokens) and falls at `20k+18`. **x_req reaches uj0 at
`20k+11`, one tick after ctl_req (`20k+10`), so x is the join's late
input.** y_req reaches uj1 4 ticks before ctl_req. Uniformly
`E(2k) = 20k+12`, `Z(2k) = 20k+15`, `ζ(2k) = 20k+16`, `XA = YA = 20k+19`
(falls 10 later). The select changes 4 ticks before each token's ctl_req
rise (`Ls = 4`, tight in both kinds of token). Gates, env (with
`H_S_PIN0/1`), enumerations, closed forms, `causal`, `static` and `hRE` are
all proved. `witness` gives the control side through `mux_ok_static`, and
`witness_values` checks `Xp 0 = 11 > C0 0 = 10`, `Yp 0 = 27 < C1 2 = 31`,
and the acks.

Data: x's bit `m` comes from x_req's rise (`Lx = 0`), y's likewise. Windows
are transport `[d, d]` on the REAL INIT `8'hE4`.

* `bnd`: `shi = 9`, `ahi = bhi = 5`. `mux_value_ok_static` applies.
* **`cex_S_Z_S1`** (item 4): at `shi = 10`, `S_Z_S0` holds (`10 ≤ 4+2+1+1+1+1`),
  `S_Z_S1` fails by one tick (`10 > 9`), and `S_Z_X`/`S_Z_Y` hold. y's token
  0 (control token 1) still reads token 0's select: `z(35) = xvC 0 = 1`,
  expected `yvC 0 = 0`. The theorem also proves `¬ MuxDataStatic run 1 10 1 1 0 4 0 0`.
  **`S_Z_S1` is necessary on its own.** The mirror statement (`S_Z_S0` alone,
  which needs `Wc1 > Wc0` with ctl late at uj0) is not built. It holds by
  the cell's x/y symmetry, but that is not proved.
* **`cex_S_Z_X`** (item 3b): at `ahi = 6`, `S_Z_X` fails by one tick and
  `S_Z_S0`, `S_Z_S1`, `S_Z_Y` hold. x's token 1 (control token 2) sees x's
  previous bit: `z(55) = xvC 0 = 1`, expected `xvC 1 = 0`. The theorem also
  proves `¬ MuxDataStatic run 1 1 6 1 0 4 0 0`. **The static `S_Z_X` is
  tight when x is the join's late input**, which completes Lt3's finding
  (4 ticks of slack in `MuxWit.run`, where ctl was late). The static form is
  exact exactly when the client is the late input.

## 5. C-element env-latency obligations (item 5, partial)

Proved (§6):

* `mux_rtz_of_J`, `mux_rtz_y_of_J`: `S_XA_RTZ` follows from `S_XA_J.1`
  whenever `Wzx.hi − Wzx.lo ≤ W0x.hi − W0x.lo`, and likewise for y.
* `merge_za_of_R`: `S_XA_ZA` follows from `S_XA_R.1` whenever
  `Wzx.hi − Wzx.lo ≤ Wxc.hi − Wxc.lo`.

So with fixed (spread-free) wires the RTZ / z_ack-pulse obligations are
redundant. They can bind only through the z_ack wire's rise/fall delay
spread.

Analysis, NOT proved (design for the next probe):

* **mux `S_XA_RTZ` is plausibly exact.** In the mux the next token's z_ack
  rise is NOT causally after x_ack's fall: the control sender reacts to
  z_ack, and the next requester is independent. If x's z_ack FALL reaches
  uxa late (`Wzx.hi`) and the next token's z_ack RISE early (`Wzx.lo`), the
  low pulse at uxa can be shorter than uxa's loop. If the node has just
  fallen, the stale high phase of the feedback gives `C(0, 1, 1) = 1`, a
  glitch on x_ack inside y's token. Candidate run: unit delays except
  `W0x = shift 6`, `Lxa.hi + wxah = 2`, `R = 8`, and `Wzx` a time-varying
  FIFO `Ret` (`lo = 1`, `hi = 8`: delay 8 at x-token z_ack falls, 1 at the
  next rises). Then `S_XA_RTZ` fails (`10 > 9`) while `S_XA_FORK` (`10 ≤ 10`)
  and `S_XA_J` (`8 ≤ 14`, `8 ≤ 13`) hold. The expected failure is
  `¬ Tok P.Tx xak P.XA …`, a high xak inside a y slot. Cost: a full new mux
  run with a non-shift `Ret` and its `fst` closed forms, about 400 lines.
* **merge `S_XA_ZA` / `H_DEP_XA` are probably NOT exact.** In the merge, the
  next request waits for the previous owner's acknowledge FALL (`H_OWN`).
  So after a real uxa node edge, the next edge of either uxa input is
  causally after `node + Wxa + Eo (+ Kz + Wzx.lo)`. The loop then has a
  node-launched slack, like `S_SEL_XA_N`:
  `Lxa.hi + wxah ≤ Lxa.lo + Wxa.lo + Eo + min(Wxc.lo, Kz + Wzx.lo)`.
  At y-owned (bookkeeping) edges uxa does not move, so the instance there is
  a proof artefact, of the same kind as `H_OR_SKEW`. Removing it needs a
  `cel_run` variant that asks `H_DEP` only at gate-on edges (the
  `Tok.retime` idea applied to the C-element). Not written.
* **mux `H_DEP_J0` via `S_J0_X` is only sufficient.** The static form bounds
  x's return path through `A0` only (`XAge` uses `A0 ≤ cx`). But `cx =
  max(A0, ZA0)` and `ZA0 ≥ E + Kz + Wzx.lo`, so the x-branch bound can use
  `max(W0x.lo, Kz + Wzx.lo)` in place of `W0x.lo`. In any realistic netlist
  `Kz` (uor + delay line + server) dominates, so `S_J0_X` as stated has
  slack. The ctl branch `S_J0_C` goes through the server and has no such
  looseness. No counter-run was attempted for either.

## Summary table (for the JSON update)

| obligation | theorem / counter-run | exactness |
|---|---|---|
| merge `S_SEL_XA_N` (new; replaces `S_SEL_XA_Z` + `S_SEL_XA_R`) | `merge_data_ok_exact`; `MergeCex.bnd_S_SEL_XA_N`, `cex_S_SEL_XA_N` | **exact** (sufficient in general, tight by 1 tick in `MergeWit.run`) |
| merge `S_SEL_XA_Z`, `S_SEL_XA_R` | `MergeDataStatic.exact`, `merge_data_ok'` | superseded: `S_SEL_XA_Z ⇒ S_SEL_XA_N`; `S_SEL_XA_R` no longer needed |
| merge `S_SEL_XR` | `merge_data_ok_exact` (does not assume it) | **redundant** (proved) |
| merge `H_SEL_START` | `MergeY.bnd_H_SEL_START`, `cex_H_SEL_START`, `surv_H_SEL_START_low` | **exact** (tight by 1) in its `Lxa.hi + hq` part, against uxa powering up high; `hr` part not shown |
| merge `H_OR_SKEW` / `S_OR` | `merge_ok_noskew`, `merge_timing_ns_of_static`, `merge_data_ok_exact` | **not necessary** (removed by a theorem) |
| mux `S_Z_S1` | `MuxA.cex_S_Z_S1` (+ `bnd`) | **exact, individually** (tight by 1 with `S_Z_S0` holding) |
| mux `S_Z_S0` | Lt3 `MuxCex.cex_S_Z_S` (joint) | exact jointly; individually by the x/y mirror of `cex_S_Z_S1` (not built) |
| mux `S_Z_X` | `MuxA.cex_S_Z_X` (+ `bnd`); Lt3 `surv_S_Z_X` | **exact when x is the join's late input** (tight by 1); slack = ctl lateness otherwise |
| mux `S_Z_Y` | Lt3 `cex_S_Z_Y` | as `S_Z_X` by symmetry (late-y run not built) |
| mux `S_XA_RTZ` / `S_YA_RTZ` | `mux_rtz_of_J`, `mux_rtz_y_of_J` | **redundant unless the z_ack wire's spread exceeds the j→uxa wire's**; plausibly exact otherwise (counter-run designed, not built) |
| merge `S_XA_ZA` | `merge_za_of_R` | redundant under the same spread condition; probably not exact (node-launched form proposed) |
| mux `H_DEP_J0/J1` (`S_J0_X`, `S_J1_Y`) | none | only sufficient (analysis: the x return path also waits for z_ack); `S_J*_C` not probed |

## What this means for `cell_constraints.json` (JSON not edited)

* `bd_merge.isochronic_forks` (x_ack branch): the gate is `S_SEL_XA_N`
  (`hq + sh + Mz ≤ Wxa.lo + Eo + Wyo.lo + Lor.lo + Dz.lo`, node-launched).
  Drop `S_SEL_XA_Z`/`S_SEL_XA_R` as separate checks, and do not add
  `sel_low_xreq` (`S_SEL_XR`).
* `bd_merge.or_skew`: drop (`merge_ok_noskew`).
* `bd_mux.bundled_z_s`: keep both pins' forms. Each is individually
  necessary (`S_Z_S1` shown; `S_Z_S0` by mirror).
* `bd_mux.bundled_z_data`: keep. The static form is exact when the client
  is the join's late input, which a routed netlist can produce. Using it
  everywhere is safe, not merely conservative.
* `bd_merge` start-up: keep `H_SEL_START` as a reset-sequencing condition
  (uxa defined and seen by usel before the first request arrives). It is a
  reset-polarity fact in the sense of CLAUDE.md ("true once at startup").
* `bd_mux.uxa_rtz_env`: the checker can skip it when the z_ack wire's
  min/max spread is no larger than the j0→uxa wire's. Otherwise keep it.

## What did not work / not done

* No mux run with x late AND `Wc1 > Wc0`, so `S_Z_S0`'s individual necessity
  is by symmetry only. No late-y run for `S_Z_Y`.
* The RTZ counter-run (non-shift `Ret` for `Wzx`) is designed above but not
  built.
* No `cel_run` variant without bookkeeping-edge `H_DEP`, so the merge's
  `H_DEP_XA` at y-owned edges is not removed.
* `H_SEL_START`'s `hr` part cannot be tested in a transport run on ℕ.
* All findings are about the MODEL: FIFO wires, transport windows on the
  data side, binary control side, and LUTs as FIFO channels (H_LUT_FIFO).

## Verdict

**Works.** Items 1–4 are done and claimed. `merge_data_ok` now holds under
the single exact x_ack condition, with `S_SEL_XR` and `S_OR` removed by
theorems. `merge_ok` holds without `H_OR_SKEW`. `H_SEL_START`, `S_Z_S1`
(alone) and `S_Z_X` (with x late) have kernel-checked counter-runs that are
tight by one tick. Item 5 is partial: the RTZ/ZA obligations are shown
redundant under a spread condition, and the remaining counter-run is
designed. Effort to finish: the RTZ counter-run, about half a day; a
`cel_run` that needs `H_DEP` only at real edges, plus the node-launched
merge env-latency form, about one day; mirror runs for `S_Z_S0` and
`S_Z_Y`, about two hours each (copy `MuxA` with roles swapped).

## Fidelity per primitive

* **usel** (LUT2 `4'hE`) and **udat** (`bd_datamux`, LUT3 `8'hE4`): REAL
  INITs evaluated with `lutB` on a transport-delay pin model, turned into
  the window relation by `Bundling.transport_gate` (window `[d, d]`). The
  counter-runs are concrete transport traces, which is one admissible
  behaviour of the window model. Grade A-: no glitch filtering, no
  metastability.
* **Control side** (uj0/uj1, uor, uxa/uya, wires, delay line): Lt's binary
  FIFO LUT arcs (H_LUT_FIFO) with REAL INITs (`j0B`, `j1B`, `c2B`, `or2B`).
  The C-elements are LUTs whose output feeds back through a 1-tick wire
  (`win11`). `MuxA` has a 2-tick transport wire (`Ret.shift 2`) on ctl→uj0.
  `MergeY` leaves uxa's output before its first evaluation free (power-up
  level). Grade B.
* **Partners**: open-loop periodic environments, causal with one-tick
  reaction (`MergeCausal … 1 1`, `MuxCausal … 1 1 1 1`).
* **Time**: ℕ ticks.
