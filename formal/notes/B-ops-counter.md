# B probe Lt3: are the operator cells' obligations necessary?

Follows Lt (`B-ops-timed.md`) and Lt2 (`B-ops-timed2.md`). Those probes proved
the timed contracts of `bd_steer`, `bd_mux`, `bd_merge` (control and value)
under named obligations, and their negative controls showed only that the
proofs USE them. This probe asks, for each obligation, whether it is
NECESSARY. It gives a concrete transport-delay run on the real INITs that
satisfies every other hypothesis, violates that one, and makes the
conclusion false. Where no such run can exist, it proves a theorem without
the obligation instead.

## File and check

| file | lines | contents | check time |
|---|---|---|---|
| `formal/lean/Formal/Cells/OpsCounter.lean` | ~960 | §1 merge data counter-runs; §2 mux data counter-runs and a survival run; §3 `Tok.retime`, `or_tok_mono`, `mux_or_step`, `mux_ok_noskew`; §4 `mux_ack_pulses_noPW`, `merge_*A_real_step`; §5 `steer_back_noskew`, `merge_or_step` | ~6-8 s |

CLAIMED, core Lean (no Mathlib), no `sorry`/`admit`/`axiom`/`native_decide`.
Imports `Formal.Cells.OpsTimed2` (read-only; it brings in OpsTimedWit,
OpsTimedMux, OpsTimed, ConstraintsMux, Bundling, LibCtlMergeMux). No shared
definitions were added. New names live in `Formal.Cells.OpsTimed` under the
sub-namespaces `MergeCex` and `MuxCex`. The other new top-level names
(`Tok.retime`, `or_tok_mono`, `MuxRun.Sor`, `MuxTimingNoSkew`,
`mux_ok_noskew`, `mux_ack_pulses_noPW`, `steer_back_noskew`, ...) do not
clash with Lt's or Lt2's. `set_option maxRecDepth 100000` is set inside
`MergeCex` and `MuxCex` only, for the kernel `decide` on trace values at
t ≤ 103.

    cd /home/user/asyncfpga3/formal/lean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsCounter.lean
    cd .. && ./check.sh Formal/Cells/OpsCounter.lean    # [check] OK (2466 declarations audited)

`#print axioms` (in a scratch copy) on all 22 main theorems below returned
`[propext, Classical.choice, Quot.sound]` only.

I did not write an olean. At the end of the probe `-o` failed, because
`MuxTree.olean` was missing (another process is rebuilding the shared
oleans). The plain check above had passed before that.

## Method

* The control side of every counter-run is Lt's unit-delay witness,
  unchanged: `MuxWit.run` / `MergeWit.run`. Every LUT and wire is 1 tick,
  partners are causal, and `gates`, `env`, `causal`, `static` are the same
  proof terms. Only the data side varies: the data and select traces, and
  the transport delay `d` on each `udat`/`usel` pin. Each pin's window is
  `[d, d]` (`Bundling.transport_gate`, real INITs `8'hE4` and `4'hE`).
* For each value-path obligation O:
  * `bnd_O`: O holds with equality, and the theorem (`merge_data_ok` /
    `mux_value_ok_static`) is applied, so the conclusion holds.
  * `cex_O`: O is violated, every other `*DataStatic` field is restated
    literally and proved, and the conclusion fails. It is shown both as the
    negated `∀ k t …` conclusion and as an explicit token, instant, delivered
    bit and expected bit. All are kernel `decide` on the simulated traces.
* For merge obligations, `cex_O_static` also proves that NO
  `MergeDataStatic` instance exists with those windows. If it did,
  `merge_data_ok` would make the conclusion true. This is a check that the
  counter-run really sits outside the theorem.
* Data vectors are not degenerate. In each failing instant the delivered
  bit differs from the expected one, and the expected bit takes both values
  over the run's tokens. Expected values come from the run's own data
  definitions (`xvC`, `yvC`), not from simulation output.

## Results

### Value path

| obligation | counter-run theorem | violation | failure | verdict |
|---|---|---|---|---|
| merge `S_ZM_SEL_X` (`bd_merge.bundled_z`) | `MergeCex.bnd_S_ZM_SEL_X`, `cex_S_ZM_SEL_X`, `cex_S_ZM_SEL_X_static` | usel `x_req` pin 3 ticks (`hr+sh = 4 > 3`, 1 past the boundary) | x token 0: select still low at `Z 0 = 7`, `z = y's bit 0`, expected `1` | **exact** in this run (boundary holds, boundary + 1 fails) |
| merge `S_ZM_X` (`bundled_z_data`) | `bnd_S_ZM_XY`, `cex_S_ZM_X`, `_static` | x_data pin 8 (`8 > Lx+3 = 7`) | x token 2: server sees x's previous bit `1`, expected `0` | **exact** in this run |
| merge `S_ZM_Y` | `bnd_S_ZM_XY`, `cex_S_ZM_Y`, `_static` | y_data pin 8 | y token 3: sees `0`, expected `1` | **exact** in this run |
| merge `S_SEL_XA_Z` (`bd_merge.isochronic_forks`, x_ack branch) | `bnd_S_SEL_XA_Z`, `cex_S_SEL_XA_Z`, `_static` | usel `x_ack` pin 5 (`1+1+5+1 = 8 > 7`); `S_SEL_XA_R` and `H_SEL_START` still hold | y token 1: the previous x token's uxa node (`xa 17 = 1`, `xa 18 = 0`) still selects x at `Z 2 = 23`, `z = 1`, expected `0` | **exact** in this run. This is the JSON's `unproved` x_ack-branch entry, now with a counter-run |
| merge `S_SEL_XR` | none | cannot be violated alone in this run family | n/a | **only sufficient, redundant** (see below) |
| merge `S_SEL_XA_R` | none | cannot be violated alone in `MergeWit.run` (needs `Wxc.hi > Wzx.hi + Kz`) | n/a | **only sufficient** (see below); not shown necessary |
| merge `H_SEL_START` | none | token 0 of `MergeWit.run` is x's, so it is never used there | n/a | **not shown** (needs a run whose token 0 is y's and a uxa output that powers up high) |
| mux `S_Z_S0` / `S_Z_S1` (`bd_mux.bundled_z_s`) | `MuxCex.bnd_S_Z`, `cex_S_Z_S` | `shi = 10` (1 past `Ls+5 = 9`); both inequalities fail, because they share the select pin and have equal right-hand sides here | y token (control token 1): stale select picks x, `z(31) = 1`, expected `0`; AND x token (control token 4): picks y, `z(85) = 0`, expected `1` | **exact** in this run, for the pair. They are not separated: that needs a run with `Wc0 ≠ Wc1` or `Lj0 ≠ Lj1` |
| mux `S_Z_X` (`bundled_z_data`) | `bnd_S_Z`, `surv_S_Z_X`, `cex_S_Z_X` | `ahi = 9` (4 past the boundary): the conclusion **still holds for every token and instant** (`surv_S_Z_X`). `ahi = 10` (5 past) fails | control token 2: `z(49) = 1` (x's previous bit), expected `0` | **only sufficient as stated** (slack 4 here). The static form bounds `Z` through x's own request path, but the join waits for the LATER of x_req and ctl_req, and in this run ctl_req is 4 ticks later. Exact condition: `ahi + Mz ≤ Lx + (Z(2k) − ξ(2m))`. The static form equals it when x is the join's late input and the arcs are at their minimum. Not exhibited (needs a run where x is the late input) |
| mux `S_Z_Y` | `bnd_S_Z`, `cex_S_Z_Y` | `bhi = 10` | control token 5: `z(103) = 0`, expected `1` | as `S_Z_X` (same 4-tick slack by symmetry; survival not written) |

Why `S_SEL_XR` and `S_SEL_XA_R` are only sufficient:

* **`S_SEL_XR`.** In a y token, x_req has been low since x's last fall. If
  that x token is the previous token, its fall reached the server through
  `Wxo`, so the exact condition is
  `hr+sh+Mz ≤ (Wxo.lo+Lor.lo+Dz.lo+Es) + Ka + (Wyo.lo+Lor.lo+Dz.lo)`.
  `S_ZM_SEL_X` (`hr+sh+Mz ≤ Wxo.lo+Lor.lo+Dz.lo`) implies it. If the last x
  token is earlier, there is even more time. The static `S_SEL_XR` has
  `wo = min(Wxo.lo, Wyo.lo)` in place of `Wxo.lo`, a looseness of the proof
  route (it bounds `ρ(2k'+1) → ζ(2k'+1)` uniformly over owners). So
  `S_SEL_XR` is redundant once the proof tracks the owner of the last x
  token. That re-proof is not written: it needs a "last x token before k"
  index, or `Tok.retime` applied to the uxa node.
* **`S_SEL_XA_Z` / `S_SEL_XA_R`.** Both are lumped forms of one exact
  condition launched by the uxa NODE's fall. The node falls at the later of
  the x_req fall and the z_ack fall at uxa. The data path is node → usel
  (`hq`) → udat select (`sh`) + `Mz`. The request path is node → `Wxa` →
  owner client (`Eo`, H_OWN) → y_req → `Wyo` → uor → line. This gives
  **`hq + sh + Mz ≤ Wxa.lo + Eo + Wyo.lo + Lor.lo + Dz.lo`** (proposed name
  `S_SEL_XA_N`), whichever input of uxa falls last. In `MergeWit.run` it has
  the same boundary as `S_SEL_XA_Z` (`hq = 4`), so `cex_S_SEL_XA_Z` also
  shows `S_SEL_XA_N` is exact there. `S_SEL_XA_R` covers the case where
  x_req's fall is the later one. Its RHS uses the `Kz + Ka` round trip
  instead of the node-launched path, so it is sufficient, and its necessity
  as stated is not shown. Proving `merge_data_ok` under `S_SEL_XA_N` alone
  is not done: it needs the same last-x-token argument as `S_SEL_XR` when
  the previous owner is y.

### Control path

| obligation | theorem | verdict |
|---|---|---|
| mux `H_OR_SKEW` (event form) and `S_OR` (static form) | `Tok.retime`, `or_tok_mono`, `mux_or_step`, `mux_ok_noskew` (+ `MuxWit.noskew_witness`) | **NOT necessary, in general.** `or_tok` required every edge of each uor pin to precede the other pin's next edge, including bookkeeping edges of tokens the pin does not carry (the pin is low across them). `Tok.retime` moves a token trace onto any monotone sequence that agrees with it on its gate-on slots. `or_tok_mono` then needs only that the SELECTED edge sequence increases, and `mux_or_step` proves it strictly increasing from `MuxCausal` alone (`1 ≤ Es`). `mux_ok_noskew` proves every conclusion of `mux_ok` except the order facts (which never used the skew) without `H_OR_SKEW` and without `H_CTL_SEQ`. No counter-run can exist. `S_OR` is used in `mux_timing_of_static` only to derive `H_OR_SKEW`, so it can be dropped from `MuxStatic` |
| merge `H_OR_SKEW` / `S_OR` | `merge_or_step` | **NOT necessary** by the same argument: the selected sequence is strictly increasing from `MergeCausal` (`1 ≤ Es`). The `merge_ok` re-plumbing, a mechanical copy of `mux_ok_noskew`, is not written |
| steer `H_ACK_SKEW` (and the static `S_ACK`) | `steer_back_noskew` | **NOT necessary**: `steer_back`'s conclusion (one clean ack per token at the sender) holds from `H_RCV`, `H_SND` and `1 ≤ Es`, with no skew condition |
| mux `S_XA_PW` / `S_YA_PW` | `mux_XA_real_step`, `mux_YA_real_step`, `mux_ack_pulses_noPW` (+ `MuxWit.ack_pulses_noPW_witness`) | **NOT necessary for the physical claim.** Every x token's acknowledge at the client is a non-empty pulse with a non-empty gap after it, and `xak` is high at its rise and low at its fall. This holds under all of `mux_pulses`' hypotheses except `S_XA_PW`/`S_YA_PW`, with `1 ≤ Ex`, `1 ≤ Ey`. The reason: the client drops its request only after seeing x_ack rise, and uxa's node falls only after that fall crossed the join. So x_ack's fall reaches the client after its rise, through the same FIFO wire. A pulse that ends because it was observed cannot be swallowed by the wire that delivered it. `S_XA_PW` is needed only for `mux_pulses`' `∀ j, XA j < XA (j+1)` over control-indexed edges, i.e. including the bookkeeping edges of y tokens, where x_ack does not move |
| merge `S_XA_PW` | `merge_XA_real_step`, `merge_YA_real_step` | **NOT necessary** for the owner's real pulse (`1 ≤ Eo`, from `H_OWN`) |
| mux `S_XA_RTZ`, `H_DEP_J0/J1`, `H_BUNDLED_S_PIN`; merge `S_XA_ZA`, `S_XA_R`, `S_XA_FORK` | none | **not probed** (time). These are C-element env-latency and fork conditions. A counter-run needs a different control run, so the open-loop witnesses would have to be rebuilt |

### Summary table (the requested form)

| obligation | counter-run / theorem | exact or only sufficient |
|---|---|---|
| S_Z_S0 / S_Z_S1 | `MuxCex.cex_S_Z_S` (+ `bnd_S_Z`) | exact (tight by 1 tick) in `MuxWit.run`, jointly |
| S_Z_X | `MuxCex.surv_S_Z_X`, `cex_S_Z_X` | only sufficient as stated (4-tick slack = ctl lateness at the join); exact form named |
| S_Z_Y | `MuxCex.cex_S_Z_Y` | as S_Z_X |
| S_ZM_SEL_X | `MergeCex.cex_S_ZM_SEL_X` (+ `bnd`, `_static`) | exact (tight by 1) |
| S_ZM_X / S_ZM_Y | `MergeCex.cex_S_ZM_X`, `cex_S_ZM_Y` (+ `bnd`, `_static`) | exact (tight by 1) |
| S_SEL_XA_Z | `MergeCex.cex_S_SEL_XA_Z` (+ `bnd`, `_static`) | exact (tight by 1) in `MergeWit.run`; equals the node-launched `S_SEL_XA_N` there |
| S_SEL_XA_R | none | only sufficient (a lumped form of `S_SEL_XA_N`); necessity as stated not shown |
| S_SEL_XR | none | redundant (exact form implied by S_ZM_SEL_X); re-proof not written |
| H_SEL_START | none | not shown (unused in `MergeWit.run`) |
| S_XA_PW / S_YA_PW | `mux_ack_pulses_noPW`, `mux_*A_real_step`, `merge_*A_real_step` | not necessary (for real pulses; causality suffices) |
| H_OR_SKEW / S_OR (mux) | `mux_ok_noskew` | not necessary (general theorem) |
| H_OR_SKEW / S_OR (merge) | `merge_or_step` | not necessary (key lemma proved; re-plumbing not written) |
| H_ACK_SKEW (steer) | `steer_back_noskew` | not necessary (general theorem) |
| S_XA_RTZ, H_DEP_J0/J1, H_BUNDLED_S_PIN | none | not probed |

## What this means for `cell_constraints.json` (JSON not edited)

* Remove or demote **`bd_mux.or_skew`, `bd_merge.or_skew`,
  `bd_steer.ack_or_skew`**, which Lt reported as missing and proposed to add.
  They are artefacts of a proof route, and no routed netlist can fail them
  in the model.
* Do not add **`bd_mux.ack_pulse_width` / `bd_merge.ack_pulse_width`**
  (Lt2's S_XA_PW) as gates. The real pulse is self-timed through its
  observer.
* `bd_mux.bundled_z_s`, `bd_merge.bundled_z`, `bd_merge.bundled_z_data`:
  keep. A one-tick violation corrupts the delivered value in a run that is
  otherwise fine.
* `bd_mux.bundled_z_data` (S_Z_X/Y): keep it as the safe form, but it is
  not tight when the control request is the join's late input. A checker
  that wants the exact margin must use `Z(2k) − ξ` along the actually-late
  path.
* `bd_merge.isochronic_forks` (x_ack branch): the counter-run shows the
  branch is real. The single exact form is `S_SEL_XA_N`
  (`hq + sh + Mz ≤ Wxa.lo + Eo + Wyo.lo + Lor.lo + Dz.lo`, node-launched).
  `S_SEL_XA_Z`/`S_SEL_XA_R` are two sufficient lumpings of it.

## What did not work / not done

* No standalone counter-runs for `S_SEL_XR`, `S_SEL_XA_R`, `H_SEL_START`.
  Each needs a new control run: long `Wxo`, long `Wxc`, or token 0 owned by
  y. Re-proving `MergeGates`/`MergeEnv`/`MergeCausal` for a new open-loop
  run is about 150-250 lines, copied from `MergeWit` with new closed forms.
* No run where x's request is the join's late input, which would show
  `S_Z_X`'s exact form tight.
* `S_Z_S0` and `S_Z_S1` are not separated (needs asymmetric control
  wires).
* Merge `merge_ok_noskew` re-plumbing; `merge_data_ok` under `S_SEL_XA_N`
  alone; dropping `S_SEL_XR`.
* The C-element obligations (`S_XA_RTZ`, `H_DEP_J*`, `S_XA_ZA`, `S_XA_R`,
  fork conditions) and `H_BUNDLED_S_PIN` are not probed.
* Every finding is about the MODEL (FIFO channels and transport windows,
  binary control side). "Not necessary" means not necessary in the model.
  The physical argument behind `S_XA_PW`, a pulse ended by its own
  observation, holds for any FIFO wire, but not for an inertial wire that
  can glitch.

## Verdict

**Works.** Of the value-path obligations, six (S_Z_S0/S1 jointly,
S_ZM_SEL_X, S_ZM_X, S_ZM_Y, S_SEL_XA_Z) are shown tight by kernel-checked
counter-runs that violate only that inequality by one tick in otherwise
fully valid runs. S_Z_X/Y are shown not tight as stated (4 ticks of slack
in a run where the control request is late), with a survival proof and a
counter-run past the slack. Four control obligations that Lt/Lt2 introduced
(H_OR_SKEW/S_OR for mux and merge, H_ACK_SKEW, S_XA_PW/S_YA_PW) are shown
UNNECESSARY by general theorems: proof artefacts from bookkeeping edges.
That removes four candidate JSON entries before anyone builds checks for
them.

Effort to finish: standalone runs for S_SEL_XR / S_SEL_XA_R / H_SEL_START
and an x-late mux run, ~0.5-1 day (new open-loop runs). `merge_ok_noskew`
and `merge_data_ok` with `S_SEL_XA_N`, ~0.5 day. The C-element
env-latency obligations, ~1 day (needs runs with feedback-window
violations).

## Fidelity per primitive

* **udat** (`bd_datamux`, LUT3 `8'hE4`) and **usel** (LUT2 `4'hE`): the real
  INITs, evaluated with `lutB` on a TRANSPORT-delay pin model (`Transport`,
  fixed integer delay per pin), turned into the window relation by
  `Bundling.transport_gate` with window `[d, d]`. The counter-runs are
  concrete transport traces, which is one admissible behaviour of the window
  model. The window model also allows others, so a failure here is a failure
  of the window model too. Grade A- (no glitch filtering, no metastability).
* **Control side** (uj0/uj1/uor/uxa/uya/u/uack, wires, delay line): Lt's
  binary FIFO LUT arcs (H_LUT_FIFO) with window feedback nets. In the
  counter-runs it is concretely unit transport delay (Lt's witnesses).
  Grade B.
* **C-elements** (uxa, uya, joins): LUTs whose output feeds back through a
  1-tick wire (`win11`), the real `bd_c2` / `uj` INITs.
* **Partners**: Lt's open-loop periodic environments, causal with one-tick
  reaction (`MuxCausal … 1 1 1 1`, `MergeCausal … 1 1`). Data senders as
  stated in each `*DataEnv`.
* **Time**: ℕ ticks.
