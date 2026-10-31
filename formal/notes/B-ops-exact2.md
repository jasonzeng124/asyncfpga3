# B probe Lt5: the remaining operator exactness items

Follows Lt4 (`B-ops-exact.md`, `OpsExact.lean`). Lt4 left three items open:

1. Is the mux's `S_XA_RTZ` exact? (Lt4 designed a counter-run with a z_ack
   wire that is slow on falls and fast on rises.)
2. Mirror runs for `S_Z_S0` on its own, and for `S_Z_Y` with y late.
3. The merge's `H_DEP_XA` at y-owned edges looks like a proof artefact.
   Remove it with a `cel_run` variant and re-prove `merge_ok`.

All three are done and claimed. Item 3 went further than asked: the
merge's acknowledge obligations now have a node-launched static form with
no spread terms, and each of its three fields has a counter-run that is
tight by one tick.

## File and check

| file | lines | contents | check time |
|---|---|---|---|
| `formal/lean/Formal/Cells/OpsExact2.lean` | ~2040 | §1 `MuxRtz` (S_XA_RTZ); §2 `MuxB` (mirror of `MuxA`); §3 `cel_run_g`, `MergeTimingG`, `merge_ok_g`, `MergeStaticG`, `merge_timing_g_of_static`, `merge_ok_gs`, `MergeN`, `MergeS`, `MergeR` | ~16 s |

The file is CLAIMED and uses core Lean only (no Mathlib). It has no
`sorry`, `admit`, `axiom` or `native_decide`. It imports
`Formal.Cells.OpsExact` read-only and edits no shared definition. New names
live in `Formal.Cells.OpsTimed`: the sub-namespaces `MuxRtz`, `MuxB`,
`MergeN`, `MergeS` and `MergeR`, plus the top-level `Ret.fst_eq_of`, `rtA`,
`vph_odd'`, `cel_run_g`, `MergeTimingG`, `MergeTimingNoSkew.g`,
`merge_ζ_step`, `merge_ok_g`, `MergeWit.g_witness`, `MergeStaticG`,
`MergeStaticNS.g`, `merge_RZ_g`, `merge_timing_g_of_static` and
`merge_ok_gs`. `set_option maxRecDepth 100000` is set only inside the five
run namespaces.

    cd /home/user/asyncfpga3/formal/lean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsExact2.lean
    cd .. && ./check.sh Formal/Cells/OpsExact2.lean      # [check] OK (2578 declarations audited)

I ran `#print axioms` on the 25 main theorems in a scratch copy. Each one
gives `[propext, Classical.choice, Quot.sound]` or a subset of it.

## 1. `S_XA_RTZ` is exact: `MuxRtz`

**The run.** `MuxRtz.run e` is a unit-delay mux run with two exceptions:

* `W0x = shift 6`, the j0 → uxa wire.
* `Wzx = Rz e`, the z_ack → uxa wire. It is a time-varying FIFO channel
  (`Ret`, not a shift). After each z_ack fall it holds the old value for
  `min e 7` extra ticks, so falls take `min e 7 + 1` ticks and rises take 1.
  `Ret.fst_eq_of` reads edge arrivals off the read-time map.

Reset is high on `[0, 8)`.

**The schedule.** Control token `k` sits on base `20k`; even tokens are x's
and odd tokens are y's. ctl_req is the late input at its join, so
`E(2k) = 20k+12`, `ζ(2k) = 20k+16` and `ζ(2k+1) = 20k+28`. The next control
token is raised by the minimal causal chain from z_ack's fall. So z_ack
rises again exactly 8 ticks after it falls, which is the RHS of `S_XA_RTZ`
(`Wzc.lo + Ec + wc + lj + wo + Lor.lo + Dz.lo + Es + Wzx.lo = 9` including
`Wzx.lo`).

**What is proved.**

* `gates e`, `env e`, `causal`, `hRL` and `hRE` hold for every `e`, with
  closed forms for every derived edge. In particular
  `ZA0 (2k+1) = 20k + 29 + min e 7`.
* **`bnd_S_XA_RTZ`**: at `e = 6` (falls 7 ticks late) every field of
  `MuxStatic` holds (`static6`), `S_XA_RTZ` holds with equality (`9 = 9`),
  and `mux_ok_static` applies. z_req, x_ack and y_ack are clean.
* **`cex_S_XA_RTZ`**: at `e = 7` (falls 8 ticks late):
  * Every `MuxStatic` field except `S_XA_RTZ` holds (`static_but_rtz`), with
    `S_XA_FORK` holding with equality (`10 = 10`).
  * `S_XA_RTZ` fails by one tick (`rtz_fails`: `10 = 9 + 1`, and
    `¬ MuxStatic …`).
  * The conclusion fails. x_ack is not a clean token trace on its x-gated
    edges, nor on x's own token sequence. The event form fails too:
    `¬ MuxTiming run 8`, at `H_DEP_XA 1` against `ZA0 2` (`38 > 37`).
* **`glitch_values`** (kernel `decide`): x's token 0 is acknowledged at
  `XA 0 = 20` and x_ack drops at `XA 1 = 38`. z_ack is low at uxa only at
  `t = 36`. uxa's LUT then computes `C(0, 0, 1) = 0` and, from its stale
  feedback, `C(0, 1, 1) = 1`. x_ack is high at 39 and at 41, inside y's
  token (control token 1), where it must be low. At `e = 6` it stays low
  there.

**Verdict.** `S_XA_RTZ` is exact, and tight by one tick. In this run the
z_ack wire's rise/fall spread (`Wzx.hi − Wzx.lo = 7`) exceeds the j0 → uxa
wire's spread (0). That is exactly the regime where Lt4's `mux_rtz_of_J`
does not make RTZ redundant. The obligation binds because the mux's next
z_ack rise is launched by z_ack's own fall, through the control sender, and
not by uxa's node. It is wire-launched, so the wire's spread enters it.

## 2. The mirror of `MuxA`: `MuxB`

`MuxB.run` is `MuxA` with the inputs' roles exchanged:

* `Wc1 = shift 2`.
* Even control tokens are y's (`svB k = (k % 2 = 0)`).
* `κ1 m = 2m` and `κ0 m = 2m+1`.
* y requests at `40m+10` and reaches uj1 one tick after ctl_req, so y is
  uj1's late input. x waits at uj0.

It reuses `MuxA.ctl`, `MuxA.za`, `MuxA.sTok` and `MuxA.sS`. The data swap
values too: x carries `MuxCex.yvC` and y carries `MuxCex.xvC`, so that
every failing instant is non-degenerate.

The control side is proved in full: `gates`, `env`, `causal`, `static`,
`hRE`, `witness` (through `mux_ok_static`), and `witness_values`
(`Yp 0 = 11 > C1 0 = 10`).

* `bnd`: `shi = 9`, `ahi = bhi = 5`. `mux_value_ok_static` applies.
* **`cex_S_Z_S0`**: at `shi = 10`, `S_Z_S0` fails by one tick
  (`10 > 4+1+1+1+1+1`). `S_Z_S1` holds with equality, and `S_Z_X` and
  `S_Z_Y` hold. x's token 0 (control token 1) still reads token 0's select:
  `z(35) = 1`, where x's bit is `yvC 0 = 0`. Also
  `¬ MuxDataStatic run 1 10 1 1 0 4 0 0`.
* **`cex_S_Z_Y`**: at `bhi = 6`, `S_Z_Y` fails by one tick and the other
  three hold. y's token 1 (control token 2) sees y's previous bit: `z(55) = 1`,
  where `xvC 1 = 0`. Also `¬ MuxDataStatic run 1 1 1 6 0 4 0 0`.

**Verdict.** Both `S_Z_S0` and `S_Z_S1` are individually necessary. `S_Z_Y`
is tight when y is its join's late input, exactly as `S_Z_X` is when x is.
Both now have kernel-checked runs; neither rests on a symmetry argument.

## 3. `H_DEP` only at real edges

### 3a. `cel_run_g` (generic)

Take a C-element whose input `a` is gated by `ga` and whose input `b`
pulses in every token. Examples are x_req (or j0) and z_ack at uxa.

In a gate-off token, `a` does not move, so its edges there are bookkeeping.
The excitation's target is 0, `a` is low, and the loop has been settled low
since the last real fall, so `b` cannot move the C-element.

`cel_run_g` keeps `cel_run`'s conclusion: the excitation is the token trace
on `max (ea j) (eb j)` with gate `ga`. It asks:

* **`hdep`**: `H_DEP` only in gate-on tokens. Each phase start plus the
  loop precedes `b`'s next edge, and `a`'s next edge when that edge is real.
* **`hbm`**: `b`'s edges are ordered.
* **`hab`**: an ordering fact with no loop latency. When a gate-off token is
  followed by a gate-on one, `b`'s fall reaches the C-element no later than
  `a`'s next real rise.
* **`hcm`, `hua`, `hub`**: the bookkeeping phase starts are ordered and the
  edge sequences are unbounded. These only shape the statement, which is
  phrased on bookkeeping edges.
* Reset as in `cel_run`, except that `a`'s first edge need not follow reset
  release: reset holds the excitation low until `b`'s first edge.

**Proof.** First, Lt3's `Tok.retime` moves `a`'s gate-off edges onto `b`'s
(`rtA`). Then a phase induction carries a "settled-low" invariant: there is
an `l` such that the excitation is 0 on `[l, phase end)` and
`l + loop ≤ eb (next)`. Gate-on phases are `cel_run`'s ordinary phases.
In gate-off phases, `exc_hold` from `l` needs only one input at 0. Finally
`Tok.retime` moves the result back to the bookkeeping phase starts.

### 3b. The merge: event form

**`MergeTimingG`** differs from `MergeTimingNoSkew` as follows:

* `H_DEP_XA` is asked only when `sv (j/2) = false` (x's tokens), and its
  x_req half only when the next edge is also x's. `H_DEP_YA` is the mirror
  image.
* Two ordering facts with no loop term are added:
  * `H_SEQ_XA`: at a y → x hand-over, the y token's z_ack fall reaches uxa
    no later than x's request does.
  * `H_SEQ_YA`: the mirror image.
* `H_RST_EARLY` needs only `ZA0 0` and `ZA1 0`.

The proved results are:

* **`MergeTimingNoSkew.g`**: the old obligations imply the new ones.
* **`merge_ok_g`**: `merge_ok`'s full conclusion follows from `MergeGates`,
  `MergeEnv`, `MergeTimingG`, `MergeCausal` and `1 ≤ Es`. Causality gives
  the needed monotonicity: `merge_ζ_step` and `merge_ρ_mono'`.
  Non-vacuity: `MergeWit.g_witness`.

### 3c. The merge: static form (node-launched, spread-free)

Once `H_DEP_XA` is needed only in x's tokens, every remaining instance is
launched by a real edge of uxa's node. The chain runs from the node to
x_ack, then the client, then the next request, and that request reaches
either x_req's next edge at uxa or, through the server, z_ack's next edge.
**`MergeStaticG`** therefore has these fields:

* `S_XA_N.1`: `Lxa.hi + wxah ≤ Lxa.lo + Wxa.lo + Eo + Wxc.lo` (the x_req
  form).
* `S_XA_N.2`: `Lxa.hi + wxah ≤ Lxa.lo + Wxa.lo + Eo + Kz + Wzx.lo`, with
  `Kz = wo + Lor.lo + Dz.lo + Es` (the z_ack form, i.e. the merge's
  RTZ / `uxa_feedback`).
* `S_XA_SEQ`: `Wzx.hi ≤ wz + la + wa + Eo + Wxc.lo`. This is the
  `z_ack → {uxa, uya}` fork at a y → x hand-over, now without a loop term.
* The y mirrors of all three, and the lower bounds `wo`, `wz`, `la`, `wa`.

The proved results are:

* **`merge_timing_g_of_static`**: `MergeTimingG` follows from `MergeCausal`,
  `MergeStaticG` and reset sequencing.
* **`merge_ok_gs`**: the whole merge contract from causal partners,
  `MergeStaticG` and reset sequencing.
* **`MergeStaticNS.g`**: the old static set implies the new one.
  `S_XA_FORK` implies `S_XA_SEQ` and `S_XA_N.1`, and `S_XA_ZA` implies
  `S_XA_N.2`. **`S_XA_R` (both halves) is no longer needed, and no field
  carries a wire-spread term on the loop side.**

### 3d. Each `MergeStaticG` field is tight

| field | run | boundary (theorem applies) | one tick past (only this field fails; conclusion false) |
|---|---|---|---|
| `S_XA_N.1` (x_req form) | `MergeN.run w`: `MergeWit` with a `w`-tick uxa feedback wire | `w = 3`: `bnd_S_XA_N` | `w = 4`: `cex_S_XA_N`. x_req's fall reaches uxa while its LUT still reads its pre-rise output, `C(0, 1, 0) = 0`, and x_ack drops at 15 inside x's token `[11, 19)` |
| `S_XA_N.2` (z_ack form) | `MergeR.run w`: all tokens x's, `Wxc = shift 6` (x_req is the late input), feedback `w` | `w = 7`: `bnd_S_XA_N2` | `w = 8`: `cex_S_XA_N2`. z_ack's fall reaches uxa at 20 before the loop settles, and x_ack drops at 22 inside `[14, 23)` |
| `S_XA_SEQ` (y → x fork) | `MergeS.run d`: `Wzx = shift d`, period 42, minimal y → x hand-over | `d = 5`: `bnd_S_XA_SEQ` | `d = 6`: `cex_S_XA_SEQ`. x_req reaches uxa while y's stale z_ack pulse is still high there, `C(1, 1, 0) = 1`, and x_ack is high at 49 inside y's slot `[42, 50)`, 7 ticks before x's real z_ack reaches uxa |

In every one of these runs, every other hypothesis of `merge_ok_gs` is
proved: `gates`, `env`, `causal`, every other `MergeStaticG` field (stated
explicitly), `hRL` and `hRE`. Each `cex_*` also proves `¬ MergeStaticG …`
and `¬ MergeTimingG …`.

**Verdict.** The merge's acknowledge obligations are now exact:
`S_XA_N` (both forms) and `S_XA_SEQ` are each tight by one tick. The
bookkeeping-edge instances of `H_DEP_XA` were a proof artefact (removed by
`merge_ok_g`), and so was `S_XA_R`. With these, Lt4's notes "merge
`S_XA_ZA` / `H_DEP_XA` probably not exact" are settled. The exact forms are
the node-launched ones, and the wire-launched `S_XA_ZA` / `S_XA_FORK` are
sufficient but carry slack equal to the z_ack wire's spread.

## Summary table (for the JSON update)

| obligation | theorem / counter-run | exactness |
|---|---|---|
| mux `S_XA_RTZ` (`bd_mux.uxa_rtz_env`) | `MuxRtz.bnd_S_XA_RTZ`, `cex_S_XA_RTZ` | **exact**, tight by 1, when the z_ack wire's rise/fall spread exceeds the j0 → uxa wire's; redundant otherwise (Lt4 `mux_rtz_of_J`) |
| mux `S_Z_S0` | `MuxB.cex_S_Z_S0` (+ `bnd`) | **exact individually** (tight by 1 with `S_Z_S1` holding) |
| mux `S_Z_Y` | `MuxB.cex_S_Z_Y` (+ `bnd`) | **exact when y is the join's late input** (tight by 1) |
| merge `H_DEP_XA/YA` at the other client's edges | `cel_run_g`, `merge_ok_g` | **not necessary** (proof artefact; removed) |
| merge `S_XA_N.1` (new; x_req form) | `merge_ok_gs`; `MergeN.bnd_S_XA_N`, `cex_S_XA_N` | **exact** (tight by 1) |
| merge `S_XA_N.2` (new; z_ack form, merge RTZ) | `merge_ok_gs`; `MergeR.bnd_S_XA_N2`, `cex_S_XA_N2` | **exact** (tight by 1) |
| merge `S_XA_SEQ` (new; y → x fork, no loop) | `merge_ok_gs`; `MergeS.bnd_S_XA_SEQ`, `cex_S_XA_SEQ` | **exact** (tight by 1) |
| merge `S_XA_FORK`, `S_XA_ZA` | `MergeStaticNS.g` | superseded: sufficient, with slack equal to the z_ack wire's spread |
| merge `S_XA_R` | `merge_ok_gs` (does not assume it) | **redundant** (proved) |
| merge `H_RST_EARLY` on `AX 0`, `AY 0` | `merge_ok_g` | **not necessary**: requests may reach uxa/uya during reset |

## What this means for `cell_constraints.json` (JSON not edited)

* `bd_mux.uxa_rtz_env` / `uya_rtz_env`: keep as is. They are exact, and
  the spread term is real. The checker may skip them when
  `Wzx.hi − Wzx.lo ≤ W0x.hi − W0x.lo` (Lt4).
* `bd_mux.bundled_z_s`: both pins' forms are needed. `bd_mux.bundled_z_x`
  and `bundled_z_y` are exact, so keep them.
* `bd_merge.uxa_feedback` / `bd_c2.env_latency` at uxa/uya: replace with
  the node-launched pair `S_XA_N` (x_req form and z_ack form). Neither has
  a spread term.
* `bd_merge.isochronic_forks` (`z_ack -> {uxa, uya}`): replace
  `S_XA_FORK` with `S_XA_SEQ`, which has no loop term.
* Drop `S_XA_R` / `S_YA_R` if the checker has them.

## What did not work / not done

* No mux analogue of `merge_ok_g` was written. The mux's uxa has the same
  bookkeeping edges (j0 in y's tokens), and `cel_run_g` applies as it is.
  But `MuxTiming` gives neither ζ's monotonicity nor unboundedness, so a
  `mux_ok_g` needs either causality or two more hypotheses. The node-launched
  analysis says the mux's `S_XA_J` could likewise become spread-free for its
  x-client branch. Its RTZ cannot: it is wire-launched and exact (§1).
  Estimated effort: half a day.
* `cel_run_g` covers only the case where the second input pulses in every
  token (`gb = true`). That covers every acknowledge C-element in
  `bd_mux` and `bd_merge`, but not a C-element with two gated inputs.
* All findings are about the MODEL: FIFO wires (`Rz` is a FIFO channel with
  a time-varying delay, so it carries no glitch and no pulse filtering),
  binary LUTs as FIFO channels (`H_LUT_FIFO`), open-loop causal partners,
  and ℕ ticks. The glitches shown (x_ack re-firing, then oscillating with
  period 2 while the stale inputs last) are transport-model behaviour.
  Silicon would show a runt pulse or metastability there, which is no
  better for the client.

## Verdict

**Works.** Items 1 to 3 are done and claimed, and 136 theorems check in
about 16 s.

* `S_XA_RTZ` is exact (tight by 1 in a run with a non-shift `Ret`).
* `S_Z_S0` alone and `S_Z_Y` (with y late) are exact.
* The merge's bookkeeping-edge `H_DEP` is removed by a theorem
  (`cel_run_g`, `merge_ok_g`).
* The merge's acknowledge obligations now have a strictly weaker static
  form (`MergeStaticG`) in which every field is exact.

**What it buys.** The operator rows of `cell_constraints.json` can now be
labelled exact or redundant throughout, except for the mux's join
env-latency (`S_J*_X`, `S_J*_C`, not probed) and its x-client acknowledge
branch (`S_XA_J`). The probable spread-free form for `S_XA_J` is above;
finishing it (`mux_ok_g` plus a static form and counter-runs) is about one
day.

## Fidelity per primitive

* **uxa / uya, uj0 / uj1** (C-element LUTs; REAL INITs `c2B`, `j0B`, `j1B`
  through `c2_spec`, `j0_spec`, `j1_spec`): binary FIFO LUT arcs
  (`H_LUT_FIFO`). The feedback is a routed wire with a window: `[1, 1]` in
  most runs, and a `w`-tick transport (window `[w, w]`) in `MergeN` and
  `MergeR`. The trace is defined by the gate recursion itself (`xaH` for a
  long feedback), so the gate fields hold by definition. Grade B.
* **uor** (`4'hE`), **bd_delay** (`H_LINE_FIFO`, FASTFALL = 0), **wires**:
  FIFO `Ret` channels. These are shifts, except `MuxRtz.Rz`, which has a
  rise/fall delay asymmetry (one admissible FIFO behaviour within
  `[lo, hi] = [1, min e 7 + 1]`). Grade B.
* **udat** (`bd_datamux`, `8'hE4`) in `MuxB`: REAL INIT through `lutB` on a
  transport pin model, turned into the window relation by
  `Bundling.transport_gate`. Grade A-: no glitch filtering, no
  metastability.
* **Partners**: open-loop periodic environments whose port-level causality
  is proved (`MuxCausal … 1 1 1 1`, `MergeCausal … 1 1`).
* **Time**: ℕ ticks.
