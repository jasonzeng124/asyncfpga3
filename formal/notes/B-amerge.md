# B probe Cm: the generated control_merge (`bdc_amerge2_0`, `bdc_amerge3_0`) and 3-way loop header (`bdc_muxn3_32`)

Shard B, Phase 2/3, gap 1 of `B-gcd-cells.md` (8 + 1 instances in gcd_hw).
2026-10-27. No route, no board, no GLS: nothing below is a routed number.
yosys 0.62 from `~/dev2/lib/fpgatoolchain/openxc7` WAS used, read-only, to
synthesise the three generated modules alone (see H_YOSYS_MAP); no nextpnr
was run, so no nextpnr fingerprint applies.

## Files (all CLAIMED, core Lean, import only `Formal.Cells.Prelim` and each other)

| file | content | check time / peak RSS |
|---|---|---|
| `formal/lean/Formal/Cells/AMergeSys.lean` | generic SI checker (`Sys`, `KTree`, `check`, `sound`, `run_reach`), adapted from `MergeMuxSI` | 2 s |
| `formal/lean/Formal/Cells/AMergeGates.lean` | every LUT of the three modules (library INITs + yosys-inferred INITs), INIT = equation lemmas, Kleene facts, `Gates`/`gI`/`gE`/`gI_eq_gE` | 1 s |
| `formal/lean/Formal/Cells/AMerge2.lean` + `AMerge2Proof.lean` | `bdc_amerge2_0` model, spec, hypotheses; certificate (183 states) and theorems | 4 s, 0.6 GB |
| `formal/lean/Formal/Cells/AMerge3.lean` + `AMerge3Proof.lean` | `bdc_amerge3_0` (cascade) model; certificate (5630 states, 16 chunks) and theorems | **115 s alone (160 s with other slots busy), 1.1 GB** |
| `formal/lean/Formal/Cells/MuxN3.lean` + `MuxN3Proof.lean` | `bdc_muxn3_32` model; certificate (1728 states, 8 chunks) and theorems | 24 s alone (41 s busy), 0.75 GB |

Check (in dependency order; the first five write oleans the proof files import):

    cd /home/user/asyncfpga3/formal/lean
    for f in AMergeSys AMergeGates AMerge2 AMerge3 MuxN3; do PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/$f.lean -o .lake/build/lib/lean/Formal/Cells/$f.olean; done
    for f in AMerge2Proof MuxN3Proof AMerge3Proof; do PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/$f.lean; done

All check clean (no output). No sorry/admit/axiom/native_decide; all finite
checks are `decide +kernel`. `#print axioms` (scratch copies): `amerge2_ok`,
`amerge3_ok`, `muxn3_ok`, `gI_eq_gE`: `propext, Quot.sound`; every witness
and Kleene theorem: `propext` only. The certificates were computed by an
explorer run with `#eval` in a scratch file outside the repo
(scratchpad `cm/lean/Scratch/Explore.lean`); Lean trusts none of it.

The `AMerge3Proof` cost (115 s) is above `MergeMuxSI`'s 38 s. Memory is
fine (1 GB, because the certificate is chunked: a single `decide` over the
7856-state first version was killed). If 115 s is too much for `check.sh`,
set `hOK.isoG := true` (index g-forks isochronic; 1906 states, about 40 s)
and regenerate; the weaker claim is then the claimed one.

## How bdc emits them (`bdc/emit.py`)

- `emit_amerge(width, n)` (control_merge and merge with >1 predecessor):
  a CASCADE of `bd_arbiter`s (stage k arbitrates the accumulated winner
  against input k: `uarb2.r1 = uarb1.R0`, `uarb2.A1 = uarb1.A0`),
  `won[k] = g2[k] | in_k_ack`, `index` = priority chain over `won`,
  `z_data` = mux on `index`, `uor` LUT1 + `bd_delay_gated #(DELAY)` on `r0`.
  gcd_hw's 8 control_merges have `W = 0` (`.z_data()` unconnected,
  `in*_data = 1'b0`): the index is their only datum, forked with the result
  by `bd_fork #(.N(2)) ucontrol_mergeN_f`.
- `emit_muxn(width, n)`: `sel[k] = ctl_req & (s == k)` (behavioural),
  `bd_c2 uj_k(in_k_req, sel[k])`, `|j -> uor -> bd_delay_gated`,
  `bd_c2 ua_k(j[k], z_ack)`, `ctl_ack = z_ack`, data mux on `s`. In gcd_hw
  `umux21`'s `s` is `n_index_97` = `ucontrol_merge12`'s (the amerge3's)
  index through a link (`ULINK_N_INDEX_97`, DELAY 8).
- Re-emitted with `python3 bdc/emit.py cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir --no-top --probe n138 -o <scratch>` (bdc knobs unset; `BDC_FASTFALL` default 1, so `request_delay` is `bd_delay_gated`).

## H_YOSYS_MAP: the inferred LUTs (from synthesis, not assumed)

Each module synthesised alone with `build_hw.sh`'s exact yosys script; both
are `(* keep_hierarchy *)`, so `-flatten` cannot merge their LUTs with the
rest of the design. LUT cells found (pins `[I0..]`):

| module | output | INIT | pins |
|---|---|---|---|
| amerge2 | `index` | LUT2 `E` | g2, in1_ack |
| amerge3 | `index[1]` | LUT2 `E` | g2(arb2), in2_ack |
| amerge3 | `index[0]` | LUT4 `000E` | in1_ack, g2(arb1), g2(arb2), in2_ack |
| muxn3 | `sel[0]` | LUT3 `10` | s0, s1, ctl_req |
| muxn3 | `sel[1]` | LUT3 `40` | s1, s0, ctl_req |
| muxn3 | `sel[2]` | LUT3 `40` | s0, s1, ctl_req |
| muxn3 | `\|j` (`udly.gate`, also `uor`'s input) | LUT3 `FE` | j2, j1, j0 |
| muxn3 | `z_data[b]` x32 | LUT5 `F0AA_CCF0` | in2[b], in1[b], in0[b], s0, s1 |

All library cells come out with their RTL INITs (`ustate`, `ugrant`, `ua*`,
`uj*`, `uor`). Proved: each inferred INIT equals the emitted Verilog
expression (`idx2_eq`, `idx3l_eq` = `won1 & ~won2`, `sel*_eq`, `or3_eq`,
`dm5_eq`). **H_YOSYS_MAP**: abc picks the same LUTs in the full gcd_hw run.
Test: dump the LUT cells under `uut.ucontrol_merge*`/`uut.umux21` from the
gcd_hw synthesis JSON (the probe's `dump.py`, scratchpad `cm/dump.py`).
Finding: the muxn decode is a SEPARATE LUT3 per input, unlike `bd_mux`
where it is folded into the join LUT: one more gate and one more wire
between `ctl_req`/`s` and each join.

## Model

`AMergeSys.Sys` = `MergeMuxSI`'s interleaving checker (one variable changes
per step; gates fire atomically to their LUT value; wires are variables
copying their driver; the environment may move whenever its four-phase
protocol allows; named hypotheses are scheduling filters), with:
- certificate = search tree of (state, excitation mask); the kernel checks
  each mask once (O(N V) gate evaluations); the gate vector is computed as
  one `nxv : Nat -> Nat`;
- liveness strengthened to "no stranded token": whenever a client waits
  and every other client is at rest, some gate/wire/server step is allowed;
- models parametrised by a gate set; theorems are stated on `gI` (the real
  INITs through Prelim's `lutB`/`o5B`/`o6B`), certificates checked on `gE`
  (Boolean equations), linked by `gI_eq_gE` (proved from the INITs).
- `q` of each arbiter stored inverted so that state 0 is the reset state
  (`bd_arbiter` resets `q` to 1).

Spec (ghost automaton; as `MergeMuxSI`'s merge with the owner chosen by the
arbiter state): `z_req` rises only for the client the arbiter state(s) name
(`q` with that client's request up; through the cascade for amerge3), which
requests and is unacknowledged and unserved; falls only after `z_ack` and the
owner's request fell; `z_ack` once per token; a client's ack rises only after
the server acknowledged THAT client's token and falls only after the server
transaction returned to zero. Data (`good`): grants of each arbiter never both
high, and in the broad window (`z_req | z_ack`) the index names the owner.

## Theorems (all on `gI`, the real INITs)

### `bdc_amerge2_0` (`AMerge2Proof`)
- `amerge2_ok` (183 states): `Props` in every reachable state (spec,
  persistence, no stranded token, grant exclusion, index = owner in the
  broad window), with unbounded delays on every gate output and on the
  `g2 -> index` fork, under H_RT1, H_RT2, H_BUNDLED_IDX, H_IDX_ACK_FORK,
  arbiter-internal isochrony, H_ARB_RESOLVED, H_FB_FAST.
  **This is (1): each output transaction carries exactly one input token and
  outputs the index of the input that won.**
- `amerge2_serves_1`: non-vacuity (client 1 wins, served, index 1).
- `amerge2_needs_rt1` (grants overlap), `amerge2_needs_rt2` (runt on
  `in0_ack`), `amerge2_needs_bundled_idx` (consumer samples index 0 for a
  client-1 token), `amerge2_needs_idx_ack_fork` (index falls inside the hold
  window: `in1_ack` reaches the client before the index LUT, client drops
  `r2`, `g2` falls, `index = g2 | in1_ack@idx = 0` while `z_ack` is high),
  `amerge2_q_race` (why `q` is exempt: from reset client 1 makes `q`
  excited, client 0's request withdraws it: the arbitration race).

### `bdc_amerge3_0` (`AMerge3Proof`)
- `amerge3_ok` (5630 states): same properties for the two-arbiter cascade,
  index `00/01/10` = owner (never `11`), grant exclusion in each arbiter, no
  token lost or duplicated through the cascade, no stranded token; unbounded
  delays on all gate outputs of both arbiters and the wrapper and on the three
  `g2 -> index` fork branches; under H_RT1 (both arbiters), H_RT2 (arbiter 2),
  **H_RT2_CASCADE** (arbiter 1, whose server is arbiter 2's `ua1`),
  H_BUNDLED_IDX, H_IDX_ACK_FORK, H_DELAY_BUF, isochrony of the cascade wires,
  H_ARB_RESOLVED. **This is (2).**
- `amerge3_serves`: each client wins and is served with its own index
  (client 0 and 1 THROUGH both arbiters).
- `amerge3_needs_rt1`, `amerge3_needs_rt2`, `amerge3_needs_rt2_cascade`
  (arbiter 2 acknowledges arbiter 1 again while arbiter 1's previous
  `in0_ack` is still excited to fall: runt), `amerge3_needs_bundled_idx`.

### `bdc_muxn3_32` (`MuxN3Proof`)
- `muxn3_ok` (1728 states): the N = 3 generalisation of `MergeMuxSI.mux_ok`:
  one output transaction per control token, carrying the token of the input
  `s` selects; only that input acknowledged; the other two keep their tokens;
  no hazard on ANY gate including the three inferred decode LUT3s; no stranded
  token; joins one-hot (so `|j` sees one moving input, the header's claim);
  `s` = owner in the broad window. Unbounded delays on all gates and on the
  `j -> ua` forks; under H_CTL_HOLD, H_MUX_RTZ, H_S_RANGE, H_S_PIN,
  H_DELAY_BUF, isochronic `ctl_req -> sel*` and `z_ack -> {ua*, ctl}`.
  **This is (3).**
- `muxn3_serves`: each input served; input 2 served while 0 and 1 wait
  unacknowledged.
- `muxn3_needs_hold` (s moves under a high `ctl_req`: `sel[0]` runt),
  `muxn3_needs_rtz` (as `bd_mux`: runt on `in0_ack`).

### Gate level (`AMergeGates`)
INIT = equation for every LUT (library and inferred); `gI_eq_gE`;
Kleene (H_KLEENE_LUT): `idx2_hold` (index holds 1 while either pin is 1),
`idx2_both_moving` (x when both move: that window IS H_BUNDLED_IDX),
`idx3l_hold`, `sel_idle` (decodes ignore `s` while `ctl_req` is low: the index
may move between tokens with no glitch), `sel_needs_setup` (a moving `s` pin
under a high `ctl_req` gives x: H_S_PIN is a real setup/hold), `or3_hold`.

## Named hypotheses (each a filter field of `Hyp`, a constant in the model, or a stated exemption)

| name | where | physical fact | test |
|---|---|---|---|
| H_RT1 | all three arbiters | a grant rises only while its sibling is low; = conclusion of `ArbHeldTimed.rt1_exclusion` from arc inequality RT1 and H_SERVER_MIN | GLS/board `!(g1&g2)` per arbiter instance (9) |
| H_RT2 | uarb (amerge2), uarb2 (amerge3) | server raises `A0` only after the previous `ua1/ua2` fell; = `ArbHeldTimed.A1_low_after` / RT2a (`rt2_exclusion_arcs` `pulse`, `g1`) | GLS min loop vs max `A0 -> A_i` fall |
| **H_RT2_CASCADE** (new) | amerge3 uarb1 | `acc1_ack` (uarb2.ua1) rises only after uarb1's previous `in0_ack`/`in1_ack` fell | GLS: `acc1_ack`-fall -> uarb1.ustate -> `acc1_req` -> uarb2 -> `r0` -> uor -> DELAY -> consumer -> `z_ack` -> uarb2.ua1 (min) vs `acc1_ack`-fall -> uarb1.ua_i fall + its feedback (max) |
| **H_BUNDLED_IDX** (new; the wrappers' own obligation) | amerge2/3 | `z_req` rises only after the index LUT(s), their input branches and `g2`, `A2` (both arbiters for amerge3) are quiescent | GLS assertion "index stable at z_req rise", per instance; rule A on the index cone |
| **H_IDX_ACK_FORK** (new) | amerge2/3 | `in_k_ack -> index LUT` faster than `in_k_ack -> client -> in_k_req -> ugrant -> g2 -> index` | GLS / routed SDF: route delay vs client round trip |
| H_ARB_RESOLVED | every arbiter | `q` Boolean (no metastability); `q`'s excitation may be withdrawn (nondeterministic winner), exempt from persistence; `amerge2_q_race` shows the race exists | not testable digitally; ArbBinary H_REQ_SEP / MTBF |
| H_A0_FORK, arbiter-internal isochrony | every arbiter | forks inside `bd_arbiter` (r1/r2/q/A0/g) read without skew | ArbA0Fork, ArbHeldTimed (cited, not re-proved) |
| cascade isochrony | amerge3 | `acc1_req -> uarb2.{ustate, ugrant}`, `acc1_ack -> uarb1.{ustate, ua1, ua2}` without skew | GLS per pin (as H_A0_FORK) |
| H_CTL_HOLD | muxn3 | `s` changes only while `ctl_req` and `ctl_ack` are low (the link `n_index_97`'s output contract) | GLS assertion on the control channel |
| H_S_PIN | muxn3 | at each decode LUT3 and data LUT5, `s` pins settle before `ctl_req` pin rises / before `z_req`, and stay until `ctl_req` pin fell / `z_ack` fell (setup/hold per pin; `sel_needs_setup`) | per-pin setup/hold on routed SDF |
| H_S_RANGE | muxn3 | `s != 3`; discharged in gcd_hw by `amerge3_ok`'s `good` (index in {0,1,2} in the window) plus the link latching it in the window (composition: C) | follows from the above |
| H_MUX_RTZ | muxn3 | `z_ack` rises only when no `ua_k` is excited to fall (`MergeMuxSI`'s finding, recurs) | GLS loop vs `z_ack -> ua_k` fall |
| iso `ctl_req -> sel*`, `z_ack -> {ua*, ctl}` | muxn3 | weak isochrony (skew < a half handshake), as `bd_mux` (`mux_needs_iso_cr`, `mux_needs_iso_za`) | GLS fork skew |
| H_DELAY_BUF | all | `uor` + `bd_delay_gated` = one unbounded buffer (amerge2: two buffers); the gated line's own flush obligation is `GcdCells`/`ConstraintsFastFall` | rule F |
| H_FB_FAST | every C-element/ustate | own feedback pin instantaneous (atomic gate) | as CElemTiming |
| H_YOSYS_MAP | inferred LUTs | the table above | dump gcd_hw synth JSON |
| H_KLEENE_LUT | Kleene lemmas only | Prelim | Prelim |

## Timing obligations for `cell_constraints.json` (not written: another agent owns it)

Proposed ids, all "sufficient, SI-filter form; arc form not derived here":
- `bdc_amerge.bundled_idx` (8 instances): owner change to the g2 side: `q`
  -> ugrant.I2 -> O6 `g2` -> index LUT -> consumer latch D, plus setup, <=
  `q` -> ustate.I2 -> O5 `R0` -> uor -> DELAY chain -> `z_req` -> consumer; owner
  change away from the g2 side: `A0`-fall -> ua2 -> `A2`-fall -> index LUT,
  same right-hand side starting at `A0`-fall -> ustate.I4. amerge3: also the
  arbiter-1 grant path `g2(arb1)` -> index[0] vs `acc1_req` -> uarb2 -> `r0` ->
  ... Rule A analogue; rule A today audits `<cell>.uor` (so these cells ARE
  found) but against the whole input cone, not the index LUT's grant/ack
  pins. Counter-trace: `amerge2_needs_bundled_idx`.
- `bdc_amerge.idx_ack_fork` (8): `in_k_ack` route to the index LUT <= the
  client round trip back to `g2` at the index LUT. Counter-trace:
  `amerge2_needs_idx_ack_fork`.
- `bdc_amerge3.rt2_cascade` (1): above. Counter-trace:
  `amerge3_needs_rt2_cascade`.
- `bd_arbiter.*` (RT1, RT2, A0 fork): per instance, the existing ids; the
  9 instances are 7 amerge2 `uarb1`, amerge3 `uarb1`, `uarb2`; for amerge3's
  `uarb1` the "server" in RT1/RT2's `smin` is `uarb2` + everything behind it.
- `bdc_muxn.rtz` (1): `z_ack`-fall -> ctl sender -> `ctl_req` -> decode LUT3
  -> `uj_k` -> `|j` -> uor -> DELAY -> server -> `z_ack`-rise at `ua_j` (min) >=
  `z_ack`-fall -> `ua_k` fall + feedback (max). Note the extra decode LUT3
  ADDS slack here relative to `bd_mux`.
- `bdc_muxn.s_setup` / `.s_hold` (1, per decode LUT and per data LUT5 bit):
  H_S_PIN. `bdc_muxn.iso_ctl`, `.iso_zack`: weak isochrony.

## What did not work / not done

- First amerge3 certificate (7856 states, one `decide`) was killed (memory).
  Fixed by: one-pass gate vector (`nxv`), excitation masks stored in the tree,
  mask-based hazard check, `uor` lumped into the delay buffer (H_DELAY_BUF),
  and chunking (16 `decide`s). Kernel speed is about 20 ms per state for 23
  variables; switching `find`/`all` to recursor form or `Nat.blt` did not
  help measurably (reverted).
- Not modelled: metastable `q` (H_ARB_RESOLVED), any timed behaviour (the
  "timed if time allows" part: NOT done; obligations above are SI filters,
  their arc forms are stated in words only), fork skew inside the arbiters
  (cited), `s` pin skew (H_S_PIN), the 32 data bits of muxn3 and the
  amerge2 data LUT (W = 0 in gcd), `rst` sequencing, X values (only the
  Kleene lemmas), fairness (none promised).
- `z_ack` is the bd_fork/consumer abstracted as a four-phase server; the
  composition with the fork and links is C's.
- No new shared definitions in Prelim; `AMergeSys` duplicates (and adapts)
  `MergeMuxSI`'s checker on purpose so that a concurrent port of other cell
  files cannot break this probe. Port to Core: only Prelim's `lutB`/`o5B`/
  `o6B`/`lutK` are used (in `AMergeGates`).

## Verdict

**Works.** All three generated modules are proved correct at gate level
(real INITs, inferred LUTs taken from an actual yosys run) in the
speed-independent model, under a finite list of named hypotheses, each shown
necessary by a kernel-checked counter-run. New findings: (a) the wrappers'
own obligations are H_BUNDLED_IDX and H_IDX_ACK_FORK (the latter is not
stated anywhere in bdc: the `in_k_ack` fork into the index LUT must be weakly
isochronic, or the index changes inside the consumer's hold window);
(b) the cascade adds H_RT2_CASCADE, an RT2 for arbiter 1 whose server is
arbiter 2's `ua1`, not covered by any arbiter theorem; (c) `bdc_muxn3`'s
decode is a separate LUT3 per input (not folded as in `bd_mux`), and the mux
is not SI without H_MUX_RTZ, exactly as `bd_mux`. Effort to finish: timed
(arc) forms of H_BUNDLED_IDX, H_IDX_ACK_FORK and H_RT2_CASCADE in the
`ArbHeldTimed` style, about 1-2 days; a GLS assertion set for all of them,
about half a day. What it buys: the control_merge and the 3-way header can
now enter C's composition as operators with proved handshake specs (closing
C-8f items 2 and 4 at the cell level), and three new per-instance constraints
for the checker.

## Fidelity per primitive

- LUT (all, library and inferred): binary function of the real INIT (`lutB`,
  `o5B`/`o6B`), atomic firing, unbounded delay; no intra-LUT skew, no runts
  (grade B). Kleene facts separately under H_KLEENE_LUT.
- LUT6_2 (`ustate`, `ugrant`): O5 and O6 are separate variables with
  independent delays reading the same pins (fractured-site shared pins:
  isochronic).
- C-element / `ustate` feedback: own output read with no delay (H_FB_FAST).
- Wires: a variable per fork branch where modelled (index g-forks, muxn
  `j -> ua` forks), unbounded delay, one transition in flight; all other
  forks isochronic (named).
- `bd_delay_gated` + `uor`: one buffer (amerge2: two), unbounded delay; its
  matching is H_BUNDLED_IDX / rule A, its flush is `GcdCells`.
- Arbiter decision node: Boolean, nondeterministic winner, no metastability
  (H_ARB_RESOLVED).
- Environment: four-phase clients, control sender and server that may move
  whenever their protocol allows (every compliant environment).
