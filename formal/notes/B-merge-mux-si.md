# B probe Lib3: bd_merge and bd_mux at the handshake level (speed independence)

Files:
* CLAIMED `formal/lean/Formal/Cells/MergeMuxSI.lean` (core Lean; imports only
  `Formal.Cells.LibCtlMergeMux`, which imports Prelim). Checks clean in about
  38 s wall, peak 2.1 GB RSS.
* WIP `formal/lean/Wip/Cells/MergeMuxWeak.lean` (imports MergeMuxSI): only
  `TxB`, `muxB_check`, `mux_ok_weak_early`. It also checks clean (no sorry, no
  native evaluation), but its 2000-state kernel check costs about 117 s and
  6.8 GB, too heavy for a claimed file that lake builds 4-way in parallel on
  15 GB. It is in Wip/ for cost only, not because anything is unproved.

Check:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/MergeMuxSI.lean -o .lake/build/lib/lean/Formal/Cells/MergeMuxSI.olean
    /home/user/asyncfpga3/formal/check.sh Formal/Cells/MergeMuxSI.lean   # -> [audit] 350 declarations checked, [check] OK
    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Wip/Cells/MergeMuxWeak.lean   # Wip, after the olean above

`#print axioms` (checked in a scratch copy): `merge_ok`, `merge_ok_early`,
`mux_ok`, `mux_ok_weak_early` use `propext, Quot.sound`; the witness theorems
use `propext` only. No sorry/admit/axiom/native_decide. All finite checks
are `decide +kernel`.

Negative controls (scratch copies, both FAIL `mergeA_check`): (a) `uxa`
replaced by an AND of its pins (the header's "the acknowledge cannot be an
AND"); (b) `usel` replaced by `x_req` alone (the header's "the select cannot
be the request"). So the check reads the gates.

New local definitions (Prelim untouched): `STree` (search tree of states,
`mem`, `all`, `all_mem`), `Sys` (a finite interleaving model with
spec/ghost/data/hazard/liveness obligations), `Sys.check`, `Sys.sound`,
`Sys.run`, `Sys.run_reach`. This generalises LinkHandshake's `gCheck`
(bitmask over the whole state space) to state spaces of 2^21 and 2^28, where
a full mask is impossible: the reachable set is given as a tree literal and
the kernel checks that it holds reset and is closed. The trees and the run
witnesses were computed by a Python explorer outside the repo (scratchpad
`mm/merge.py`, `mux.py`, `gen.py`, `emit.py`); Lean trusts none of it.

## Model

Interleaving, one variable changes per step, unbounded delays everywhere:
* Gates (`uor`, `usel`, `uxa`, `uya`, `uj0`, `uj1`) fire atomically from their
  real INITs (Lib1's `or2B`, `c2B`, `j0B`, `j1B`), own output fed back with no
  delay (LinkHandshake's H_FB_FAST, not re-examined here). `rst = 0`; states
  start at reset (all 0).
* Every fork branch is its own variable copying its driver, unbounded delay,
  as LinkHandshake's `di_pipe`. A fork marked isochronic: its readers read the
  driver itself. `bd_delay` is one buffer (`either -> z_req`).
* Environment: four-phase clients (`req` toggles when it equals its ack as seen
  by the client), four-phase server (`z_ack` copies `z_req`), the mux's control
  sender (`ctl_req` toggles when it equals `ctl_ack`=`z_ack` as it sees it) and
  `s`, a free data bit that may toggle at any time the hypotheses allow. They
  MAY move, never must: every compliant environment is covered.
* Environment and timing hypotheses are scheduling filters (`allow s v`):
  trace-level constraints, since a run is admissible iff each of its steps
  satisfies them in the state where it is taken.

Obligations checked in every reachable state (`Sys.Props`):
* `spec`: every allowed step is a step of the cell's specification automaton.
  Ghost bits record the owner of the server transaction (`o`, set when
  `z_req` rises), per client "server has acknowledged your token" (`gx`,
  `gy`), and for the mux "control token consumed" (`gk`). Spec: `z_req` rises
  only for exactly one requesting, unserved client (merge) / only with
  `ctl_req` high, a fresh control token, and the client SELECTED BY `s`
  requesting (mux); it falls only after `z_ack` and after the owner's request
  (and `ctl_req`) fell; `z_ack` rises at most once per token; a client
  acknowledge rises only after the server acknowledged THAT client's token, and
  falls only after the server's transaction returned to zero; the control
  sender drops `ctl_req` only after `ctl_ack`. This is "every server
  transaction acknowledges exactly the client that requested it".
* `persist`: no excited gate or wire is disabled by another step (no hazard,
  including no wire carrying two transitions at once). Exempt, as data: the
  merge's select cone (`sel`, `xr@usel`, `xa@usel`) and the mux's `s` branches
  (`s@uj0`, `s@uj1`, `s@datamux`). Their correctness is the data obligation
  and the bundling hypotheses; for `s@uj_i` the exemption rests on Lib1's
  `j0_s_free_idle` (a join ignores `s` while its `ctl_req` pin is low), which
  H_BUNDLED_S_PIN guarantees whenever `s@uj_i` moves.
* `live`: some allowed step (other than a free toggle of `s`) exists.
* `good` (data): while the server samples, the data select names the owner.
  `early` window: `z_req ∧ ¬z_ack`; `broad`: `z_req ∨ z_ack` (data held until
  the acknowledge falls, the library's convention per the bd_mux header).

## Named hypotheses (all in `allow`)

* **H_MERGE_SEQ**: a merge client raises its request only when the other
  client's request and acknowledge are both low (read on the wires, the most
  adversarial reading). Test: GLS/board assertion at every x_req/y_req rise.
* **H_BUNDLED_Z** (`H_BUNDLED_Z_M`, `H_BUNDLED_Z_X`): `z_req` rises only when
  the data select has settled (merge: `usel` and both its input branches
  quiescent; mux: `s@datamux` settled). The matched `bd_delay` (rule A). Note:
  the merge form's `xa@usel` conjunct also asks a previous x transaction's
  `x_ack` fall to have reached `usel` (relative timing on the x_ack fork with
  the delay line as slack).
* **H_BUNDLED_S** in two parts. Sender (`H_CTL_HOLD`): `hs = 1` (the brief's
  form) `s` changes only while `ctl_req` is low; `hs = 2` (the header's form)
  also only while the control sender sees `ctl_ack` low, i.e. held until
  `ctl_ack` falls. Pins (`H_BUNDLED_S_PIN`): at each join, the `s` pin settles
  before the `ctl_req` pin rises and moves only while the `ctl_req` pin is low
  (setup/hold of the control bundle at both joins).
* **H_MUX_RTZ** (new, found by this probe): after `z_ack` falls, the previous
  transaction's acknowledge C-element (`uxa`/`uya`, excited to fall) fires
  before `z_ack` rises again at its pin. Slack: `z_ack` fall -> control sender ->
  `ctl_req` -> join -> `uor` -> DELAY -> server -> `z_ack` rise, against one
  LUT. Test: GLS, that loop's min delay vs max `z_ack -> x_ack` fall.
* **H_ISO_FORK**, per fork, by choosing which fork groups are isochronic.

## Theorems

### bd_merge (V = 17 wires + 4 ghost bits)
* `merge_ok` (85 reachable states): under H_MERGE_SEQ and H_BUNDLED_Z, with
  isochronic forks ONLY on `z_ack -> {uxa, uya}` and
  `x_ack -> {usel, client x}` (the `x_req` and `y_req` forks delayed
  independently): spec, persistence, liveness, broad data window.
* `merge_ok_early` (230 states): only the `z_ack` fork isochronic: the same
  with the early window.
* `merge_broad_needs_iso_xa`: with the x_ack fork delayed, a reachable state
  where `sel` has fallen while `z_ack` is high (`x_ack@client` overtook
  `x_ack@usel`, x dropped its request, `sel = x_req + x_ack@usel` fell): the
  header's "select cannot be the request", re-entering through the fork.
* `merge_needs_seq`: without H_MERGE_SEQ, every fork isochronic: y's
  transaction in flight, x requests, server acknowledges, and `x_ack` may fire
  although the server acknowledged y's token (spec fails). Run: `y_req,
  either, z_req, x_req, z_ack`, then `x_ack`.
* `merge_needs_iso_za`: everything else isochronic, all hypotheses: in a y
  transaction `za@uxa` sees the rise of `z_ack` but not yet its fall; y
  completes, x starts legally, `x_ack = C(x_req, za@uxa)` fires on the stale
  value: a spurious acknowledge.

### bd_mux (V = 23 wires + 5 ghost bits)
* `mux_ok` (560 states): under H_BUNDLED_S (header form, sender + pins),
  H_MUX_RTZ and H_BUNDLED_Z, with the `s`, `j0`, `j1` forks delayed
  independently and isochronic forks ONLY on `ctl_req -> {uj0, uj1}` and
  `z_ack -> {uxa, uya, ctl sender}`: spec (only the selected input is
  acknowledged; one server transaction per control token), persistence,
  liveness, broad data window.
* `mux_ok_weak_early` (2000 states; **Wip**, `Wip/Cells/MergeMuxWeak.lean`, proved but
  too heavy to claim): the brief's weaker sender form (`s` held
  only until `ctl_req` falls): all the same with the early window.
* `mux_weak_broad_fails` (claimed): with that form, `s` moves after `ctl_req` fell while
  `z_ack` is high, so z_data changes before the acknowledge falls. The broad
  protocol needs the header's "until ctl_ack falls".
* `mux_needs_rtz`: **bd_mux is not speed independent even with every fork
  isochronic.** Run: x and y both request, control token selects x, x's
  transaction completes up to `z_ack` falling; `x_ack` is now excited to fall;
  a new control token with `s = 1` lets `j1` fire on y's waiting request and
  the server raises `z_ack`, which withdraws `x_ack`'s fall (hazard on
  `x_ack`; if x has seen a runt it may raise a new request and then read the
  re-risen `x_ack` as its acknowledge). Needs H_MUX_RTZ.
* `mux_needs_iso_za`: `za@uya` lags a whole y transaction; later `y_ack` fires on
  the stale value (spurious acknowledge).
* `mux_needs_iso_cr`: the control sender sees `ctl_ack` and drops `ctl_req`
  before its rise reached the DESELECTED join (`cr@uj1`): the branch carries
  two transitions at once. Harmless if the pulse dies, but a transport-delayed
  pulse reaching `uj1` after `s` flipped to 1 for the next token would fire it.
* `mux_needs_bundled_s`, `mux_needs_bundled_s_hazard`: with no H_BUNDLED_S
  (every fork isochronic), `s` flips while `ctl_req` is high: `j0`'s
  excitation is withdrawn (hazard), and `z_req` rises for a token whose `s`
  now names y while `j0` fired on x (wrong input transferred).

### (3) Which forks must be isochronic (answer)
Established in Lean by a positive theorem with the fork delayed or a witness
with only that fork delayed:
* bd_merge: **`z_ack -> {uxa, uya}`** must be isochronic (spurious
  acknowledge otherwise). **`x_ack -> {usel, client x}`** only for the broad
  data window: `x_ack` must reach `usel` before x's falling request does
  (`xa@usel` before `xa@client -> client -> x_req -> usel`). `x_req` and
  `y_req` forks: not needed (under H_BUNDLED_Z, which already asks
  `x_req@usel` to be ahead of `z_req`, i.e. rule A).
* bd_mux: **`z_ack -> {uxa, uya, ctl_ack}`** (spurious acknowledge otherwise)
  and **`ctl_req -> {uj0, uj1}`** (a branch must not lag its source by a whole
  half handshake). `s`, `j0`, `j1` forks: not needed (`s` is covered by
  H_BUNDLED_S_PIN, which is a bundling, not an isochrony, condition).
* In all four cases the race is long: the stale branch must lag by a whole
  transaction or half handshake (through the server and a client, including
  the DELAY line for z_ack/ctl_req). So "isochronic" here is the weak form:
  branch skew < one environment round trip, which a GLS can measure.

Python-only (not claimed): with a narrower H_BUNDLED_Z (only `usel` itself
settled), the merge additionally needs the `x_req` fork isochronic; the
exhaustive sweep of all 16 merge and 32 mux fork subsets (both H_BUNDLED_S
strengths) agrees with the Lean results above.

## What did not work / not done
* First merge run flagged a hazard on `sel` (x_ack falling, x_req rising
  again): a static hazard on a data-path LUT2, legitimate in bundled data;
  hence the data-cone exemption plus H_BUNDLED_Z. Stated explicitly above.
* Not modelled: H_FB_FAST for `uxa`/`uya`/`uj0`/`uj1` (atomic gates);
  `FASTFALL` of bd_delay (one buffer, fall included); `rst` sequencing; the
  data bits themselves (only the select; client data validity is the client's
  obligation); X values (binary model, Lib1 covers the Kleene side); metastable
  behaviour. Liveness is deadlock freedom only, no fairness/starvation bound.
* Size: `muxB_check` (2000 states) costs ~2 min and ~7 GB, so it and
  `mux_ok_weak_early` live in Wip/. A cheaper encoding (fewer branch bits for
  the weak-H_BUNDLED_S question, or a bitmask over a projected state) could
  bring it back.

## Verdict
Works. bd_merge is speed independent and correct under H_MERGE_SEQ +
H_BUNDLED_Z with two (weakly) isochronic forks; bd_mux the same under
H_BUNDLED_S + H_BUNDLED_Z with two isochronic forks **plus one relative-timing
assumption the header does not state, H_MUX_RTZ** (bd_mux is not SI without
it). Every hypothesis is shown needed by a kernel-checked run. What it buys:
the exact list of cell constraints for `cell_constraints.json` / GLS
assertions: merge sequencing; z_ack fork skew (both cells); x_ack fork skew
(merge, broad window); ctl_req fork skew; s setup/hold at both join pins and
s held until ctl_ack falls; and the x_ack/y_ack return-to-zero race in bd_mux.
Effort to extend: N-input `bdc_muxn` variants and FASTFALL ~0.5 day each with
this checker; coupling to a timed model (bounded delays instead of filters)
~2 days.

## Fidelity
* LUT6 / LUT2 / bd_c2: binary function of the real INIT (Lib1 defs), atomic
  firing; Kleene/glitch behaviour is Lib1's (H_KLEENE_LUT). Grade B: no
  intra-LUT delay, no runts, feedback pin instantaneous (H_FB_FAST).
* Wires: one variable per fork branch, unbounded delay, at most one transition
  in flight (two in flight is reported as a hazard rather than modelled).
* bd_delay: one buffer, unbounded delay; its matching is H_BUNDLED_Z.
* bd_datamux: modelled only through its select pin.
