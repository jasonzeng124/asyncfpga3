# A-gls-resolve: the trace semantics of research's FID_RESOLVE on the bd_c2 loop

Probe GLSResolve, shard A, session 2026-10-29. STATUS: DONE (the file checks; nothing unproved).

File: `formal/lean/Formal/Core/Delay/GLSResolve.lean` (core Lean, no Mathlib). Imports
`Formal.Core.Delay.GLSFid` (A; no olean in .lake/build yet, so check.sh is given it first) and
`Formal.Cells.CElemTiming` (B, read-only, core Lean, has an olean). No Wip Lean; the iverilog
cross-check is kept in `formal/lean/Wip/GLSResolve/sim/` (`run.sh`, testbenches, checker).

Research side read-only at `origin/claude/research` tip `6524fa3`: `cells/gls/fid_core.vh`
(md5 2422ccea…, unchanged since 5567170), `cells/gls/prims.v` (md5 3e7423cb…), `cells/gls/gen.py`.
Written `R:<file>:<line>`.

## What checks

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Core/Delay/GLSFid.lean Formal/Core/Delay/GLSResolve.lean
    -> [audit] 665 declarations checked   (includes the imported GLSFid, SAF, Discrete, B's Prelim/CElemTiming)
    -> [check] OK
    (autoImplicit=false; a plain `lake env lean` of the file prints no error and no warning;
    no sorry/axiom/native_decide; file md5 54d0bef8…, 854 lines.)

## 0. The model (what `FID_RESOLVE` is, as a trace)

`R:fid_core.vh:47-119`, with `en = 1`, `TLOOP = L ≥ 1`, `+META_OFF`/`+META_X` unset, binary.
A per-step state machine on end-of-step values (1 step = 1 ps):

| Verilog | Lean |
|---|---|
| regs `o_r busy v_before t_last ign_until` (`:52-58`) + the one pending `o_r <= #(trp) choose; busy <= #(trp) 0` (`:108-109`) | `St` (`o busy vb tl ign pt pv`) |
| `always @(f or kick)` body (`:71-118`) | `eval` |
| blocked: `busy \|\| $time < ign_until` (`:74`) | `blocked` |
| runt test `f!==o_r && t_last>0 && f===v_before && $time-t_last < TLOOP` (`:77-78`) | `isRunt` |
| decision `delta = p-(TLOOP-win/2)+noise`, reject / commit / back (`:82-92`) | `GLSFid.resolve` (unchanged from GLSPass2) |
| reject: `o_r=f; t_last=0; ign_until=$time+TLOOP+1; kick` (`:87-90`) | `.reject` branch |
| meta: `o_r=f; busy=1; t_last=0; ign_until=$time+trp+TLOOP+1; o_r<=#trp choose` (`:104-110`) | `.commit` (`choose = runt_val = o_r`) / `.back` (`choose = f`) |
| normal edge `v_before=o_r; o_r=f; t_last=$time` (`:113-115`) | last branch |
| NBA region | `nba`; `step = nba ∘ eval` |
| noise `$dist_normal` (`:81`) | free `nz : Nat → Int` (draw at the decision time) |
| `trp = min(40τ, rtoi(τ ln(win/2|δ|)))` or `0` if `2|δ| ≥ win` (`:93-98`) | free `R : Int → Nat`; `ResLaw` = the `0` clause |
| single-cell loop, `TLOOP = feedback wire + pin arc` (`R:gen.py:661-682`) | `Run`: `f t = fC2(a t, b t, o(t-L), rst t)` |

Modelling arguments (not theorems; checked with iverilog, §3):
* Evaluating the body at EVERY step equals evaluating it on `f` events and kicks: after any
  non-blocked evaluation `o_r = f` or the node is busy, so a step with no event is a no-op;
  the kick fires at exactly `ign_until`, where `$time < ign_until` is false, and the per-step
  evaluation at that step does the same re-read (`:74,90,107,110`).
* Order within a step: the sampler's `o = f` is an active-region event, the `<= #trp` updates
  are NBAs, so the body runs before the pending update lands (`step = nba ∘ eval`); with
  `trp = 0` the update lands in the same step (a 0-width glitch, which end-of-step values and
  every downstream `FID_SAMPLE` erase).
* Feedback delay: `o` → ICBUF `W` → pin copy `T3 - 1` → mux → sampler `1` = `W + T3 = TLOOP`
  exactly when `FID_LEVEL_PS = 0` (`GLSFid.fidO6_default`). The other pins are the traces the
  mux sees (already delayed by their arcs).
* The bd_c2 INIT is `bd_ce.v:34` verbatim (= `Gen/Cells.lean:29` = B's `INIT_c2`); `fC2_eq`
  (decide) and `fC2_eq_exc` (= B's `CElemTiming.exc`, through B's `c2_eq`).

Runs exist and are unique (`run_exists`, `run_unique`, by a causal recursion `cr`).

## 1. What fanout sees, for every runt width and every noise draw (theorems)

Scenario: bd_c2 empty (`q = 0`), `a = 1`, `rst = 0`, `b` = pulse `[t0, t0+w)` at the mux
(`t0 ≥ 1`, `w ≥ 1`). Every statement holds for EVERY noise sequence `nz`, EVERY law `R`, every
`win`, every `L ≥ 1`.
* `run_wide`, `out_wide`: `w ≥ L` → `o` = clean set at `t0` (never a runt; the boundary
  `w = L` included).
* `run_runt`, `out_runt` (`w < L`): the exact state at every step (`Srunt`) and output:
  `o t = [t0 ≤ t ∧ (t < t0+w ∨ (commit ∧ t0+w+trp ≤ t))]`, decision at `t0+w` by
  `resolve w L win (nz (t0+w))`.
* `rejected_runt_emitted`: for reject AND back, `o` is the full-swing pulse `[t0, t0+w)`
  then 0 forever. **The "rejected" runt is on the output wire, so on every fanout pin and on
  the feedback.** `R:fid_core.vh:29` ("the node never left") is true only of the final value.
* `commit_gap`: a commit with `trp > 0` is seen as `1` on `[t0, t0+w)`, `0` on
  `[t0+w, t0+w+trp)`, then `1`: two rising edges for one set event (the "hold the runt-end
  value" of `:34` is a 0, i.e. a second runt, of width `trp`).
* `step_emits` (any resolver, any input): every non-blocked reversal of `f` is on the output
  in the same step, unless it is a runt that commits with `trp = 0`.
* `run_runt_gen`: the run is `Srunt` for ANY `b` that is the pulse up to `t0+w`, arbitrary in
  the ignore window `(t0+w, Iend)` (`Iend = t0+w+trp+L+1`, `trp = 0` for reject), and 0 after.
  Input activity inside the window leaves no trace.

## 2. What a passing fid run with the resolver on implies, and what it hides (theorems)

Positive:
* `noRunt_free`, `noRunt_loop`: a run that printed no RUNT/META line (`n_rej = n_meta = 0`)
  is the identity resolver, and `(o, o(·-TLOOP))` satisfies B's gate relations
  `CElemTiming.Loop INIT_c2 … 0 0 TLOOP TLOOP`; so every B theorem about `Loop` applies to the
  run, at that one delay point (GLSPass2's band caveat applies: one point is not the band).
* `spaced_identity`: if the transport loop (`+META_OFF=1`) has no two output edges closer than
  `TLOOP`, the resolver run equals it, state by state.
* `fourphase_identity`: B's four-phase hypotheses (`c2_four_phase`, copied verbatim at
  `dl = 0`, `dw = TLOOP`, with `H_ENV_LATENCY : TLOOP ≤ E`) plus "quiet before the first
  phase" imply the spacing, so the resolver never fires: under B's discipline the resolver is
  invisible.

Seed dependence:
* `seed_dependence`: for every `w < L`, every `win ≥ 2`, every `L`, every law, there are
  draws with final value 0 and draws with final value 1 (same circuit, delays, inputs). A
  passing run at one `META_SEED` says nothing about another.

Counterexamples (what the transport / band model allows and a passing run hides):
* `hides_oscillation`: every resolver run is constant from `t0+w+trp` (≤ 3 output edges);
  B's `Loop` at the same point admits B's `runt_loop`/`runt_oscillates` trace, switching
  forever with period TLOOP. iverilog with `+META_OFF=1` prints exactly that trace (§3).
  Properties "q settles", "q has ≤ k edges" pass every resolver run and fail a transport
  behaviour. (Under the involution model: InvLoop's `laps_unbounded_*` /
  B's `CElemInvolution.c2_slow_resolution` give arbitrarily long pulse trains near the
  critical width; not imported, Mathlib.)
* `follow_lost`, `follow_lost_always`: after a runt whose draw does not commit, a second `b`
  pulse of width `≥ TLOOP` that starts after the decision and ends inside the window is LOST:
  every resolver run has `o = 0` forever, while every B `Loop` behaviour at the same point
  with the same pins has `O = 1` from the pulse on (B's `c2_follow_hold`, which assumes
  nothing about the loop state), and such a behaviour exists (`bloop_exists`). The window
  always admits one (`t1 = t0+w+1`, `w2 = TLOOP`), for rejections too. So
  `R:fid_core.vh:36-37` ("a genuine input change inside that window is applied late, not
  lost") is false for any change that is gone again by `ign_until`. A test "no spurious
  ack" passes; a test expecting the ack fails spuriously.

Plain-language problem statements:
* `out_runt` / `rejected_runt_emitted` / `commit_gap`: ASSUME the resolver as transcribed
  (binary, xmode 0, self-loop, `FID_LEVEL_PS = 0`), bd_c2 empty with `a = 1`, `rst = 0`,
  one pulse on `b`. PROVE the output at every step for every draw and every resolution law.
  DO NOT cover X, multi-cell loops, other cells (only bd_c2's INIT; the resolver part is
  generic), or the real distribution of the draws.
* `noRunt_loop` / `spaced_identity` / `fourphase_identity`: ASSUME a run with no runt
  (resp. L-spaced transport edges, resp. B's four-phase hypotheses at the run's delay point).
  PROVE the run is the transport loop and a B `Loop` behaviour. DO NOT say anything about
  other delay points in the band, or about runs that did print RUNT/META.
* `seed_dependence`, `hides_oscillation`, `follow_lost`: concrete scenario families with
  explicit hypotheses; they show what one passing run cannot certify. They do not say how
  often these shapes occur in gcd_hw.

## 3. iverilog cross-check (unmodified research sources, scratch only)

Rerun: `sh formal/lean/Wip/GLSResolve/sim/run.sh` (about 1 min; takes the research files with
`git show` into a temp dir). Files:
`fid_core.vh`, `prims.v` from `git show origin/claude/research:cells/gls/…` (md5s above);
`tb_c2.v` = bd_c2 as the baked fid build makes it (`SLICE_LUTX` under `-DGLS_FID`, INIT
`00E8…`, q → transport `ICBUF` (`-DGLS_TRANSPORT_IC`, TW = 100) → A3 (arc 100), other arcs
50, `META6=1`, `TLOOP6 = 200`, SEED 7), iverilog 12, `-g2012 -gspecify`.
12 pulse widths on `b` (20 … 199 runts, 200 and 300 wide), each followed by a reset, 40
seeds = 480 pulses. `check_c2.py` computes the expected q edges from the Lean closed form
(`t0 = tb + 50`, `out_runt`/`out_wide`), using only the decision the resolver printed
(reject / commit / back, trp), and also checks the printed decision against `resolve`
(commit iff δ > 0, back iff −75 < δ ≤ 0) and `ResLaw`:
`pulses checked: 480 outcomes: {'reject': 35, 'back': 113, 'commit': 191, 'commit0': 61,
'wide': 80} mismatches: 0`.
Negative control: the same checker on `+META_OFF=1` reports 10 mismatches out of 12 (the
runts circulate forever: q 7050↑ 7070↓ 7250↑ 7270↓ …, which is B's `OR 0 200 20 7050`).
`tb_lost.v` (`follow_lost`): runt 20, 1 ps gap, b high 200 ps: q = 0 forever at seeds 0-2
(reject, back); with `+META_OFF=1` q latches at 7071. Runt 140 + 300 ps pulse, seed 5 (back,
trp 439): q = 0 forever. Seed 2 (back, trp 57) shows a further effect not formalised here:
the window ends while b is still high, so q rises late (7448) and the fall of b 43 ps later
is itself a runt, rejected: a 300 ps (≥ TLOOP) input pulse ends with q = 0.

## 4. B's C-element theorems: which hypotheses the resolver silently assumes

| B result (Formal/Cells) | relation to the resolver (this file) |
|---|---|
| `CElemTiming.Loop` (H_LUT, H_FB window/transport channels, H_LOOP_POS) | a resolver run with no runt IS a Loop behaviour at its point (`noRunt_loop`); with a runt it is not: `hides_oscillation` (Loop forces the circulating trace at a fixed point) and `follow_lost` (Loop forces the set). So the resolver is not a channel of B's family. |
| `c2_follow_hold` (H_PULSE ≥ Dmax, H_NORST, H_NOT_BOTH; "no assumption on the loop's state") | **violated** (`follow_lost`). The resolver silently assumes an extra environment hypothesis B does not have: no input change that is gone again within `trp + TLOOP + 1` after a runt decision ("H_QUIET_AFTER_RUNT"). |
| `c2_four_phase` (H_ACK, H_ENV_LATENCY `Dmax ≤ dlmin + E`) | implies no runt, so the resolver is the identity (`fourphase_identity`). The resolver only acts where B's hypotheses fail, and there it replaces B's behaviours with one chosen behaviour. |
| `runt_oscillates` (transport: a runt `< D` circulates forever) | hidden (`hides_oscillation`): the resolver assumes the echo dies after the first lap. That is not B's inertial hypothesis either: `c2_inertial_runt_lost` (H_LUT_INERTIAL: a runt `< ρ` never reaches O) — the resolver emits the runt in full (`rejected_runt_emitted`) and filters only the echo. |
| `CElemInvolution.c2_eternal`, `c2_slow_resolution` (an eternal width; unbounded resolution with switching) | the resolver assumes bounded resolution (`trp ≤ 40 τ`, `:97`) and a clean hold (≤ 3 output edges, `out_runt`). Not imported (Mathlib); stated by reference. |
| `CElemStrict(2)` (strict race `tb + D + wb ≤ s`, X window `w`) | binary resolver at `wb = 0`: `w ≥ L` latches cleanly, boundary `w = L` included (`run_wide`), the same boundary as B's `clean` at `wb = 0`. With X (`+META_X=1`) not modelled. |
| `CElemTiming.c2_reset` | not exercised here (the runs start after a quiet reset; `hinit`). |

## 5. Not done / limits
* `+META_X=1` (X while resolving), the time-0 X window, Kleene values.
* Multi-cell loops; other state nodes (bd_c2n, the arbiter's q). `St`, `eval`, `step` and
  `step_emits` are cell-independent, but `Run` fixes bd_c2's `fC2`; generalising `Run` to
  any cell function is mechanical and not done.
* `FID_LEVEL_PS ≠ 0` (loop delay ≠ TLOOP: the runt test then uses the wrong loop delay).
* The late-application runt of §3 seed 2 (iverilog only).
* The involution comparison is by reference (InvLoop / CElemInvolution need Mathlib).

## For the lead
* Optionally add `import Formal.Core.Delay.GLSResolve` to `Formal.lean` (GLSFid first).
* For FOR-RESEARCH §8: `fid_core.vh:29` and `:36-37` comments are wrong as stated
  (`rejected_runt_emitted`, `follow_lost`); counters undercount what fanout saw; evidence runs
  should report runts emitted, and a run that printed any RUNT/META line is not covered by
  B's theorems (only runs with none are, `noRunt_loop`).


---

# Probe GLSResolve2 (shard A, session 2026-10-29): any single-cell loop, bd_c2n, the arbiter's q

STATUS: DONE. One new file checks; GLSResolve.lean is unchanged (md5 54d0bef8…, every existing
statement kept). Nothing unproved in the claimed file. (§5's "generalising Run", "other state
nodes" and "the late-application runt" items are done here.)

File: `formal/lean/Formal/Core/Delay/GLSResolveGen.lean` (745 lines, md5 ca8d052e…, core Lean).
Imports GLSResolve (A) and B's `Formal.Cells.ArbHandover` (read-only, olean present).

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Core/Delay/GLSFid.lean Formal/Core/Delay/GLSResolve.lean Formal/Core/Delay/GLSResolveGen.lean
    -> [audit] 979 declarations checked
    -> [check] OK          (a plain lean -DautoImplicit=false of the file: no error, no warning)

## 1. The generalisation (task 1)

* `GRun p F v0 st`: a resolver run of ANY single-cell loop, `f t = F t (o (t - TLOOP))`;
  `grun_exists`, `grun_unique`. `lutF INIT k P` = the fid mux tree `GLSFid.lut6` of a cell's
  INIT with pin `k` the feedback and `P t i` the other pins.
* `run_iff_grun`: GLSResolve's `Run` (bd_c2) IS `GRun p (c2F a b rst)`; `c2F_lut`: `c2F` is
  `lutF INIT_c2 2 …`. So every theorem of GLSResolve is a statement about the bd_c2 instance.
* Generic set-event theorems, for any cell that reads `F t false = x t` (`x` the set pulse) and
  `F t true = true` along the run, from a `Quiet` state `Q` at `s - 1` (q = 0, not busy, window
  over, last edge none or ≥ TLOOP before `s`) with `q = 0` one loop back:
  `seg_wide` (`x = 1` for ≥ TLOOP: clean set), `seg_runt_pre` (runt `w < TLOOP`: the exact
  state `Sseg` up to `ign_until`, inputs ARBITRARY in the window), `seg_runt` (whole run when
  `x = 0` from `ign_until`), `seg_window_end` (**at `ign_until` the output is `F Iend final`:
  a change still present at `ign_until` is applied exactly there, one that is gone leaves no
  trace** — the precise form of `fid_core.vh:36-37`), `grun_quiet`, `grun_runt`, `grun_wide`,
  `grun_runt_o` (from the reset state at 0).
* `run_runt_gen'`: GLSResolve's `run_runt_gen`, word for word, re-derived from `grun_runt`
  (`Srunt_eq_Sseg`): the generic theorems specialise to the old ones.

## 2. Instances (task 2)

* bd_c2n (INIT `00B2…`, `bd_ce.v:49` = `Gen/Cells.lean:59` by text = B's `CElemTiming.INIT_c2n`):
  `fC2n_eq` (= `!r ∧ maj(a, ¬b, q)`, decide), `fC2n_eq_exc` (= B's `exc`, via B's `c2n_eq`),
  `c2nF_lut`; `c2n_out_runt`, `c2n_out_wide` (runt on `a` with `b = 0`): the same three shapes
  as bd_c2 (rejected runt emitted in full; commit gap of width trp).
* arbiter q (`ustate` O6, INIT `FFF0_FFB2_ACAC_ACAC`, pins I0 r1 I1 r2 I2 q I3 rst I4 A0 I5 1,
  `bd_arb.v:245` = `Gen/Cells.lean:1193` by text): `fArb_eq` (`rst ∨ (A0 ? q : maj(r1,¬r2,q))`),
  `fArb_eq_B` (= B's `o6B INIT_HELD`, via `ArbHandover.held_q_eqn`), `arbF_lut`.
  In fid, `ustate` is split into two SLICE_LUTX (O6 q with META6=1, O5 R0 without: no self-loop,
  `R:gen.py:661-682`, `R:prims.v:76`).
* `arb_near_tie`: q = 0 and quiet, rst = 0, at ustate's mux r1 rises at T0, r2 at T0 + w
  (`w < TLOOP`), both stay up, A0 low up to the decision and ARBITRARY after it. For every
  draw and law: `q = [T0 ≤ t ∧ (t < T0+w ∨ (commit ∧ T0+w+trp ≤ t))]`. Nothing A0 does after the
  decision (the hold included) changes q: the resolver ignores every pin until `ign_until`.

## 3. Does the A0 hold tolerate the commit gap and the lost follow? (task 2, decided)

**Commit gap: NO. Counterexample `arb_double_ack` (proved).** Assumed: the q node as in
`arb_near_tie` from a quiet reset at q = 0, the draw commits (client 1 wins); `ugrant`
(transport, real INIT via B's `g1F`/`g2F`) reads `r_k` and q with one delay `D_k` to
`ua_k`'s pin; `ua1`, `ua2` are bd_c2 resolver runs from reset; A0 rises ONCE and stays high,
at `ua_k`'s pin at `sA_k`, with `T0+w+D2 ≤ sA2`, `sA2 + L2 ≤ T0+w+trp+D2`,
`T0+w+D1 ≤ sA1 ≤ T0+w+trp+D1`. Proved: from `max(T0+w+trp+D1, sA2)` on, `A1 = A2 = 1` with A0
high: two clients acknowledged for one server transaction (`bd_arb.v` header: the failure the
hold exists to prevent). Mechanism: during the commit gap q = 0, so g2 = r2·¬q is a clean
full-swing 1 for `trp` ps, A0 arrives, ua2 sets; then q lands at 1 WHILE A0 IS HIGH (the hold
is a pin function, the resolver's scheduled `o_r <= #trp` ignores it), g1 rises, ua1 sets.
Grants are exclusive at every instant (one q), A0 is one clean step, no X: neither a grant-
exclusion check nor an X check flags it. `arb_gap_closed` (proved, commit case): if A0 reaches
ua2 only after the gap (`T0+w+trp+D2 ≤ sA2`), A2 stays 0 for every ua2 draw.
Realisability: needs a server whose A0 reaches ua2 within `trp + w + D2 − L2` of the decision;
at the defaults (TAU = WIN = 150) `trp ≤ τ ln(WIN/2) ≈ 647 ps`. iverilog (below) shows it with a
`A0 <= #100..300 R0` server. NOT a contradiction of B's rows: the near tie violates
`bd_arbcell.req_separation` (H_REQ_SEP, necessary for exclusion, an environment rate that
arbitration cannot assume), i.e. it is the header's "metastable q: NOT EXCLUDED" tier. What is
new: (i) the fid GLS renders that tier as a clean, definite, X-free double acknowledge after a
"resolved" META line; (ii) the header's consumer rule "must not read a grant within ONE LOOP
DELAY of the decision" is met in every double-ack run (A0 reaches ua2 230-450 ps after the
q decision, TLOOP = 200) and still fails: under the resolver the rule would have to be "within trp_max + TLOOP".
(iii) In B's transport model the same near tie circulates forever (`hides_oscillation`'s
shape: `f = maj(1,0,q(t−L)) = q(t−L)` once both requests are up, A0 high or low), so B's model
also breaks exclusion there; the resolver replaces that with one specific bad behaviour.

**Lost follow: tolerated for the arbiter under the four-phase discipline (argued from a proved
lemma; the protocol step is not proved).** `seg_window_end` (proved, generic): a change of the
cell function still present at `ign_until` is applied there. In the arbiter a set/reset
condition `r1·¬r2·¬A0` / `¬r1·r2·¬A0` can disappear only if a request falls (a full
acknowledge cycle of that client inside the window, `trp + TLOOP + 1` ≤ ~850 ps at the
defaults), the other request rises (tie: q holds by the function too), or A0 rises (hold: q holds
by the function too). In the near tie itself (`arb_near_tie`) the function is `q` after the
decision whatever A0 does, so there is nothing to lose. Not proved: that four-phase clients and
server keep a condition up until q moves (no closed-loop arbiter+server+clients model here).

## 4. The late runt (task 3)

`late_runt` (proved, bd_c2, a = 1): a runt `[t0, t0+w)` whose draw does not commit, then a
pulse `[t1, t1+w2)` with `t0+w < t1 ≤ I = ign_until < t1+w2 < I + TLOOP`. Then q = 1 on
`[I, t1+w2)` (applied late at I), and the fall of b at `t1+w2` is a runt of width
`t1+w2−I` decided by the draw at `t1+w2`: from then on `q = [commit' ∧ t1+w2+trp' ≤ t]`.
`late_runt_B`: with `w2 ≥ TLOOP` every B `Loop` behaviour at that point has O = 1 from t1 on
(B's `c2_follow_hold`), and one exists. So a 300 ps pulse with a non-committing second draw
ends with q = 0 (the notes' seed-2 trace).

## 5. iverilog cross-check (unmodified research sources: `git show origin/claude/research:…`,
fid_core.vh md5 2422ccea… = 6524fa3; iverilog 12, `-DGLS_FID -DGLS_TRANSPORT_IC`)

`sh formal/lean/Wip/GLSResolve/sim/run.sh` (≈ 3 min). New: `tb_arb.v` (bd_arbiter as fid builds
it: ustate split O6/O5, ugrant, ua1/ua2, transport ICBUFs, TLOOP 200 everywhere, D1 = D2 = 300,
server `A0 <= #SMIN R0`; one client-2 transaction first so the near tie starts from q = 0),
`check_arb.py`; `tb_late.v`, `check_late.py`. Expected edges from the Lean closed forms; only
the printed decisions and A0's rise (environment) are read from the logs.
* arbiter, W ∈ {130,150,170} × SMIN ∈ {100,300,500,800} × 10 seeds = 120 runs:
  `cases: back 27, gap_closed 52, double_ack 3, ua2_runt_commit 1, ua2_runt_nocommit 7,
  {back,commit}_A0_before_grant 9/21 (A0 overlaps the first runt: q checked only, outside the
  theorems) — mismatches: 0`. 12 of the 120 runs end with A1 = A2 = 1 under one A0 pulse
  (e.g. W=150 SMIN=300 seed 2: META delta=6 → 1 after 378 ps; q 11700↑ 11850↓ 12228↑; A2↑ 12300,
  A1↑ 12528). In the `ua2_runt` cases the ua2 runt is emitted on A2 in full (`A2 = 1` on
  `[sA, G1)`, checked): an acknowledge pulse of tens of ps to client 2.
  Negative control `+META_OFF=1`: q has 201 edges, mismatches: 1.
* late runt, W = 140, gap 1, W2 ∈ {250,300,350,400} × 40 seeds = 160 runs: `first_commit 112,
  follow_lost 35, late_runt_reject 7, late_runt_back 4, late_runt_commit 2 — mismatches: 0`;
  negative control `CHK_L=210` (wrong loop delay in the checker): 13 mismatches.

## 6. Not covered
X (`+META_X=1`), `FID_LEVEL_PS ≠ 0`, multi-cell loops; reset-direction runts (q falling) are
not instantiated (the arbiter's handover runt needs H_Q_BEFORE_REREQ to fail); the ugrant
single-delay hypothesis (real pin skew can add hazard pulses; not needed for a counterexample);
A0 as an open-loop environment trace (no closed server model); how often the double ack occurs
in gcd_hw (it needs a near tie AND a server faster than trp).

## For the lead
* Add `import Formal.Core.Delay.GLSResolveGen` to Formal.lean (after GLSFid, GLSResolve).
* For FOR-RESEARCH: the resolver's commit gap turns a near tie into a clean double acknowledge
  when the server answers within trp; `bd_arb.v`'s consumer rule ("one loop delay") is not
  enough under the resolver; `fid_core.vh:36-37` holds exactly for changes still present at
  `ign_until` (`seg_window_end`) and a pulse straddling `ign_until` becomes a new runt.
* B (read-only for me): `bd_arbiter` rows carry no row for the q node's resolution time; the
  natural new hypothesis is "A0 reaches ua_k later than trp_max + TLOOP after a q decision".
