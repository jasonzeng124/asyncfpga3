# A-gls-resolve: the trace semantics of research's FID_RESOLVE on the bd_c2 loop

Probe GLSResolve, shard A, session 2026-10-29. STATUS: DONE pending the final check.sh run
(see "What checks" for the exact command and its last lines).

File: `formal/lean/Formal/Core/Delay/GLSResolve.lean` (core Lean, no Mathlib). Imports
`Formal.Core.Delay.GLSFid` (A; no olean in .lake/build yet, so check.sh is given it first) and
`Formal.Cells.CElemTiming` (B, read-only, core Lean, has an olean). No Wip files.

Research side read-only at `origin/claude/research` tip `6524fa3`: `cells/gls/fid_core.vh`
(md5 2422ccea…, unchanged since 5567170), `cells/gls/prims.v` (md5 3e7423cb…), `cells/gls/gen.py`.
Written `R:<file>:<line>`.

## What checks

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Core/Delay/GLSFid.lean Formal/Core/Delay/GLSResolve.lean
    (last lines: see the report; filled in at the end of this note)

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

Scratch dir `/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/GLSResolve/sim/`:
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
