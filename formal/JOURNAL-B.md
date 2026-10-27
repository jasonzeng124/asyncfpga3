# Shard B journal (cells: C-element, latch/link, arbiter)

## Verdicts (shard B)

All files below check with `formal/check.sh` (lake build of `Formal/`) and
standalone with `cd formal/lean && LEAN_PATH=.lake/build/lib/lean lean
Formal/Cells/<F>.lean` (core Lean, no Mathlib). Notes: `formal/notes/B-*.md`.

| track | verdict | evidence | effort to finish | buys |
|---|---|---|---|---|
| 5 C-element | **works** | CElemFn (8 INITs = spec; Kleene closed forms), CElemTiming (bounded delay: enabling input >= LUT+feedback delay, tight; four-phase spec with new fork condition), CTree (tree = flat C-element, all shapes, under four-phase with ack wait) | ~1-2 d: port to Core's real-time channels (probe 5d running), inertial/involution regimes, bd_c3/c4 timing | INITs machine-checked; the exact timing condition per cell; the ack wait shown necessary |
| 6 latch/link | **works** | Latch (mux latch, setup/hold, DACK rule H sufficient), LinkHandshake (four-phase refinement, token conservation, half-token bound, deadlock freedom for any N; exact bundling inequality), Bundling (delay lines; capture condition derived; rules I and F each miss a term) | ~2-3 d: compose C-element + latch into a link stage, W-bit lift, pipe | a derived spec for tighten.py rules H/I/F; reference spec for track 10 |
| 7 arbiter | **works for binary/Kleene/handover; analog pending** | ArbKleene (exclusion for all 3-valued inputs; only (X,X) fails), ArbHandover (16 ps claim exact; held INIT meets the merge's counting precondition in all interleavings), MuxTree (fidelity of the Kleene LUT) | analog (7c/7d) pending; RT1/RT2 timed (7h), A0 fork (7g), ternary-sim soundness (7f) running | exclusion tiers made precise: settled q structural; handover with hold is relative timing, not structural; metastable tier only (X,X) |

Fidelity (per primitive, shard B): LUT function exact (real INIT, pin map);
Kleene LUT = hypothesis on ONE 2:1 pass-transistor mux (MuxTree proves the
tree then gives closure semantics in any input order), graded B: credible
for clean or late select edges, doubtful for a mid-rail select while the
legs move (NMOS-only tree). Delays: bounded window/transport channels on ℕ
or ℤ ps; no R/C, no buffered vs pass-transistor pip distinction yet; per-pin
LUT arcs only in 7e. Feedback: a routed wire with an interval.

Findings for the cell owner (not confirmed on a route):
- tighten.py rule I omits the latch's I2 (feedback) pin arc; rule F omits a
  value in flight on the FASTFALL chain wire. Lean counter-traces; today the
  guardband covers both numerically.
- H_A0_FORK: bd_arbiter's hold needs A0's fall to reach ua_k before
  A0 -> q -> g_k does. CORRECTION (7g): this IS checked, by rule J
  (cells/verify/arb_fork.py); my earlier note and owner notification saying
  "unchecked" were wrong. 7g proves rule J's condition exact (iff, both
  clients, box version) and finds rule J optimistic by ignoring per-pin
  site-pin delays (up to ~0.5 ns, not in nextpnr's SDF) and using a flat
  124 ps LUT arc (68-161 ps the wrong way). Proposed rule J' in
  formal/notes/B-arb-a0fork.md. Survey raw minimum +618 ps; worst pin
  assignment leaves ~0 across the full box on the tightest route.
- C-element fork: after seeing the ack the environment must wait out the
  feedback wire (E >= dwmax + dlmax - dlmin). Unchecked.
- Held arbiter: g1/g2 and A1/A2 exclusion across a handover are relative
  timing (RT1/RT2), contrary to the header's "structural WITH THE HOLD".
- Bare-cell filtered overlap (8%): an isolated handover overlaps <= 72/94 ps
  for any request skew, below the filter; the observed events are not the
  digital handover overlap.

## Session Tue Oct 27 02:48:05 UTC 2026

### progress 02:48
Took LOCK-B. Running A's setup.sh next; then probes for tracks 5/6/7.

### progress 02:52
A's setup.sh running (Lean 4.35.0 via GitHub zip; Mathlib by git, built from
source since the cache hosts are blocked). Wrote Formal/Cells/Prelim.lean (core
Lean only: K3, lutB/lutK, muxTree, LUT6_2 O5/O6) so the binary and Kleene cell
proofs need not wait for Mathlib. Sanity: bd_c2's INIT = ~rst.maj(a,b,q) by
decide in 0.3 s.
Launched 12 probes: 5a CElemFn, 5b CElemTiming, 5c CTree, 6a Latch,
6b LinkHandshake, 6c Bundling, 7a ArbBinary, 7b ArbKleene, 7c ArbAnalog
(Mathlib), 7d ArbResolve (Mathlib), 7e ArbHandover, Bf MuxTree (fidelity of
H_KLEENE_LUT: per-mux hypothesis vs closure semantics).
Choice: discrete time (ℕ ps ticks, traces ℕ → Bool) for the cell timing
probes, ℝ only for the analog loop. Reason: the cell lemmas are about finite
delay intervals and finite INITs; ℕ keeps them in core Lean with decide/omega.
To reconcile with A's trace choice once Core lands.

### progress 02:59
Checked and pushed: 5a CElemFn, 6a Latch, 7b ArbKleene (all core Lean, clean,
axioms propext/Quot.sound). setup.sh was looping on `lake update` because
Mathlib's post-update hook runs `cache get`, which fails file by file
(cache host 403); killed it and started `lake build` of Formal plus the
Mathlib ODE/exp/log/IVT/Lebesgue modules directly.
Finding from 7b (to check on a route, not a confirmed defect): the A0 hold in
bd_arbiter relies on the A0 fork ordering H_A0_FORK: A0's fall must reach ua2
before the path A0 -> ustate -> q -> ugrant -> g2 does, or A2 = C(g2, A0)
fires for a transaction the server never started.
Untracked files in the tree are probes still being written; they are
committed only after they check.

### progress 03:07
In and pushed: 5b CElemTiming, 5c CTree, 6c Bundling, 7e ArbHandover, Bf
MuxTree. Verdict table at the top. Launched 5d (C-element on A's ℝ-time
Core channels; inertial/involution), 7f (ternary-sim soundness), 7g (A0
fork), 7h (RT1/RT2 timed). Running: 6b, 7a, 7c, 7d. Note: A's Core uses ℝ
time and a FIFO pure delay; 5b's window channel is weaker than FIFO, so its
positive results transfer and its counter-trace (fixed transport) is FIFO.
