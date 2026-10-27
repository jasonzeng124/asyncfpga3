# Shard B journal (cells: C-element, latch/link, arbiter)

## Verdicts (shard B)

(pending: tracks 5, 6, 7 in progress)

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
