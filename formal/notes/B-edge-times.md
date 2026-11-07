# B-edge-times (probe Bedge): the edge-time equations have solutions, every N

Lean, core only (no Mathlib in the closure). Each file checked OK with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/<file>` (autoImplicit=false):

| file | contents |
|---|---|
| `formal/lean/Formal/Cells/EdgeTimes.lean` | chains: the run `nd`, the edge times `tau`, `chain_c`/`chainT_c` (degenerate bands), `chain_b` (given bands), `schedule`, `chain_solution`, `chain_exists`, `chain_env1_solution`, `chain_solution_witness`; generic `nt_phase`, `wire_band`, `bRet` |
| `formal/lean/Formal/Cells/EdgeTimesNet.lean` | a chain as an `AssumeGuaranteeEndsNet` network: `chain_netW` (H_SP derived), `chain_linkSpec` (departure bounds derived), `chain_src`/`chain_snk` (contracts), `chain_as_net`, `net_solution` |
| `formal/lean/Formal/Cells/EdgeTimesRing.lean` | rings: the run `nr`, the potential `phi`/`key`, the edge times `tauR`, `ring_c`, `ring_b`, `ring_solution`, `ring_exists`, `ring_solution_witness`, `ring_run_iff`, `ring_reset_exists`; generic `nt_phase'`, `noRevertI_tr` |

The definitions are imported, not restated: `Chain`, `ChainT`, `ChainData` and its `εF`,
`εB`, `ρL`, `αL`, `Es`, `Ea`, `RT` (AssumeGuaranteeLinks); `RingData`, `PRing`, `PRingT`,
`StageB`, `WireB`, `SetStage`, `xr` (RingPhys); `GD`, `LinkSpec`, `NetW`, `Contract`,
`Proved` (AssumeGuaranteeEndsNet); `Stage`, `Env1`, `Timing1`, `nt`, `τs`, `cph`
(WinFifoCausal); C's `Ring.prv/nxt/tok/D/cnt/resetState`.

No sorry, axiom or native_decide. `#print axioms` on the 11 headline theorems (appended
temporarily, then removed): all `[propext, Classical.choice, Quot.sound]`.

## The problem

B's chain, ring and network theorems hold for EVERY solution of their edge-time
equations (H_TIMES: a node's `j`-th edge is read off its own trace after its pins' phase
starts; a pin's edges are read off the pin). Solutions had been exhibited only by hand:
the chain for uniform delays 1 (`chain_witness`), rings for N = 3 and N = 5. So
non-vacuity was open for other delays and other ring sizes, and the departure bounds and
wire spacing of the mixed-network rule were assumptions.

## Method

1. **The run.** Fix one constant delay per gate inside its band. Define every trace by
   strong recursion on time: a LUT node at `t` is its real INIT applied to its pins at
   `t - d`, a pin is its driver at `t - w`. All LUT delays are `>= 1`, so the recursion is
   well founded. A fixed transport delay is a legal behaviour of every `Win`/`WinDelay`
   channel of the band.
2. **The edge times.** Define them by H_TIMES itself, read with every band shrunk to its
   realised delay (the degenerate band `[d, d]`). For a chain, event `(i, j)` needs
   `(i - 1, j)` and `(i + 1, j - 1)`, so recursion on `(j, i)` lexicographically works.
   For a ring the same-level dependencies go in both directions (see below).
3. **Degenerate bands.** Prove every gate relation for the degenerate bands. Win and
   H_NO_REVERT of a transport delay equal to its band are immediate (`noRevertI_shift`).
   H_TIMES holds by construction. B's closure theorem (`chain_nodes`, `ring_nodes`) then
   says every node is a clean step signal.
4. **Real bands.** Widen to the given bands. Win is immediate. H_NO_REVERT of the band
   follows from cleanness: the input of a transport read is the output shifted back by
   `d`, and its edges are spaced above the spread (`wire_band`, `noRevertI_tr`, through
   `noRevertI_of_ret`). H_TIMES of the band follows from `nt_phase`/`nt_phase'`: a wider
   band's search finds the same edge, because the previous edge is early enough. That
   spacing comes from B's own unconditional inequalities (`c_spL`, `c_spR`, `s_gap`,
   `r_snd`, `r_spF`, `r_spB`). The timing rows are needed on the BANDS only; they imply
   the same rows on the realised delays (`chainT_c`, `ringT_c`).

## Results

- **Chains, every N, every delay assignment in the bands** (`chain_solution`,
  `chain_exists`).
  - *Assumed:* bands with `lo, wl, vl >= 1`; realised delays in the bands; a source start
    `T0` with `R <= T0 + wl 0` and `wh 0 <= T0`; `ChainT` on the bands. The source is
    modelled as raising at `T0` and then answering each acknowledge edge after `d 0`. The
    sink copies its request.
  - *Proved:* every field of `Chain` and `ChainT`, including both end contracts. The edges
    are the max-plus schedule
    `τ(m+1, j) = max(τ(m, j) + w m, [j = 0: R | τ(m+2, j-1) + v(m+1)]) + d(m+1)`,
    `τ(0, j+1) = τ(1, j) + v 0 + d 0`, `τ(N+1, j) = τ(N, j) + w N + d(N+1)` (`schedule`).
    So `chain_env1` is non-vacuous for every such assignment (`chain_env1_solution`).
  - *Witness:* `chain_solution_witness`, for every N. It uses band `[1, 3]` with realised
    delays `1 + i % 3`, so the low end, the middle and the high end of the band all occur,
    and H_LAT holds with equality.
- **Departure bounds and H_SP, derived for link chains** (`chain_as_net`, `net_solution`).
  - *Assumed:* `Chain`, `ChainT`.
  - *Proved:* the chain as a `GD` network over `Fin (N + 2)` satisfies `NetW`, so the wire
    spacing H_SP is derived. Every link is a `LinkSpec` with `H_SND`, `H_RCV` and
    `H_RST_EARLY` derived, with slacks `Es = vl m + lo m + wl m` and
    `Ea = wl (m+1) + lo (m+2) + vl (m+1)`. These come from the path around each handshake
    cycle: node, wire, neighbour LUT, wire back (Bnet's `c_snd`, `c_rcv`, `c_hspF`,
    `c_hspB`). The ends are `Contract` cells, with their H_WAIT taken from
    `SRC_WAIT`/`SNK_WAIT`.
  - *Consequence:* `mixed_closed` applies. With the chain construction, everything holds
    on a constructed run for every delay assignment in the bands.
- **Rings, every N, every reset pattern with `0 < D < N`** (`ring_solution`,
  `ring_exists`).
  - *The recursion order.* The recurrence has same-level dependencies. Stage `i` waits for
    `τ(prv i, j)` when `tok i = false`, and for `τ(nxt i, j)` when `tok (nxt i) = true`.
    Orient each channel by its wavefront bit: the result is acyclic iff the wavefronts are
    neither absent nor everywhere. The order used is the potential
    `phi i = N² + D·(i+1) − N·cnt(tok, i+1)`. It rises by `D` across a channel without a
    wavefront and falls by `N − D` across one with. It is consistent around the ring
    (`phi(N−1) = N²`, `phi_zero`). The key is `(2N²+1)·j + phi i` (`key_prv`, `key_nxt`,
    `key_low`). `tauR` is defined with these guards. They hold whenever `0 < D < N`, so
    `tauR_eq` gives H_TIMES for every stage and every edge index.
  - *Proved:* every field of `PRing` (both INIT polarities) and `PRingT`. The witness
    `ring_solution_witness` covers every N and every `b` with `0 < D < N`.
  - **`ring_run_iff`:** a ring with reset pattern `b` has a run satisfying
    `PRing ∧ PRingT` iff `0 < D < N`. This is the converse of `RingPhys.ring_cond`,
    RingPhys's open item, which had been shown only for N = 3 and 5.
  - `ring_reset_exists`: C's reset rings (`resetState K`, `0 < K < N`, `N >= 3`) have a
    run that circulates forever with `D = 2`.

## Not covered / open

- **Delays that vary from edge to edge inside the band.** Each constructed run uses one
  constant per gate. B's theorems cover the varying runs too, but their existence is not
  constructed.
- **Exact max-plus form for rings.** `tauR` is the degenerate read
  `nt (On i) d d (cph j) (Vph j)`, which lies in `[cph j + d, cph j + d + 1]`. To get
  exactly `cph j + d` one would show that the excitation is already at `Vph j` at
  `cph j`, via `exc_phase_w` on the normalised stage; not done. There is also no
  periodic-regime or cycle-time theorem.
- **Departure bounds for mixed networks** (forks, joins, steers): only link chains are
  done. The same path argument through `CelSpec`/`SteerSpec` remains open.
- **Uniqueness.** The bands admit many runs; uniqueness is not claimed.
- **The chain's ends** are concrete models here, not arbitrary contracts.
