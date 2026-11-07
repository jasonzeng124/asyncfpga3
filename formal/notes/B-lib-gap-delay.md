# B-lib-gap-delay: `bd_delay_gated`'s flush (H_GFLUSH) made exact, per pin

Probe Bdg (shard B, library gap), 2026-10-27. New file
`formal/lean/Formal/Cells/LibGapDelay.lean` (core Lean, no imports). JSON
draft (not merged; the JSON and its generator were not edited):
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Bdg/draft_entries.json`,
made by `draft_entries.py` in the same directory. No route, board or toolchain was run.

## 1. What correct behaviour of the gated line is

The cell is modelled as bdc instantiates it (same indexing as `GcdCells`):
`s 0 = uor(gate)`, `s 1 = g[0](s 0)`, `s (i+1) = s i AND gate` (LUT2 INIT 8,
`1 <= i < N`), `z = s N`. Each LUT pin is read through its own read map inside
a delay window (H_PIN_READ, `Box`/`Fits`). Read maps need not be monotone, so
this model has more behaviours than GcdCells' FIFO `Ret`. The gate is high
before `F` (the previous token, so the chain was full), low on `[F, T)`, and
high from `T` (H_GATE_PULSE).

- `fresh T` is the gate with the previous token erased. `run (fresh T)` is the
  line's response to the new token alone.
- **Flushed** (no stale pulse): from the fast-fall point `F + (q (N-1)).hi` on,
  `z` equals the new token's response.
- **NoEarly** (no early request): from that point on, `z` is high only at or
  after `T + Llo N`. `Llo N` is the full matched length: the sum of the
  chain's lower bounds, which is what rule A compares the data cone against.
  The new token's response is never early (`fresh_late`), so Flushed implies
  NoEarly.

`GF i` (H_GFLUSH i) is exactly the JSON row's inequality:
stage 1: `F + r0.hi + r1.hi + (p 1).hi <= T + (q 1).lo`;
stage i >= 2: `F + (q (i-1)).hi + (p i).hi <= T + (q i).lo`.

## 2. Results (all in `LibGapDelay.lean`)

| theorem | assumed | proved |
|---|---|---|
| `flush_of_gflush`, `no_early_of_gflush` | maps in box, GF i for all i | Flushed, NoEarly (any maps, no side condition) |
| `stale_pulse` | WF box, F < T, GF i false (by any amount), H_BAL_HI (k < i), H_LO_ORDER (k > i), H_START | at the box corner (constant delays) `z` is high at `t = T + (q i).lo + Pl i (N-1) >= F + Vd N` and the new-token response is low there |
| `stale_pulse_early` | + H_SHORT `(q i).lo < Llo (i+1)` | that `t < T + Llo N` (an early request) |
| `box_exact_flushed` | side conditions at every stage | Flushed for every map in the box **iff** GF i for all `1 <= i < N` |
| `box_exact_no_early` | + H_SHORT | NoEarly for every map **iff** GF i for all i |
| `rescue_*` | N = 3 fixed delays, GF 1 false, H_LO_ORDER false | Flushed and NoEarly still hold for every map |
| `real_ok`, `real_rises`, `real_bad` | realistic SLOW-corner box, N = 12 | non-vacuity, and the 1 ps counter-trace (section 3) |

Side conditions. These mark the boundary inside which per-stage necessity holds:
- **H_BAL_HI** (stages before i): `(q 1).hi <= r0.hi + r1.hi + (p 1).hi`, and
  `(q k).hi <= (q (k-1)).hi + (p k).hi`. A tap's slow arrival is not later
  than the previous one's plus a chain hop, so the stale value of `s i`
  really lasts until `F + Vd i`. If this fails, `Vd` overestimates when the
  stale value disappears. GF is then still sufficient, but it may be
  conservative.
- **H_LO_ORDER** (stages after i): `(q k).lo <= (q i).lo + sum_{j=i+1..k} (p j).lo`.
  No later tap is slow enough to still read the gate low when the stale
  pulse passes it. **This one is really needed**: `rescue_flushed` is a case
  where GF 1 fails and tap 2 is slower than tap 1 plus a chain hop (28 > 20).
  Tap 2's read of the low gate covers stage 1's hole, so the line is correct
  anyway. Per-stage H_GFLUSH is not necessary in general, which confirms
  Blt's caveat. The fully general exact condition is that the union of the
  tap read windows covers the interval. I did not formalise it.
- **H_START**: the stale pulse comes after the fast-fall point. On realistic
  numbers this means `T - F >= (q (N-1)).hi - (q i).lo - sum (p j).lo`.
- **H_SHORT** (NoEarly only): the tap path to stage i+1 is shorter than the
  chain path. Without it the stale pulse arrives after `T + Llo` and NoEarly
  is not violated, but Flushed still is: the pulse is a glitch on top of the
  new request.

## 3. Realistic numbers (SLOW corner only)

Units are ps, N = 12 (bdc's smallest gated line). The LUT arc is prjxray-db
(100, 124) for every pin (C-10c). The wires are assumed, not routed: an
in-slice chain hop is 210..264 (the C-10c hand check gives 264 slow_max), and
the gate net, which has high fanout, is 400..500. Each pin is wire plus arc:
`r0 = q = [500, 624]` and `r1 = p = [310, 388]`. The boundary is
`T - F >= 900` (stage 1 binds; stages >= 2 need only 512).
- `real_ok`: with a 900 ps low phase (slack 0), every hypothesis of both iff
  theorems holds, and the line is Flushed and NoEarly for every map tuple in
  the box.
- `real_rises`: at all-SLOW_MAX, `z` is still the old token at 623, falls at 624
  (`F + Vd 12`), and rises at 6180.
- `real_bad`: with an 899 ps low phase (GF 1 short by 1 ps), `z` is high at
  4499 while the new-token response is low. 4499 < 5119 = T + Llo 12, so this
  is an early request 620 ps before the matched length: the previous token's
  stale pulse, passed by stage 1.

## 4. Checks

`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/LibGapDelay.lean`
prints `[bchk] OK`. `#print axioms` (scratch `Bdg/ax.lean`) on the 13 main
theorems shows only `propext`, `Quot.sound` and `Classical.choice`. The
`decide` facts `real_rises` and `rescue_hyps` use no axioms. There is no
sorry, admit, native_decide or declared axiom.

## 5. Not covered, and a finding for the cell owner

- Not covered:
  - Whether the new token's own rising edge is glitch-free. With
    non-monotone maps the AND can bounce inside `[T + Llo, T + Lhi)`.
    Flushed only says that such a bounce belongs to the new token. FIFO maps
    rule it out (`GcdCells.rises`).
  - The data that the request bundles (rule A).
  - The gate's waveform itself (H_GATE_PULSE).
  - Correlated corners. Necessity takes the pins' corners independently. For
    sufficiency the box is always sound.
- Finding: the requirement on the gate's low phase is
  `max(r0.hi + r1.hi + (p 1).hi - (q 1).lo, max_i (q(i-1)).hi + (p i).hi - (q i).lo)`,
  so stage 1, with the two ungated hops, binds. Rule F still lacks the
  in-flight term `(p i).hi - (q i).lo` (row D2's gap, B-gcd-cells.md). Every
  route should also be checked for H_LO_ORDER, because a slow tap makes the
  per-stage check conservative but not wrong. No gcd_hw route has been
  measured against any of this.
