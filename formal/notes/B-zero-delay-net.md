# B-zero-delay-net (probe Bzd2): the network half of physical -> zero-delay refinement

Files (core Lean; each checks with `/tmp/claude-0/btools/bcheck.py Formal/Cells/<File>.lean`):

| file | content |
|---|---|
| `formal/lean/Formal/Cells/ZeroDelayNet.lean` | abstract chain run, key retiming, closed loop at the parameter level, `Causal` from the loop, counter-loop |
| `formal/lean/Formal/Cells/ZeroDelayNetPhys.lean` | trace level: every stage a real `LinkExact` behaviour, wired to its neighbours; `chain_spec`, `chain_refines` |
| `formal/lean/Formal/Cells/ZeroDelayNetWit.lean` | non-vacuity: two coupled stages, nonzero delays, joint simulator |
| `formal/lean/Formal/Cells/ZeroDelayNetTok.lean` | k tokens, partial: pulse trains, C's `Protocol` for k tokens, one retiming across tokens |

Axioms (checked with a temporary companion file, since removed): every headline theorem uses
only `propext`, `Classical.choice`, `Quot.sound` (`chain_causal`, `train_at`,
`key_mono_family` use only `propext`, `Quot.sound`).

This builds on Bzd (`ZeroDelayRefine`, the cell half). C's definitions (`Chan`, `Protocol`,
`Ops.Held`, `Ops.Link.Link`) are imported, never restated.

## The construction: one retiming for the whole network

A physical event is a window `[lo, hi]`, as in Bzd. The global retiming gives an event the
abstract step `key T D lo d = (lo - T).toNat * D + d`. Here `T` is the source request's window
start and `d < D` is the event's causal depth in the ideal four-phase order. For the chain:
source rise 0; node `i` rise `2i+2`; its wire copies `2i+3`; sink rise `2N+2`; source fall
`2N+4`; node `i` fall `2N+6+2i`; sink fall `4N+6`; `D = 4N+8`.

- **Monotonicity is free.** If `e.hi < e'.lo` then `e.lo < e'.lo`, so `e` gets the earlier
  step (`net_mono`, `key_mono_family`). This holds for any family of windows, tokens included.
- **The real content is C's gate fields.** Every cause must get a strictly earlier step than
  its effect (`SchOK`, the order list). The key schedule meets `SchOK` when the windows are
  **lo-causal** (`LoOrd`: each effect's window starts no earlier than its cause's). That is
  `kS_ok`.
- **Shared wires are consistent by construction.** There is one abstract `Chan` per channel:
  channel `i+1` is both `o` of stage `i` and `i` of stage `i+1`. `stage_mono` checks that the
  global retiming restricted to each stage's own six events (that stage's `Par` windows) is a
  monotone retiming in Bzd's sense.

## Results

| theorem | assumed | proved |
|---|---|---|
| `chain_link`, `chain_proto`, `chain_held` | any schedule meeting `SchOK` | the abstract chain run `chA`/`ndA` satisfies C's `Link` at every stage (shared channels), `Protocol` and `Held` on every channel `0..N` |
| `kS_ok` | `LoOrd` | the key schedule meets `SchOK` |
| `chain_loOrd`, **`chain_causal`** (goal 1) | `ChainPar`: `Wf` per stage (reads `>= 0`), H_LOOP (each neighbour pin's driver windows ARE the neighbour node's windows), H_SRC `U0_0 <= Fa_0`, H_SNK `U0 <= Rb`, `V0 <= Fb` at the last stage | `LoOrd`, and Bzd's `Causal` at EVERY stage |
| `causal_iff_mono` | `Wf` | `Causal` is exactly the `Mono` of Bzd's per-cell retiming |
| `negdelay_breaks_causal` | a two-stage loop meeting H_LOOP exactly, the upstream stage `Wf` and `Conj`, the downstream stage reading its request at `-300 ps` | upstream `Causal` fails, so Bzd's retiming of that stage is not monotone (it is the loop, not a cell row, that breaks) |
| `net_mono`, `stage_mono` | `ChainPar` | one global retiming, monotone on the whole network and on every stage |
| `chain_abstract` | `ChainPar` | the bundle of all the above |
| `chain_rst`, `chain_hi`, `chain_lo`, **`chain_spec`** | `ChainCell` (below) + `ChainBeh` | every stage meets LinkExact's `Spec` IN THE CLOSED LOOP |
| **`chain_refines`** (goal 2, chain) | `ChainCell` + `ChainBeh` | C's `Link`/`Protocol`/`Held` on one zero-delay run of the whole chain, `Causal` per stage, and `NetRef`: global and per-stage monotone retiming; every node, every internal wire as its reader sees it, and both end wires are window images; every latch captures `v` |
| `chain_witness` | concrete numbers | `ChainCell 2 Pw`, a coupled behaviour exists (`jr` simulator), so `NetRef` holds |
| `train_at`, `train_move`, `proto_train` (goal 3, partial) | wire order | k-token pulse trains; C's `Protocol` for a k-token channel with interleaved edges |
| `key_mono_family` | `T <= lo <= hi`, depth `< D` | the key retiming is monotone across tokens |

### The closed loop at trace level (`ChainCell`, `ChainBeh`)

- Wiring: stage `i+1`'s request pin reads stage `i`'s node; stage `i`'s acknowledge pin reads
  stage `i+1`'s node; stage `i+1`'s data pin reads stage `i`'s latch output. Each read goes
  through the pin's own read map, with the wire folded into the window. This matches
  `bd_link.v`: `req_out` and `ack_in` ARE the node when `DELAY = DACK = 0`.
- Only the source (request and data of stage 0) and the sink (acknowledge of stage `N-1`)
  are environment wires.
- Power-up of every node and latch is arbitrary (X included), as in LinkExact.

Hypotheses beyond Bzd/LinkExact, all named:

- **H_WIRE_POS**: every inter-stage read takes `>= 1 ps`. The reset phase needs a joint time
  induction over all stages (stage `i` reads `i±1` in its reset phase and vice versa), and
  that induction needs strictly earlier reads.
- **H_RST_SEEN**: `Rhi_nbr + pinHi <= W + Rlo`. A stage must still read reset high until its
  neighbours' nodes are surely read out of power-up. LinkExact's `Env.a_lo0` (request low
  for ALL `x < Ra`, power-up included) is NOT available in a closed loop, because the
  neighbour node is arbitrary before its own `Rhi`. That is why this hypothesis is new.
- **H_DATA_LOOP**: `Td_{i+1} >= U1_i + Ehi_i` and `>= Td_i + Dhi_i`. The next stage's data
  window starts when LinkExact's `Spec.out` guarantees the upstream latch output.

The high and low phases are plain inductions over the stage index:

- `hi_i` needs `hi_{i-1}` and `rst_{i+1}`;
- `lo_i` needs `lo_{i-1}` and `hi_{i+1}`.

### What H_CAUSAL needs, exactly

- In the closed loop, `Causal` holds at every interior stage from nonnegative reads alone.
  For example `Rb_i = U0_{i+1} = U0_i + Alo_{i+1} >= U0_i`.
- At the two ends it needs the environment's own causality, in the **lo form** (H_SRC,
  H_SNK). This is stronger than Bzd's `Causal`, which compares with `hi`: the network
  retiming needs every effect's window to START no earlier than its cause's.
- Bzd's weaker hi-form is not enough for a key retiming. Whether some other retiming works
  under only the hi-form is not decided.

## NOT covered / open

- **Goal 3 is partial.** C's `Link` for a k-token chain run is not proved: the train lemmas
  are there, the per-gate case analysis is not written. The physical k-token stage is not
  modelled either:
  - LinkExact's `Spec` is one token.
  - A second token needs the node to read the previous acknowledge fall before the next
    request rise. That is a cross-token race and not one of the six `bd_link.stage` rows
    (stated, not proved).
  - A multi-token latch capture is needed too, which `LibGapLatch.EnTok` (enable low forever
    after `C`) cannot express.
- Fork/join and the steer->mux diamond: only the general principle applies (key retiming plus
  that operator's order list). Their order lists and C-field proofs are not written.
- Rings (gcd_hw's loop needs initial tokens; the chain here starts empty).
- Zero-delay inter-stage reads: whether H_WIRE_POS is necessary is not decided.
- `DELAY`/`DACK` lines: the asymmetric FASTRISE line is covered only when lumped into a
  symmetric read window.
- A data bus wider than one bit, beyond "one `LutEq` per bit, shared node".
- Correlated corners (box form only).
