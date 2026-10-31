# C probe 8c: the `bd_pipe` control chain at gate level (speed-independence)

## Verdict

**Works, at the finite-state level (option 2 of the brief), for 1 to 4 stages.
The trace-level version (option 1) was not attempted. That gap is described below.**

On the real chain (`bd_pipe` → `bd_link` → `bd_c2n` with its real INIT,
evaluated by shard B's `lutB`), with every LUT and every wire treated as a
node of unknown delay:

1. **The C-element by itself is not speed-independent** (`free_hazard_n1`,
   `free_hazard_n2`). If the O→I2 feedback wire is just another wire of
   unbounded delay, the LUT glitches. In each case the race is the feedback
   wire against the loop through a neighbour: the sink side for n = 1, the
   source side for n = 2. This is the C-element's timing condition, found
   mechanically as a hazard.
2. **With an isochronic feedback** (pin I2 reads O), the chain is hazard-free
   and obeys the four-phase protocol on every link. Tokens move in order. All
   other wires keep an unbounded delay. Proved for n = 1, 2, 3, 4 (`iso_good_n`).
3. **The feedback wire can also be a free wire if one relative-timing
   hypothesis holds, H_FB_BEFORE_INPUT:** no driver of a pin of `c_k` fires
   while `c_k`'s feedback is still in flight. The same result then holds.
   Proved for n = 1, 2, 3 (`rt_good_n`). n = 4 has 6076 states and was too
   heavy for the kernel here (see below).
4. **Trace corollaries hold for every execution** (stuttering is allowed, so
   any interleaving and any idling counts):
   - every link channel satisfies `Formal.Net.Handshake.Protocol` from probe
     8a (`run_protocol`);
   - consecutive stages satisfy `#c_k ≤ #c_{k-1} ≤ #c_k + 1`
     (`run_token_order`).

   The generic theorems hold for any n and take the per-instance `Good`
   invariant as their hypothesis. Instantiated: `iso4_protocol`,
   `iso4_token_order`, `rt3_protocol`, `rt3_token_order`.

## Files

- `formal/lean/Formal/Net/Muller.lean`: the model, the checker, and the
  soundness proofs (`inv_sound`, `check_sound`, `cert_sound`).
- `formal/lean/Formal/Net/MullerRun.lean`: executions as traces:
  `run_reach`, `get_fire`, `run_protocol`, `protocol_tog`, `run_token_order`.
- `formal/lean/Formal/Net/MullerSI.lean`: the instances: `free_hazard_n1/2`,
  `iso_check_1..4`, `iso_good_1..4`, `rt_check_1..3`, `rt_good_1..3`,
  `iso4_protocol`, `iso4_token_order`, `rt3_protocol`, `rt3_token_order`.
- `formal/lean/Wip/C8c/`: unfinished and unclaimed work.
  - `Gen.lean` prints the certificates.
  - `MullerCert.lean` holds the literal reachable sets for iso4, rt3, rt4
    and iso5.
  - `Rt4Cert.lean` is the chunked rt n = 4 attempt.
  - `Axioms.lean` contains the `#print axioms` calls.

## Check

    cd /home/user/asyncfpga3/formal && ./check.sh Formal/Net/Muller.lean Formal/Net/MullerRun.lean Formal/Net/MullerSI.lean

Result: `[check] OK`, with 434 declarations audited. There is no `sorry`,
`admit`, `axiom` or `native_decide`. `#print axioms` gives `propext` and
`Quot.sound`, plus `Classical.choice` on the token theorem (it comes from
`omega` and `simp`). Cost: `MullerSI.lean` takes about 190 s wall and about
6 GB peak RSS (one slot). The other two files take a few seconds each.

## Model

**Chain.** The chain is read from `cells/rtl/bd_link.v`: the default
`bd_link`, without `BD_LINK_DC`, chained by `bd_pipe`. Stage k consists of:
- `c_k = bd_c2n(I0 = r[k], I1 = a[k+1], I2 = c_k, I3 = rst)`, which is
  `C(r[k], ~a[k+1])`;
- `r[k+1] = bd_delay(c_k)`, with SDELAY = 1, i.e. one LUT1 `2'h2`;
- `a[k] = c_k`, since DACK = 0 is a bypass.

This is the Muller pipeline. The last stage's DELAY is modelled like a LUT1;
its delay is unknown in any case.

**Nodes.** One bit per node:
- `src`: a four-phase active source that toggles req when it sees req = ack;
- `snk`: a passive sink whose ack follows req;
- for each stage: `c k` (the LUT6), `b k` (the LUT1 plus the req wire),
  `w k` (the ack wire to the previous stage or the source), and `f k` (the
  feedback wire).

**Semantics.** The asynchronous interleaving of speed-independent theory:
any excited node may fire. This assumes nothing about any delay except that
it is positive and finite. Hazard = a node is excited, another node fires,
and the first node is no longer excited. The check covers all nodes,
environment included.

**Pair rules.** Each pair of `pairs n` has the form "X moves only when X = Y,
Y moves only when Y ≠ X". This is the same rule as SendStep/RecvStep in 8a.
The pairs checked are:
- (src, c0) and (src, w0);
- (c_{k-1}, c_k), (b_{k-1}, c_k) and (b_{k-1}, w_k) for each internal link;
- (c_k, b_k) and (c_k, w_k), which are wire persistence;
- (c_{n-1}, snk) and (b_{n-1}, snk).

**Method.** `check m n` is a Boolean function. It runs an in-kernel BFS (an
uncertified generator), then checks that reset belongs to the set, that the
set is closed under every enabled transition, and every per-transition
property. `check_sound` is the only proof the result depends on.
`decide +kernel` evaluates `check` in the kernel. Negative control: `#eval
check .free 1` and `check .free 2` both return `false`, so the checker can
fail.

**State counts.** These agree with an independent Python model in the
scratchpad:

| n | iso | rt | free |
|---|---|---|---|
| 1 | 18 | 26 | 48 (hazards) |
| 2 | 72 | 160 | 784 (hazards) |
| 3 | 288 | 986 | — |
| 4 | 1152 | 6076 | — |
| 5 | 4608 | 37442 | — |

## Fidelity of each primitive

**`bd_c2n` LUT6.** The model uses the real INIT `0x00B200B200B200B2`, the
real pin map, and `lutB` from `Formal.Cells.Prelim`. B's `c2n_spec` proves
this INIT equals C(a, ~b) with a clearing reset. The values are binary: no X
and no runts below the switching threshold. Because the result is
hazard-freedom, binary values are enough: hazard-free SI circuits produce no
glitches under pure or inertial delays. X and metastability are B's Kleene
results and are not needed here.

**The `rst` pin** is held at 0. The initial state is all-zero, which is
justified by `c2n_rst_forced` plus the wires settling during the reset pulse.
The reset release itself is not modelled.

**LUT1 buffer.** The model uses the real INIT `2'h2` via `lutB`.

**Wires and pips.** Each is a node with arbitrary positive delay. This is
more general than any `[lo, hi]` bound from prjxray, so all positive results
are conservative for routing. The exception is the feedback wire, which
needs the hypothesis below. The routing tree of a multi-load net is modelled
as an independent branch per load: `b`, `w` and `f` are separate nodes. That
is delay-insensitive on the forks: no isochronic-fork assumption is made
except, in iso mode, on the feedback branch.

**Environment.** The source and sink are idealised four-phase parties. A
real Dynamatic unit is not modelled here; 8a's `StageSpec` is the
assume-guarantee interface for that.

**Latch and data.** The latch and data path (bundling) are not modelled.
Probe 8a covers bundling.

## The C-element's timing condition, as it appears here

**H_FB_BEFORE_INPUT (rt mode).** A node that drives pin I0 or I1 of `c_k`
fires only when `f_k = c_k`. This is the discrete form of shard B's
`H_ENV_LATENCY` (`Formal/Cells/CElemTiming.lean`, `c2_four_phase`): after O
changes, the inputs must not move until the loop has captured the new value.

**Reduction to path delays (argued, not proved).** In this chain every input
change of `c_k` while `f_k ≠ c_k` is caused by `c_k`'s own transition. The
search shows the input pins cannot be excited concurrently, and the hazard
witnesses show exactly which paths compete. So the hypothesis follows from
two path-delay inequalities:

    dfb_max(k) < d_b(k)_min + d_c(k+1)_min + d_w(k+1)_min      (successor loop)
    dfb_max(k) < d_w(k)_min + d_c(k-1)_min + d_b(k-1)_min      (predecessor loop)

Here `d_c` is the LUT6 I→O delay, `d_b` is the LUT1 plus req route, `d_w`
is the ack route, and `dfb` is the O→I2 route. At the ends of the chain, the
neighbour term is replaced by the source's or the sink's response time.

**What these inequalities say.** The feedback route must be shorter than a
path of two LUTs and two routes. On 7-series that is plausibly a factor of
about 2, but it is NOT guaranteed by placement. Testable on routed SDF in
`cells/gls/`: extract the `q` net of every `bd_c2n` and compare it with the
two neighbour paths at the fast corner, over at least 4 seeds, as CLAUDE.md
requires. With `--ignore-loops`, nothing in the toolchain checks this today.
A verified timing checker (track 10) could check it exactly.

## What does not work, and why

**Trace-level proof (option 1), not done.** That would make every node a
`BoundedDelay lo hi` relation over `Nat → Bool`, take the inequalities above
as hypotheses, and prove the protocol for all traces. It would replace both
the interleaving abstraction and the informal reduction above. Two pieces
are missing:
- (a) an abstraction theorem: a circuit of `BoundedDelay`/`WinDelay` gates
  whose excitations are never withdrawn behaves as an interleaving of the
  transition system, so `Good` transfers to traces. Simultaneous firings in
  one tick need a "step = set of non-conflicting nodes" lemma; that is
  harmless here because no two nodes share a pin.
- (b) the derivation of H_FB_BEFORE_INPUT from the path-delay inequalities,
  in the style of B's `c2_four_phase`.

Estimate: 2 to 4 days of Lean for (a) and (b) on a generic n. It could reuse
B's `CElemTiming` loop lemmas.

**rt, n = 4 (6076 states).**
- The in-kernel BFS ran out of the 15 GB of memory.
- The literal-certificate checker (`cert_sound`, which is proved, with the
  data in `Wip/C8c/MullerCert.lean`) works, but each 1/8 chunk takes about
  166 s and 7.5 GB. So the full instance needs about 25 minutes of kernel
  time in 8 or more theorems. It was not completed (`Wip/C8c/Rt4Cert.lean`).
- A micro-benchmark shows that kernel `decide` scales super-linearly even for
  `List.contains` over `List.range` (100 → 0.17 s, 400 → 1.6 s), so the
  bottleneck is kernel reduction, not the model.
- Fixes, untried:
  - (i) prove n ≥ 4 from n = 3 by an inductive "stage cut" argument: the
    chain is a cascade, and 8a's assume-guarantee `pipeline_protocol` does
    this at protocol level;
  - (ii) a compiled checker with `native_decide`, which is forbidden by
    PROGRAM.md;
  - (iii) an external SI checker (Petrify, MPSat, or track 12), whose output
    would serve as a certificate.

**Generic n.** Generic n is proved only for the trace corollaries, which are
conditional on `Good`. Hazard-freedom is proved per instance up to n = 4
(iso) and n = 3 (rt). By the cascade argument it most likely holds for all
n, but that is not proved.

## What it buys the project

- **A gate-level, real-INIT result about the control chain the cells
  actually form.** The four-phase protocol of probe 8a is now DERIVED from
  LUTs for small n, instead of assumed per stage.
- **A sharp statement of the only timing condition the default link
  control needs.** Every other wire may have any delay. The condition is the
  feedback route against two neighbour loops, and it is testable on routed
  SDF.
- **A reusable, proved-sound pattern for other cells' control networks**
  (fork/join trees, `bd_link_dctl`, merge): give the node functions as
  `lutB INIT pins`, the checker and its soundness are generic in the node
  function, then `decide +kernel`. Its practical limit in the kernel is about
  1–2 thousand states per theorem.

## Surprises

- In the free-feedback model a hazard appears already at n = 1. The
  shortest witness is 4 transitions long: `src↑ c0↑ b0↑ snk↑`, then `c0`
  falls. A real `bd_link` whose sink answers faster than the C-element's own
  feedback route would emit a runt on `ack_in`.
- Kernel `decide` cost is dominated by kernel reduction overhead, not by the
  size of the state space (see the benchmark above).
