# B-steersafe: what the steer screen proves, assumes and checks (shard B, 2026-11-21)

**Problem, plainly.** A branch steer (`bd_steer`, cells `ucond_brN`) is a LUT that reads a request (from its join,
`ucond_brN_j`) and a condition (a loop test or branch predicate). If the request arrives while the condition is still
moving, the token goes the wrong way, or the steer's other output pulses. Research's rule E checks this on nextpnr's
SDF with a guard. `formal/tools-B/auto/steersafe.py` bounds it on the circuit decoded from the bitstream, for every
delay in the prjxray band up to a scatter kappa (g = 1). `racescreen.sh` runs it with simulations that try to break the
same race.

## The bound

For one steer, steersafe finds:

- **Launch nodes.** These are storage nodes whose rise starts both sides of the race. The condition comes from one of
  four kinds of source:
  - *A compare with a join* (`ucmpiK.ujoin`): one term per input link of the join, launched at that link's ctl. That
    link's operand latches are opened, their data pins are cut as roots, and other links' latches are left out
    (B27, 2026-11-20).
  - *A one-channel compare* (no join), or *any other compute's logic* (e.g. dot2's `uandi0`): the input link's ctl that
    its `.uor` reads, with the same opening.
  - *A link latch holding the condition* (`ulink_*.lat.*`). There are two kinds of term:
    - the latch's own ctl (the enable path: the latch opens and the request goes through the link's `rdly` and the
      steer's join; this is the latch-fed race of B21);
    - one term per input link of the compute that feeds the latch (B29 for joinless feeders, B30 for all; before
      B30 this term launched at the feeder's join with the operand latches counted settled there, which was unsound).
  - *No compute behind the latch*: the ctl term only.
- **Request bound R, a lower bound.** This is the longest forcing walk from the launch to the steer's request pin.
  Each hop is a pin that alone forces its gate to 0 (`ChainHold.chain_hold`), or a storage gate's pin that forces 0
  together with its feedback at 0 (`CtlChain.hold_mem`). The second case is a PREMISE: the storage node is 0 at the
  launch (four-phase return to zero), and it is listed. Minimum arcs are used.
- **Condition bound D, an upper bound.** This is the longest path of maximum arcs through the condition's backward
  cone (`SettleAll.settle_all`; an opened latch uses `ForceTree` with the pins its INIT reads while enabled). Roots
  are counted settled at the launch. That is a PREMISE: for cut latch data pins it is the input link's bundling, and
  for other storage it is that the storage is quiet. The cone must be acyclic, and the script checks it.
- **Per term:** kappa_lo = min over corners of (R - D) / (R + D), with both pins' arcs into the steer included. The
  steer's kappa_lo is the minimum over its terms (`SteerSettleMulti.steer_reads_settled_multi`: a slack on every
  term gives the settled read). The output form is `steer_out_forced(_multi)`.

**Lean** (all check.sh OK, standard axioms): SteerSettle, SteerSettleMulti, SettleAll, ForceTree, ChainHold, CtlChain.

**Untrusted:**
- the extraction: the decoded netlist, the cell names, which pin is the request and which the condition, and the
  launch found by name patterns;
- the arithmetic;
- the premises listed above.

## The checks that can fail (racescreen.sh)

- **weaksweep.sh**, the weakest steer's race-only adversary: that steer's condition cone is slow (S), its request
  walk fast (F), everything else at mid band. simx runs kappa 0 .. 0.20 at both corners, and the first kappa with a
  wrong answer or no verdict is reported. The bound must sit below this. Over 230 routes (B32-B35), none has its
  bound above its own adversary's first failure.
- **ctlsweep.sh**: the latch-fed race's own 32 nodes, as an adversary.
- **xtol.sh**: the weakest steer at research's bands with an opposite path error x on each side.
- **The host sample.** These checks must run with `DRAW_DOUT=23000` on CA_BENCHCAP routes (B31; racescreen's default
  since 2026-11-21). At the old 3 ns, false failures appear.

## Known gaps

- **Mux joins** (`umuxN.ujK`): `--mux` gives bounds too pessimistic to use. The join also waits for the data request,
  and that request has no common launch with the select.
- **The hold half:** the condition changing while the request is still high. A swapped adversary was screened on four
  routes and passed to 0.30, but nothing is proved.
- **Links' own captures:** rules H / I. Their Lean is SelectCapture / SelectHold, but nothing emits rows for
  research's routes.
- **Memory kernels:** decoded through shard C's memtask.sh. The adversary runs through the RAM boundary
  (`SIMX_EXTRA=--mem`); xtol and ctlsweep do not.

## What the census says (B32)

The latch-fed race's ctl-term kappa_lo predicts its adversary on all 32 distinct races of flow v10 / v11:
- at <= 0.125, 9 of 10 fail inside kappa 0.20;
- at >= 0.129, 1 of 22 does.
