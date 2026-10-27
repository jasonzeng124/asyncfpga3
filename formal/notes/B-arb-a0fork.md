# B probe 7g: the A0 fork of bd_arbiter (H_A0_FORK)

File: `formal/lean/Formal/Cells/ArbA0Fork.lean` (459 lines, core Lean, imports
only `Formal.Cells.Prelim`; no new shared defs, local `cel`, `F1/F2`, `G1/G2`,
`Dl`, `Run`, `ATr`, `ite_t/ite_f/dite_t` live in the file).

Check (clean, about 2 s, no output, no warnings):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbA0Fork.lean

`#print axioms` (run with temporary `#print` lines, since removed) on
`client{1,2}_{iff,counter,latches,box}` and `run_exists`: only `propext`,
`Quot.sound`, and (for the `iff`/`box` theorems) `Classical.choice`. No sorry,
admit, axiom or native_decide in the file.

## Claim settled

Probe 7b found that `sc_a0_fall_skewed` ends with A2 = x. This probe answers it
exactly. When A0 falls with client 2 waiting (r1 = 0, r2 = 1, q held at 1),
ustate resets q, ugrant raises g2 = r2.~q (O6), and ua2 = C(g2, A0) acknowledges
client 2 early **iff** the A0 branch into ua2 is slower than the chain
A0 -> ustate -> q -> ugrant -> g2 -> ua2. Client 1 is the mirror image:
r1 = 1, r2 = 0, q held at 0, q is set, g1 = r1.q on O5, ua1 = C(g1, A0).
The condition and the proofs are identical; only the INIT facts differ.

## Model (gate relations, `Run`)

Time `Nat` (1 tick = 1 ps). Each LUT is a per-pin transport-delay LUT. The
function sees pin i's net delayed by its route plus the pin's site-pin
(input buffer) delay, and the output follows the function by the cell's output
arc. Every gate uses the REAL INIT through `lutB/o5B/o6B`:

* `ustate` 64'hFFF0_FFB2_ACAC_ACAC: (I0 r1, I1 r2, I2 q, I3 rst, I4 A0, I5 1) -> O6 q.
* `ugrant` 64'h0C0C_0C0C_A0A0_A0A0: O6 g2, O5 g1.
* `ua_k` = `bd_c2` 64'h00E8_00E8_00E8_00E8: (I0 g_k, I1 A0, I2 own output, I3 rst).

INIT lemmas (by `decide`): `cel_eq` (ua = maj(g, A0, fb) with rst = 0),
`F2_hold`/`F1_hold` (A0 = 1 holds q), `F2_go` (A0 = 0, r1 = 0, r2 = 1 -> q = 0),
`F1_go` (A0 = 0, r1 = 1, r2 = 0 -> q = 1), `G2_vals`, `G1_vals`.

Named hypotheses (fields of `Dl` and `Run`, each with a doc comment):

| name | meaning | where the number comes from |
|---|---|---|
| H_A0_SHARED `c` | A0 route from the driver to the divergence point | routed JSON route tree (arb_fork.py's `shared_ps`) |
| H_W_A0_ST `wSt`, H_P_A0_ST `pSt` | A0 branch into ustate, and its pin's site delay | SDF INTERCONNECT; prjxray site-pin table |
| H_ARC_ST `aSt` | ustate output arc (fall for client 2, rise for client 1) | prjxray CLBLL_L.sdf |
| H_W_QFB, H_P_QFB | ustate's q feedback | SDF |
| H_W_QG `wQG`, H_P_QG `pQG`, H_ARC_G `aG` | q route into ugrant, its pin, ugrant's RISING arc | SDF, prjxray |
| H_W_GC `wGC`, H_P_GC `pGC` | grant route into ua_k, its pin | SDF, prjxray |
| H_W_A0_C `wAC`, H_P_A0_C `pAC` | A0 branch into ua_k, its pin | SDF, prjxray |
| H_ARC_C `aC`, H_W_CFB, H_P_CFB | ua_k's arc and feedback | SDF |
| H_A0_FALL, H_T0 | A0 falls once, at T0 > 0, and stays low | protocol |
| H_Q_INIT, H_A_INIT | q holds the previous winner, A_k = 0 before | protocol (7b `sc_a0_fall_*`) |
| H_LOOP_ST, H_LOOP_UA | both feedback loops have positive delay | a routed wire (>= 295 ps on nextpnr) |
| H_REQ_STEADY (prose) | r1, r2, rst steady through the window | protocol: client k waits for A_k; the other client cannot re-request before its ack falls |
| H_DELAY_BOX (`box_safe_iff`) | every delay lies in [lo, hi] | prjxray fast-min / slow-max, or SDF x guardband |

Each net makes at most one transition in the scenario (`q_trace`, `g_trace`,
H_A0_FALL). A per-edge (rise/fall) transport delay is therefore exactly a fixed
delay whose value belongs to the edge exercised.

Define (past the shared prefix, without ua_k's arc):

    late  = wAC + pAC
    early = wSt + pSt + aSt + wQG + pQG + aG + wGC + pGC

## Theorems (namespace `Formal.Cells.ArbA0Fork`)

* `q_trace`: q = old value until T0 + c + wSt + pSt + aSt, then the new one.
  `g_trace`: the grant rises once, at T0 + dS + dG.
* **`no_early_ack_iff`** (generic), **`client2_iff`**, **`client1_iff`**: for
  every run of the gate relations, A_k never rises <-> `late <= early`. Both
  directions. The knife edge is `late = early`: equality means A0 is already
  low on the tick the grant arrives. The shared prefix `c` and ua_k's own arc
  `aC` cancel.
* **`early_ack_at`**, `client{1,2}_counter` (the counter-trace): if
  `early < late`, then A_k = 1 at exactly T0 + aC + c + early.
* **`early_ack_latches`**, `client{1,2}_latches`: if the overlap is at least
  one ua_k loop (`early + dCf <= late`), then A_k is 1 from that instant on,
  for ever. The false ack latches; it is not a glitch. A shorter overlap gives
  a transport-model runt, which is the C-element's own behaviour
  (CElemTiming's runt results). Inertial filtering could swallow it, which
  this model does not claim.
* `run_exists`: the relations are satisfiable for every parameter set
  (ua_k's trace is built by well-founded recursion, `ATr`). So the "for all
  runs" statements are not vacuous.
* **`box_safe_iff`**, `client{1,2}_box`: if every delay is only known to lie in
  `[lo, hi]` (with lo <= hi and both loops positive at lo), then no run with
  delays in the box acknowledges early <-> `hi.late <= lo.early`, i.e.
  max(A0 -> ua_k pin) <= min(chain). Both directions. The "only if" direction
  uses `run_exists` at the worst corner `worst lo hi`. Rule J (arb_fork.py) is
  this theorem with lo = 0.772 x SDF and hi = 1.155 x SDF on the unshared
  part. `c` drops out, which justifies its shared-prefix credit exactly,
  provided `c` really is one wire.

## Numbers (part 2)

**Which pins.** Logically A0 is ustate.I4 and ua_k.I1 (bd_c2 `b`), q is
ugrant.I2, and g_k is ua_k.I0. Physically nextpnr-xilinx permutes LUT inputs
freely (`PIP_LUT_PERMUTATION` pseudo-pips, patches/README.md; tighten.py reads
`X_ORIG_PORT_A<k>`), so the physical pin is chosen per route. The identity map
would put A0 on ustate A5 and ua_k A2, q on ugrant A3, and g_k on ua_k A1.
Constraints: ustate and ugrant are LUT6_2 with I5 = 1, so their A6 is tied
high and A0/q land on A1..A5. ua_k is a 4-input LUT6 and may use A6. The
router's chipdb gives every LUT pin the same delay, so the choice is
effectively arbitrary. No routed JSON or SDF is on disk in this container (the
toolchain is absent), so the pins of any real route could not be read. The
survey rows (`research/data/ruleJ_survey/rows.json.gz`) do not record them.

**Delays used** (prjxray-db, ns, [fast min, slow max]):
* Site-pin (input buffer + select), `tile_type_CLBLL_L.json` (from
  B-muxtree-fidelity.md): A1 0.172-0.516, A2 0.170-0.507, A3 0.107-0.344,
  A4 0.086-0.284, A5 0.033-0.112, A6 0.002-0.005.
* LUT arcs, `CLBLL_L.sdf`: O6 rise 45-56 ps, fall 100-124 ps; O5 rise 42-61 ps.
* nextpnr's SDF (what rule J reads) has a flat 124 ps for every LUT arc, a
  flat 25 ps per site pip, and no per-pin site delay (TOOLING.md;
  research/PROGRAM.md).
* Routes: the same-slice O6 -> A hop is 295 ps on the patched nextpnr; the
  next tile is 426-576 ps. Rule J survey (168 routes, 1562 arbiter x client
  rows): raw early - late min +618 ps, median +1188 ps. Guarded min -103 ps
  (2 violations, isprime, long A0 nets).

**Where the margin comes from.** early - late = (A0 branch divergence) + ustate
arc + q hop + ugrant arc + grant hop + pin terms. With the arbiter's four LUTs
in one slice and A0 splitting at it, the two extra routed hops (2 x ~295 ps)
plus two arcs (145-180 ps for client 2, 87-117 ps for client 1) give about
+0.7-0.8 ns. That matches the survey median. **This ordering is safe by
routing, not by construction.** The early side always contains two more routed
hops than the late side. Nothing structural stops the A0 branch into ua_k from
being long (the survey's tail is exactly the long-A0 routes).

**What rule J does not see** (corrections to its raw margin, true minus rule J):
1. LUT arcs. Rule J counts 124 ps for ustate and for ugrant. True: client 2
   is ustate fall + ugrant O6 rise = 145-180 ps, so -68 to -103 ps. Client 1
   is ustate rise + ugrant O5 rise = 87-117 ps, so -131 to -161 ps. ua_k's
   arcs cancel (theorem: `aC` drops out), and rule J's equal flat values
   cancel too.
2. Site-pin delays, which are absent from nextpnr's SDF. The correction is
   (pSt + pQG + pGC - pAC) - (3 - 1) x 25 ps. Worst pin assignment: A0 on
   ua_k's A1, everything else on the fastest legal pin (A5, A5, A6).
   * Same slow corner: 112 + 112 + 5 - 516 - 50 = -337 ps.
   * Box (fast-min early, slow-max late): 33 + 33 + 2 - 516 - 50 = -498 ps.
   * Best assignment (A0 on ua_k's A6, the rest on A1): about +1.4 ns.

   So the unmodelled pin term spans roughly -0.5 ns to +1.4 ns.
3. Totals in the worst case:

   | case | slow corner | full box |
   |---|---|---|
   | client 2 | -405 ps | -601 ps |
   | client 1 | -468 ps | -657 ps |

   Against the tightest raw margin ever seen (+618 ps), that leaves about
   +150 ps at a consistent slow corner and about 0 in the box. At the survey
   median (+1188 ps) about +0.7 ns remains.

**Verdict on risk.** It is real but bounded: a timing dependency of the same
order as the uncertainties that rule J does not model, not a defect seen on
any nominal route. The 7b finding stands: the ack-hold fix needs H_A0_FORK.
GLS has already shown it failing. Under delay scatter, and with ua2's arcs
x2.5, gcd_hw deadlocked by exactly this mechanism, and the raw sign predicted
GLS in 4/4 cases (research/JOURNAL.md, rule J entries). That raw sign is
precisely `no_early_ack_iff`'s condition.

## Do the project's post-route rules check it?

Yes, partly. `cells/verify/arb_fork.py` (rule J, commits ff52ded, f64b63f) is
wired into converge.sh and tighten_loop.sh. A failure makes the build NOT
SHIPPABLE. It computes late = A0 -> ua_k + ua_k A0-arc and early = A0 ->
ustate + ustate arc + q -> ugrant + ugrant arc + g_k -> ua_k + ua_k g-arc,
guarded 0.772 / 1.155 past the shared prefix. That is `box_safe_iff`
instantiated on nextpnr's SDF. tb_arb and the sim prims do not exercise it:
the testbench's A0 is one reg, and BD_ROUTE_PS is uniform, so the late branch
carries no extra wire. skew.py and tighten.py do not look inside the arbiter.

**Proposed refinement (rule J'), precisely.** For each bd_arbiter and client
k, with physical pins as arb_fork.py already resolves them (the routed
JSON's connections are physical A1..A6):

    late_hi  = 1.155 * (IC(A0 -> ua_k.PA) - c) + SP_hi[PA] - 25
    early_lo = 0.772 * ((IC(A0 -> ustate.PS) - c) + IC(q -> ugrant.PQ) + IC(g_k -> ua_k.PG))
             + SP_lo[PS] + SP_lo[PQ] + SP_lo[PG] - 3*25
             + ARC_lo(ustate, O6, fall if k = 2 else rise)
             + ARC_lo(ugrant, O6 rise if k = 2 else O5 rise, pin PQ)
    pass iff early_lo - late_hi > 0

* `SP_lo/SP_hi[A_i]`: prjxray-db `tile_type_CLBL{L,M}_{L,R}.json`
  site-pin delay, fast-min and slow-max.
* `ARC`: prjxray `CLBLL_L.sdf` / `CLBLM_*.sdf` per pin, fast-min.
* Drop ua_k's IOPATH from both sides: it is common (the theorem). With nextpnr
  it cancels anyway, but a future per-pin SDF that folds site delays into the
  IOPATH must then keep both sides' ua_k arcs instead of the SP terms.
* The `- 25` removes nextpnr's flat site pip, if the INTERCONNECT includes it.
  Check that against one routed SDF before relying on it.

A quick screen that needs no prjxray file: flag any row where A0 lands on
ua_k's A1/A2 and the raw margin is < 600 ps.

## What did not work / not done

* The real pins and per-hop numbers of a routed bd_arbiter could not be read.
  There is no routed JSON or SDF and no toolchain in this container, so the
  pin-dependent figures above are bounds over assignments, not measurements.
  To finish: run the rule J' arithmetic over the 168 survey routes (needs the
  routed JSONs again).
* The model is transport delay. Inertial rejection of a short overlap (GLS
  prims) is not modelled. Positive results do not depend on it; the latch
  theorem needs overlap >= one ua_k loop.
* There is no metastability or slow-edge model: an A0 edge is instantaneous at
  each pin. Kleene/analog behaviour is 7b/7c.
* The requests are folded into F/G under the prose hypothesis H_REQ_STEADY,
  which is not proved from the clients' protocol.

## Verdict

**Works.** Both directions of the exact condition, the counter-trace, latching,
non-vacuity, and the interval (worst-corner) form are proved for both clients
on the real INITs, in core Lean in about 2 s.

* Effort to finish: about 0.5 day to evaluate rule J' over existing routes once
  routed JSONs are available. About 1-2 days to lift the transport model to
  the WinDelay (varying-delay) channel of CElemTiming. Positive direction only;
  monotone, so routine.
* What it buys:
  1. The obligation is the exact condition, not just a sufficient one, so rule
     J's raw sign is the right test.
  2. The shared-prefix credit and the cancellation of ua_k's arc are justified.
  3. Two concrete gaps in rule J are named: per-pin site delays (up to about
     0.5 ns, the same order as the smallest observed raw margin) and flat
     124 ps arcs (biased unsafe by 68-161 ps). Both bias rule J optimistic.

## Fidelity per primitive

* LUT (ustate, ugrant, ua_k): the binary INIT via `lutB/o5B/o6B` with the RTL
  pin map. Timing is per-pin transport: site-pin delay per physical pin plus
  one output arc, which is the SDF IOPATH model refined by prjxray's site-pin
  table. It is exact for binary single-transition scenarios. It ignores the
  mux-tree level dependence of glitches (the scenario has no hazards on these
  LUTs, since each output moves once) and X/metastable inputs (probe Bf, 7b).
* Feedback wires (ustate q, ua_k): fixed positive transport delays. Only
  positivity is used.
* Fork (A0): one shared segment `c` plus two independent branches. `c`
  cancels exactly. Branch delays are independent within their intervals.
* Tied pins (rst = 0, I3..I5 constants): definite rails.
* Requests r1/r2: constant through the window (H_REQ_STEADY).
