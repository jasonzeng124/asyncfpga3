# `cells/` — the four-phase bundled-data primitive library

Built to the Stage 0 cell library design review, on xc7z010clg400 (EBAZ4205)
through openXC7. The review is frozen; where the library disagrees with it,
the disagreement is written up in the cell's own header and listed under
**Findings** below — nothing was quietly changed.

Every cell is instantiated LUT primitives. There is no inferred logic anywhere
in `rtl/`, because the whole point of the review is a specific LUT count and
you cannot hit a specific LUT count by describing behaviour and hoping.

---

## Layout

| Path | What it is |
|---|---|
| `rtl/` | the library. Nothing else in the tree is synthesised. |
| `sim/bd_prims_sim.v` | LUT/BUFG/RAMB18E1 models with real prjxray `specify` arcs |
| `sim/bd_env.v` | four-phase source, sink, and the protocol monitor |
| `tb/` | one bench per cell family |
| `verify/inits.py` | derives and exhaustively proves every LUT constant |
| `verify/lutcost.py` | synthesises each cell alone, checks its LUT count |
| `verify/tighten.py` | post-route bundling audit and matched-delay sizing |
| `verify/teeth.sh` | rebuilds the soak design with a delay removed, requires the sizing pass to catch it |
| `verify/resize.sh` | applies the sizing, re-routes, keeps only what survived |
| `verify/soak_top.v` | one of everything, for place-and-route |
| `verify/probes/` | the measurements the cell headers quote, re-runnable |
| `verify/attempts/` | derivations that did not work, kept with the evidence |
| `verify/MTBF.md` | the hardware experiment `bd_arb.v` refuses to do without |
| `hw/` | the eighth gate, and the only one that runs on silicon |
| `run_sim.sh` | the simulation gate |
| `flow.sh` | the place-and-route gate |
| `check.sh` | all of them, in order |

## The gates, and what each one does not prove

`./check.sh` runs all of them. They are ordered weakest-claim to
strongest-claim and no two overlap:

```
python3 verify/inits.py --check-rtl     # the constants
./run_sim.sh                            # the protocol, arc-only timing
BD_ROUTE_PS=354 ./run_sim.sh            # the protocol, routed-estimate timing
python3 verify/lutcost.py               # the cost
./flow.sh                               # packing, placement, routing
python3 verify/tighten.py               # the bundling constraint, as routed
./verify/teeth.sh                       # and that that gate can fail
```

Two things are deliberately *not* gates. `verify/probes/run.sh` re-derives the
picosecond figures quoted in the cell headers — run it after touching anything
timing-related, or those write-ups quietly stop being true. `verify/resize.sh`
is a design activity, not a check; see below.

**`verify/inits.py`** states every LUT function as a Python lambda plus a pin
order and *computes* the INIT from it, then re-reads that INIT the way silicon
addresses it, on all 2⁶ rows. 1560 rows across 30 cells. The six constants the
review states independently are checked against the computed ones, so a drift
between the library and the review shows up here first. `--check-rtl` audits
the other direction: every hexadecimal literal in `rtl/` must be one of the
proved constants, so a number nobody derived cannot reach a LUT.

*Does not prove* that the cell built from those constants does anything useful.

**`hw/`** is outside the seven and above them. Every gate below is a statement
about the toolchain — that yosys emits the cells, that nextpnr routes them,
that the SDF is consistent with itself. None of them asks whether the SDF is
*true of the die*, and every matched delay in this library is sized against it.
`hw/ro_measure.py` puts five ring oscillators of different lengths on an
EBAZ4205 and compares each one's measured period against its own routed
prediction. Measured 2026-08-03: **measured = 0.975 x predicted across an 18x
span of length**, every ring faster than predicted, residual 8.5% with no trend
in length. The sizing pass rests on a model that is good to about a tenth and
errs long. See `hw/README.md`.

**`run_sim.sh`** runs ten benches against models carrying prjxray's own arcs
— `CLBLL_L.sdf` for the LUTs (6LUT 56/124 ps, 5LUT 55–60 rise, 118–152 fall)
and `BRAM_L.sdf` for the RAM (t_su 566/737/532 ps, t_co 2454 ps). Every channel
in every bench carries a `bd_monitor` asserting the four-phase order, that no
new request precedes the acknowledge falling, and that data is stable across
the whole hold window `req↑ → ack↓`.

`BD_ROUTE_PS` adds a per-arc routing figure. Zero is arc-only, which is where
the library is most fragile; 354 ps is the routed-hop estimate. **Both must be
green** and they are not the same test — one arbiter ordering only holds in the
second, and `tb_arb` says so out loud.

*Does not prove* anything about routed silicon. Simulation drives the protocol
perfectly and cannot show you a bundling failure, with exactly one exception:
`tb_mem`, where the RAM model enforces the vendor setup windows and an
undersized matched delay is a message in the log.

**`verify/lutcost.py`** synthesises each cell on its own and compares the LUT
count against the review's packing and cost tables. 29 cases, all matching. A
`LUT6_2` counts once, because it is one site — that is the claim the whole cost
model rests on.

*Does not prove* that the design places or routes.

**`flow.sh`** puts one design containing every cell through yosys and
`nextpnr-xilinx` onto the real chipdb, and checks the FASM. It is the only
gate that exercises three load-bearing toolchain properties: the
`split_lut6_2` packer patch (without it a stock nextpnr fails on the first
fractured cell with *no wire found for port O5*), `--ignore-loops` (every
C-element and latch here is a LUT feedback loop, and the loop *is* the storage
element), and `-noclkbuf` (yosys inserts a global buffer on anything reaching
a clock pin, and `bd_mem`'s manufactured edge reaches one — about two
nanoseconds landing on a path a matched delay was sized against, invisible in
simulation). The FASM is checked for occupied LUT sites tracking cell count,
and for the absence of any global clock buffer.

*Does not prove* timing — but it writes the SDF that does.

**`verify/tighten.py`** is the post-route pass. It reads nextpnr's routed SDF,
where the interconnect delays are the delays of the routes actually chosen
(434–945 ps a hop on this build), and checks three things:

- **the request is the last thing its cell emits** — the general form of
  `z_req = Δ(…)`, with the review's `guard = max(0.2·t_data, 200 ps)`;
- **the RAM boundary**, the only edge-sampled boundary in the library, against
  prjxray's own setup windows rather than a percentage;
- **clock-to-out**, that the acknowledge trails the read data by `t_co`.

A setup check needs the late signal on its *shortest* path and the early one on
its *longest*, both from a **common start point confined to the cell** — a
matched delay covers logic inside one cell's datapath, and measuring from a
distant state node inflates `t_data`, inflates `0.2·t_data` with it, and turns
every line in the design into a false violation. The netlist is not a DAG
(every C-element and latch is a loop), so any pin on a cycle is treated as a
state node and traversal starts and stops there — which is exactly the
four-phase model, one hop per phase.

It reports what each placeholder should become **for that route and no other**.
A line that needs to *grow* is not a sizing result and the tool says so: that
is a bundling violation, and the answer is to re-place or shorten the datapath,
not to pad.

On this build it reports `bd_merge`'s `DELAY(4)` — the artifact's default — as
**already exact**, with 213 ps of margin over a 342 ps guardband. `bd_mux`'s
and `bd_dr2bd`'s want tightening. The RAM boundary clears its address setup by
1615 ps and its clock-to-out by 1674 ps.

`verify/teeth.sh` is what makes that result mean anything: it rebuilds the same
design with `bd_merge`'s delay set to `DELAY(0)` — which `bd_delay` renders as
a bare wire, leaving nothing in the netlist to find — routes it, and requires
the sizing pass to fail. It does, at −1133 ps. An earlier version of the pass
discovered work by looking for delay chains, so the one configuration
guaranteed to violate the constraint was the one it could not see; that is why
this script exists.

*Does not prove* silicon timing. **Nothing here does.** Interconnect delays are
real, but the cell arcs are nextpnr's flat 124 ps model, not the per-pin
prjxray arcs the simulation uses.

## Sizing the matched delays, and why it is a search

`verify/resize.sh` closes the loop: apply what `tighten.py` measured, re-route,
and keep the change only if the design still passes.

The obvious version of this does not work, and the reason is worth stating.
The recommendation is the *smallest* length meeting the guardband, so applying
it leaves essentially zero margin by construction — and applying it also
changes the netlist, which moves the placement, which changes the routing the
recommendation was measured against. Run naively, round 1 proposes `UMUX 4→0`
and `UMEM_UCO 12→8`; round 2 then reports umux at **−485 ps** and the memory's
clock-to-out at **−59 ps**. The proposal was right about the route it saw and
wrong about the route it caused.

So the script proposes one change at a time, re-routes, and reverts anything
that stops checking out. It terminates because lengths only decrease and are
bounded below by zero. On this design:

```
baseline (placeholders)   UDEC=4 UMERGE=6 UMUX=4 UMEM_USETUP=8 UMEM_UCO=12
verified assignment       UDEC=16 UMERGE=4 UMUX=2 UMEM_USETUP=2 UMEM_UCO=9
                          4 sweeps, 25 place-and-route runs
```

**Four of the five lines could be tightened at all; seventeen of twenty-four
proposals were reverted.** That is the result worth keeping: on this fabric and this
router, a matched delay cannot be shaved close to its measured requirement,
because the act of shaving it perturbs placement by more than the margin the
measurement claimed. Budget matched delays conservatively and do not expect
the toolchain to recover the slack.

Measured lengths are opt-in — `BD_SIZES=build/resize/sizes.vh ./flow.sh`.
Nothing picks them up automatically, so a bare `./flow.sh` is always the
placeholder build and you always know which design you just checked.

---

## The cells

| Module | File | Cost | Review section |
|---|---|---|---|
| `bd_c2` `bd_c3` `bd_c4` | `bd_ce.v` | 1 LUT | C-element |
| `bd_c2_set` `bd_c2n` `bd_c2n_set` | `bd_ce.v` | 1 LUT | Reset |
| `bd_ctree #(N)` | `bd_ce.v` | ⌈N/4⌉-ish tree | fork/join fan-in |
| `bd_latch #(W)` | `bd_latch.v` | ½ LUT/bit | Storage |
| `bd_latch_rst #(W)` | `bd_latch.v` | 1 LUT/bit | Storage — resettable |
| `bd_delay #(N)` | `bd_latch.v` | N LUTs | Matched delay |
| `bd_datamux #(W)` | `bd_latch.v` | ½ LUT/bit | packing table |
| `bd_link_ctl` | `bd_link.v` | 1 LUT/stage | Pipeline link |
| `bd_link #(W,DELAY,DACK)` `bd_pipe #(W,N,DELAY,SDELAY,DACK)` | `bd_link.v` | 1 + W/2 per stage, plus its delay lines | Controller family |
| `bd_fork #(N)` `bd_join #(N)` | `bd_ctl.v` | 1 LUT to fan-in 4 | Duals |
| `bd_steer` | `bd_ctl.v` | 2 LUTs | Steer |
| `bd_bd2dr` | `bd_ctl.v` | 1 LUT | Protocol converters |
| `bd_dr2bd #(DELAY, HOLD)` | `bd_ctl.v` | 1 LUT + delay, either way | Protocol converters |
| `bd_merge #(W,DELAY)` | `bd_merge.v` | 4 + delay + W/2 | Merge |
| `bd_mux #(W,DELAY)` | `bd_mux.v` | 5 + delay + W/2 | Mux |
| `bd_arbcell` | `bd_arb.v` | 2 LUTs | Arbitration cell |
| `bd_arbiter` | `bd_arb.v` | 4 LUTs | Arbiter |
| `bd_mem` | `bd_mem.v` | 2 delays + 1 buffer + BRAM | Memory port |
| `bd_src #(W,VAL)` | `bd_end.v` | 1 LUT (`req = ~ack`) | — added since |
| `bd_snk #(W)` | `bd_end.v` | free (`ack = req`) | — added since |

Two cells carry a risk note in their own header and you should read it before
using them: `bd_arb.v` (**this is not a mutex** — the decision element is
buildable in one LUT, the analog metastability filter is not buildable at all,
so the failure rate has to be measured on hardware and nothing in this tree
discharges that) and `bd_mem.v` (the request manufactures a clock edge).

---

## Findings

Three places where the library and the frozen review disagree. All three are
built **as the review specifies** by default; each fix is an opt-in parameter,
and each is measured by a bench rather than argued.

1. **`bd_dr2bd`: the spacer eats the data.** `d = t` releases the payload one
   whole phase before the bundled hold window closes, because `ack_dr` *is*
   the bundled `ack`, so the dual-rail sender drops its rails while the
   consumer's latch is still transparent. Any latch consumer captures zero.
   `tb_conv` measures 12 hold-window violations in 24 transactions on the
   specified cell and 0 with `HOLD(1)`. The fix is `d = C(t, ~f)`: the spacer
   is the code on which a C-element holds, so the decode holds itself. It
   **costs nothing** — the decode and the request OR share four inputs between
   them and fit one fractured LUT6_2, which is the same one LUT the review
   budgets. An earlier version of this note claimed +1 LUT for an ack-gated
   latch; that latch was both dearer and weaker, since it reopens at `ack`-fall
   with the rails already at the spacer and so clears the payload on the very
   edge it exists to protect. The C-element holds until the next *valid* code,
   a full phase later.

2. **`bd_arbiter` does not meet `bd_merge`'s precondition.** The merge requires
   that no second input asserts until the first transaction has fully
   completed; exclusive grants are weaker than that, and an arbiter under
   sustained contention gives the opposite. `q` flips during the *other*
   client's return-to-zero, so `g2` rises while `A0` is still high and
   `C(g2,A0)` fires immediately. `tb_arb` measures 80 client acknowledges
   against 40 server transactions — half of them manufactured. The cell now
   freezes `q` while `A0` is high, unconditionally: 80 against 80. `A0` is one
   more pin on a node whose partner function already uses the pins it needs, so
   it is **the same four LUTs**, a different constant. This is the one cell
   that ships fixed rather than as specified — its consumer is a compiler, and
   an opt-out defect is a defect that ships.

3. **`bd_link` / `bd_pipe`: the request outruns its own data.** Structural, not
   a sizing error: `req_out` is the C-element node itself while `data_out` is
   that node through a latch. Measured at 152 ps for one stage and 441 ps for
   four — the lead grows with depth, because filling an empty pipe sets off a
   control wave that hops faster than the data wave ripples. A real violation
   at any edge-sampling boundary (`DELAY` pads `req_out`; default 0, the
   review's exact cost) — and, it turned out, inside a pipe being filled
   behind a fast source: the closing wave gains on the data wave at every
   stage, so `bd_pipe` now carries a one-element `SDELAY` request line on each
   internal boundary (rule I sizes it post-route). The mirror image is on the
   acknowledge: the node reaches its last latch enable ~1 ns after its first
   on a routed 32-bit link, while `ack_in` is already telling the sender to
   release. `DACK` holds the *fall* of `ack_in` back (rule H sizes it); the
   rise is untouched. Routed GLS of the fused xorshift kernel corrupted two
   bits of token 1 before this and passes after it.

Two smaller inconsistencies inside the review itself, resolved in favour of the
majority reading and noted here rather than in the RTL:

- Fork/join fan-in: one caption says five, the in-figure caption and the
  C-element section say four, and 6 pins − feedback − rst = 4. Built to four,
  with `bd_ctree` chunking in fours beyond that.
- Merge acknowledge pair: one cost row says "1 (shared)", contradicted three
  times elsewhere (packing table, figure caption, reset section) — and it must
  be two, because each C-element needs `rst`, making six distinct pins. Built
  as two.

---

## An attempt at the semi-decoupled controller, and why it is not in `rtl/`

The review names a semi-decoupled controller in its family table — *1
token/stage, breaks DV* — and says plainly it was specified by what it must
achieve and never derived. `verify/attempts/bd_semi_attempt.v` is an attempt at
that derivation. **It does not work**, it is outside `rtl/` for that reason, and
it is kept because the way it fails is worth knowing.

The idea was to split the simple controller's one overloaded node in two:

```
L = ~rst . C(Rin, ~R)     latch enable, and the acknowledge
R = ~rst . C(L,  ~Aout)   the outgoing request
```

Two things it got right:

- **The occupancy is real** — a four-stage pipe holds four tokens against the
  simple controller's two.
- **The cost is real, and it is a pretty result.** `L` and `R` touch
  `{Rin, L, R, Aout, rst}` — five pins, one fractured LUT6_2 a stage — and the
  constant that falls out is `64'h0000_C0FC_0000_8E8E`, **bit for bit the
  constant the since-removed `bd_link_pair` used for two adjacent simple stages**. Same function,
  pins renamed: `(req_in, ci, cj, c_next) ↔ (Rin, L, R, Aout)`. Same control
  silicon, half the storage per token.

And the defect. `L` closes when `Rin` is low *and* `R` is high — neither of
which this stage controls. **A stage that cannot decide when its own latch
closes has no latch**, and it loses data from either side:

| trigger | what it is | arc-only | routed (354 ps) |
|---|---|---|---|
| 1 — upstream | a sender that turns round quickly; the stage above reopens before this one has closed | **18/20 wrong** | 0 — a one-arc race, routing removes it |
| 2 — downstream | a consumer slow to drop its acknowledge; `R` cannot rise, so `L` never closes | **9/20 wrong** | **15/20 wrong** — structural |
| — | long setup only, or long gap only | 0 | 0 |

The two are different kinds of defect and `tb_ctl` asserts the difference per
regime. Trigger 1 is a race that routing fixes — a post-route check, the same
shape as the arbiter's handover overlap. Trigger 2 survives every regime and
gets *worse* with routing; that one alone is why the cell can never ship.
Slack on either side hides both. That matters: the
first sweep that found this used a leisurely source and varied only the
consumer, so it saw trigger 2 and concluded the problem *was* the consumer. It
wasn't. The conformance suite found trigger 1 on its first run.

The simple controller fills every column of the same matrix and is still
correct with a consumer that takes 200 000 ps to respond. There is no bound to
find, because there a slow partner holds the latch *closed* — the safe
direction — and the latch closes only when **both** neighbours agree, so
neither can hold it open alone.

So the coupling that was removed was the load-bearing one. A correct decoupled
stage cannot get away with two nodes: it needs a third piece of state recording
"this stage is loaded", independent of both handshakes, so the close is a
decision the stage makes on its own. That is why the published fully-decoupled
controllers carry more state than looks necessary.

`verify/attempts/bd_deco_attempt.v` is that third-state derivation, and it is
**unresolved rather than wrong**. It adds `F` — "this stage is loaded" — so the
close depends on `Rin` alone, and it costs 2 LUTs of control plus `W/2` of latch
per stage, which beats the simple controller per token stored from `W = 2` up.
Swept against the one variable `tb_ctl` cannot change, the sender's turnaround
after being acknowledged, it blocks correctly at `N` tokens and holds its data
for every value down to one arc — and collapses at exactly zero, which is all
`bd_source` can present and is not a value silicon can produce.

`bd_src` closed the second half of that argument. The synthesisable source is
`req = ~ack`, so its turnaround is one LUT arc — 56 ps rising, 124 falling,
before any routing — and the general form is stronger than the one cell: every
producer here derives its request from the consumer's acknowledge through at
least one LUT, because a Muller stage's request *is* a C-element with `ack` on
a pin. The library has a structural turnaround floor of one arc, everywhere.
Zero was a property of the bench model, not of the fabric.

That is still not an acquittal. Tying the latch-open window to a partner's
response time is an obligation the simple controller does not have: it holds
from req-rise to ack-fall and is indifferent to how fast anyone turns round.
The trade may be worth one token a stage, but it is a trade, it is not in the
review, and nothing has measured its cost. Settling it needs a source that
models a physical turnaround — a change to a harness every bench shares. Until
then `tb_ctl` asserts the measured state in *both* directions, so the cell
cannot quietly go green.

## `tb_ctl` — the conformance suite

Built because the above took a hand-trace and a parameter sweep to find, and
still only found half of it. Every controller gets the same matrix:

```
controller      OCC   FAST  SLOWA SLOWR SLOWS PROTO
--------------------------------------------------
simple          2/2    ok    ok    ok    ok    ok
semi (attempt)  4/4   FAIL  FAIL  FAIL   ok    ok
```

`OCC` occupancy, measured not claimed · `FAST` brisk consumer · `SLOWA` consumer
slow to acknowledge · `SLOWR` consumer slow to *release* — slow to drop its
acknowledge after the request falls, the phase everyone forgets · `SLOWS` slow
sender · `PROTO` four-phase order and hold window on both channels.

Every stress is a **delay, never a reordering** — none of the rigs violate the
protocol, they just take their time. A controller that needs a partner to hurry
is not a four-phase controller.

One rule the bench itself has to obey: **the consumer may not sample early.** A
stage's request leads its own data by up to one latch arc per stage, so a
consumer latching a fixed short time after req-rise reads mid-flight and *every*
controller "fails". The first version of this bench sampled at 300 ps and
produced exactly that — a matrix of failures that were the bench's fault.
`T_SAMPLE` is now derived from the library's own documented bound rather than
chosen.

## Two things the library learned that the review does not state

**A C-element tree is not a flat N-input C-element.** Not in general: feed
`[0,1,1,1,1]` to a 5-input tree and it answers 1 where the flat element answers
0, because the sub-trees are holding ones captured at different moments. It
*is* equal under the four-phase discipline — all inputs rise, then all fall —
which is the only way this library ever drives one. `tb_prims` exercises that
discipline in randomised orders; `bd_ce.v` carries the counter-example.

**Grant exclusion in `bd_arbcell` is an arc ordering, not a structure.** For a
settled `q` exactly one grant can be high, which is what the review argues, but
during handover the two grants read `q` through different arcs. On the r2→r1
direction the falling grant travels one fall arc (124 ps) and the rising grant
travels two rise arcs (56 + 52), so with zero routing the rise wins by 16 ps
and both grants are briefly high. Routing puts a full hop in the `q` feedback
and restores the order with roughly twenty times the margin. `tb_arb` counts it
in both regimes: 1 instant at `BD_ROUTE_PS=0`, 0 at 354. It is a post-route
check, not a defect — but it is a check, and the review presents exclusion as
needing none.
