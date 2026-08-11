# `bd_*` — cell library reference

The four-phase bundled-data primitive library in `rtl/`, targeting xc7z010clg400
(EBAZ4205) through openXC7. This document is the per-cell reference: what each
cell's interface is, what it does, what it costs in LUTs and *why* that is the
cost, and the design decisions recorded in each cell's own header.

It is a companion to `README.md`, which covers the verification gates and what
each one does and does not prove, and to `docs/ARBITER.md`, which carries the
arbiter's risk analysis. Arbiter coverage here is structural only.

Everything in `rtl/` is instantiated LUT primitives. There is no inferred logic
anywhere in the library, because the point of the exercise is a specific LUT
count and you cannot hit a specific LUT count by describing behaviour and
hoping.

---

## Cross-cutting rules

Four things are true of the whole library rather than of any one cell, and they
explain most of what the cells look like.

### The four-phase bundled-data protocol

A channel is a request wire, an acknowledge wire, and a bundle of data wires.
One transaction is the ring

```
req↑   ack↑   req↓   ack↓
```

and the four phases are traversed in that order, always, with no phase skipped
and no new request before the previous `ack` has fallen. The bundling
obligation is that **data is stable from `req↑` to `ack↓`** — the whole hold
window, not just until `req↓`.

That the window ends at `ack↓` rather than at `req↓` is not a convention chosen
for convenience; it falls out of the controller. In `bd_link` a single
C-element node drives the latch enable, the outgoing request, *and* the
acknowledge returned to the sender. The latch is still transparent until the
acknowledge drops, and the node only falls in response to `req↓`, a gate delay
later. Release the data at `req↓` and the next value walks through a latch that
has not closed.

Every channel in every bench carries a `bd_monitor` that asserts this order,
that no new request precedes the acknowledge falling, and that data is stable
across the whole `req↑ → ack↓` window.

Two structural consequences worth carrying in your head:

- **Requests lead their own data.** A stage's `req_out` is the C-element node
  itself, one arc from `req_in`; `data_out` is that node through a latch, two
  arcs. No wiring of a Muller stage makes the enable and the enabled data land
  together. Measured at 152 ps for one stage and 441 ps for four (see
  `bd_link`). This is harmless everywhere inside the library, because every
  consumer here is a transparent latch that closes a phase later, and it is a
  real violation at any boundary that *samples* the request edge.
- **The turnaround floor is one LUT arc.** Every producer in this library
  derives its request from the consumer's acknowledge through at least one LUT
  — a Muller stage's request *is* a C-element with `ack` on a pin. Zero
  turnaround is a property of the bench source model, not of the fabric.

### LUT INITs are derived and proved, never written

No hexadecimal constant in `rtl/` was typed from a truth table by hand.
`verify/inits.py` states every LUT function as a Python lambda plus a pin order
and *computes* the INIT from it, then re-reads that INIT the way silicon
addresses it — address bit 0 is I0 — across all 2⁶ rows. That is 1560 rows over
30 cells, exhaustive rather than sampled, because the space is small enough that
sampling would be a choice rather than a necessity.

The pin-order convention matters for the fractured cells: for a `LUT6_2`, O5 is
`INIT[31:0]` read with I0..I4 and O6 is `INIT[63:32]` read with I0..I4,
**provided I5 is tied high**. That tie is the only way two independent
five-input functions share one site, which is why `.I5(1'b1)` appears on every
fractured instance in the library.

The check runs in both directions. The six constants the frozen design review
states independently are compared against the computed ones, so drift between
the library and the review surfaces here first; and `--check-rtl` audits every
hexadecimal literal in `rtl/` against the set of proved constants, so a number
nobody derived cannot reach a LUT. It is the first gate in `check.sh` and the
weakest claim of the set: it says nothing about whether the cell built from
those constants does anything useful.

### Matched delays are placeholders, sized per-route

`bd_delay #(N)` appears in `bd_merge`, `bd_mux`, `bd_dr2bd`, `bd_mem` and
optionally `bd_link`/`bd_pipe`. **`N` is a placeholder in every one of them.**
It is not a design constant, not a synthesis estimate, and not abc9's timing
model. Chain depth is tightened unconditionally after place-and-route from
measured routed arrival times.

`verify/tighten.py` reads nextpnr's routed SDF — where interconnect delays are
the delays of the routes actually chosen, 434–945 ps a hop on this build — and
reports what each placeholder should become **for that route and no other**. It
checks three things: that the request is the last thing its cell emits (the
general form of `z_req = Δ(…)`, against the review's
`guard = max(0.2·t_data, 200 ps)`); the RAM boundary, the only edge-sampled
boundary in the library, against prjxray's own setup windows rather than a
percentage; and clock-to-out, that the acknowledge trails the read data by
`t_co`.

The pass tightens; **it never pads**. A line that needs to *grow* is not a
sizing result, it is a bundling violation, and the answer is to re-place or
shorten the datapath.

The measurement is confined to one cell by construction. A setup check needs the
late signal on its shortest path and the early one on its longest, both from a
common start point inside the cell — a matched delay covers logic inside one
cell's datapath, and measuring from a distant state node inflates `t_data`,
inflates `0.2·t_data` with it, and turns every line in the design into a false
violation. The netlist is not a DAG (every C-element and latch is a loop), so
any pin on a cycle is treated as a state node where traversal starts and stops,
which is exactly the four-phase model: one hop per phase.

And the sizing cannot be shaved close. `verify/resize.sh` applies one
recommendation at a time, re-routes, and reverts anything that stops checking
out. On this design only two of five lines could be tightened at all and eleven
of thirteen proposals were reverted, because the recommendation is the
*smallest* length meeting the guardband — so applying it leaves zero margin by
construction, and applying it also changes the netlist, which moves the
placement, which changes the routing the recommendation was measured against.
Budget matched delays conservatively and do not expect the toolchain to recover
the slack. Measured lengths are opt-in via `BD_SIZES=…`; a bare `./flow.sh` is
always the placeholder build.

The whole apparatus rests on the routed SDF being true of the die, which no
software gate can establish. `hw/ro_measure.py` is the one measurement that
addresses it: five ring oscillators of different lengths on an EBAZ4205, each
compared against its own routed prediction. Measured 2026-08-03,
`measured = 0.975 × predicted` across an 18× span of length, every ring faster
than predicted, residual 8.5% with no trend in length. The model is good to
about a tenth and errs long.

One further licence limit, stated in `bd_delay`'s own header: a matched delay
covers combinational logic inside *one cell's own datapath*, where there is no
request to wait on. If you are reaching for one so that a request will wait for
a computation happening elsewhere, you want a fork and a join instead.

### Combinational loops must carry `(* keep *)`

Every C-element, every latch bit, and `bd_src`'s inverter is a deliberate
combinational feedback loop, and in the C-elements and latches **the loop is the
storage element**. There is no flip-flop behind it to fall back on. So:

- The instance carries `(* keep *)`, or synthesis dissolves the loop and the
  storage with it.
- nextpnr needs `--ignore-loops` to accept the resulting strongly-connected
  component.
- The feedback must remain an internal wire. Promoting it to a module port
  costs 2 LUTs instead of 1.

`bd_src` is the one loop in the library that is *not* storage — nothing is
remembered, the ring just turns — and it is why `tighten.py`'s state-node census
can exceed the count of latches and C-elements.

Reset follows from the same fact. A LUT feedback loop has no defined power-up
value and configuration does not clear it, so every C-element that holds control
state carries `rst` on a real pin. There are exactly three documented exemptions
in the library, each argued in place: `bd_c2_norst`/`bd_c3_norst` (legal only
inside a cell that defines the node some other way), `bd_latch` (nothing reads a
latch before its own request arrives), and `bd_dr2bd`'s `HOLD` C-element (the
unknown it powers up holding is overwritten by the first valid code, before
anything can look at it).

---

## C-elements — `rtl/bd_ce.v`

The rendezvous primitive: follow when the inputs agree, hold when they differ.
Symmetric `C(a,b)` is exactly `majority(a, b, q)`, so one LUT6 holds both the
cell and its own feedback.

**Interface.** `bd_c2(a, b, rst) → q`, `bd_c3(a, b, c, rst) → q`,
`bd_c4(a, b, c, d, rst) → q`, plus the inverting and set variants below.

**Cost: 1 LUT6 each.** The packing argument is the pin budget. A LUT6 has six
inputs; the feedback wire takes one and `rst` takes another, so **fan-in of four
is the hard ceiling** — `bd_c4` uses exactly six pins and is the widest
C-element this fabric holds. Beyond four, use `bd_ctree`, and the tree depth
becomes a term in the delay model.

**Reset polarity is per cell**, and the choice is semantic:

| Cell | Function | INIT | Comes up |
|---|---|---|---|
| `bd_c2` | `~rst · C(a,b)` | `64'h00E8_00E8_00E8_00E8` | empty |
| `bd_c2_set` | `rst + C(a,b)` | `64'hFFE8_FFE8_FFE8_FFE8` | holding |
| `bd_c2n` | `~rst · C(a,~b)` | `64'h00B2_00B2_00B2_00B2` | empty |
| `bd_c2n_set` | `rst + C(a,~b)` | `64'hFFB2_FFB2_FFB2_FFB2` | holding |
| `bd_c3` | `~rst · C(a,b,c)` | `64'h0000_FE80_0000_FE80` | empty |
| `bd_c4` | `~rst · C(a,b,c,d)` | `64'h0000_0000_FFFE_8000` | empty |

The `bd_c2*` cells come up empty and are what the link, fork, join, merge
acknowledges and mux joins use. `bd_c2_set` comes up holding and exists for a
loop's initial select token.

**An inverted input is a bubble on the pin that reads it, never a cell.**
`bd_c2n` is `C(a, ~b)` at exactly the same cost as `bd_c2`. Read as an SR latch
it is set on `a·~b`, reset on `~a·b`, hold on a tie — which is simultaneously
the pipeline link's controller and, set/reset swapped, the arbitration cell's
state node.

### `bd_c2_norst`, `bd_c3_norst`

The two rows of the review's mapping table that carry no reset pin, INITs
`64'hE8E8_…` and `64'hFE80_…`. Legal only inside a cell that defines the node
some other way. Never in a control network, where "it will probably come up
empty" is not an assumption available.

### `bd_ctree #(N)`

Rendezvous over N inputs. `bd_ctree(a[N-1:0], rst) → q`. Up to four inputs it is
one LUT; wider is a balanced tree whose depth is a real term in the bundling
budget. Cost `ceil((N-1)/3)` LUT6 for `N > 1`, rounded up by the tree's shape.

**It chunks in fours, not halves**, and that is the packing decision. A node
holds four inputs — six pins less the feedback wire and `rst` — so filling every
node to its ceiling is what minimises the count. Halving wastes nodes: five
inputs split 2+3 costs three LUTs, split 4+1 costs two.

**A C-element tree is not a flat N-input C-element.** This is the library's
sharpest correctness caveat and it is not academic. Each sub-tree carries its own
memory, so two sub-trees can hold stale ones captured at different moments. With
`N = 5` split as `C(C(a0,a1), C(a2,a3,a4))`, the input vector `0 1 1 1 1` drives
the tree to 1 while a flat five-input C-element holds at 0: the left sub-tree
tracks `a0` and `a1`, the right one is still holding a one from an earlier
all-high moment, and the top sees two ones.

Under the four-phase discipline that state is unreachable — every input is a
request that rises once and falls once per transaction, all rise before any
falls, and nothing moves again until the acknowledge has completed the cycle, so
every sub-tree returns to zero every cycle and can never be stale. `tb_prims`
exercises that discipline in randomised interleavings. So: fine for a join or a
fork, **wrong for anything that samples N unrelated levels**.

---

## Storage, delay and datapath — `rtl/bd_latch.v`

### `bd_latch #(W)`

Transparent-high D-latch. `bd_latch(d[W-1:0], en) → q[W-1:0]`. `EN = 1` makes Q
follow D; `EN = 0` holds. The enable is not a clock — it comes from the local
handshake and the latch stays transparent for as long as it is high.

**Cost: W/2 LUTs.** Two bits share `{EN, D_i, Q_i, D_j, Q_j}`, exactly five
distinct inputs, which is precisely the fracturing budget of a `LUT6_2` with I5
tied high. INIT `64'hFF33_CC00_B8B8_B8B8`. An odd trailing bit falls back to a
whole LUT6 at `64'hB8B8_…`.

**Why storage is on LUTs and not on the slice's LDCE.** The reason is routing,
not area. `LDCE.G` lands on the slice clock pin — prjxray puts it in the `FDRE.C`
column — reachable only through an interconnect tile's two CLK wires, each with
four fabric sources. A self-timed pipeline wants one locally generated enable per
stage and stages are dense, so that per-tile ceiling is the disqualifier. The
secondary benefit is that keeping the latch and the delay line on the same
primitive makes the two track each other across voltage and temperature, which is
what a matched delay depends on.

**No reset, deliberately.** `req` is what makes data meaningful, so nothing reads
a latch before its own request arrives and arbitrary power-up contents are never
observed. The corollary: **do not carry an initial token in one**, because an
initial token is by definition read before anything has written it.

### `bd_latch_rst #(W, RESET_VALUE)`

The resettable variant. `bd_latch_rst(d, en, rst) → q`.

**Cost: 1 LUT per bit.** `rst` folds into the feedback loop, making the bit a
function of `{D, EN, Q, rst}` — a sixth pin on the pair, so the pair breaks and
the bit costs a whole LUT6. Reset polarity is chosen per bit from
`RESET_VALUE`: `64'h00B8_…` clears, `64'hFFB8_…` presets.

Affordable for a control bit, not for a word. Use it only where an initial value
is genuinely read before anything writes it, which in practice means a loop's
initial token.

### `bd_delay #(N)`

Matched delay line. `bd_delay(a) → z`, a chain of N `LUT1` inverters-as-buffers
(INIT `2'h2`) on a `(* keep *)` wire vector. `N = 0` renders as a bare wire —
which is what makes `verify/teeth.sh` a meaningful test, since a `DELAY(0)`
leaves nothing in the netlist for a chain-hunting audit to find.

**Cost: N LUTs.** See the cross-cutting section above for the sizing discipline;
the short version is that N is always a placeholder and the header says so.
Built from the same LUT primitive as the datapath it covers, so the two track
each other across PVT.

### `bd_datamux #(W)`

`z = s ? b : a`, two bits to a fractured `LUT6_2`, INIT `64'hFFAA_5500_E4E4_E4E4`.

**Cost: W/2 LUTs**, by the same argument as the latch: `{sel, x_i, y_i, x_j, y_j}`
is five distinct inputs. An odd trailing bit is a `LUT3` at `8'hE4`.

Shared by the merge (`sel ? x : y`) and the mux (`s ? y : x`); the two differ
only in which channel is wired to which port.

---

## The pipeline link — `rtl/bd_link.v`

The simple (Muller) controller:

```
C_i = C(req_in, ~C_i+1)
```

One node drives three things — the latch enable, the outgoing request, and the
acknowledge returned to the sender. That single overloading is where the
four-phase hold window comes from, and it is also what makes the controller
robust: a slow partner holds the latch *closed*, the safe direction, and the
latch closes only when both neighbours agree, so neither can hold it open alone.

**Occupancy is half a token per stage**, so two stages make one
register-equivalent. The semi- and fully-decoupled controllers are not in `rtl/`;
they were specified by what they must achieve and never derived. `README.md`
carries the attempted derivations and exactly how they fail.

### `bd_link_ctl`

`bd_link_ctl(req_in, c_next, rst) → c`. One stage's controller, a `bd_c2n`.
**1 LUT6.**

### `bd_link_pair`

`bd_link_pair(req_in, c_next, rst) → ci, cj`. Two stages' controllers in one
fractured `LUT6_2`, INIT `64'h0000_C0FC_0000_8E8E`:

```
ci = ~rst · C(req_in, ~cj)
cj = ~rst · C(ci,     ~c_next)      with c_next = C_i+2
```

**Cost: 1 LUT for two stages, so half a LUT per stage.** Two adjacent stages
touch `{req, C_i, C_i+1, C_i+2, rst}` — five distinct pins, exactly the
fracturing budget. **One more control input anywhere and adjacent stages stop
sharing**, which is the sentence to remember before adding a feature to this
controller.

### `bd_link #(W, DELAY)`

One pipeline stage: controller plus latch. Ports `rst`, `req_in`/`ack_in`/
`data_in`, `req_out`/`ack_out`/`data_out`. **Cost: 1 LUT + W/2 LUTs**, plus
`DELAY`, which defaults to 0.

`ack_in` is wired to the raw node and must stay that way. Delaying it would only
lengthen the sender's hold window, never shorten it — so it is not a correctness
risk — but it would also stop the pair of adjacent controllers sharing a LUT, and
that is a cost risk.

### `bd_pipe #(W, N, DELAY)`

N stages, paired: stages 0,1 share a `LUT6_2`, stages 2,3 the next, and an odd
final stage falls back to a whole LUT6. **Cost: `ceil(N/2)` LUTs + `N·W/2` LUTs.**

`DELAY` pads the pipeline's own outgoing request only. The internal stage
boundaries need nothing, because each one is a transparent latch.

### The finding: the request outruns its own data

This is structural, not a sizing error. `req_out` is the C-element node itself
while `data_out` is that node through a latch.

`verify/probes/link_skew.v` measures a one-stage `bd_link` at **152 ps** of lead
— exactly the latch's own 5LUT fall arc. `verify/probes/pipe_skew.v` measures a
four-stage `bd_pipe` at **441 ps**. The lead *grows with depth*, and that is the
part worth understanding: filling an empty pipe sets off two waves. The control
wave hops C-element to C-element at one arc each; the data wave ripples latch to
latch, also one arc each, but the latch arc is the slower of the two (152 ps fall
against 55 ps on the controller pair). The control wave outruns its own data by
the difference, once per stage — roughly `N·(t_latch − t_ctl)` across N empty
stages.

Inside the library the lead is harmless, and *why* it is harmless is the entire
argument for the hold window: every consumer is a transparent latch, and it does
not close at `req↑`, it closes at `ack↓`, a full phase later. Nothing samples on
the edge. The lead bites only at a boundary that samples the request edge — a
BRAM clock pin, a synchronous vendor block, an off-library consumer. There, and
only there, `req_out` on its own is not a valid bundled-data request.

`bd_mem` handles its own boundary with an explicit `DSETUP` line. For any other
edge-sampling consumer, `DELAY` inserts a matched line on `req_out` alone — not
on `ack_in`, which must keep ending the hold window at the node itself. It
defaults to 0, which is the cell the review costs: zero extra LUTs, identical to
the frozen specification. Set it only where the boundary needs it, size it from
the measured lead at that depth, and tighten it post-route like every other
matched line.

---

## Fork, join and steer — `rtl/bd_ctl.v`

Everything in this file except the fork/join rendezvous is stateless, so nothing
here carries reset except where a C-element does.

### `bd_fork #(N)` and `bd_join #(N)`

`bd_fork(rst, req, ack_in[N-1:0]) → ack, req_out[N-1:0]` broadcasts the request
and joins the acknowledges. Data is broadcast too — a fork routes the handshake,
and the copies are wires. `bd_join(rst, req_in[N-1:0], ack) → ack_out[N-1:0], req`
is the dual: join the requests, broadcast the acknowledge, and the output data is
the concatenation of the inputs, which is again wiring.

**Cost for both is the rendezvous alone: 1 LUT to fan-in 4, a `bd_ctree` beyond
that.** Fan-in four rather than five is a resolved inconsistency in the frozen
review — one caption says five, the in-figure caption and the C-element section
say four, and the arithmetic settles it: 6 pins − feedback − rst = 4.

### `bd_steer`

```
req0 = req · ~s      req1 = req · s      ack = ack0 + ack1
```

`bd_steer(req, s, ack0, ack1) → ack, req0, req1`. **Cost: 2 LUTs** — one
fractured `LUT6_2` at `64'h8888_8888_2222_2222` for both branch requests, and a
`LUT2` at `4'hE` for the acknowledge OR.

Both branches together touch two distinct inputs, so they share one fractured
LUT **with four pins spare — the widest margin in the library**. There is no
feedback wire, hence no keep attribute, no loop for nextpnr to be told about, and
no reset.

**Why a plain AND is enough, and why an earlier draft's C-elements were removed.**
`s` is data, not a control wire. The bundling contract holds it still from `req↑`
to `ack↓`, a window that strictly contains the time `req` is high, so within a
transaction `s` is a constant and a constant cannot glitch a branch. Outside that
window `req` is already low and `req·s` is zero whatever `s` does, so return to
zero is immediate and unconditional on both branches. An earlier draft built this
from two asymmetric C-elements to harden it against `s` moving mid-transaction —
but the only thing that could move `s` mid-transaction is a violation of the
bundling contract, and if that is broken then the data being routed is invalid
too. The acknowledge OR is safe as a plain OR because only one branch was ever
requested.

Data is broadcast to both branches ungated: the steer routes the request, never
the data.

---

## Protocol converters — `rtl/bd_ctl.v`

The compiler rule these implement: bundled everywhere, dual-rail only on control
channels that arrive separately from the data they steer, converters at that
boundary. When the condition rides in the bundle there is no boundary and no
converter.

### `bd_bd2dr`

```
t = req · d          f = req · ~d
```

`bd_bd2dr(req, d, ack_dr) → ack, t, f`. **Cost: 1 LUT**, INIT
`64'h8888_8888_2222_2222` — pin for pin the same circuit as `bd_steer`, which is
not a coincidence: steering a request down one of two branches and encoding it
onto one of two rails are the same operation, and the branches *are* the rails.
Both rails are functions of `{req, d}`, so the pair costs one fractured LUT and
the inverter costs nothing, folding into the AND that consumes it. The
acknowledge is a wire, since a dual-rail channel returns one.

### `bd_dr2bd #(DELAY, HOLD)`

```
d = t                req = Δ(t + f)
```

`bd_dr2bd(t, f, ack) → ack_dr, req, d`. **Cost: 1 LUT + delay, either way** —
that is the point of the fix below.

Decoding is the direction that costs a delay: `d` and `req` derive from the same
two wires and would otherwise arrive together, which is exactly the bundling
constraint being violated at the boundary.

**Finding — the spacer eats the data.** `d = t` is correct for the whole of the
valid phase and wrong for the phase after it. Trace the two protocols against
each other:

```
rails go valid            → req rises a delay later
bundled receiver latches, raises ack
ack_dr IS ack, so the dual-rail sender drops BOTH RAILS to the spacer
d = t collapses to 0      — and req has not fallen yet, it falls a delay later
only after that does the receiver's latch close
```

So `d` moves inside the bundled hold window, which runs to `ack↓` and not to
rail-fall. A receiver that samples early — a testbench, a synchroniser — never
sees it. A receiver that is a transparent latch, which is every consumer in this
library, is still open when the rails collapse and closes on the spacer. It
captures zero. `tb_conv` measures **twelve hold-window violations in twenty-four
transactions** on a `DELAY(4), HOLD(0)` instance, exactly the transactions
carrying a one, and 0 with `HOLD(1)`.

This is not a delay-sizing problem and no amount of `DELAY` fixes it. The
return-to-zero phases of the two protocols are driven by the same acknowledge and
are one phase out of step by construction; the data has to be held across the
difference, and holding is a latch.

`HOLD` defaults to 0, which is the cell exactly as the review specifies it. The
fix is opt-in and reported rather than silently patched.

**The right hold is a C-element, not an ack-gated latch.** The rails already
carry their own validity: the spacer is not "no data", it is "hold what you had".
So

```
d = C(t, ~f)      set on t·~f, reset on ~t·f, HOLD on the spacer
```

Reading the four codes: valid ONE is `t=1,f=0`, both inputs agree high, set;
valid ZERO is `t=0,f=1`, both agree low, reset; the SPACER is `t=0,f=0`, the
inputs disagree, so the C-element holds — which is the entire fix. The fourth
code cannot occur and would give a hold if it did.

**It costs nothing.** `d` touches `{t, f, d}` and `either` touches `{t, f}` —
three distinct inputs between them, well under the five that let two functions
share one fractured `LUT6_2`. The OR that was a `LUT2` becomes O6 of that same
LUT and the decode becomes O5, INIT `64'hEEEE_EEEE_B2B2_B2B2`. One LUT before,
one LUT after; the review's budget is met exactly. An earlier version of this
file spent a whole extra LUT6 on an ack-gated latch and was wrong to.

It is also the *stronger* fix, not merely the cheaper one. An ack-gated latch
reopens at `ack↓`, and at `ack↓` the rails are already sitting at the spacer, so
`d` collapses on the closing edge of the very window it exists to protect —
correct by one arc. The C-element does not reopen until the next *valid* code,
which the dual-rail sender may not drive until it has seen `ack_dr` fall. The
value stands from its own valid code, across the spacer, to the next valid code,
and the bundled hold window sits strictly inside that with a full phase of margin
on the closing side.

**And it takes no reset**, which is unusual here. The rule that every feedback
loop needs one still holds; this loop just does not need the *value*. The unknown
it powers up holding is never read: `d` is only ever consumed behind `req`, `req`
only rises behind the matched delay off a valid code, and a valid code is exactly
what overwrites `d`. That survives simulation as well as silicon, which is worth
stating because an X is stricter than a real fabric and would have found the hole
if there were one — a mux-tree LUT model merges bitwise, so with an X on the
feedback pin it evaluates both halves of the table and returns the agreed value
wherever they agree; on a valid code they always agree, so `d` resolves on the
first token and the X never propagates. The pin is not free-but-harmless, it is
absent: three inputs, not four.

---

## Merge — `rtl/bd_merge.v`

```
z_req  = Δ(x_req + y_req)
x_ack  = C(x_req, z_ack)        y_ack = C(y_req, z_ack)
sel    = x_req + x_ack
z_data = sel ? x_data : y_data
```

`bd_merge #(W, DELAY)` with channels `x`, `y` in and `z` out. There is no select
port — which input is live is *inferred* from the requests, and that inference is
where the cell is delicate.

**Cost: 4 + DELAY + W/2.** That is 1 for the request OR (`LUT2`, `4'hE`), plus
`DELAY`, plus 2 for the acknowledges, plus 1 for the select (`LUT2`, `4'hE`),
plus `W/2` for the data mux.

The acknowledge pair is **two LUTs, not one shared**. The two C-elements touch
five wires between them, which would fit a fractured site, but each also needs
`rst` — making six distinct pins — so they land in separate LUT6s. The frozen
review has one cost row saying "1 (shared)", contradicted three times elsewhere
in its own text; built as two, and the pin count is why.

`DELAY` defaults to 4, and on this build `tighten.py` reports that default as
**already exact**, with 213 ps of margin over a 342 ps guardband.

**Two mistakes this cell exists in order not to make.**

*The acknowledge cannot be an AND.* With `x_ack = x_req · z_ack` the acknowledge
collapses the instant `x` drops its request, while `z_ack` is still high; `x`
believes it is finished and may raise a new request into a channel that has not
returned to zero. `C(x_req, z_ack)` holds until both have fallen, and handles the
idle input for free, since `C(0, z_ack)` stays at zero.

*The select cannot be the request.* Selecting on `x_req` flips the mux the moment
`x` enters phase three, while the downstream latch is still transparent. The
select must rise with the request and fall with the acknowledge, which is
`x_req + x_ack`.

**The obligation, rarely met.** Exclusivity is not enough. The cell also requires
that the second input cannot assert until the first transaction has *fully
completed*, otherwise `C(y_req, z_ack)` fires into a still-high `z_ack` and
acknowledges a token the merge never carried. Pipelined code does not satisfy
that, which is why the join at the bottom of an `if` is `bd_mux` and not this
cell — and it is also why `bd_arbiter` in front of a plain merge has a finding
against it.

---

## Mux — `rtl/bd_mux.v`

```
j0      = C(x_req, ctl_req · ~s)
j1      = C(y_req, ctl_req ·  s)
z_req   = Δ(j0 + j1)
x_ack   = C(j0, z_ack)          y_ack = C(j1, z_ack)
ctl_ack = z_ack
z_data  = s ? y_data : x_data
```

`bd_mux #(W, DELAY)` with data channels `x`, `y`, a control channel
(`ctl_req`/`ctl_ack`/`s`) and output `z`. The classical dual-rail-control form
rebuilt on bundled data: a control channel picks the input, so the sources need
not be exclusive.

**Cost: 5 + DELAY + W/2** — 2 for the joins, 1 for the request OR, `DELAY`, 2 for
the acknowledges, `W/2` for the data.

**The control decode needs no gates of its own.** Folding `ctl_req·~s` into the
C-element leaves a function of four wires, which is one LUT6 once `rst` joins it
— INITs `64'h0000_AE08_…` for `j0` and `64'h0000_EA80_…` for `j1`. But the two
joins together touch six distinct wires, so — unlike `bd_steer` — they cannot
share a fractured LUT. `tighten.py` reports this cell's delay as wanting
tightening on the current build.

**Only the selected input is acknowledged.** `x_ack` can only rise if `j0` fired,
and `j0` can only fire if the control said x. The other input keeps its token,
untouched, which is exactly what a loop header needs.

**`ctl_ack` is `z_ack` directly.** The control token is consumed by whichever
branch fired, and `z_ack` cannot rise until that branch's data has been taken, so
it already carries the right timing.

**Why the select is safe here where the merge's is not.** The merge infers which
input is live from a request wire, which falls a phase too early. The mux infers
nothing. `s` is ordinary channel data, held by the control channel's own contract
from `ctl_req↑` until `ctl_ack↓` — and since `ctl_ack` *is* `z_ack`, the select is
valid across exactly the output window. That is the real argument for paying for a
control channel: **it converts a timing obligation into a data one.**

**On dual-rail control.** Dual-rail is used classically because one wire cannot
distinguish "control has not arrived" from "control arrived and says zero".
Bundled control carries the same information split across `ctl_req` and `s`, so
the decode recovers the rail pair exactly and the rest of the circuit is
identical — and here the decode is free, because it disappears into the join's
LUT.

---

## Endpoints — `rtl/bd_end.v`

```
bd_src   req = ~ack        a constant, offered forever
bd_snk   ack = req         accept everything, keep nothing
```

Both are one line and both are exactly right, which is why they are a file rather
than a comment somewhere. A four-phase channel is a ring; close it on itself with
an inversion and it free-runs at whatever rate the far end can take, close it
without one and it mirrors, which is precisely "I accepted that".

`bd_src #(W, VAL) → req, data`, `ack` in. `bd_snk #(W)(req, data) → ack`.

**Cost: `bd_src` is 1 LUT** (`LUT1`, INIT `2'h1`); **`bd_snk` is free** — a wire,
zero LUTs, and the unread data port is wiring the emitter does not have to
special-case. The port exists so that a channel is a channel everywhere and the
emitter has one shape to emit.

A compiler should expect to get `bd_src`'s LUT back: `~ack` folds into whatever
consumes `req`, and a join's C-element has the acknowledge on a pin already and
can absorb the inversion by complementing its constant, for no cells at all. That
is a peephole for Stage 2, deliberately *not* built into the cell — a cell that is
only correct once it has been optimised away is worse than a cell that costs one
LUT.

**Why the inverter is an instantiated `LUT1` and not `assign req = ~ack`.** The
library is simulated from `rtl/` directly, so an `assign` would be a zero-delay
inversion sitting in a combinational loop through the consumer: the source would
raise and drop its request forever inside one timestep and the simulator would
never advance. The `LUT1` model in `sim/bd_prims_sim.v` carries the real
56/124 ps arc, so the ring runs at a finite rate and the bench can watch it. Every
other loop in the library is a C-element and got its delay for free by being a
primitive; this one has to ask.

**Bundling.** `bd_src` takes no matched delay and needs none, which is unique to
it: the obligation is that data is stable from `req↑` to `ack↓`, and this data is
stable from configuration to power-down. A source of something that *moves* is not
this cell — it is a compute unit or a memory port, and it pays for its delay like
everything else.

**Names.** `sim/bd_env.v` already has `bd_source` and `bd_sink`, the *bench*
models, which sequence a scripted list of values and record what arrived. These
are the synthesisable endpoints and are deliberately named differently, because
they are not the same thing and a bench reaching for the wrong one should not
compile.

---

## Memory port — `rtl/bd_mem.v`

**Second highest risk cell in the library.** The request manufactures the clock
edge.

```
req --[ Δ DSETUP ]--[ buffer ]--+--> RAMB18E1.CLK
                                |
                                +--[ Δ DCO ]--> ack
```

`bd_mem #(AW, DW, DSETUP, DCO, USE_BUFG)` with ports `req`/`ack`, `addr`,
`wdata`, `we`, `rdata`. One `RAMB18E1` in TDP mode, port A at x18, `DOA_REG(0)`,
`WRITE_FIRST`; the word address is placed at `a14[13:4]`.

**Cost: 2 matched delays + 1 buffer + the BRAM.** `DSETUP` defaults to 8 and
`DCO` to 12, and both are explicitly labelled placeholders in the source, sized
post-route like every other delay.

**Failure modes this cell owns.**

*Automatic clock buffering.* yosys inserts a global buffer on anything that looks
like a clock pin, unasked. Roughly two nanoseconds arrive on a path a matched
delay was sized against, and capture lands after the acknowledge. Simulation
never shows it — there is no buffer in the simulation model. This is why the flow
passes `-noclkbuf` and why `flow.sh` checks the FASM for the absence of any
global clock buffer.

*Pipelined return-to-zero overlap.* Back-to-back accesses whose reset phases
overlap corrupt the port. It has a known history of being misdiagnosed as a
margin problem and "fixed" by scaling guard delays, which never worked because
the mechanism is sequencing, not timing.

*Vacuous audit.* If the structural audit treats a clock buffer as a zero-depth
source, it truncates the strobe cone, reports a request arrival of zero, and
passes.

**Design rules the cell implements.** Instantiate every buffer explicitly and
never let a pass infer one — `USE_BUFG` picks *which* buffer exists and there is
always exactly one named driver of the clock net; with `USE_BUFG = 0` the net
carries `(* clkbuf_inhibit *)` and the flow additionally passes `-noclkbuf`. Keep
the capture edge and the timing tap downstream of the same buffer: `ram_clk` is
that single net and both the RAM and the acknowledge delay read it. Audit the RAM
boundary as a bundling boundary — CLK is the request, address and write data are
the payload, same depth-slack rule as a latch. Serialise accesses until the
return-to-zero phase is proven complete, and treat the port as a shared resource
with a full four-phase cycle rather than a pipelined element; a second read port
is a second copy of this structure, and sharing one port between two requesters
needs `bd_arbiter`.

**On the "pulse" stage.** The schematic labels the stage between the setup delay
and the RAM "pulse" without specifying its internals. It is built here as the
single explicit buffer the design rules demand, so CLK is high for as long as
`req` is and the acknowledge is a level rather than a pulse. Narrowing it into a
true one-shot would make `ack` a pulse, which is not a four-phase acknowledge.

This is the only edge-sampled boundary in the library and the only place
simulation can catch a bundling failure: `tb_mem`'s RAM model enforces the vendor
setup windows (prjxray `BRAM_L.sdf`, t_su 566/737/532 ps, t_co 2454 ps), so an
undersized matched delay is a message in the log. On the current build the
boundary clears its address setup by 1615 ps and its clock-to-out by 1674 ps.

---

## Arbitration — `rtl/bd_arb.v`

**Highest risk cell in the library.** Structure only here; the risk analysis, the
metastability argument and the MTBF obligation are in `docs/ARBITER.md` and
`verify/MTBF.md`. Read those before using either cell.

### `bd_arbcell`

```
q  = C(r1, ~r2)
g1 = r1 ·  q
g2 = r2 · ~q
```

`bd_arbcell(r1, r2, rst) → g1, g2`. **Cost: 2 LUTs** — a `bd_c2n_set` for the
state node, and one fractured `LUT6_2` at `64'h0C0C_0C0C_A0A0_A0A0` carrying both
grants.

A C-element is exactly an SR latch whose set is `r1·~r2` and whose reset is
`~r1·r2` — the two conditions under which one channel is unambiguously asking
alone. On a tie both are false, so `q` holds and the previous winner is asked to
give way first. Because `q` only ever moves while exactly one request is up,
sustained contention forces alternation.

The complement costs nothing: `~q` is a bubble on the pin that reads it, and an
inverter is never a cell on this fabric. So there is **one feedback wire in the
whole element and one logic level in its loop**, where the textbook NAND mutex has
two of each — and loop delay is what sets the resolution time constant.

`rst` drives `q` to 1. It may come up either way, since it only decides who wins
the first tie, but it must come up *defined*.

**Both grants must sit in one fractured site**, and this is a placement
requirement, not an optimisation. Two separate LUTs have identical intrinsic
delay but land in different sites with different routing, and routing on this part
moves about a nanosecond between builds. One fractured site has a fixed
O5-versus-O6 delta of tens of picoseconds, identical every time. A constant
asymmetry only biases tie-breaking; an asymmetry that moves between builds means a
measured MTBF does not transfer to the next bitstream, which would make the whole
characterisation worthless.

Exclusion is structural **for a settled `q`** — exactly one of `q` and `~q` is
high, both grant LUTs read the same net, and no routing skew changes which value
it holds. Exclusion *during handover* is a weaker claim that has to be checked
rather than asserted; `tb_arb` counts the overlap in both timing regimes (1
instant at `BD_ROUTE_PS=0`, 0 at 354). See `docs/ARBITER.md`.

### `bd_arbiter #(HOLD_ON_ACK)`

The arbitration cell in front of a plain merge, with nothing between them.
`bd_arbiter(rst, r1, r2, A0) → A1, A2, R0, g1, g2`. Control only, matching the
schematic; a data-carrying arbitrated merge adds `bd_merge`'s select LUT, data mux
and matched delay on `R0`.

```
q, R0    one fractured LUT: q = C(r1,~r2) and R0 = g1 + g2
g1, g2   one fractured LUT: r1·q and r2·~q
A1, A2   C(g1, A0) and C(g2, A0)
```

**Cost: 4 LUTs for a two-way arbiter.** `R0` pairs with the state node rather than
with the grants because `r1·q + r2·~q` is a function of the same three wires, and
adding `rst` still only makes four; it reads the routed-back copy of `q`, the same
net the grants read, so the three outputs stay consistent with each other. That
number is derived from the packing rule, and `verify/lutcost.py` confirms it
against a routed netlist.

The separate exclusion stage an earlier draft carried is gone. It was a patch on a
broken cell — the cross-coupled element it protected could reach a stable
both-granted state, so something downstream had to catch it. With one state node
there is nothing to catch, and a LUT-built exclusion stage would not help with a
metastable `q` either, since it would be fed the same intermediate level. What is
still worth buying with an extra stage is *resolution time*, which is a different
thing from exclusion.

**Finding — the arbiter does not meet the merge's precondition.** `bd_merge`
requires that the second input may not assert until the first transaction has
fully completed. Exclusive grants are weaker than that, and an arbiter under
sustained contention gives the opposite: `q` is allowed to flip during the *other*
client's return-to-zero, so `g2` rises while `A0` is still high and `C(g2,A0)`
fires immediately, acknowledging a transaction the server never began. `R0 = g1 +
g2` never returns to zero either — the OR bridges straight across the handover, so
the server sees one long request where two clients were served. `tb_arb` measures
eighty client acknowledges against forty server transactions on the unfixed cell.

`HOLD_ON_ACK` defaults to 0, which is the arbiter exactly as specified; the fix is
opt-in and reported rather than silently patched. `HOLD_ON_ACK(1)` freezes `q`
while `A0` is high, giving 80 against 80. **`A0` is one more pin on a node whose
partner function already uses the pins it needs, so the pair is still five
distinct inputs: the fix is a different constant, not a different cost.** Still
four LUTs — INIT `64'hFFF0_FFB2_ACAC_ACAC` against the plain
`64'hFFB2_FFB2_ACAC_ACAC`, both derived and proved in `verify/inits.py`.

The full trace, the narrower grant-overlap problem it also removes, and the limits
of what it fixes — fairness holds by one arc of margin, not by construction — are
in `docs/ARBITER.md`.

---

## Cost summary

| Module | File | Cost |
|---|---|---|
| `bd_c2` `bd_c2_set` `bd_c2n` `bd_c2n_set` `bd_c3` `bd_c4` | `bd_ce.v` | 1 LUT |
| `bd_c2_norst` `bd_c3_norst` | `bd_ce.v` | 1 LUT |
| `bd_ctree #(N)` | `bd_ce.v` | `ceil((N-1)/3)`, chunked in fours |
| `bd_latch #(W)` | `bd_latch.v` | W/2 LUTs |
| `bd_latch_rst #(W)` | `bd_latch.v` | W LUTs |
| `bd_delay #(N)` | `bd_latch.v` | N LUTs (0 = a wire) |
| `bd_datamux #(W)` | `bd_latch.v` | W/2 LUTs |
| `bd_link_ctl` | `bd_link.v` | 1 LUT |
| `bd_link_pair` | `bd_link.v` | 1 LUT for two stages |
| `bd_link #(W)` | `bd_link.v` | 1 + W/2 |
| `bd_pipe #(W,N)` | `bd_link.v` | `ceil(N/2)` + `N·W/2` |
| `bd_fork #(N)` `bd_join #(N)` | `bd_ctl.v` | 1 LUT to fan-in 4 |
| `bd_steer` | `bd_ctl.v` | 2 LUTs |
| `bd_bd2dr` | `bd_ctl.v` | 1 LUT |
| `bd_dr2bd #(DELAY,HOLD)` | `bd_ctl.v` | 1 LUT + delay, either way |
| `bd_merge #(W,DELAY)` | `bd_merge.v` | 4 + delay + W/2 |
| `bd_mux #(W,DELAY)` | `bd_mux.v` | 5 + delay + W/2 |
| `bd_arbcell` | `bd_arb.v` | 2 LUTs |
| `bd_arbiter` | `bd_arb.v` | 4 LUTs |
| `bd_mem` | `bd_mem.v` | 2 delays + 1 buffer + BRAM |
| `bd_src #(W,VAL)` | `bd_end.v` | 1 LUT |
| `bd_snk #(W)` | `bd_end.v` | free |

A `LUT6_2` counts once, because it is one site. That is the claim the whole cost
model rests on, and `verify/lutcost.py` is what tests it: 29 cases synthesised
individually against the review's packing and cost tables, all matching.

## What this document does not tell you

It describes the cells as built. It does not establish that they are correct on
silicon, and neither does anything else in the tree. `README.md` sets out each
gate and what it fails to prove; the two limits worth repeating here are that
`verify/tighten.py` uses nextpnr's flat 124 ps cell-arc model rather than the
per-pin prjxray arcs the simulation uses, and that the arbiter's failure rate is
a hardware measurement that nothing in this repository discharges.

Three cells ship with a known finding against them, all three built as the frozen
review specifies by default with the fix behind an opt-in parameter:
`bd_dr2bd` (`HOLD`), `bd_arbiter` (`HOLD_ON_ACK`) and `bd_link`/`bd_pipe`
(`DELAY`). Each is measured by a bench rather than argued.
