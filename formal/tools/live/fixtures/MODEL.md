## Model, semantics, limits (live.py)

**What is modelled.** The circuit bdc emits, read off bdc's own `Emitter` (research tree 7197d85c2, `LIVE_BDC_DIR`):
which channels are linked and their final depth (`e.linked`, `e.depth`, after ring floor, token floor, ring pad,
slack stages, BDC_LINK_DEPTHS), merge olink / rlink (MERGE_OUT_LINK / MERGE_RES_LINK / MERGE_RES_DEPTH), fork output
links (FORK_OUT_LINK), BDC_OP_FUSION regions (one join over `region.ext_inputs`), absorbed source->constant pairs,
memory accessors (`accessor_info`, `mc_info`), the store completion join and the call join in `_op_end`. Nothing of
`token_graph` / `short_walk` / `token_floor` / ring_tokens.py is used. Every state-holding element is a gate that fires
when excited (speed-independent interleaving); combinational gates are zero-delay functions:

| cell (emit.py lowering) | gates (state) | combinational |
|---|---|---|
| bd_link / bd_pipe stage, olink, rlink, fork-out link, mem uhold | c = C(req_in, ~ack_out); latches the input's value at c rise | req_out = ack_in = c |
| bd_fork (fork, lazy_fork, control_merge's result/index fork, end forks) | ack_in = C(ack_out_1..n) | req_out_k = req_in |
| bd_join, compute unit, fused region, mem_controller uend, end joins | req_out = C(req_in_1..n); output value set at its rise | ack_in_k = ack_out |
| cond_br (bd_join + bd_steer) | j = C(cond.req, data.req) | req1 = j.s, req0 = j.~s, ack = ack0 + ack1 |
| mux (bd_mux / bdc_muxn) | j_k = C(in_k.req, ctl.req.(s==k)), a_k = C(j_k, z.ack) | z.req = OR j_k, ctl.ack = z.ack |
| merge / control_merge (bdc_amerge cascade of bd_arbiter) | q (decoded from the LUT INITs, reset 1), A1 = C(g1, A0), A2 = C(g2, A0) | R0 = q ? r1 : r2, g1 = q.r1, g2 = ~q.r2 |
| bd_src | req = ~ack (a gate) | data 0 |
| bd_snk | - | ack = req |
| load / store station (bdc/mem.py) | joined = C(c?, a, d?), done = joined.(p_ack + done), hold = z_ack + hold.p_ack | p_req = joined.~done, z.req = done, operand acks = hold; an unconsumed store z is tied (ack = req) |
| bdc_memport (1 slot / program-order slots / 2-slot arbitrated) | ram ack follows OR(p_req) (or R0 of a bd_arbiter on the 2 slots) | p_ack = ram (or A1 / A2) |
| constant, br, extui/extsi/trunci | - | wires; value: constant / pass / truncate |

**One timing assumption** (bundled data, not speed independence): the arbitrated merge's output request (R0 behind
its matched delay) is taken to rise only after the index it announces has settled (`won[k] = g2[k] | A2[k]` of the
previous winner back to 0). Without it the zero-delay model latches a stale index (a real race only if the matched
delay is shorter than one C-element); with it gcd is live, without it gcd "deadlocks".

**Data.** Only values that can steer are tracked: constants, cond_br conditions, mux selects, control_merge indices
(the arbiter's winner), andi/ori/xori/select of tracked values, ext/trunc. An i1 output of a compute cell (cmpi, or any
op on untracked data) is a NONDETERMINISTIC bit chosen when the cell's output request rises, then copied by forks,
stages and steers (so every steer fed from one condition fork sees the same value). Memory contents and loaded values
are untracked (a condition computed from a loaded value is nondeterministic). So the model over-approximates the
data: a DEADLOCK found may need a condition sequence no input produces (each trace lists the condition choices, so it
can be checked); `--pattern CELL=BITS` replays fixed trip counts (matrix below).

**Environment.** One 4-phase source per non-memref argument; invocation k+1 is offered only after every result of
invocation k arrived; one 4-phase sink per result. Verdicts are for 1 invocation, and for 2 back-to-back where the
1-invocation search was under 100000 states. Finished with tokens left anywhere (stages / forks / joins / steers /
muxes not back at reset) is counted as `residue`. **Correction (C, 2026-11-18 21:35 UTC): residue is NOT zero** -- it is
nonzero on many LIVE rows (results.jsonl: collatz 4-6, gcd 128, branchloop 63-125, if_loop_1 4, matrix 42, ...). In every
example read (collatz fork6, matrix fork12 / fork13, gcd fork11 / fork19) the tokens left are copies of a constant driven
by a free-running `source`, waiting in the fork's output links: the next invocation's constants, made early. That is benign
(sources never run out, the values are constant), but no classifier checks that every residue state is of this kind.

**Search.** BFS over states hashed with blake2b-128 (collision probability negligible but not zero), partial-order
reduced: a transition that is not an arbiter's and does not drive an arbiter input (r1, r2, A0) is persistent and
fired alone (persistence checked on every firing: a firing that disables another excited non-arbiter gate is counted
as a hazard: none found anywhere); a nondeterministic bit branches 2 ways; when only arbiter-related transitions remain
all enabled ones are expanded. These are stubborn sets for deadlock, so every reachable deadlock of the model is
found. **No trip-count bound is used**: the state space is finite, so LIVE-exhaustive covers every trip count of
every loop (0, 1, many), entering and leaving loops, and arbitrary condition sequences. When the search exceeds its
budget (states or time), 300 random walks (uniform among reduced successors) replace it: SAMPLED-LIVE is a sample, not
a proof; a deadlock found that way is real (in the model).

**Stage-level projection / Z-cycle.** Stages = Muller stages + sources + result sinks; p -> t iff p reaches t's input
through rendezvous cells under the routing read off the state (steer: its condition stage's current value; mux: its
select's; arbiter: its q). Z(x) = {p->t : x_p = x_t} u {t->p : x_p != x_t}. For each deadlock the Z-cycle (`trap`)
and, for up to 4 routing modes per run (first branch state seen in each), the graph and state are dumped to
`graphs/<fixture>.<flow>.<floor>.<which>.json` (which = deadlock / s0..s3; validation runs as validate.<config>). A
steer or mux whose condition never arrived has no route: its out-edges are omitted (listed as undetermined).
The projection drops the C-element state of forks / joins / muxes / arbiters and the memory stations' done / hold.

**Not covered.** Timing (beyond the one assumption above); the decoupled link controller (BD_LINK_DC, not used by bdc);
BDC_HOST_MEM ports; memory ordering / contents; more than 2 invocations; fixtures bdc refuses (listed REFUSED with its
error); exhaustive verdicts beyond the state budget.
