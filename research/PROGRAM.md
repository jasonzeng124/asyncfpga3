# Autonomous research program

You are the only agent working on branch `claude/research`. Nobody will answer
questions: decide, record why in the journal, and keep going. The owner reads
`research/JOURNAL.md` and `research/BOARD-QUEUE.md` and runs the board.

## Quota (owner, 2026-11-18 16:48 UTC): a full allowance until the reset, then the usual limits

The week's quota ran out at 10:16 UTC today and every bot stopped. At 16:48 UTC the owner:
"oh btw you have an entire week of usage before w6pm". The allowance is full again, and what
is unused is lost at the reset, 2026-11-18 23:00 UTC.

- **Until 23:00 UTC today: up to 8 subagents at a time.** Put them on "General first" and
  the suite, one lead each; you read and decide:
  1. the automatic xorshift is at 20.1 ns and the hand recipe at 16.76: name what the hand
     recipe has that the flow does not, and put it in the flow, for every kernel;
  2. the automatic loop is too slow for gcd and isprime (one rule step in four hours): make
     it finish;
  3. the suite kernels that deadlock or hang (quadrec's tokens on its ring, inner loops with
     zero trips, the search with a break): fixed in bdc, for every kernel;
  4. division and modulo (the frontend's remui; a divider cell under CLAUDE.md's rule);
  5. Dynamatic's integer integration tests into the suite, and which of them compile;
  6. the memory kernels through the automatic path;
  7. the suite table over everything, on many routes (the farm, 200 cores);
  8. Dynamatic's own figure for each suite kernel, so the ratio column is not empty.
- **From 23:00 UTC: the limits of before 2026-11-17 again: at most 4 subagents at a time.**
  Owner, 2026-11-18 18:35 UTC: "the previous setup worked, with quite room to spare" (that
  week stood at 52 % with a day and a quarter to go). For your judgement, not a limit:
  measured from the log of your first session here, 86 % of what it cost was its subagents;
  one that is kept busy costs two to three times what you cost per hour. Use them where
  they pay. Wait for a build or the farm in one long command, not in twenty short checks.
- Re-read this file every two hours, and once more at 23:00 UTC.

## This bot now runs on the cluster (owner, 2026-11-17)

The owner: "you could also just run them on cluster". A wrapper on the farm's cluster now runs
this bot inside the farm's own image, with 16 cores and 64 GB of its own, and starts a new
session the moment one ends. Its session ids start with `cluster-research`. It waits while a
cloud session holds the lock, so:

- **If your session id does not start with `cluster-research`, you are a cloud session: hand
  over.** At your next re-read of this file, bring the journal up to date (every lead in
  flight, every farm request you are waiting for by name, and what to read first), push,
  clear `research/LOCK`, and end the session. This once, it overrides "never end a session on
  your own". Do not start new work first.
- A cloud session that starts later and finds a fresh `cluster-research` lock stops, as for any
  live lock. If it finds the lock clear or dead, the cluster bot is down: work as normal.
- A cluster session follows this file as written, with the differences its prompt lists (no
  `cloud/setup-toolchain.sh`; `RUNS` in place of `/home/user/runs`; the node's cores for local
  builds and simulations; the farm, through requests as before, for anything wider).

## General first: the compiler does it, with nothing set per kernel (owner, 2026-11-17)

The owner looked at what the farm was running (shrink and candidate sweeps, one kernel at a
time, about 900 cores) and said: "are these really efficient ways to get faster i feel like
this cant possibly give more than eps of improvement", and "especially in the general case
(rmb that it would be ideal if the compiler did the optimizations automatically)".

He is right, on your own numbers. The sweeps were this file's instruction, not your mistake;
the instruction changes here.

- **Sizing is nearly used up on xorshift.** x1.0 is 18.91 ns and x0.55 is 16.85, so the sized
  delays were about 4.6 ns of the period and about 2.5 ns are left. x0.40 already fails. More
  shrinking can give well under 1 ns, and the gap to 15 is 1.85.
- **Nothing since item 14 is in the compiler.** Every result is a recipe: a sizes file for
  one kernel, and knobs that name instances (`BDC_FORK_OUT_LINK=n11__0`,
  `BDC_MERGE_RES_LINK=ucontrol_merge0`, `BDC_LINK_DEPTHS=ulink_n_trueResult_8=2`), all off
  by default. A kernel nobody tuned gets none of it.

From now on the first lead is the automatic path. This comes before the list under "Use the
quota that is left" and before more work on any one kernel.

1. **One switch, the same for every kernel.** Call it what you like (`BDC_AUTO=1`); unset,
   the output stays byte-identical. With it, and with no instance name, no sizes file and no
   factor given by hand, the flow chooses by itself what the recipes chose by hand: where the
   latches go and how deep the links are (the event graph's search, run inside the flow),
   ring-floor counting, fast fall, the loop-test rewrite and every other MLIR rewrite that
   has a proof from formal or a simcheck over the full range, the incrementer's short delay
   where the graph says it pays, and the sizes.
2. **Sizes from one rule, not a factor per kernel.** The draws say the static sizes are 1.4
   to 1.8 times longer than needed (x0.55 passes on xorshift, x0.70 on collatz and ipow).
   Find which part of the sizing rule carries that (the guard, the corner, the band position,
   a floor) and change the rule once, for every kernel, with the reason written down. The
   draws then check it. A factor found per kernel by a farm sweep is no longer a result.
3. **The headline is one table over all kernels, built with the one switch**: ns per
   iteration, Dynamatic's number, the ratio, and the hand recipe's best beside it. The gap
   between the automatic column and the hand column is the work. Put it at the top of
   `research/data/fifteen/README.md` and of every report. Include kernels nobody tuned:
   isprime and gcd are in the fixtures now, and fir, single_loop and test_loop_free are
   there if they build. For a new one, commit the C under `kernels/` and write
   `ASK: frontend output for <name>` in the journal: the frontend runs on the owner's
   machine and its output comes back as a fixture. Ask for at least three with different
   shapes (a nested loop, a branch that survives if-conversion, memory).
   **Answered 2026-11-17 22:13 UTC:** the frontend output for `nested`, `branchloop` and
   `memsum` is in `cloud/fixtures/frontend/` (made with `bdc/frontend.sh` at this branch's
   head, default knobs; the same run reproduces xorshift's and isprime's fixtures byte for
   byte). They are untuned by construction: keep them that way.
4. **xorshift's 15 ns target stands, and it now has to be reached by the automatic path.**
   A recipe that reaches it by hand is a lead for what the compiler should learn, not the
   result.
5. **The farm is for this**: the automatic flow on every kernel, many routes, the draws. Let
   the requests that are running finish and read them: they check candidates already on
   the list. Do not submit new shrink or scale sweeps for one kernel.
6. **Where more than a few percent can come from**, by your own budget (ideas, not a list to
   follow; write the prediction before each build):
   - wires were about 5 ns of the cycle on lever 3's route. Placement helped on some seeds
     and not others when it was set by hand; a constraint the compiler emits for every ring
     has not been tried as a rule;
   - latch placement took xorshift from 30 to 20.6 ns. On collatz, ipow and collatz64 the
     search found nothing with the knobs it had. What would a search over all sites find
     (Dynamatic places its buffers with a solver over the same kind of graph)?
   - the rising pass: handshake stages on the counter ring, fused by a pass, for any loop.

When a lever needs a choice that only one kernel can justify, say so and leave it out of the
automatic path.

## A benchmark suite for the compiler (owner, 2026-11-17)

The owner, when the three untuned kernels arrived: "tell it to make more kernels too, ideally
a bench suite for the compiler". This is part of "General first": the suite is what the
automatic path is judged on.

- **What.** `kernels/` grows into a suite a compiler can be judged on: 20 to 30 small kernels
  to begin with, chosen to cover shapes, not to flatter the flow. `kernels/SUITE.md` lists
  each one: what it exercises, its input range, where its expected values come from.
- **Shapes, at least one kernel each:** straight-line arithmetic; a counted loop; a trip
  count that depends on the data; loop nests two and three deep; two loops in sequence; a
  loop inside a branch, and a branch inside a loop that if-conversion cannot remove; an early
  exit (a search); several live values across the back edge; multiply (the DSP path), 64-bit
  arithmetic, shifts by a variable, a chain of compares; memory: read only, write,
  read-modify-write (a histogram), two arrays (dot product, fir), an index read from memory
  (`a[b[i]]`). Division and modulo if they lower; `kernels/README.md` lists the frontend's
  traps.
- **Take Dynamatic's own integration tests too**, the integer ones that fit
  (`dynamatic/integration-test/`, 95 of them, sources only). They are what Dynamatic reports
  on, so they make the comparison fair. Say which do not compile, and why.
- **Rules for a suite kernel.** Small enough to route in minutes. Its expected values are
  computed from the C source, never recorded from a run. Its vectors include the edges of
  the range (0, 1, the largest value, a trip count of 0). Nothing anywhere in the flow is
  set for it by name. A kernel the compiler refuses, or gets wrong, stays in the suite and
  is marked so: "does not compile" and "wrong answer" are results, and each is work for
  goal 1 or goal 3.
- **One command runs the suite through the automatic path and writes the table:** compiles;
  every answer right under the delay draws; ns per iteration; LUTs; Dynamatic's figure where
  one exists (say how it was obtained, and mark an estimate as one) and the ratio. Last
  line: how many of N pass, and the geometric mean of the ratio. When it exists, this table
  is the headline, in place of the six-kernel one.
- **You can run the frontend yourself now.** On the cluster its tools are in
  `$HOME/dynamatic` (clang, opt, dynamatic-opt and the rest, the owner's own build; checked
  2026-11-17 22:17 UTC: `bdc/frontend.sh` there reproduces the fixtures of xorshift,
  isprime, collatz64, nested, branchloop and memsum byte for byte). In the clone:
  `ln -sfn $HOME/dynamatic dynamatic`, then `./bdc/frontend.sh <kernel>`. Never commit that
  link (`echo /dynamatic >> .git/info/exclude`; from the next job on the wrapper does both).
  Commit the six `comp/*.mlir` files under `cloud/fixtures/frontend/<kernel>/comp/`, so farm
  tasks and the cloud bots have them. No `ASK` is needed for a new kernel any more.
- **Order.** About ten kernels across the shapes first, and the one command working end to
  end on them; then widen. The farm's 200 cores are for this.

## First: where does the board sit in the delay band? (2026-11-17 17:15 UTC)

Research and formal disagree, and the xorshift candidate depends on the answer.

- Research: the board runs at 0.22 to 0.29 of the prjxray band (rings 0.288; the August
  kernels within 1% at 0.222).
- Formal A: about 0.75 to 0.9 (gcd's measured latencies; tightened rebuilds of collatz and
  collatz64 at 0.75).
- Formal C36: item 35's board route keeps only 15 ps at its loop-entry steer, with live
  runts, when CARRY / F7 sit at the slow end of their band. That end has never been measured.
  With CARRY / F7 at the fast end every route keeps 245 ps or more.

Both positions cannot be right, and a kernel is mostly carry chains where a ring has none.
So fit them separately. The August bitstreams that ran on the board are in
`research/data/board-august/` on `claude/research` (the same five files for both of you).

- **Both:** simulate those same files with the August vectors and put predicted against
  measured ns per iteration, per kernel, into one shared table in `research/SIM-VS-BOARD.md`
  (formal sends its rows through `formal/FOR-RESEARCH.md`). Fit the LUT-and-routing band and
  the CARRY / F7 band as two numbers, and say how well the five kernels pin each one down.
- **Then** redraw the candidates with CARRY / F7 where the fit puts them, not uniform over
  the whole band, and say what that does to item 35 and to the ipow and collatz leads.
- This comes before the next speed headline. A candidate whose weakest spot sits in a band
  nobody has fitted is not yet the closest approximation of the board.

## Paths no vector can reach (2026-11-17; interim answer to your ASK)

Your ASK of 2026-11-16 (xorshift's counter: its 31-bit carry needs 2^31 iterations, so no
draw can judge UADDI0 and the compares) has gone to the owner. Until he answers:

- **Yes, keep the static size on a path the simulation cannot exercise.** The draws say
  nothing about it, so the static size is the only evidence there.
- **But first try to make the simulation reach it.** Start the run with the loop state
  preloaded: the counter a few steps below 2^31 and n to match, written into the state nodes
  once reset is released, on the same routed design and the same bits. The long carry then
  happens in the first iterations. Check the result against the oracle compiled from the C,
  started from the same state. If this works, the draws judge the incrementer like any other
  line, and the same trick gives collatz64 its 63-bit values.
- In each item, say which long paths were reached by vectors, which by preload, and which by
  neither.

## The board decides; every check is a proxy (owner, 2026-11-16)

The owner, asked whether to drop rule E at loop-header mux joins: "idc about the checks, they
dont matter, as long is it works on board / closest approximation to board. other checks are
just not-very-good proxies of correctness possibly".

There is one question about a build: **would it work on the board?** With no board, the answer
comes from the closest approximation of the board we can run. Every other check is a proxy.
This overrides any place below that makes a static rule a gate (the verification ladder, "No
blanket rules", BOARD-QUEUE wording).

- **Static rules are not gates.** A, A', E, H, I, M, TSE, hold_bits and corner_audit neither
  block a result nor certify one. They stay as tools: to choose what to shorten, and to find
  where a simulation failure comes from. Spend no more sessions on whether a rule earns its
  place, and build no more known-bad builds for rules. The questions about rule E at mux
  joins and about rule M's pessimism are closed: they decide nothing now.
- **What decides is the routed design, simulated as the board would run it:** the bits that
  are in the bitstream, the routed delays, the kernel's full input range (owner, 2026-11-14,
  unchanged). `toolchain.sh`, `fasm_equiv` and `ffmux_scan` stay required. They are not
  timing proxies: they make the simulated circuit the one on the board, and two board
  failures in August were exactly that.
- **The gate's start-up stays as it is (owner, 2026-11-16: "make it no").** +META_INIT is not
  the default. It stays opt-in, to tell a real failure from a start-up unknown when a run
  hangs.
- **One SDF at three corners is not the board.** The only measured delay error we have is the
  August ring data (`research/data/fid/`). Turn it into the delay model's uncertainty,
  reasonable and parametric, with the parameters and their source written down (owner,
  earlier: pick one and run, measure later): scatter per arc, an offset that grows with
  route length, a global scale. Simulate each candidate over many draws of its delays, on
  its routes, and report **the fraction of draws that return the right answers**. That
  fraction and the speed are the result.
- **Show how close the approximation is, on board data.** The fid model's acceptance on rings
  is a start. Kernels ran on the board in August with measured ns per iteration (xorshift
  47.66, collatz 91.96, collatz64 112.71; gcd 310 ns to 6.34 us by input). Simulate those
  same builds today and report predicted against measured. If this exists, cite it in the
  headline. If not, it is the first job of the next session, beside the speed work. The
  August `.fasm` and `.sdf` of the five bench builds, xorshift's included, are in
  `research/data/board-august/` since 2026-11-17 (read its README first).
- **Keep `research/SIM-VS-BOARD.md`:** every known way the simulation is not the board (glitch
  filtering, arbiters, start-up, voltage and temperature, the host), what the board showed
  in August if anything, and what the simulation does about it.
- **Sizes may be chosen by this simulation.** Shorten while the passing fraction stays at its
  ceiling, and say how far the choice sits from the first size that fails. Too short is
  still the silent direction: between two sizes that tie, take the longer.
- **Reporting:** per kernel, ns per iteration, the fraction of draws passing, routes and
  draws, and the model's error on the August builds. No rule tables in headlines or in
  BOARD-QUEUE items; a rule row may be named as a lead.
- **Formal's simulator of the decoded bitstream** (`formal/tools/margin`, simx) is a second,
  independent approximation and is asked to run the same draws. A build where the two
  disagree is the most useful thing either of you can look at.

## No blanket rules (owner, 2026-11-15)

Asked whether select links may be shortened (your question, journal 2026-11-15), the owner
answered "blanket rules are not real", and then "just like in general". Those two sentences
are the owner's. The rest of this section is how to apply them.

A blanket rule forbids a class of change ("never shorten a select link") without naming a
failure that a check could catch. It is not a property of the circuit. A real constraint
names the two signals that race, where each is launched and where it is captured, and comes
with a check that fails on a build known to be wrong.

- **The select rule is withdrawn.** A select link is sized like any other link, by the checks
  that model its races. There are two, and both must be clean at both corners on at least 32
  routes:
  - *arrival:* the select reaches the mux or steer before the request it gates. Rule E at
    that cell; in simulation, the select must not change while the cell's output request is
    high;
  - *hold:* the select stays until its data is captured. Rules H and I, and `hold_bits`.

  A result with shortened select links counts for the headline and may go to BOARD-QUEUE. The
  item says which links were shortened and which checks covered them.
  **Correction, 2026-11-15 (audit T116):** the first version of this bullet named only the hold
  checks. They do not test the arrival race. On collatz with select links at 0 the gate passed
  at three corners and H, I and `hold_bits` were clean, while umux0's select changed under its
  request on 960 of about 1460 rises. You had already found this with the corrected rule E
  summary and sized the selects by E; the text now says so.
- **A check earns its place by failing.** Before a result rests on the select checks, show
  them fail on a select link shortened until it races, on each kernel family and not only on
  the collatz64 failure. A check that cannot fail on a known-bad build is a blanket rule under
  another name.
- **Find the others.** Go through the gates, the tools and this file for every rule that says
  "never" or "always", or sets a fixed floor or a fixed guard, without a named race or a
  measurement behind it. For each one, write the mechanism it stands in for, the check that
  would replace it, and what it costs today in ns per iteration. One table in the journal.
  Replace or drop them, the costly ones first.
- **What stays.** The full gate over the full input range at both corners, `ffmux_scan`,
  `fasm_equiv`. A failing simulation always blocks. Too short is the direction a simulation
  can miss, so a shortened delay needs its own check clean at the worst corner. The rules
  about git, the lock, the audit branch, the farm and the toolchain fingerprint are not
  timing rules and are not affected.

## Formal works with you (owner, 2026-11-15)

Formal (`claude/formal`, three Lean shards) is back on, and the owner let it be pointed at
your builds: "maybe even hav it colab with rsch". It has the netlist decoded from the
bitstream, prjxray delay bands with a within-die variation parameter kappa, and an adversary
that searches for a delay assignment that breaks a build. On gcd_ps that gave a margin (it
fails at kappa = 0.36) and the race that sets it. Its first job now is the same for your
builds: every race, the kappa at which each can fail, and a failing trace you can replay. That
is the kind of rule "No blanket rules" asks for. It is also proving your two MLIR rewrites
(`pre_dec.py`, `pre_eq2.py`) equal to the originals over the full input range.

You cannot talk to it. You can read each other's branch.
- Keep `research/FOR-FORMAL.md`, newest first. For each build you want a margin for: kernel,
  build command and seed, SDF md5, what changed against the previous build (which links were
  shortened), and where its files are. Start with item 27's route, the first shortened-select
  candidate, and collatz items 25 and 26. Also list builds you know are bad (the collatz64
  select failure, `xf2_1`) with one good neighbour each: formal's tool has to tell them apart,
  and that is its negative control.
- Formal can rebuild a route from your command and seed. Where a file saves it time, commit it
  under `research/data/for-formal/NAME/` (the `.fasm` and the SDF, xz, under 1 MB each, no
  bitstreams).
- Read `formal/FOR-RESEARCH.md` on `origin/claude/formal` at the start of every session and
  again every two hours. A margin or a counterexample there is evidence about your build:
  replay the trace in your gate-level simulation and say in the journal whether it reproduces.
  A counterexample to a rewrite blocks the items that use it.
- Do not wait for formal. Its numbers add to your gates and do not replace them yet. When its
  tool runs from one command, run it on the farm over your routes and report the margin next
  to the period.

## FIRST: xorshift at 15 ns per iteration, in four-phase (owner, 2026-11-12)

The owner read `research/data/eventgraph/README.md` and decided two things:

- **The protocol stays four-phase for now.** Do not start a two-phase rewrite.
- **About 15 ns per iteration on xorshift is doable in four-phase, and the owner wants a
  harder push for it.** Do not stop at the knobs bdc already has.

Where it stands (bench top, simulation). The best gated xorshift is board item 14, about
30 ns (28.5 to 32.4 by seed). Dynamatic is 12.73. Two gaps separate 30 from 15:

1. **30 to 20: return-to-zero is still on the critical cycle.** The worst cycle with no
   polarity change is 19.2 to 20.7 ns. The step-4 search had three edits only (link depth,
   merge-output link, fast fall). What binds after them is the falling pass of handshake
   cells (9.08 ns of the x0.5 period), with the polarity changes at the merge and at the
   merge-output link's fork.
2. **20 to 15: the rising pass itself.** On x0.5 seed 1 it is excess delay 11.79, req/ack
   wires 7.85, handshake cells 1.23, logic 1.03. At least 5 ns has to come out of excess
   delay and wires.

**Every kernel is judged over its full input range (owner, 2026-11-14).** The owner read
the hold on item 18 and the finding on the x0.5 xorshift family, and decided: xorshift must
be correct for any 32-bit `rounds`, not only the bench's 12-bit range. The same holds for
every kernel and every input its C signature allows. From now on:

- **A gate pass is not enough where the vectors cannot reach a path.** For every path whose
  data range the gate's vectors do not span (loop counters and what compares them first),
  rules A and E must hold statically, at nominal and at the worst corner with the usual
  guards, for the longest carry the input type allows. Run this check before reading the
  gate, on every candidate.
- **Re-baseline the x0.5 xorshift family** (board items 4, 11, 14, 17, and 18 on hold). Give
  the counter's add and compare the sizes the static check asks for, measure again, gate
  again. In `BOARD-QUEUE.md`, mark every item that holds only on the bench's range as
  that, and say which items pass over the full range.
- **The headline of `research/data/fifteen/README.md` is the best xorshift build that passes
  both the gate and the static check over the full range.** Expect it to get slower first.
  Report both numbers once, so the cost of the full range is on record.
- **Check the other kernels the same way** (ipow's and gcd's counters and compares too), and
  the board items already listed for them.
- **A large static miss on a spanned path still needs an explanation** (2026-11-14, on the
  flag in the journal). ipow item 19's `umux3` misses rule A by 1.7 ns at nominal, and the
  select race traced on 2026-11-10 was on the same mux. Before the item stays on the list,
  either name the false path that makes the rule pessimistic there and show it with a trace,
  or restore the size and gate again. Do the same for any miss over 0.5 ns at nominal on a
  board item, whether or not the vectors span the path.
- **Then win the time back with a delay that depends on the data.** For `i + 1` the carry is
  as long as the run of trailing ones in `i`, so almost every iteration needs only a short
  delay and a rare one needs the long one. Choosing the delay from the operands is the known
  technique (speculative completion, Nowick and others); read it before designing. A delay
  that merely copies the carry chain tracks process and voltage but still pays the full
  length every time. This is a cell-level change under CLAUDE.md's rule, and it needs the
  static check above to cover both the short and the long case.

- **The `!=` loop test: yes, and LLVM already does it** (answer to the journal's question,
  2026-11-14). The owner's point: the kernel goes through LLVM first. It does, and
  `bdc/frontend.sh` step 4 runs `indvars`, whose exit-test rewrite turns `i + 1 < rounds`
  into `i + 1 != rounds` with LLVM's own proof. It does not fire because step 3 strips
  `target datalayout` (copied from Dynamatic's `compile.sh`): without it no integer width
  is legal, and `indvars` finds no loop counter to rewrite. Checked on xorshift's
  `clang.opt.ll` with LLVM 18: `-passes='function(loop(indvars))'` leaves `icmp slt`; the
  same command with a data layout line gives `%exitcond = icmp ne i32 %10, %1`. With the
  data layout through the whole step-4 pass list, the result is `icmp ne` against
  `smax(rounds, 0)` computed once before the loop.
  So this is a frontend fix, not a bdc rewrite and not a change to the loop lowering:
  - add it as an opt-in knob in `bdc/frontend.sh`, default off and byte-identical;
  - prefer the narrow form: one extra `indvars` after `loop-rotate`, with a data layout
    whose only native width is 32 bits, so that nothing is widened to 64 bits;
  - a data layout can change other passes' output, so diff the handshake MLIR of every
    kernel with the knob on and say what else moved;
  - then the usual: simcheck with `rounds` at 0, 1 and INT_MAX, the static check over the
    full range, the gate.

The 15 ns target stands, under this rule.

What to do, in this order:

1. **The budget, from the graph, before any build.** For item 14's routes:
   - every falling arc on a critical or near-critical cycle, by cell, and the edit that would
     take it off the cycle;
   - every delay on the rising ring: what it is, what its data needed in the worst iteration
     and corner, and what the rules (A, E, the select checks) require. That makes the removable
     part of the 11.8 ns a number;
   - every req/ack wire on the ring: its routed delay against the shortest it could be with
     the two cells adjacent. That makes the removable part of the 7.85 ns a number.
   Then the predicted period with all three taken. If it is not under 15, say what it is and
   what blocks it, and carry on with the levers anyway.
2. **New levers, the largest first.** Anything four-phase is allowed. That includes changing
   or adding cells under CLAUDE.md's rule (a stated reason and a routed-GLS check); new
   variants are opt-in and off by default. Ideas, not a list to follow:
   - return-to-zero off the cycle: storage at sites the search could not use (mux, steer and
     fork outputs, acknowledge paths); handshake cells whose falling arc is short where the
     protocol allows it (read the notes on `bd_join`'s acknowledge before trying); letting
     the counter ring's handshake stop waiting on the datapath;
   - a shorter rising pass: fewer handshake stages on the counter ring (13 today), by fusing
     its mux, add, compare and steer; per-instance sizing of the ring's delays under the
     select checks; a delay built from the same primitive as the data it bundles, so it tracks
     the data instead of covering it with margin;
   - shorter wires: place the ring's cells together (`RLOC_GROUP`, `PLACE_WEIGHT`).
3. **Predict, build, measure, gate, as in the event-graph work.** Write every prediction
   before the build. The graph under-charges an inserted stage by 1 to 3 ns of wire, so add
   that. The correctness bar does not move: the full gate, the select checks (see "No blanket
   rules" above), `ffmux_scan.py`.
4. **Keep going.** A lever that fails is a journal entry, not a stopping point: take the
   next one. Stop only when the budget shows no lever left, and then say what 15 ns would
   need.
5. **Then the other kernels.** Apply what worked to collatz, ipow and collatz64, and report
   each beside Dynamatic's number (collatz 14.05, collatz64 17.84). They have no target yet.

The loop lowering stays as it is (owner). If the budget shows that 15 ns cannot be reached
without changing it, say so with the number.

Report in `research/data/fifteen/README.md`: one table, a row per lever in the order
applied, with predicted and measured period on four seeds and the gate status. Its first
line is the best gated xorshift period and the gap to 15.

## Second lead: account for every delay on collatz's loop (owner, 2026-11-15)

The owner, on being told the odd/even select stage costs 7.5 ns of collatz's iteration: "surely
select cannot be taking 7ns". The select does not; its delay line does. On `graphs/colsz2_6`
(item 22's structure, 40.8 ns) the critical loop is all rising edges, and 25.1 ns of it (62%) is
delay-chain elements:

| stage | on the loop | of which delay chain | elements |
|---|---|---|---|
| ulink_n14__0 (umux0's select link) | 8.35 | 6.87 | 18 |
| uselect0 (`n & 1 ? 3n+1 : n >> 1`) | 7.46 | 5.63 | 16 |
| ucmpi2 | 7.30 | 5.39 | 16 |
| uaddi0 | 5.95 | 4.27 | 12 |
| umux0 | 3.55 | 1.75 | 6 |

uselect0 is one or two LUT levels behind a 16-element line. Before any more levers on collatz:

- For every delay line on the loop of the current build (item 25), on at least 8 routes, report
  the constraint that sets its length (rule, launch, capture), the data path it covers split into
  logic, wire and latch-enable skew, the request path, the guard, and the length the logic alone
  would need. One table, in `research/data/itercost/README.md`.
- If a line covers a path that cannot happen (a false path, a shifter built for a shift by a
  constant, a path through a constant operand), fix the cause, not the size.
- If it is real wire, say which wire, and whether placement of that one region would shorten it.
- This is diagnosis. No line is shortened because of it without the usual checks.
- Then the same table for collatz64 and ipow, whose loops are also datapath loops.

## The farm: thousands of cores, by request (owner, 2026-11-14)

**2026-11-17: the farm now holds at most 200 cores at a time (owner). Read "Limits" in
`research/cluster/README.md` before the next request; where this section says thousands, read 200.**

The owner: "you can use as many cpus as you want if it helps you". A cluster now runs jobs for
this branch. You commit a request, it runs as up to 256 parallel tasks in the cloud's own
toolchain image, and the results come back on the branch `claude/cluster`. A seed gives the same
route there as here. **Read `research/cluster/README.md` before the first use**; it has the
request format, what a task sees, what comes back, and the limits.

- Use it for everything wide: gates, route means, a sizing round checked across many routes,
  the static check on every route of a candidate. Keep quick single experiments local.
- Routes are now cheap, so stop deciding on two seeds. A lever is not "mixed" after two routes:
  ask for 32. Report a candidate as a distribution over at least 32 routes (median, worst, and
  how many routes pass the static check), not as a mean of 8. Twice already, sizes that held on the
  routes tried failed on one more.
- Never wait on it. If `status.txt` does not say `submitted` within 30 minutes of your push, the
  runner is down: say so in the journal, work locally, try again next session. While a request
  runs, do other work and look again later. Do not sit in a loop.
- The first request is already there: `farm_check` (the xfr candidate, seeds 1 and 3). Its
  results on `claude/cluster` are the proof that the round trip works.

## Done (kept for the record; do not redo)

- **Where one iteration's time goes** (owner, 2026-11-06): `research/data/itercost/README.md`.
  xorshift x0.5 is 39.06 ns: logic 1.03, excess delay 11.79, handshake 1.23, routing 7.85,
  RTZ 17.15. The critical cycle is the loop-control ring, not the datapath.
- **A second latch where the cycle waits on a handshake** (owner, 2026-11-09):
  `research/data/itercost/second_latch/README.md`. xorshift p8mo is 1.25-1.27x per round and
  passed the full gate (board item 11). collatz gained 1.8 ns only.
- **Storage chosen from the event graph** (owner, 2026-11-10): `research/data/eventgraph/README.md`.
  The graph reproduces all 26 itercost runs exactly and predicts new builds to about 1.4 ns.
  Storage plus fast fall: xorshift 1.34x, ipow 1.18x, collatz 1.13x (board items 13 to 15).
  Two-phase bound 1.78x on xorshift, 1.40 to 1.46x on collatz and ipow; the decoupled
  controller buys nothing. The owner chose to stay four-phase (2026-11-12).

## Effort and subagents (owner, 2026-11-05)

The owner raised the budget to about twice the single-thread, high-effort level.
Sessions run at max effort (`.claude/settings.json`). **You may use subagents,
but at most 4 at a time** (the owner's setting of 2026-11-07; it was 2 from 2026-11-15 20:15 to
2026-11-16 19:10 UTC on a usage scare, which a 16-hour reading has cleared). Wait for one to finish before starting another. A
subagent never touches git: it works in its own worktree or scratch directory
and reports back, and you review and commit what it found. Use them for
independent work that would otherwise wait (a second sweep while a build runs, a
proof while a check builds, a claim to reproduce), never to run the same work
twice. Never create scheduled routines or reminders.

The limit on progress is now memory and disk, not usage: the session has logged OOM kills
and disk-full restarts. Before starting a job, check `free -g` and `df -h`, and do not
run more than fits. A killed job is a lost result.

## No board for a long time (owner, 2026-10-25)

Nobody will run anything on silicon for the foreseeable future. Keep adding to
`BOARD-QUEUE.md` (one short entry per candidate; don't commit a bitstream for
each one), but never wait on it and never count it as verification. Goal 1 is
therefore as strong as the evidence available without a board, so make that
evidence stronger:
- more seeds (8+ for anything you ship as a default), with the worst seed
  reported, not just the mean;
- routed GLS at the slow AND fast corners of the SDF, plus delay scatter
  injected around the routed values (at least the measured 8.5% median ring
  scatter, and the tails beyond it), showing which margin fails first;
- negative controls that prove each audit and each GLS check can fail;
- re-checking the August silicon failures (bitstream bugs, memory inference,
  async latch, stale operands) as regression tests, wherever they can be
  reproduced without a board.

## Next, now that ring128 matches (owner, 2026-11-04)

Every runnable hard acceptance item matches, ring128 included at band 0.288 with a
0.76% residual. The gap left is the cell types the rings do not exercise, and only
the board can close it. The owner's rule for gaps like this: **pick a reasonable
parametric model, say what it is, run with it, and measure more later.** Do not
wait on data the project cannot get.

1. **The sim is the gate** (see "Once it passes acceptance"). For the cell types
   ring128 does not calibrate (CARRY4, MUXF7/F8, the slice output muxes), the
   default is the same band as LUT + wire, 0.288: same die, same process. Keep it a
   parameter (`GLS_SDF_BAND_CELL`), and also gate every design at the corner
   where those cells are at SLOW_MAX while everything else is at 0.288 (you
   already ran that check). Flops: none in the kernels, and the harness's flops
   are clocked logic covered by nextpnr STA plus the synchronizer rule, so they
   need no calibration.
2. **Fit the datapath band on the August gcd build.** The owner committed the
   August board builds and logs: `research/board/aug/` (README.md pairs each log with
   the `.bit` it programmed). `gcd_bench_gen` is the build behind the gcd cost model's
   board column (54-72% of the band on the datapath, against 0.288 from the rings).
   Run that exact build in the full stack, fit the per-iteration costs against
   `logs/gcd_cost.tsv` and `_gcdcost_*.log`, and do the same for the other matched
   kernels (collatz, collatz64, ipow, isprime, and their null builds for the
   harness overhead). If one band fits rings and kernels, the cell default
   stands. If the datapath sits slower, set the cell band from the fit, say so,
   and keep it a parameter.
3. **Speed: shrink the matched delays to what the sim proves.** The sizing guards
   were set for ~8.5% scatter, and the board shows 0.76%. A matched delay and the
   path it tracks are on the same die, so the shared corner cancels and only the
   residual and the cell-type mismatch need a guard. Shrink in small steps and run
   the full stack after each one (both corners, the measured residual as scatter,
   >= 8 seeds, derived oracles). A step that fails is reverted. Never go below
   what the sim proves at the slow-cell corner of item 1. Report the per-kernel
   speedup against BOARD-QUEUE #1/#2.
4. **Run every other kernel through the full stack** (ipow, xorshift, collatz,
   collatz64, isprime). So far only the rules have judged them.
5. **One ordered board list** at the top of BOARD-QUEUE.md for when the board is
   back, best first: gcd_ps with the 1000 vectors; the short-pulse C-element test
   (H_RUNT); the fastest design the sim accepts; a ring set on a second route, which
   would test the band transfer. Each item judges itself.

## First lead: a full-width gcd target for formal (owner, 2026-11-01)

Formal is proving that a gcd_hw bitstream is correct (claude/formal,
`formal/PROGRAM.md`, "THE goal"). Its current target, the BOARD-QUEUE #1
build, takes inputs from a 16-entry vector table, so "every a, b" cannot be
stated for it (`formal/FOR-RESEARCH.md` section 1). Build the same kernel
inside `cells/hw/gcd_ps.v` (32-bit operand registers from the PS, no vector
table), with the same flags and sizing flow as BOARD-QUEUE #1, put it through
the full stack (every audit, the fid GLS at both corners on >=4 seeds, with
operands from outside the 16 vectors and a derived oracle), and add it to
BOARD-QUEUE.md as a new item. Name one seed's `.bit` and `.fasm`, with md5s,
as "formal target" in that item. Check how the STATUS bits (i_ack, o_req)
cross from the async kernel into the PS clock domain; if there is no
synchronizer, that is a finding to fix first (see the async-latch lesson in
the journal). Do this before other leads. Also read FOR-RESEARCH sections 2
and 3: the kernel reorders pipelined pairs (the board harnesses must stay
sequential; check gcd_ps's FSM does), and the ua1 runt test is a cheap fid
GLS experiment.

## THE priority: a board-fidelity gate-level simulation (owner, 2026-10-27)

The owner considers this the most important thing for developing without a
board. It comes before every speed lead. Give it the main thread until it is done. Other work only fills idle cores.

### The audits are heuristics; an accurate GLS is the ground truth

The post-route rules (A/E/F/H/I/J, `tighten.py`, `skew.py`) are heuristics:
fast screens that say where to look and propose sizes. The ground truth is
meant to be a very accurate gate-level simulation of the routed FPGA. The
data for one exists in prjxray, so build it. This is the top lead under
goal 1, and it also unlocks goal 2: today a rule violation blocks a build
even when routed GLS passes, and that is where most of the remaining speed
is held back.

Why today's GLS is not that ground truth yet: `cells/gls/` simulates
nextpnr's SDF, and nextpnr's `getPipDelay` (`xilinx/arch.h`) is a single
number per pip. It is the pip's max delay plus one lumped RC term, with
the upstream wire length guessed from the Manhattan distance to the driving
pip. There is no fanout loading, no rise/fall, no fast corner, LUT
route-throughs are a flat 300 ps and site pips are 25 ps. The x0.9/x1.1
"corners" only scale those numbers. Silicon already disagreed: 76 of 128
rings ran slower than the SDF, by an offset of about +988 ps.

What prjxray's numbers are, and what they are not: they were extracted from
Vivado's timing model (`prjxray/fuzzers/007-timing`). prjxray's reduced model
matches Vivado to about +/-1.5% on most nets; clock nets are the exception
(`prjxray/minitests/timing/README.md`). Vivado's model is a sign-off model:
fast/slow, min/max corner bounds across PVT for a speed grade. It is not the
delay of this chip. Expect the board to fall inside [fast min, slow max] and
not on any one corner, and expect paths on one die not to sit at the same
point in that band. Check which speed grade the zynq7 data is for (the board
is -1). The ring data says where in the band this board sits. If a ring runs
slower than prjxray's slow max, the model or the comparison is wrong: chase
that before anything else.

Build it:
- A delay calculator that takes the routed design (`*_routed.json`: each
  net's pip list, so the real RC tree) and prjxray-db `zynq7/`
  (`tile_type_*.json`: pip intrinsic delays at 4 corners, pip and wire R/C;
  `timings/*.sdf`: cell arcs with rise/fall, fast/slow). Compute every
  sink's delay with the Elmore RC tree in `prjxray/prjxray/timing.py`
  (Outpin/Buffer/PassTransistor/Wire/Inpin, pi-model wires, `PvtCorner`);
  reuse it, don't rewrite it. Emit an SDF with min:typ:max per arc that
  `gls/gen.py` can read in place of nextpnr's.
- Check it on small cases by hand (one buffered pip; one pass-transistor
  chain; a fanout-of-N net) and against nextpnr's numbers. Explain every
  large disagreement before trusting either.
- **Validate against silicon already in the repo:** the n=128 ring
  measurements and the five rings in `cells/hw/README.md`, plus the
  board-measured kernel timings (gcd 310 ns to 6.34 us, the ns-per-iteration
  table) wherever the measured bitstream's route can be reproduced. Report the
  model's error distribution (median, tails, and whether it depends on length).
  What is left over becomes the scatter that GLS injects, and the measured
  ring scatter remains a floor.

Delay is not the only gap. A board-fidelity sim also needs:
- **The netlist the board actually runs.** Build the simulation netlist from
  the FASM or bitstream (with prjxray-db's segbits; look at existing fasm2bels
  work first) rather than from nextpnr's routed JSON. Three of the four worst
  bugs here were in the bitstream, where the netlist, the SDF and every
  simulation were correct. `fasm_audit.py` checks LUTs and DSPs only. A sim
  built from the FASM covers routing and every other bit.
- **Glitches and pulses as silicon has them.** Wires are already transport
  delays (`prims.v`). LUTs, MUXF7/8 and FF clock/SR pins still use iverilog
  module-path (inertial) delays, which swallow narrow pulses. A LUT is evaluated
  as a zero-time mux tree, so its internal hazards on multi-input changes are
  not modelled. Model what the silicon does (look for published LUT hazard
  behaviour), or show that no C-element or latch in the library depends on it.
- **Metastability.** The arbiter and synchronizers resolve in zero time in sim.
  Model near-simultaneous arrivals: random resolution time, or X, both
  choices exercised.
- **Within-die variation.** Use correlated per-region scatter plus per-wire
  random scatter, both sized from the ring data, not a single global scale.

### Acceptance: the sim must reproduce the board
Before the sim is trusted, it has to reproduce what silicon already showed,
from the same bitstreams or rebuilt identical routes:
- **timings:** the ring periods (n=128) and the board-measured kernel timings,
  within the measured scatter;
- **failures:** each August failure that was observed on silicon, simulated
  from the failing bitstream: gcd's livelock (the lut-pinmap bug), abs going
  negative, the gcd_bench_gen hang (the async latch corrupting the state
  register), the DSP products gated to zero, isprime's late read. A sim that
  passes a bitstream the board failed is not board-fidelity.

The owner is not sure how accurate the statistics on some of those board
failures are. Before using a silicon datum as an acceptance test, grade it
from what is on record: sample size; whether it was reproduced; whether the
instrument was itself verified (two board probes read stale operands, and
one checker was blind at all 24 points); and whether the stated cause was
later revised. Use only the well-established data as hard acceptance tests.
Deterministic bitstream bugs (lut-pinmap, dsp-constpins, dsp-areg) and the
n=128 ring set are good candidates. Treat the rest as soft evidence, and say
which is which in the journal. A soft datum the sim disagrees with is
something to look into, not proof that the model is wrong.

Write down each mismatch against hard data, then fix the model, not the test.

### Once it passes acceptance
A design is verified when this sim passes it: slow and fast corners, the
measured residual as scatter, at least 8 seeds, and derived oracles. **The
rules then do not matter.** They are possibly-inaccurate heuristics. Use them
to propose sizes and to say where to look, and never as a gate. Remove rule
gates from the ship path (keep the scripts as tools). A GLS failure always
blocks. Until acceptance is met, keep the current gates exactly as they are.

## Goals, in strict priority order

1. **Works on hardware, as far as can be verified without a board.** A faster
   design that might fail on silicon is worth less than nothing. The
   verification ladder, weakest to strongest:
   `cells/check.sh` gates, then every post-route audit in `cells/verify/`
   (rules A/E/H, loop audits, `tighten.py`), then routed back-annotated GLS
   (`cells/gls/`) across at least 4 placer seeds, with oracles derived from the
   C in `kernels/`. Anything that reaches the top of this ladder goes into
   `BOARD-QUEUE.md` with the exact command and the pass criterion. Prove that
   each audit can fail before trusting it to pass.
2. **As fast as possible.** The metric is ns per loop iteration (the critical
   cycle; delay sums do not predict it) and transaction latency for each kernel
   in `kernels/`. Report means across seeds, compared against the numbers in
   README.md and the most recent journal entry. Leads already known, in no
   particular order: rule E blocks tightening (rule A alone gave 1.99x on the
   board); enable replication for `bd_mux` control inputs; launch selection in
   rule E; placement (`rloc_stamp.py`); per-kernel RTZ tail (gcd pays 23
   cycles, cause unexplained); two-phase links (`bd_mlink.v`, standalone so
   far). A speedup counts only if every rung of goal 1 still passes.
3. **Features.** More of C lowered: memory, new kernels, and wider op coverage
   in `bdc/`. Dynamatic is not built in this sandbox and the frontend outputs
   in `cloud/fixtures/` cover the existing kernels. Building Dynamatic (LLVM)
   is allowed, but only as a background job, and only when goals 1 and 2 have
   nothing to work on.

## Budget

One session starts per day (owner, 2026-10-29). Run continuously: never end a
session on your own. When one lead is done or blocked, journal it and start the
next one; the leads under goal 2 and the journal's `Next:` lines are never empty. The lock keeps there from being two sessions at once, so:
- Refresh `research/LOCK` (commit and push) at least every 45 minutes. A lock
  older than 90 minutes counts as dead.
- Background processes die with the session. Commit before starting anything
  long, so that a killed session loses only the job that was running.

## Each session

1. `git fetch origin && git checkout claude/research && git pull --ff-only`.
2. **Lock.** Read `research/LOCK`. If its timestamp is less than 90 minutes old
   and it names a different session, another run is alive: stop immediately and
   change nothing. Otherwise write `<UTC ISO time> <your session id or random
   tag>` to it, then commit and push. Refresh it at every commit. If the push is
   rejected, someone else holds the lock: stop.
3. `cloud/setup-toolchain.sh` (from cold this takes a long time). If it fails,
   fixing it is the session's work. Never weaken `toolchain.sh`.
4. Read the last few entries of `JOURNAL.md` and pick the next step: the
   highest-priority goal with an open, concrete lead.
5. Work in small, verified steps. Commit and push at least every 45 minutes,
   with a `### progress HH:MM` note under this session's entry each time (take
   the time from `date -u +%H:%M` and the session heading's from `date -u`; never
   estimate it, since past entries ran up to 11 hours off the commit times), so that a
   killed session loses little. Exactly one `## Session` heading per session.
6. Keep the branch in a state the next session can pick up at any moment, since
   the session can end without warning: write the journal entry, update `BOARD-QUEUE.md`,
   clear `LOCK` (empty file), and commit and push.

## Journal entry format (append, newest last)

```
## Session <UTC date time> -- <one-line result>
Toolchain: <patch sha from $TC/openxc7/.patches.sha>   Seeds: <list>
Did: ...
Measured: <table: kernel, metric, mean, range, n, vs previous>
Does NOT show: ...
Next: ...
```

A negative or null result is a result: record it, including leads you
disproved.

## Landing work

- Push only to `claude/research`. Keep one draft PR `claude/research -> main`
  open and keep its description current (if `gh` is not available, skip this).
  Never merge.
- Revert anything that breaks a gate. A red branch blocks the next session.
- Never delete or rewrite the owner's or Devin's history.

## Read the independent audit every session (owner, 2026-10-27)

An independent auditor works on branch `claude/audit`. It writes only
`audit/REPORT.md` and `audit/findings/`. At the start of every session, run
`git fetch origin && git show origin/claude/audit:audit/REPORT.md`. Fix every
REFUTED or OVERSTATED row that concerns your files, or answer it in your
journal with evidence. Never edit the audit branch.

**First, the corner misreading (REFUTED by the audit).** The prjxray SDF
triples are `(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`
(`prjxray/utils/makesdf.py:63`). They are **fast and slow corners, not rise and
fall.** So the "O6 rise 45-56 ps, fall 100-124 ps" and the "rise and fall differ
by 2.2x" figures are wrong: 56 and 124 are the fast-corner and slow-corner
bounds of one arc. Nothing in prjxray-db separates rise from fall. Never mix
corners within one analysis (a fast-corner rise with a slow-corner fall);
use one consistent corner, or the corner model with scatter κ.
- Fix `cells/sim/bd_prims_sim.v:57-61` (BD_T_RISE 56 / BD_T_FALL 124, 5LUT
  55/152). Then re-run and re-judge every result that used it:
  tb_arb_overlap, arb_mtbf and the null-generator testbenches. The routed GLS
  (nextpnr SDF, 124 ps on both edges) is not affected.
- The audit also CONFIRMED the GLS sample-at-fire early edge, rule J's missing
  site-pin delays (BQ#1 may be negative under fast-early/slow-late), and the
  rule F in-flight gap. It found that the ring validation rests on ONE ring
  measured on silicon. Treat these as open defects.
