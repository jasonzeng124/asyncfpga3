# Formal-model feasibility program

## Effort and subagents (owner, 2026-11-05)

The owner raised the budget to about twice the single-thread, high-effort level.
Sessions run at max effort (`.claude/settings.json`). **You may use subagents,
at most 2 at a time for shard A and 4 at a time for shards B and C** (raised, owner, 2026-11-07). Wait for one to finish before starting another. A
subagent never touches git: it works in its own worktree or scratch directory
and reports back, and you review and commit what it found. Use them for
independent work that would otherwise wait (a second sweep while a build runs, a
proof while a check builds, a claim to reproduce), never to run the same work
twice. Never create scheduled routines or reminders.

Spend the extra capacity on what is still missing, S4 (composition) and S6 (liveness),
not on more counterexamples or margin points. Shards A and C both proved the same
refutations on 2026-11-07: read the other shards' journals before starting a probe.
Memory is the limit (OOM kills in check.sh and the audit's builds): keep Lean under
`formal/slot.sh`.

## THE goal: the real gcd bitstream is correct (owner, 2026-10-31)

The owner wants **one theorem: the gcd_hw bitstream, as it will be flashed,
computes gcd on the board.** This replaces goal 2 below and the phase plan
(the 48-hour phases are over). Every session works toward this theorem and
nothing else, until it is proved or refuted. The model work (goal 1) and the
reusable checker (goal 3) are worth doing only where this theorem needs them.

**The target is a file, not a design.**
- Shard A picks the bitstream: the BOARD-QUEUE #1 build on `claude/research`,
  one seed. It copies the `.bit`, and the `.fasm` it was made from, into
  `formal/target/` and records their md5s in `formal/target/README.md`. The
  theorem is about those bytes. If research changes the design later, the
  theorem stays about this file; a new target is a new decision, journaled.

**The statement.** For every a, b < 2^31: when the PS-side harness offers
(a, b) on the input channel under the four-phase protocol, the circuit
configured by the target bitstream eventually returns gcd(a, b) on the output
channel, returns to idle, and accepts the next pair. That is **safety and
liveness**, for every input, for every assignment of delays allowed below.
The environment is **not** sequential: it may offer pair k+1 as soon as the
input handshake of pair k completes, without waiting for its output
(pipelining, owner 2026-10-31). The board harness (`cells/hw/gcd_bench.v`)
waits for each output, so it is one special case. The theorem must cover the
general one: the k-th output is gcd of the k-th pair, in order, for any
number of pairs. If a second pair can enter the loop while the first is
still in it (through an arbiter at the loop's entry merge, say), the theorem
must show that this is harmless or that it cannot happen. If it is not
harmless, that is the counterexample.
The statement, with every definition it uses, goes in
`formal/lean/Formal/Target/Spec.lean`. Shard A writes it first, then it is
frozen: changing it after that needs a journaled reason and an audit row.

**The only assumptions allowed**, each a named hypothesis in that one
statement. None may assume a property of the gcd circuit itself.
1. *H_DECODE:* the prjxray database maps the target's bits to the configuration
   correctly: which LUT INITs, which pips, which site muxes are set. This is
   the one trusted step. Make it small: decode the `.fasm` into the Lean
   netlist with a checked decoder, and re-encode the netlist back into FASM
   lines and compare with the target, so that a decoder bug shows up.
2. *H_DELAY(g):* every arc of the decoded netlist (LUT pin to output, pip,
   wire, site hop) has its delay in the prjxray band `[FAST_MIN, SLOW_MAX]`,
   widened by a guard factor g, with within-die variation bounded by a
   parameter κ (the corner model already in Core). The theorem is
   parametric in g and κ. **Its value is the largest g and κ for which it
   holds**, since the owner cannot measure them; report that margin.
3. *H_PRIM:* each primitive behaves as its Core digital model: a LUT is its
   Kleene mux tree, glitches included; MUXF, CARRY4 and the flops as modelled.
   Use the delay semantics (transport, inertial or involution) that is
   pessimistic for what is being proved, or prove the result for all three.
4. *H_ARB(T):* each arbiter cell's internal race resolves within T ps. The
   theorem is parametric in T.
5. *H_ENV:* the PS harness obeys the four-phase protocol on the boundary
   channels, with no timing assumption on it.
Unit-time gate models, `Held`/H_BUNDLE, H_CELLS, H_START_ONCE and every other
contract on the circuit's own cells must be **derived**, not assumed. They
may appear in intermediate lemmas only.

**How: a verified checker, not 465 hand proofs.** Prove, once, a generic
theorem: if a checker accepts a decoded netlist and the bands, then the
circuit is safe and live for every delay in the bands. Then run that checker
on the target. Reuse `tcheck`, the Core primitives, the cell proofs and the
token-level `gcd_hw_graph_computes_gcd`; bridge, don't rebuild. The
pieces that must close, in order:
- the netlist comes from the bitstream, not from the Verilog or nextpnr's
  output, so `extract.py`'s role goes away or is proved;
- the timing obligations are generated by the checker from the netlist, and
  their **completeness** is part of what is proved: every race the semantics
  allows is covered;
- the feedback loops (C-elements, rings, the arbiter) are handled inside the
  proof, not cut by hand;
- the per-cell results compose over the whole network, and the network
  refines the token graph, so `gcd_hw_graph_computes_gcd` gives the answer
  and its liveness.

**A counterexample is a result.** If the theorem is false at g = 1, the
deliverable is a concrete delay assignment within the bands, as a trace,
checked against research's fid GLS, plus the race it exposes. The 9 FASTFALL
lines that fail under the band and the ArbOrd failure under scatter are
leads. A refutation found early is worth more than a proof found late; say
so plainly in the journal, and put it in `formal/FOR-RESEARCH.md`.

**Shards.** Keep your files and locks.
- A: target, Spec.lean, the decoder and its round trip, and the top-level
  assembly.
- B: H_PRIM for every primitive the target uses, with prjxray arcs, and the
  arbiter under H_ARB(T).
- C: the generic checker theorem: completeness of obligations, loops,
  composition, refinement to the token graph.

**Progress is measured by one list,** in `formal/target/STATUS.md`: every
hypothesis of the current best theorem about the target, and for each one
whether it is one of the five allowed or still to be derived. The list must
shrink. A day that does not shrink it, or produce a counterexample, has to
say why in the journal.

### Owner decisions, 2026-11-01 (answers to FOR-RESEARCH 1 and 3, and the g/κ question)
1. **New target: a full-width gcd bitstream.** Research builds `cells/hw/gcd_ps.v`
   (32-bit A_DATA/B_DATA registers driven from the PS, separate request
   path, no vector table) as a BOARD-QUEUE item and names its `.bit`/`.fasm`.
   When it lands, shard A makes it THE target (copy, md5s, journal the
   switch). Keep the 16-vector target's results: the proof is generic in the
   boundary, so the second target should cost only the decode. The boundary
   of the theorem is the kernel's handshake ports inside gcd_ps. The AXI
   register slave is the environment: state what H_ENV then requires of it,
   including how STATUS inputs cross into the PS clock (a missing
   synchronizer there is a finding, not an assumption).
2. **H_RUNT(w) is a sixth allowed hypothesis:** a LUT input pulse narrower
   than w ps does not propagate to its output. Use `SpecRunt.lean`
   (`NetCorrectSeqRunt w`). Report the margin as a function of w, with
   w = 20 ps as the headline; w = 0 (no runt filtering) stays the
   pessimistic bound and is still reported.
3. **Approve the g/κ fix to `Adm`:** g scales the corner window,
   `[(1-κ)·lerp(FAST_MIN,SLOW_MIN,c)/g, (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)·g]`.
   This is a change to the frozen Spec with the owner's reason, so journal
   it and give the audit a row. Fix the six B/C files that build on the old
   shape, and say which claimed lemmas become false (C's `adm_le_dmax`) and
   what replaces them. The margin is the (g, κ) frontier.
4. The pipelined statement stays refuted for this kernel; the owner keeps
   the lowering as is. The target theorem is `NetCorrectSeq` (sequential
   env: next pair only after the previous output's handshake completes).

## North star (owner, 2026-10-27). The goal above overrides this and everything below.

**Keep it digital for now.** No analog models, no ODEs, no MTBF, no slew. Make
the digital model **as faithful to the chip as a digital model can be**. Three
goals, in this order:

1. **A correct mathematical model of the chip.** A digital semantics for every
   primitive the designs use (LUT6/LUT6_2, MUXF7/F8, CARRY4, the flops and
   latches, DSP48E1 and RAMB18E1 if a design uses them, wires and pips), with delays
   from prjxray-db. Within digital, push fidelity as far as it goes:
   - a LUT is its mux tree, so input skew can glitch the output (a digital
     hazard), not "all pins sampled at one instant";
   - per-edge (rise and fall) windows where the data distinguishes them,
     otherwise one shared band, with the reason written down;
   - transport, inertial or involution delay per primitive, chosen and
     justified against the fabric (pulse shrinking and runts are digital
     effects and belong here);
   - corner-correlated delays (shared corner plus local scatter).
   Every place the model is less faithful than the chip is a named hypothesis
   or an entry in `FEASIBILITY.md`'s fidelity table.
2. **A correct gcd.** (Superseded by THE goal above.) A theorem that the routed gcd_hw, as built (netlist and
   routed delays), computes the C gcd on every input, under the model. Every
   hypothesis is named, and none is vacuous.
3. **Useful for verifying other designs.** The model, the netlist import and the
   verified checker form a reusable tool: given any routed design from this
   flow, it proves it correct or prints a counterexample trace. Document how
   to run it on a new kernel, and run it on at least one kernel besides gcd.

Results that do not serve one of these three are low priority. Every claimed
result carries a plain-language problem statement next to it: what is
assumed, what is proved, and what it does NOT cover. The journals must not say
more than the Lean says.


You are the only agent on branch `claude/formal`. A separate agent works on
`claude/research`. Never push there, never push to `main`, never merge.
Nobody will answer questions: decide, write down why in `formal/JOURNAL.md`,
and keep going.

## The question

The owner asked: **can this project's circuits be formalized at gate level,
and proved correct (in Lean 4 or similar), and how feasible is that?** Answer
it with working prototypes, not opinion. The deliverable is
`formal/FEASIBILITY.md`: for each track below, a verdict (works / works with
effort X / blocked by Y), the evidence (files that check, with their run
command), the estimated effort to finish, and what it would buy the project.

Background, in this order: `CLAUDE.md`, `cells/docs/LIBRARY.md`,
`cells/docs/ARBITER.md`, `cells/rtl/*.v` (the frozen cell library; read
`bd_arb.v`'s header carefully), and the "board-fidelity GLS" section of
`research/PROGRAM.md`. Cells are LUTs. C-elements and latches are LUTs whose
output feeds back to their own input. The arbiter is a decision element
with NO analog metastability filter, because a filter cannot be built on
this fabric.

## The model must be gate-fidelity (owner)

The model is only worth proving things about if its gates are faithful to the
fabric's real gates. A proof about an idealized gate says nothing about the
chip. So each primitive is modelled as what it physically is on a 7-series
part, and the fidelity of each choice is stated and, where possible, checked:
- **LUT:** an SRAM-driven pass-transistor mux tree behind input buffers, not
  a Boolean function. That is what decides its glitch, X and runt behaviour.
- **Routing:** buffered pips and pass-transistor pips (prjxray-db marks which
  is which), and wires with R and C, with delay bounds taken from prjxray-db's
  fast/slow min/max for this part (`prjxray/prjxray/timing.py` is the model).
- **MUXF7/F8, carry, FFs (CK->Q, setup/hold, async SR):** as the silicon has
  them.
- **Where the fabric is not known:** for example, whether a real LUT follows
  Kleene semantics exactly. Make it an explicit hypothesis, write down how it
  could be tested (a GLS or board experiment), and never assume it silently.
Compare the model with the board-fidelity GLS being built on
`claude/research` (read-only). Where the two disagree, find out which is wrong.
`FEASIBILITY.md` must say, for every primitive, how faithful its model is.

## The model the owner has in mind

Gate level: an arbiter is just a collection of gates, and its behaviour,
metastability included, should come out of the gate model rather than being
postulated. The expected layering (test it, and change it if it fails):
1. **Signals** are traces over time. **Gates** are relations between input and
   output traces, not functions, because delays are only known to lie in a
   range. **A circuit** is the conjunction of its gates. Theorems have the form
   "for all traces that satisfy every gate relation, property P".
2. **Delay channels:** bounded pure delay; inertial; and the involution channels
   of Fuegger/Najvirt/Nowak/Schmid (a faithful binary model; check the paper).
   Find out which ones admit the proofs below.
3. **Values:** binary first. Then Kleene three-valued {0,1,X}, with LUT
   semantics "1 if every INIT entry consistent with the inputs is 1, 0 if every
   one is 0, else X" (compare Lenzen/Fuegger/Friedrichs on
   metastability-containing circuits).
4. **The arbiter is a digital race, not a special element (owner,
   2026-10-27).** `bd_arb` is LUTs, so model it as the same gates and channels
   as everything else: two requests racing through LUTs and wires with
   bounded (and involution) delays. "Metastability" then shows up digitally:
   a nondeterministic winner when the arrivals are close, runts, a loop that
   oscillates or holds undecided for an unbounded time. Prove what holds
   for EVERY such digital behaviour (exclusion, the handshake, what
   downstream can see), or produce the counterexample trace, and derive the
   exact race conditions (the timing windows) under which each property holds.
   This is the primary model. No MTBF.
Every assumption is a named hypothesis in the theorem statement. **No `sorry`,
no `axiom` (other than Lean/Mathlib's standard ones) and no `native_decide` in
anything reported as proved.** `formal/check.sh` must build every claimed file
and fail on any of them. Report unproved goals as unproved.

## Tracks

Work the probes below for your shard (see Shards). Each probe writes only its
own files under `formal/lean/Formal/<Track>/` and `formal/notes/<track>.md`.
Record what checks, what doesn't, and why.

1. **Toolchain** (you, first): install elan, Lean 4 and Mathlib (use
   `lake exe cache get`; never build Mathlib from source unless that fails).
   Make one lake project at `formal/lean` and write `formal/setup.sh` (idempotent,
   timed) and `formal/check.sh`. Lean with a Mathlib import uses several GB of
   RAM per process. Check `nproc`/`free -g` and write `formal/slot.sh`, a
   `flock`-based semaphore that caps concurrent `lean`/`lake` processes at what
   fits. Every Lean process goes through it. Check single files with
   `lake env lean <file>` while iterating.
2. **Trace representations** (3 probes, compete): ℝ → Val; event lists
   (time-sorted transitions); discrete time ℕ with bounded steps. Compare how
   easy the delay-channel lemmas below are in each, then pick one and record why.
3. **Delay channels** (3 probes): bounded pure delay, inertial, involution.
   Prove basic lemmas (composition, monotonicity, how short pulses behave).
4. **Kleene LUT** (2 probes): the semantics; prove that a single input change
   with an unchanged output is glitch-free, and that X containment holds for a
   chosen LUT. Decide whether `decide`/`bv_decide` handles 6-input LUTs.
5. **C-element from a feedback LUT** (`bd_ce.v`, 2 probes): prove it behaves
   as a C-element, and derive the exact timing conditions it needs under
   bounded delays.
6. **Latch and link** (`bd_latch.v`, `bd_link.v`, 3 probes): the four-phase
   handshake, and the bundling condition (request after data) as a derived
   hypothesis.
7. **Arbiter** (`bd_arb.v`, 4 probes): binary (the tie and runt cases);
   Kleene (does X reach both grants?); the digital race (item 4: all
   arrival orders and gaps, runts, oscillation); the handover-ordering claim in the header.
8. **Composition** (2 probes): correct cells plus their timing conditions
   give a correct handshake network; deterministic dataflow equals sequential
   semantics (Kahn) on a small graph, e.g. a gcd-shaped loop.
9. **Ring needs three stages** (1 probe): the project's decided rule, proved.
10. **Verified timing checker** (2 probes): a checker over a toy routed netlist,
    with delay intervals, proved sound against the bounded-delay semantics.
    Would it make rule E/A/J exact?
11. **Netlist import** (2 probes): turn a yosys JSON netlist of one cell into
    Lean terms automatically, so the proofs are about the real cells and not
    hand transcriptions.
12. **Other tools** (2 probes): try the same C-element/arbiter checks in an
    async-circuit tool (Workcraft/Petrify, UPPAAL for timed automata) and in
    a SAT/SMT model checker. Compare effort and coverage with Lean.
13. **Literature** (2 probes, web search): formal verification of bundled-data
    and self-timed circuits; metastability-containing logic; the involution
    model; Lean or Coq hardware projects; any Lean work on Dynamatic or
    dataflow circuits. Notes with citations go in `formal/notes/literature.md`.

When a probe finishes, start the next most informative one. Use the cores.
When `FEASIBILITY.md` has a verdict for every track, keep going on the most
promising track toward a real result: the Kleene cell-library proofs or the
verified timing checker are the likely candidates. Keep `FEASIBILITY.md`
current.

## Shards: three sandboxes at once

One sandbox cannot run 30 Lean processes, so the work is split across three
routines, each a separate sandbox with its own lock. The routine prompt names
your shard. All three push to `claude/formal`.

| shard | lock | tracks | owns |
|---|---|---|---|
| A (lead) | `formal/LOCK` | 1 toolchain, 2 traces, 3 delay channels, 4 Kleene LUT, 13 literature | `formal/setup.sh`, `check.sh`, `slot.sh`, `formal/lean/` project files (lakefile, toolchain, root `Formal.lean`), `Formal/Core/`, `FEASIBILITY.md` |
| B | `formal/LOCK-B` | 5 C-element, 6 latch/link, 7 arbiter | `Formal/Cells/`, `formal/notes/B-*.md`, `formal/JOURNAL-B.md` |
| C | `formal/LOCK-C` | 8 composition, 9 ring, 10 timing checker, 11 netlist import, 12 other tools | `Formal/Net/`, `Formal/Timing/`, `Formal/Gen/` (generated cells), `formal/tools/`, `formal/notes/C-*.md`, `formal/JOURNAL-C.md` |

- Write only the files your shard owns. Before every push, run `git pull --rebase`.
  Since no two shards share a file, rebases do not conflict. If one does, you
  touched a file you do not own: undo that change, don't resolve it.
- Shards B and C: if `formal/setup.sh` does not exist yet, install Lean and Mathlib
  yourselves for local use, but don't commit any setup files. Switch to A's
  `setup.sh` once it exists. Until A's `Formal/Core/` (traces, delay channels,
  LUT semantics) lands, define what you need in a local `Formal/Cells/Prelim.lean`
  or `Formal/Net/Prelim.lean`, and port to Core afterwards. Note any mismatches.
- Shard A writes `FEASIBILITY.md` from all three journals and the notes. B and C
  put their verdicts at the top of their journals, in the same form.
- Lock and journal rules are the same for every shard (B and C use their own
  lock file and journal).

## After the feasibility verdicts: the next 48 hours (owner, 2026-10-27)

Feasibility is a few hours from done. Then turn it into something the project
uses. The capstone is one end-to-end theorem: **the routed gcd_hw computes gcd
(the C in `kernels/`) under an explicit, finite list of hypotheses about the
silicon**, where every hypothesis is named, graded, and paired with a test.
Work in phases; within a phase, shards run in parallel. Keep `FEASIBILITY.md`
and the journals current, and keep `check.sh` green.

### Phase 1 (about 0-12 h): one substrate, the real cells
- **A:** consolidate `Core`: one discrete ℕ-ps substrate plus the ℝ bridge and
  the discretisation theorem. Settle the corner model (shared corner plus local
  scatter κ) as the delay model everyone uses. Write the κ estimator so it can
  run on per-route two-path data.
- **B:** port every `Cells/` proof from `Prelim` to `Core`. Delete `Prelim`.
- **C:** netlist import, done properly. Generate Lean from the yosys JSON of
  every cell in `cells/rtl/` (INITs, pin maps, feedback wires), and prove it
  equal to B's hand transcriptions. From then on, proofs are about the
  generated terms, so a changed INIT breaks the build.

### Phase 2 (about 12-30 h): the whole library, and a checker that runs on real routes
- **B: the whole cell library.** Prove every cell (`bd_mux`, `bd_merge`,
  `bd_ctl`, `bd_end`, `bd_mem`, `bd_mlink`, the C3/C4 trees, delay lines)
  against a handshake spec. For each cell, emit its **exact timing conditions**
  as machine-readable data (`formal/out/cell_constraints.json`): these are what
  rules A/E/F/H/I/J approximate. The arbiter as a digital race (see item 4 above): for every
  digital behaviour of its LUTs and wires, the exact windows in which
  exclusion and the handshake hold, the counterexample traces outside them,
  and whether a race trace explains the unexplained bd_arbcell overlap. 
- **C: a verified timing checker on real routes.** It is a compiled Lean
  executable (`lake exe`), proved sound, that reads a routed JSON, per-arc delay
  intervals (prjxray via the research branch's `xray_delay.py`, read-only, or
  nextpnr's SDF), the corner model, and B's constraints, and reports every
  condition with its margin. Run it on the gcd_hw R5 routes and on the
  collatz/xorshift/ipow routes whose SDFs the research journal points to,
  rebuilding them if needed. **Compare its verdicts, row by row, with
  rules A/E/F/H/I/J**, and explain every disagreement.
- **A: a verified X/hazard audit for whole designs.** Ternary simulation,
  proved sound, as an executable over the full routed netlist: every possible
  X or hazard that could reach a storage node, for any delays in the band.
  Also formalise the research GLS's "sample-at-fire" LUT channel, and prove
  what a passing GLS run does and does not imply.

### Phase 3 (about 30-48 h): end to end
- **C (with B's cells):** composition through Dynamatic's operators (fork,
  join, merge, mux, branch, buffer) and Kahn determinacy. The gcd dataflow graph
  that `bdc` emits for gcd_hw (from its netlist, not hand-drawn) computes the C
  gcd (8b/8e).
- **All:** the capstone theorem for gcd_hw. Its hypotheses, listed in
  `formal/out/gcd_hw_hypotheses.md`, are each graded A/B/C (as in the fidelity
  table), and each comes with the GLS or board experiment that would test it.
  Then a second kernel, if time remains.
- **A:** `formal/out/FOR-RESEARCH.md`: what the research branch should change.
  Which rules the verified checker replaces, the GLS model fixes (early edges,
  inertial LUT paths), and the tests for each hypothesis. Keep it short and
  concrete, with commands.

If a phase finishes early, start the next. If one is blocked, record why and
go around it. Never weaken a statement to make it prove; an unproved goal stays
reported as unproved.

## Housekeeping

- **Lock:** `formal/LOCK` holds `<UTC ISO time> <session id>`. At start: if it is
  less than 90 minutes old and names another session, stop at once and change
  nothing. Otherwise write yours, commit, and push. Refresh it at every
  commit, and at least every 45 minutes. A rejected push means someone else
  holds the lock: stop.
- **Journal:** `formal/JOURNAL.md`, with one `## Session <date -u>` heading per
  session and `### progress HH:MM` notes, the times taken from `date -u`. Say
  what checks, what doesn't, and why. Negative results count.
- **Commits:** plain `git commit` (no `-c` identity overrides), small and
  frequent, pushed at least every 45 minutes. Background processes die with the session, so commit before anything long.
- **Draft PR:** keep one draft PR from `claude/formal`, titled
  "Formal-model feasibility", with a running summary. Never merge it.
- Do not edit `cells/`, `bdc/` or `research/`. Read them only.
- One session per shard starts per day (owner, 2026-10-30). Run continuously:
  never end the session on your own. Never create scheduled routines or reminders.

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
- Shard B: ArbHeldTimed/ArbHeldTimed2 and notes/B-arb-a0fork.md took 56/124
  (from `bd_prims_sim.v`) as rise/fall. The 16 ps threshold, the 96 ps margin
  and the "112 ps server" are artefacts of that. Redo them with one
  consistent corner or the corner model, and correct the journal.
