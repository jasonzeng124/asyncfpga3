# Formal-model feasibility program

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
4. **Analog, only for storage loops:** a first-order ODE per gate
   (tau * v' = f(v_in) - v), and the saddle point of the arbiter's loop.
   Linearizing gives the resolution constant and the e^(-t/tau) law. The
   expected result is that a LUT arbiter's mutual exclusion is NOT
   unconditionally provable: only a probabilistic bound holds. Confirm or
   refute this, and connect it to the unexplained bd_arbcell grant overlap
   in the repo's notes.
Every assumption is a named hypothesis in the theorem statement. **No `sorry`,
no `axiom` (other than Lean/Mathlib's standard ones) and no `native_decide` in
anything reported as proved.** `formal/check.sh` must build every claimed file
and fail on any of them. Report unproved goals as unproved.

## Tracks: run them in parallel with subagents

Spawn one subagent per probe below (split or merge as you see fit; see
Shards for which tracks are yours). Each subagent writes ONLY its own files under
`formal/lean/Formal/<Track>/` and `formal/notes/<track>.md` and never touches
git. You review, run `formal/check.sh`, commit, and push. Give each subagent:
the background reading list, this file, its probe, and a time box. It should
come back with what checks, what doesn't, and why.

1. **Toolchain** (you, first): install elan, Lean 4 and Mathlib (use
   `lake exe cache get`; never build Mathlib from source unless that fails).
   Make one lake project at `formal/lean` and write `formal/setup.sh` (idempotent,
   timed) and `formal/check.sh`. Lean with a Mathlib import uses several GB of
   RAM per process. Check `nproc`/`free -g` and write `formal/slot.sh`, a
   `flock`-based semaphore that caps concurrent `lean`/`lake` processes at what
   fits. Every subagent compiles through it. Subagents check single files with
   `lake env lean <file>`; only you run `lake build`.
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
   Kleene (does X reach both grants?); analog loop (ODE, saddle, e^(-t/tau)
   with Mathlib's ODE library); the handover-ordering claim in the header.
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
- Each shard uses 10-15 subagents, through its own `formal/slot.sh` cap.
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
  rules A/E/F/H/I/J approximate. The arbiter's metastability, from an analog model of its own gates. There
  is no analog arbiter: `bd_arb` is LUTs. The analog part is only how
  those LUTs' feedback loop behaves near mid-rail, which no digital model
  represents. Derive the saddle point, τ from the loop and the MTBF bound. Then the no-filter theorem for a LUT arbiter: the
  overlap probability in terms of loop gain, threshold spread and the grant
  window. Say whether it can explain the unexplained bd_arbcell overlap.
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
  frequent, pushed at least every 45 minutes. Background processes and
  subagents die with the session, so commit before anything long.
- **Draft PR:** keep one draft PR from `claude/formal`, titled
  "Formal-model feasibility", with a running summary. Never merge it.
- Do not edit `cells/`, `bdc/` or `research/`. Read them only.
- No usage cap. Run continuously: never end the session on your own.
