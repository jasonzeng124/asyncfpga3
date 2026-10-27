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

## Tracks: run them in parallel with about 30 subagents

Spawn roughly 30 subagents, one per probe below (split or merge as you see
fit). Each subagent writes ONLY its own files under
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
