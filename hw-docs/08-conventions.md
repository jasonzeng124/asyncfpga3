# 08 — Standing preferences

## Evidence

- **Objective readback over human observation.** LED blink encodings are
  not an acceptable substitute for serial readback. Ask the user for
  physical actions (replug, power) only — never for observations a data
  stream could provide.
- **Real routed numbers are the endpoint**, not a delay model's heuristic.
  A claimed win must be shown through P&R.
- **Jitter sims are not signoff.** Delays are over-compensated by several
  factors; test post-P&R. Keep jitter runs for handshake-*protocol*
  changes only.

## Optimization

Improve the compiler, not the programs.

- Every optimization must be a general transformation any qualifying
  program benefits from — never keyed to one benchmark's shape.
- Before landing, answer: *which class of programs does this help?* If the
  answer names one kernel, don't.
- Idiom folds are acceptable (competing frontends do the same) but must be
  **labeled as idiom folds in the code** so they cannot masquerade as
  general performance results.
- Don't edit benchmark sources to dodge compiler weaknesses; fix the
  weakness. Source edits are legitimate only for fairness (`06`).

## Benchmark realism

Read data from memory, not fabric constants.

| Data | Placement |
|---|---|
| scales with problem size, or dynamic | BRAM |
| small fixed algorithm constants (weights, round keys, patterns) | fabric `const` |

MachSuite is the reference suite for integer-only kernels (sort, gemm,
bfs, kmp, spmv, nw, stencil). CHStone is mostly out of scope for an
integer-only language.

## Design

- **Keep control elements simple; avoid arbitration.** Delay elements
  belong on compute-match lines, not control. Where two things must not
  coincide, make it impossible by construction.
- **Root cause before margin.** A guard whose purpose you can't state is
  debt.

## Process

- **De-risk first, integrate second.** Hand-build and prove each
  structural shape (branch, loop, memory sharing, persistent state) as a
  standalone TB before a compiler emits it.
- **Write the acceptance test before the change**, especially before
  removing anything load-bearing.
- **Instrument from day one.** Report transaction latency and post-P&R
  resource counts as you go.
- **Report gaps explicitly.** State what is proven on silicon, what passed
  a gate, and what is untested — never blur them. "Passes on 7/8 seeds, a
  genuine if modest margin cost" is the expected register.
