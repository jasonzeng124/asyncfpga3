# C-10e: tcheck, the verified timing checker as a compiled executable on real routes

(In progress: routes of gcd_hw running; results pending.)

## Design decisions (no one to ask)
- **Dependency on formal/lean: copied, not `require`d.** formal/lean's lakefile requires
  Mathlib from git. A `require formal from "../../lean"` makes lake resolve Mathlib for this
  package as well (clone and a lakefile.lean elaboration), and lake builds a path dependency's
  modules into that dependency's own `.lake/build`. That is formal/lean/.lake/build, which
  every shard's LEAN_PATH reads while other agents compile into it. So the four proved modules
  the checker needs (`Formal/Net/Prelim`, `Formal/Timing/{Semantics,Checker,WinArray}`, all
  core-only) are copied VERBATIM by `sync.sh`, and `sync.sh --check` (run by `run.sh`) fails
  on any drift.
- **Obligations:** these are rule H (hold) and rule I (capture) per bd_latch controller, using
  the same structural identification as tighten.py: its helper functions are imported read-only.
  Rules A/E/F/J are not re-derived (see below).
