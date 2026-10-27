# C-12b: async-circuit and timed-automata tools (Workcraft, UPPAAL, ...)

Status: DRAFT, being filled in (session may die; the numbers below are from
completed runs).

## Verdict

**Works with effort ~1 day, but not with the tools named in the probe.**
Workcraft, UPPAAL, TChecker and PRISM could not be obtained here (below).
Storm (the probabilistic model checker, which reads the PRISM language)
installs from PyPI in 40 s. On top of it, a 300-line Python front end
(`formal/tools/async/tamodel.py`) builds gate-level timed-automata networks
with digital-clock semantics, using the real INITs. It checked the C-element
and the arbiter in seconds. It found the delay bounds where each one breaks,
and it reproduced the header's 16 ps finding exactly. It also found two
timing conditions on bd_arbiter that the header calls structural.
