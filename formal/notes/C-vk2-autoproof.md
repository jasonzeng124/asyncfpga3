# C-vk2: automatic all-inputs token proofs for loop kernels (`formal/tools/autoproof/`)

Probe C-vk2, 2026-10-29. North-star goal 3. WORK IN PROGRESS (this note is saved early and
completed below as results come in).

## Status so far
* `Formal/Net/AutoLib.lean`: generic simulation theorem `sim_call` + generic tactic `auto_ops`.
* `formal/tools/autoproof/cfront.py` (C subset -> test-point automaton),
  `autoproof.py` (co-simulation, guessing, Lean emission).
* Generated and checked (check.sh OK, 1489 decls, axioms within the standard three):
  `Formal/Net/AutoIpow.lean`, `AutoCollatz.lean`, `AutoXorshift.lean`, `AutoGcd.lean`.
