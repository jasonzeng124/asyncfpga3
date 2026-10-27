# C-10a: verified interval timing checker (track 10, core)

Status: IN PROGRESS (stub written first so a dead session leaves something).

Plan: Formal/Timing/Semantics.lean (netlist, run semantics = per-arc
H_BOUNDED_DELAY pins + zero-delay local node functions), Formal/Timing/Checker.lean
(earliest/latest windows by topological table, bundling check, soundness,
per-node exactness), Formal/Timing/CheckerToy.lean (bd_link-shaped toy netlist,
correlated-delay example).
