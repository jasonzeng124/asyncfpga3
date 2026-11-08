# Timed occurrence-net certificate on THE target, pair (12,18), g = 1, κ = 0, c = 0 and c = 1 (shard C, 2026-11-08; UNTRUSTED)
Produced by a shard-C subagent (scratch /tmp/claude-0/tocc), copied here. Pipeline: build.py (kernel cone, collapsed
copy chains, per-pin corner windows) → classify.py (exact/data split) → sim.py (transport run at window midpoints,
SeqEnv one pair) → cert.py (events, causes, L by vector clocks) → lcheck.py (LCheck/LCheckX enumeration) →
timing.py (Sep lower / Up upper longest paths) → analyze.py, minimize.py (lowering L), data.py (guards, bundling
windows), conflict.py. Results summarised in formal/JOURNAL-C.md (2026-11-08) and min_c*.txt, data_c*.txt.

## AO re-run (2026-11-08, session_01HC49FuGvem3PXi79C1GHgd)
`ao.py [0|1] [--prevanc|--noprev]` measures the (12,18) certificate against `Formal/Net/AO/Timed.lean` (AND-OR
alternatives, per-reader L, TOA, ownB filter, RT edges). `--prevanc` lets an upper bound's previous event count as
`hi'(v,v)` when it is causally below `e0`; that clause is now in the Lean (`UpOKA` second disjunct, via a `Sep` entry
prev → e0). `--noprev` drops the clause (unsound; diagnostic only). Outputs: `ao_c{0,1}.txt` (strict),
`ao_c{0,1}_prevanc.txt`, `diag_c{0,1}p.txt`. Untrusted Python; one simulated run per corner. The input pickles are
not committed (they live in /tmp/claude-0/tocc and are rebuilt by build.py/sim.py).
