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

## Diagnosis of the failing TO rows (2026-11-08)
`ao.py` flags:
- `--cyc`: cut each cause cycle by removing only the alternative whose cause most precedes its effect in time.
- `--causeanc`: a cause in Up's chosen alternative may carry a Sep entry to e0. This is now in the Lean (`UpOKA`).
- `--deep`, `--bcp`, `--robust`, `ROBNODES`: diagnostics.
Results: `ao2_c{0,1}_{base,deep,bcp,cyc,ca,rob,robn}.txt`.
Traces: `q1*.py` (b nodes and worst rows), `q2.py` (needed rows), `q3*.py` (residual failures), `simx.py`/`advcmp.py`
(adversarial pin delays).
Untrusted; one midpoint run per corner.

## Final control configuration (2026-11-08)
The default of `ao.py` is `--cyc --causeanc --prevanc` plus don't-care placement. A net absorbed change is carried to
the first later event that needs it. `--legacy` and `--nodcp` turn those off. `ao3_c*.txt`: 0 local-check failures
for (12,18) and (17,5). `data2.py`: GuardTime margins under the final Sep/Up (`data2_c*.txt`). `q5.py`: one L shared
by both corners. `q6.py`: the failing guard windows characterised. `cornercmp.py`: structure equality across corners.

## Comparator re-open check (2026-11-08)
`hazchk.py` + `hzrun.sh`: 12 operand pairs × 2 corners × 6 delay settings (mid, all-lo, all-hi, 3 random per-pin).
For each, it checks whether any control gate's output depends on a data node at the moment it reads it.
`hz/res_c*.txt`: 0 such events, and every gcd is right. `q7.py`/`q8.py`: the 33 guard terms, all masked by a datapath
mux whose select is a 1-bit condition latch.
