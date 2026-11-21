# Occurrence-net certificates for THE target's abstract machine (shard C, 2026-11-08; UNTRUSTED tools)
Produced by a shard-C subagent (scratch /tmp/claude-0/occ), reviewed and copied here by shard C.
- `run.py`: records one run of huffx's latches-first machine (one operand pair, RT orders applied strictly).
- `check2.py`: builds the candidate partial order (events = every node flip incl. latch flips; causes = previous
  event + latest events of support nodes sensitive when the node became enabled + latest events of its RT blockers;
  latch causes followed transitively) and runs the local check of Net/OccNet over the order ideals of each node's
  local event set (latch closure enforced in the local search). Options --witness/--witdir/--extra-rt/--only/--cert.
- `huffr.cpp`: huffx.cpp plus `--replay` (replays a witness move list).
- `rt_final36.txt`: the 30 RT orders of 2026-11-06 plus 6 new ones found here (each with a replayed witness, `wit/`).
- `cert_*.txt.gz`: certificates (one line per event: node id, cause event ids).
Inputs (net.json from lean2json.py on Formal/Target/NetPS, prep.txt from tools/huff/prep.py, init from
`huffx --dump-init`) are regenerated, not stored. The local-to-global argument the checker relies on is the one
proved generically in Formal/Net/OccNet.lean, but the checker's encoding of latches-first is the subagent's own.
