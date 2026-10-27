# C-8n: Ops gate models bound to generated cells (O4), circuit liveness with bounded delays (O5)

Shard C, probe 8n, 2026-10-27. IN PROGRESS (notes kept current as work proceeds).

Plan:
- O4: `Formal/Net/OpsGen.lean`: each Ops gate field derived from the generated cell's gate
  (Formal/Gen/Cells.lean, `Netlist.gateN boolSem`) plus the step form of B's C2 (feedback first).
- O5: `Formal/Net/OpsTimedLive.lean`: generic latency chain lemma under bounded-delay settle;
  linear pipeline of links (any n), then ring.
