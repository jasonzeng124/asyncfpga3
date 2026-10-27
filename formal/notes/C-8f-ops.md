# C-8f: composition through Dynamatic's operators (track 8, Phase 3)

Status: IN PROGRESS (skeleton first, so a dead session leaves something).

Plan (decided 2026-10-27, no one to ask):
- `Formal/Net/Ops.lean`: offer-based tokens (k-th req rise), `Held` (H_BUNDLE),
  generic network (every channel one producer op, one consumer op, any graph,
  cycles allowed), `net_protocol` (causal AG, strong induction on time) and
  `net_refines` (every offered token on every channel equals ANY solution of
  the token-level equations; strong induction on the offer time).
- `Formal/Net/OpsFork.lean`, `OpsJoin.lean`, ...: gate-level SI/DI models of
  bdc's cells, each proved to meet the network's per-op protocol and data spec.
- gcd-shaped network last.
