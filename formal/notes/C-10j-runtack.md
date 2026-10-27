# C-10j: does the grant-fork runt break the handshake? (H_RUNT_ACK)

Shard C, probe 10j, 2026-10-27. STATUS: in progress (skeleton written first so a
dead session leaves something).

Plan: Lean theory `Formal/Timing/RuntAck.lean` (both directions, real INITs),
generated per-instance verdicts `Formal/Timing/RuntAckInst.lean` (server min path
by a proved potential certificate), tools in `formal/tools/runtack/`.
