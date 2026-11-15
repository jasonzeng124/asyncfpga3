# Shard A: THE statement from one run certificate (`Formal/Target/CertRun.lean`, 2026-11-15)

**Problem.** Per-pair certificates cannot be chained under a fastest sequential environment (notes/A-S6-chaining.md:
the env re-requests 1-4 ps after out0.req falls, while the circuit still settles, so no episode k ≥ 2 has a quiet
start). What must ONE certificate per behaviour, started during reset, deliver for `NetCorrectSeq` to follow?

**Proved (Lean, check.sh OK, standard axioms).** `CertRun.netCorrectSeq_of_run` (generic in the netlist, any
`Assembly.OneReq` boundary, every p, T, R, su, Δo, every number of pairs): if every behaviour meeting Behaves, ArbOK,
Env and SeqEnv has a count base `t0 ≤ R` and certificates `C s` (the one in force at time s) with `EpRun C B x t0 R Δo`,
THE statement holds. No island, reset-length bound, `Sane p` or per-episode quiet start is needed.

**`EpRun` field by field, and where each should come from.** Counts are `cnt x t0 u s`. For THE target, t0 is a time
in C's reset-island window (`CViewPS.RIslAll.reset_quiet_all`: the island is constant from ⌈(1+κ)g⌉·89 ns to R − 1),
and `C s` is the unrolled word certificate (`AO/Unroll*`) over the pairs offered by s, with a pair-boundary letter
between pairs.
| field | content | source |
|---|---|---|
| t0R, low0 | t0 ≤ R, boundary low at t0 | choice of t0 in the reset window; Env (requests and env acks low on [0, R]) plus reset_quiet_all for a/b/start.ack, out0.req |
| interA/B/S/O/P | the five handshakes interleave in count form at every time | `CertSpec.inter_of_ord` on the cntE ideal (`timedA_follows`), boundary nodes not data |
| ordA/B/S/O/P | an ack's (req's) alternative fired by s ⇒ the partner event fired by s (transitively) | `CertSpec.happened_of_ideal`, the certificate's cause lists |
| ordQ | out0.req event 2k (its k-th rise) needs the request's event 2k | the word: each pair's out0 rise is caused (transitively) by that pair's request rise |
| en | each change of a/b/start.ack, out0.req, the request is enabled at counts ≤ those at s − 1 | gates: `ChangeOKA` + `CertSpec.enabled_of_changeOKA` with TBehX rd/lo1; the request: the env premise `hEnvE` |
| data | from Δo after an out0 rise until out0.ack, out0's bus = gcd of the operands at one past the latest request rise | data claims on out0.data bits (`CertSpec.busVal_of_bits`), symbolic claims (C's `AO/Sym*`) |
| last | after the last request rise, some later time has a low boundary and cnt out0.req ≥ cnt req | `timedA_live` (every event of the finite word fires) + even counts (`CertSpec.low_of_even`) |
What CertRun proves itself: the episode chaining (`plan_of_run`, invariant cnt out0.req = cnt req), using Env's
request moves and SeqEnv at each re-request, so the certificate need not say anything about where episodes end.

**Not shown.** Any instance. Conditional: false wherever THE statement is refuted (g = 1, κ ≥ 9/25; g ≥ 8/5).
