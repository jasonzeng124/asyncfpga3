# A-e8causal (probe E8Causal, shard A): a prefix (time-inductive) verdict

STATUS (2026-10-29, start): IN PROGRESS. Nothing claimed yet.

## Plan
1. `Formal/Core/XAudit/Events9Prefix.lean`: `safe8_upto` (Events8.safe8 with SelOK and the
   residual obligations restricted to samples `s < t0`, conclusion on `[0, t0]`, lag L = 0),
   `verdict9_upto`, `design_verdict9_upto`; the all-times `design_verdict9` re-derived as a
   corollary with its exact statement; a causal-closure combinator (SelOK at sample s from the
   link at times < s ⇒ link at all times).
2. `Events9PrefixSel.lean`: H_ACK_LAG(_w) replaced by count-level facts (walk judgements of the
   accepted log, decidable) plus checked wire identities; proof by the prefix verdict + closure.
3. Notes for E8Arb's Unc discharge (what the prefix form gives, what is missing: an ND7
   prefix-extension lemma).

Early finding (argued, being checked): H_ACK_LAG_w with D = plo π (π from the ack down to the
pin's OWN junction) is not a causal consequence for tokens routed to the SIBLING branch (mux
uj0/uj1, steer branches): the ack then closes through the sibling's arm, which does not pass
through the junction.
