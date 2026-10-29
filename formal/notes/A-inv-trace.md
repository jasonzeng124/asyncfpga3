# A-inv-trace: full trace semantics of the involution channel (probe InvTrace)

STATUS (07:17 UTC): in progress. Starting from last session's lost draft
(Wip/_snapA/Formal/Core/Delay/InvolutionTrace.lean, copied to Wip/InvTrace/). Mathlib is
still building (150 oleans), so the file cannot be checked yet.

Plan:
1. Check the paper's construction (web search) and cite it here.
2. Review the draft's semantics against the paper (cancellation rule, T measured from the
   previous tentative output, chains).
3. Add what the brief asks and the draft lacks: explicit runt-cancellation example on
   ratPair, pulse_out monotone relation statement, alternation stated on the output list.
4. Check with check.sh once the needed Mathlib oleans exist; claim
   Formal/Core/Delay/InvolutionTrace.lean.
