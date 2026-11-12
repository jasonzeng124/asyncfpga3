# What Lean already gives for an arbiter-aware upper bound (`UpOKA`) — shard B, 2026-11-08

C's open item (JOURNAL-C 2026-11-08 15:21, R1): the reader's guard fails because no `Up` bound exists from a common
ancestor when the path crosses an arbiter (or environment) event; C asks "what `UpOKA` could admit through an
arbiter event, given Spec's ArbOK". These are the Lean facts on the arbiter side that such a rule can rest on (all
standard axioms, check.sh OK at the commits named in JOURNAL-B). None of them is an `UpOKA` rule yet.

## 1. Uncontended request: the state switches within the state LUT's feedback window (no H_ARB needed)
`Formal.Cells.ArbClean.q_clean_set` / `q_clean_reset` (state LUT `qInit`, 5 pins: r1 = 0, r2 = 1, fb = 2,
rst = 3, A0 = 4). If, over pin i's read windows of every t in [s, e], r1 reads 1, r2 reads 0, rst and A0 read 0
(`OnReads`), the gate has started (`g.start p ≤ s`) and the condition lasts one feedback read (`s + hi 2 ≤ e + 1`),
then **q = 1 on [s, e']**. Mirror for r2. So for an uncontended request the Up bound through the arbiter is an
ordinary gate bound: (time the request is visible on pin 0's reads) + hi(pin 2), i.e. the state LUT behaves like a
C-element with its own feedback. Instances on THE target: `ArbViewPS` / `ArbViewPSReset` (all 9 state LUTs, both
directions); chain form for routed feedback: `ArbCleanChain.cq_clean_set_gen`.

## 2. Contended (both requests up): only H_ARB(T) bounds the decision time
Spec's `ArbOK T A x`: if every input of the state LUT is constant on [t1, t2], q is constant on [t1 + T, t2]. It
says nothing about WHICH value. So the only sound Up through a contended arbiter event is: **"q has its final value
(either one) by t1 + T"**, where t1 is the last input change. A certificate whose exact node is q must therefore
treat the decision as an environment-like choice (two branches, both certified) with the Up edge
(last input event) -> (q settled) of length T. Lemma that packages this with the grant gates and the one-acknowledge
property: `ArbOneAck.one_ack` (losing client's acknowledge stays low, given q settled and the server-path
certificate) and `ArbServer.q_settles` (q settles before the server answers; premise: a hold certificate on A0).

## 3. Caveats C's rule has to respect
- `ArbTSpec.spec_double_ack`: H_ARB(T) alone allows both clients to be acknowledged unless q is settled before A0
  can rise (the server-path race). So an `UpOKA` edge must come with that separation (`Sep ≥ 1` between "q
  settled" and "A0 can rise"), as `one_ack` requires.
- Residual vacuity (audit T5): `ArbOK T` is unsatisfiable for T below the state LUT's own delay; any instance should
  use T ≥ the slowest state-LUT arc ((1+κ)·664·g ps on the target).
- Today's κ = 0.40 refutation (FOR-RESEARCH B1) is at merge4's arbiter acknowledge C-element `ua2`, reading the fork
  on pin 0: a positive theorem must sit below κ ≈ 0.35 for wide operands.
