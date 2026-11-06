# The top-level assembly: what is left for THE theorem (shard A, 2026-11-06)

`Formal/Target/AssemblyPS.lean` (check.sh OK):

    the_shape_of_plan : (∀ x n va vb, Behaves p (circuit net boundary) x → ArbOK T arbs x →
        Env x boundary R su Δo n va vb → SeqEnv x boundary R → ∃ I, Plan x boundary R Δo I) →
      net.WF ∧ boundary.OK net ∧ NetCorrectSeq net boundary arbs p T R su Δo

So THE theorem on gcd_ps_e6bb4aec is exactly: for every behaviour meeting the hypotheses, find an invariant `I : Nat → Prop`
and prove `Assembly.Plan` (Formal/Target/Assembly.lean):

* `base_inv : I R`, `base_low`: a.ack, b.ack, start.ack, out0.req low at R.
* `quiet`: I t, every boundary node low at t, request low at t+1 ⇒ those four outputs low at t+1 and I (t+1).
* `step`: I t, all low at t, request rises at t ⇒ ∃ t2 t0 with `StepCore`: no further request edge in (t, t2); on
  [t, t2) input acks move only when different from the request and out0/end requests only when equal to their acks;
  out0.req has exactly one edge in [t, t2), at t0; from t0+1+Δo while out0.req high and ack low, out0.data =
  gcd(a.data at t+1, b.data at t+1); every boundary node low at t2; I t2.

Everything else in `Correct` (liveness, counting, quiescence for finite n, the k-th output's index) is proved once in
`Assembly.correct_of_plan`. SeqEnv and ArbOK are hypotheses available to the prover of `step`; the assembly does not use them.

Choosing `I`: the env may raise the next request as soon as SeqEnv allows (out0 req and ack low again, input acks low),
so `I t2` must hold while the circuit may still be settling from the pair; an "every island member idle for the last M ps"
invariant is too strong. Simulation (journal 2026-11-06: aggressive env, request gap 0-2000 ps, 134 runs) found no
failure there.

Parameters (`SpecMono.seq_weaken`): prove at the largest T and (g, κ), smallest su and Δo. For the board, Δo must be at
most (1-κ)·535/g ps (end channel's sink, target/BOUNDARY-ps.md); Δo = 0 is strongest.
