# Shard C: a Lean-checked counterexample to NetCorrectSeq on THE target (2026-11-06)

## Statement
`Formal.Net.CexPS.not_netCorrectSeq : ∀ T su Δo, 36 ≤ T → Δo ≤ 3000 →
  ¬ NetCorrectSeq DecodedPS.net DecodedPS.boundary DecodedPS.arbs ⟨1, 21/25⟩ T 400000 su Δo`
(`lean/Formal/Net/CexPS/Refute.lean`; `lake build Formal.Net.CexPS.Refute`; axioms propext, Classical.choice,
Quot.sound; no sorry / native_decide).

Plainly: with no guard, within-die scatter κ = 0.84, a 400 ns reset and any arbiter bound T ≥ 36 ps, there is a
behaviour of THE target's decoded circuit, with an environment obeying H_ENV and SeqEnv, in which the pair
(1071, 462) is accepted and no result ever comes back.

## The witness
- Delays (corner 0, transport): `umux16.uya` (the input-ack C-element of mux16's y input, SLICE_X36Y47.C6) and the
  35 pips/hops on its input routes read at ⌊46·FAST_MAX/25⌋; every other pin at ⌈4·FAST_MIN/25⌉ (`CexPS.dK`).
- Environment: reset high on [0, 400000); operands 1071 / 462 constant from t = 0; shared request up at 401,000 ps,
  down at 417,243 ps once a/b/start acks are high; pend's ack 3 ns after each request move; out0's ack never moves
  (out0's request never rises).
- Data: `tools/huff/simadv.py --exact --data0` (copy of shard A's sim.py with the adversary), `gen_cex.py` ->
  L000..L074 (node codes: 106,500 transitions), X000..X074 (one `decide +kernel` per 2,500 gates of
  `gateWK`, 22-83 s and <= 6.2 GB each).
- Mechanism: in the abstract (zero-delay, latches-first) machine, uya's falling excitation can be withdrawn by the
  next token's link stage (`ulink_n_falseResult_85` / `ulink_n_trueResult_72`); C's walks show it is one of 30
  relative-timing orders the control relies on (`tools/huff/out_rt_pairs.txt`). Slowed this much, uya is
  re-enabled mid-fall, emits ~6 ps runts, and the mux's handshake is lost.

## Proof structure
- `KBase.gateOK_of_gateWK`: finite per-gate check (equation at the gate's start and at every breakpoint; per arc
  `4·fmin ≤ 25·d ≤ 46·fmax`, `d ≤ startK`) ⇒ `Spec.GateOK pK 0`. `startK_le`: the check starts no later than
  `Gate.start pK`.
- `Wit.behaves_k`: every gate of `circuit net boundary` passes (chunks).
- `Refute.k_hyps`: Env (any su, Δo ≤ 3000) and SeqEnv from the pulse shapes of the 8 boundary signals.
- `Refute.k_arbOK`: ArbOK T for T ≥ 36 (every arbiter-state toggle < 36 ps after an input toggle).
- `Refute.k_not_correct`: Correct's last clause (out0 risen once from some time on) fails: out0.req is constant 0.

## Scope and caveats
- w = 0 only: `SpecRunt.NetCorrectSeqRunt w` is not addressed; the run has sub-20 ps pulses on many nodes.
- κ = 21/25 is large. The same adversary is correct at κ = 0.82; a stronger one gives a non-quiet livelock (runt
  ring) at κ = 0.70 in simulation only.
- One corner (fast). R, su, Δo as stated. `T` is the H_ARB bound; every T ≥ 36 is refuted, which includes every T
  above the state LUTs' own delays (audit T5's non-vacuity range).

## Second refutation, κ = 18/25 (`Formal/Net/CexPS72/`, same structure)
`not_netCorrectSeq : ∀ T su Δo, 62 ≤ T → Δo ≤ 3000 → ¬ NetCorrectSeq net boundary arbs ⟨1, 18/25⟩ T 400000 su Δo`.
Slow set: umux16.uya, ulink_n_falseResult_85 stage 0, ulink_n_trueResult_72 stage 0, umux16.uj1, SLICE_X32Y28.A6
and the pips on their input routes (`tools/huff/cex/k72_slow.txt`), at ⌊43·FAST_MAX/25⌋; all else ⌈7·FAST_MIN/25⌉.
Data: `tools/huff/cex/k72_dump.json.xz`. With these adversaries: correct at 0.64/0.67, runt-ring livelock at 0.70
(simulation, never quiet; not in Lean), quiet deadlock at 0.72.
