# B probe 7b: the arbiter in Kleene three-valued logic

File: `formal/lean/Formal/Cells/ArbKleene.lean` (core Lean, imports only
`Formal.Cells.Prelim`, no new shared defs needed; local helpers `kand`, `kor`,
`cloK`, the `Net`/`Inp`/`step`/`settle`/`run` simulator live in the file).

Check (clean, ~2.5 s wall, no output):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbKleene.lean

`#print axioms` on all 36 theorems: every one depends on `[propext]` only.
No sorry / admit / axiom / native_decide. All proofs are `cases ... <;> decide`
or a single `decide` on closed terms (`maxRecDepth 20000` for the scenarios).

Every Kleene value is `lutK`/`o5K`/`o6K` on the real INITs and pin maps:
`ustate` 64'hFFF0_FFB2_ACAC_ACAC (I0 r1, I1 r2, I2 q, I3 rst, I4 A0, I5 1;
O6 q, O5 R0), `ugrant` 64'h0C0C_0C0C_A0A0_A0A0 (I0 r1, I1 r2, I2 q, I3 0,
I4 0, I5 1; O5 g1, O6 g2), `bd_arbcell` state `bd_c2n_set` 64'hFFB2_FFB2_...,
`bd_c2` 64'h00E8_00E8_... (I0 a, I1 b, I2 q, I3 rst).

## Hypotheses

* **H_KLEENE_LUT** (Prelim): LUT Kleene output = closure over completions.
  Used by every `K` theorem. Fidelity of this vs the mux tree: probe Bf.
* **H_TERNARY_SIM** (prose only; the scenario theorems are concrete
  computations, so they hold unconditionally *as statements about the
  ternary simulator*; their meaning for silicon needs this): Eichelberger
  two-phase ternary simulation (phase A changing inputs = x, phase B final
  values, unit-delay Jacobi iteration to a fixed point) over-approximates
  every bounded-delay binary run (Brzozowski–Seger). NOT proved here. Test:
  GLS of the same input sequences with swept route delays.
* **H_A0_FORK** (encoded in the input sequence of two scenarios by giving the
  two A0 branches separate pins `a0`/`a0c`): A0's fall reaches `ua1`/`ua2`
  before it reaches `ustate.I4`. Test: routed SDF arcs; GLS with the A0->ua2
  branch delayed.

## Results (theorem names in `Formal.Cells.ArbKleene`)

Binary sanity (no hypothesis): `g1_bin` g1 = r1.q, `g2_bin` g2 = r2.~q,
`r0_bin` R0 = r1.q + r2.~q, `qArb_bin` q' = rst + (A0 ? q : C(r1,~r2)),
`c2_bin` C' = ~rst.maj(a,b,q). Kleene: `g1K_eq`/`g2K_eq`: the grant LUT is
exactly strong-Kleene AND (g1 = r1 ∧ q, g2 = r2 ∧ ¬q).

**(1) Does X on q reach the grants?** `g1_qx`: with q = x, g1 = 0 if r1 = 0,
else x (r2 irrelevant). `g2_qx`: g2 = 0 if r2 = 0, else x.
`both_grants_x_iff`: g1 = g2 = x ⟺ q = x ∧ r1 ≠ 0 ∧ r2 ≠ 0. So yes: an X on q
reaches BOTH grants exactly when neither request is a definite 0; the
(r1,r2) values are {1,x}².

**(2) Kleene exclusion holds, in a strong form.** `kleene_exclusion`: for all
ternary r1,r2,q, never g1 = 1 ∧ g2 = 1. Stronger, `g1_t_forces`/`g2_t_forces`:
a definite 1 on one grant forces a definite 0 on the other. `grant_pairs`: the
reachable pairs are exactly {00,10,01,x0,0x,xx}; (1,x), (x,1), (1,1) never
occur. Both-x does occur (above). So the Kleene model refutes nothing about
exclusion: a definite-high grant is always safe; the only failure is xx, the
ternary shadow of the metastable tier.

**(3) Downstream.**
* R0: `r0_qx`: with q = x, R0 = 0 if r1 = r2 = 0, 1 if r1 = r2 = 1, else x.
  `r0_vs_or`: R0 equals the Kleene OR of the two grants everywhere except
  r1 = r2 = 1, q = x, where both grants are x but R0 is a DEFINITE 1. Because
  R0 is one LUT over (r1, r2, q) it computes the closure of r1.q + r2.~q and
  the q cancels; a two-level g1 + g2 would not. So an X on both grants does
  NOT reach R0 in the contested case: the server is asked definitely.
* Ack C-elements: `c_x_left`/`c_x_right`: C(x, b) with held value q is q if
  q = b (b definite), else x. `c_restore_iff`: from q = x the next value is
  definite iff both inputs are definite and equal. `c_fixpoints` (rst = 0):
  fixed points per input pair: (0,0) {0}; (1,1) {1}; (x,x) {x}; (0,1),(1,0)
  {0,1,x}; (x,0),(0,x) {0,x}; (x,1),(1,x) {1,x}. So x is absorbing in the
  loop on every non-agreeing input, and an X grant is latched into A_i exactly
  when A0 differs from the held A_i. `c_rst`: rst = 1 forces 0 always.
  `a1_is_closure`: A1' = C(g1(r1,r2,q), A0, A1) computed LUT-by-LUT equals
  the closure of the composite Boolean function (243 cases): the grant -> ack
  composition adds no Kleene pessimism.

**(4) When the state loop restores a definite q from q = x.**
`arb_restore_iff` (bd_arbiter): q' ≠ x ⟺ rst = 1, or (A0 = 0 ∧ r1 = 1 ∧
r2 = 0) [q' = 1, any rst], or (rst = 0 ∧ A0 = 0 ∧ r1 = 0 ∧ r2 = 1) [q' = 0].
`cell_restore_iff` (bd_arbcell): same without A0. `arb_restore_values` gives
the values. I.e. only a DEFINITE set or reset condition (one request
definitely alone, server idle) or reset restores q; the loop never restores it
on its own. `arb_x_held`: on every hold input (tie r1 = r2, or A0 = 1) q = x
is a fixed point forever. This is the logical shadow of metastability: the
ternary model says "unbounded", only the analog model (7c/7d) gives a rate.
`hold_shields`: with A0 = 1 a definite q ignores any x on r1/r2.
`a0_x_corrupts`: an x on A0 makes a definite q go x whenever the unheld node
would move (e.g. q = 0, r1 = 1, r2 = 0, A0 = x).

**(5) Ternary simulation of bd_arbiter** (`step`, `settle`, `run`; every
scenario also proves its end state is a fixed point of `step`):
* `sc_reset`: all-x power-up + rst = 1 -> definite (q = 1, rest 0).
* `sc_runt_opposite` (the asked-for runt: r1 falling, r2 rising, A0 = 0, both
  x in the window): window state q,g1,g2,R0 = x,x,x,x with A1 = A2 = 0 (A0 = 0
  holds them); after the window r1 = 0, r2 = 1 is a definite reset, so
  q = 0, g2 = 1, R0 = 1, all definite. In this direction the Kleene model
  self-heals: the header's "opposite senses" runt is contained once the
  inputs settle into a definite set/reset.
* `sc_runt_held`: the same window with A0 = 1: q stays 1 (hold), only g1/R0
  go x, g2 stays 0, A1 stays 1.
* `sc_tie_rising`: both requests RISING inside one window from idle: ends on
  a tie (hold) with q = x forever, g1 = g2 = x, R0 = definite 1, A1 = A2 = 0.
  `sc_tie_acked`: when the server answers with A0 = 1, both acks latch x
  (A1 = A2 = x, fixed point). Note the header calls a both-rising tie
  "resolved deterministically"; that is only true for an EXACT tie. Kleene
  cannot express correlated X (r1 = r2 both x but equal), so any skew within
  the window is a set runt and the model reports it as unresolved.
* `sc_a0_fall_skewed`: A0 falls with client 2 waiting, client 1 not
  re-requesting, A0 fork skew unconstrained: q restores to 0 but
  **A2 ends x**. This is a real binary hazard, not Kleene pessimism: if the
  A0 branch to ua2 lags A0 -> ustate -> q -> ugrant -> g2, A2 = C(g2, A0) sees
  g2 = 1 against a still-high A0 and fires early (the header's early-ack
  defect, reopened by fork skew). `sc_a0_fall_ordered`: under H_A0_FORK the
  same sequence is fully definite. **Finding for the cell owner: the ack-hold
  fix relies on an (unstated) isochronic-fork ordering on A0, with a margin
  of roughly two LUT delays plus the q feedback hop.** Worth a routed-SDF
  check; it is not claimed to be violated on any real route.
* `sc_a0_fall_runt`: the header's aperture case (client 1 re-requests on the
  edge where ustate sees A0 fall), fork ordered: q = x, both grants x, R0 = 1,
  acks 0; then after the server acks, A1 = A2 = x.

**Comparison with Lenzen/Függer/Friedrichs (metastability-containing
circuits).** Their closure: f_M(x) = bitwise superposition of f over all
resolutions of x; a circuit is mc for f if its Kleene evaluation equals f_M.
Verdict:
* Per evaluation, YES. Each output LUT is f_M of its own function by
  H_KLEENE_LUT (definition of lutK); the grant pair is the closure of
  (r1,r2,q) -> (r1.q, r2.~q) because LFF's closure is bitwise; R0 is the
  closure of r1.q + r2.~q (strictly better than the Kleene OR of the grants,
  `r0_vs_or`); A1 = C(g1, A0) is the closure of its composite (`a1_is_closure`).
  The one-step next-state map of the whole arbiter is therefore mc.
* With respect to the arbitration spec, it is the closure and nothing better:
  on a contested input the spec admits both winners, so the closure is
  (M, M) on the grants, which is exactly `both_grants_x_iff`; and it never
  produces (1,1) (`kleene_exclusion`). So "mc in their sense" holds, with the
  mutex spec closed bitwise.
* It is NOT metastability-resolving, and cannot be (LFF, after Marino: no
  circuit deterministically maps M to a definite value): `arb_x_held` shows x
  is a fixed point of the state loop on every hold input. LFF's framework
  contains M; the arbiter's tier-3 obligation (a consumer must not read a
  grant within one loop delay) is outside it and needs the analog rate.
* Caveat: LFF and lutK treat each M independently. A correlated pair (exact
  tie) is more definite in silicon than in either model.

## What did not work / not done

* H_TERNARY_SIM (soundness of ternary simulation w.r.t. bounded-delay binary
  traces) is stated, not proved. That is the link that turns the scenario
  computations into theorems about traces; it belongs with track 3/4 (Core
  traces) and is a known result (Brzozowski–Seger, "Asynchronous Circuits",
  ch. 7), so it is effort, not research: estimate 2-4 days in Lean once the
  trace type is fixed.
* The scenarios are fixed sequences, not "for all input sequences". A general
  theorem (e.g. "q = x after a window only if the inputs after the window are
  a hold") is the restore lemma lifted to traces; not done.
* Gate fidelity of lutK vs the mux tree is probe Bf's job; nothing here
  depends on pin order inside the tree except through that hypothesis.

## Verdict

**Works.** All five questions answered with machine-checked proofs on the real
INITs in ~2.5 s of core Lean. Effort to finish: 2-4 days to prove
H_TERNARY_SIM against Core's trace semantics (then the scenarios become trace
theorems); +1 day to state the scenarios for all input sequences. What it
buys: (a) exclusion in Kleene logic is proved for any ternary inputs, so the
only exclusion failure the ternary model admits is (x,x), i.e. the metastable
tier is isolated exactly; (b) R0 is definite in the contested case, so the
server never sees an X request from a tie; (c) one new concrete obligation,
H_A0_FORK, that the ack-hold fix silently relies on.

## Fidelity per primitive

* LUT6 / LUT6_2: closure semantics (H_KLEENE_LUT) on the real INIT and pin
  map; O5 = lower 32 bits over I0..I4 with I5 tied 1 on these cells (correct
  for LUT6_2 with I5 = 1). Fidelity: exact for binary; the X behaviour is the
  hypothesis (compare probe Bf's per-mux model).
* Feedback wire (q -> I2, C-element q -> I2): modelled as a unit delay in
  Jacobi iteration. Ternary fixed points do not depend on the delay value
  (under H_TERNARY_SIM); no analog behaviour, so X on a loop is "unknown,
  possibly forever", never a rate.
* Fork wires (A0 to ustate vs ua1/ua2): one pin per branch in the skewed /
  ordered scenarios; otherwise ideal (same value at every reader, x during the
  phase-A window covering any skew).
* Constants I3..I5 tied in RTL: modelled as definite f/t (assumes tie-offs are
  clean rails).
