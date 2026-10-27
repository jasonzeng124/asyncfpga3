# B / probe 7a: arbiter, binary model (tie and runt)

File: `formal/lean/Formal/Cells/ArbBinary.lean` (core Lean, imports only
`Formal.Cells.Prelim`; about 1000 lines). Checks clean, no sorry, axioms only
`propext`, `Classical.choice`, `Quot.sound` (checked with `#print axioms` on
all 28 main theorems). Check time about 7 s; nearly all of it is the kernel
evaluating the 114-state reachability certificate in Section 5
(`decide +kernel`, which uses no extra axiom).

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ArbBinary.lean

## What is modelled, from the real INITs

| node | INIT | pins | lemma (INIT = equation) |
|---|---|---|---|
| `bd_arbcell` q (`bd_c2n_set`) | `FFB2_FFB2_FFB2_FFB2` | r1 r2 q rst 0 0 | `stF_eq`: `r1.~r2 + q.~(~r1.r2)`; `stF_reset` |
| g1 / g2 (`ugrant`, O5/O6) | `0C0C_0C0C_A0A0_A0A0` | r1 r2 q 0 0 1 | `gr1_eq`: `r1.q`, `gr2_eq`: `r2.~q` |
| `bd_arbiter` q (O6) / R0 (O5) | `FFF0_FFB2_ACAC_ACAC` | r1 r2 q rst A0 1 | `stA_eq`: `A0 ? q : stF`; `r0A_eq`: `g1+g2`; `stA_reset` |
| A1, A2 (`bd_c2`) | `00E8_00E8_00E8_00E8` | a b q rst 0 0 | `c2_eq` |

All of these are evaluated through `lutB`/`o5B`/`o6B`; the equations are proved
lemmas, not the definitions.

## Theorems

### (1) Settled exclusion (tier 1): structural
* `settled_exclusion`: for all r1, r2, q, `g1 && g2 = false` when both grant
  outputs read the same q value. No hypotheses.
* `kleene_x_reaches_both`: under H_KLEENE_LUT (Prelim), r1 = r2 = 1 and q = x
  gives g1 = x AND g2 = x. Tier 1 is about Boolean q only.

### (2) The tie
* `tie_holds`: from either q, `F(1,1,q) = q`, `g1 = q`, `g2 = ~q`.
* `tie_grants_previous_winner`: settled-step (fundamental-mode) model with a
  ghost `last` (last side granted). Invariant `SInv`: q points at the last side
  granted, or is the reset value 1 if nobody has been granted. After any
  history ending with both requests down, raising both together leaves q
  unchanged and grants side 1 iff side 1 was the last winner (or nobody yet),
  side 2 iff side 2 was. Exactly one grant is high.
* `tie_holds_arbiter`: the same for `bd_arbiter` at any A0.

**Previous winner or the other one? The previous winner, again.** The INIT
derivation is unambiguous: q is only ever moved by a lone request, the moved q
immediately grants that side, so q always names the last winner, and a tie
holds q. The header's "the previous winner is asked to give way first" is
consistent with this only if read as "the previous winner keeps the grant and
the other side waits until it gives way (drops its request)". It must not be
read as "the tie goes to the other side": tie-breaking is anti-fair (winner
repeats). Reset makes side 1 the "previous winner" of the first tie.

### (3) The runt: discrete-time transport model
Delay channel: **pure (transport) delay**, time `Nat`, delays constant within
a trace (a constant-delay trace is a trace of the bounded-delay model for any
interval containing those constants, so counterexamples transfer; positive
theorems are for every `L`). `L` = q loop (state LUT arc + feedback route),
the same q value read by the state LUT and the grant LUT; `d5`, `d6` = grant
LUT to g1 / g2. Requests reach both LUTs at the same instant.

Named hypotheses:
* `H_INIT_SETTLED`: requests and q constant on `[0, L]`, q a fixpoint.
* `H_REQ_SEP`: ANY two request edges (any signal, any sense) more than `L`
  apart. Physically an environment property that independent clients violate
  at a nonzero rate; that rate is the MTBF question.
* `H_GRANT_SKEW`: `|d6 - d5| <= L`.

Results:
* `runt_sat`, `runt_init`, `runt_skew`, `runt_not_sep`, `runt_oscillates`,
  `runt_overlap`: a CONCRETE trace (`L=4, d5=1, d6=2`) satisfying every gate
  relation, starting settled, with skew within bounds; r1 rises at 6, r2 at 8
  (both rising, 2 ticks apart < L). The set condition is a runt of width 2;
  since `r1=r2=1` afterwards holds q, the pulse circulates forever
  (q high at `4k+10`, low at `4k+12` for all k), and g1 and g2 are BOTH high at
  `4k+11` for every k.
* `exclusion_needs_sep`: hence exclusion does not follow from gate relations +
  settled start + skew bound; the separation hypothesis is necessary.
* `runt_overlap_needs_skew` / `exclusion_zero_skew`: with `d5 = d6` exclusion
  holds for EVERY trace, oscillating or not. Binary overlap needs a runt AND
  O5/O6 skew. (With zero skew the runt shows as grant pulses for one side.)
* `qedge_cause`: under the three hypotheses, every q edge is caused by a
  request edge exactly one loop delay earlier (strong induction on time).
* `exclusion_transport`: **under `0 < L`, H_INIT_SETTLED, H_REQ_SEP,
  H_GRANT_SKEW, g1 and g2 are never both high.** Non-vacuity: `ho_sat`,
  `ho_init`, `ho_sep`, `ho_serves`, `ho_exclusion` (a real contended handover
  r1 -> r2 satisfying all hypotheses).
* Note the hypothesis is "edges more than L apart" plus "skew at most L", not
  "more than L + skew": the skew enters only through the skew bound.

**Opposite or same sense?** The header and ARBITER.md place the runt at "r1
and r2 moving in OPPOSITE senses within one loop delay". In this model that
case is always clean, at any gap, zero or less than L:
* `opposite_sense_clean_rise` / `_fall`: r1 rises at e1, r2 falls at e2 (or
  the reverse), any e1, e2: q has exactly one edge, at `max e1 e2 + L`. (The
  set `r1.~r2` is monotone and the reset `~r1.r2` antitone.)
* `opposite_sense_exclusion`: and the grants never overlap, given only the
  skew bound.

The runt needs the set/reset LITERALS (`r1`, `~r2`) to move in opposite senses,
i.e. **r1 and r2 moving in the SAME sense within one loop delay** (both rising:
the runt trace; both falling), or one request pulsing for less than L. For
`bd_arbiter` the third literal `~A0` adds the A0-fall-vs-request case the header
describes. Consequence for the header's "A plain tie (both requests rising
together from idle) is resolved deterministically": in this model that is true
only for EXACTLY simultaneous arrival at the LUT pins (one edge of the request
vector). Any gap `0 < g < L` is the runt. In continuous time the safe "plain
tie" has measure zero; the near-tie is the dangerous case.

**Does inertial delay change the runt result?** Only the threshold.
`inertialOK`, `InSat`: inertial LUT output (window δ) plus transport
feedback wire W. With `δ = 1, W = 3`:
* `inertial_swallows_narrow_runt`: a width-1 runt (r1 at 6, r2 at 7) is
  swallowed; q stays 0 forever, so r2 is granted although r1 asked first (the
  race is decided silently).
* `inertial_passes_wider_runt` + `inertial_runt_oscillates`: a width-2 runt
  (r1 at 6, r2 at 8) passes and circulates forever, like the transport case.
Runts wider than the inertial window and narrower than the loop survive (the
general statement is argued, proved only for the instance). Neither binary
channel is faithful here: in silicon the runt decays or grows (involution
channel or analog model, probe 7c).

### (4) Sustained contention and alternation (`bd_arbiter`, interleaving model)
Speed-independent interleaving model: any one excited gate fires; gates q, R0,
g1, g2, A1, A2 from the real INITs, two always-wanting four-phase clients, a
four-phase server (A0 follows R0), reset state q = 1. State as a 9-bit vector
plus ghosts `last` (last side acked) and `owed` (side that was waiting when the
server ended the other side's transaction). Timing hypotheses as switches that
disable transitions:
* `h1` H_SERVER_AFTER_GRANTS: A0 does not move while g1/g2 is excited.
* `h2` H_Q_BEFORE_REREQ: a client does not raise its request while q is excited.
* `h3` H_SERVER_AFTER_ACKS: A0 does not move while A1/A2 is excited.

Results:
* `stA_moves_only_if_alone`, `q_moves_only_alone`: q moves only while exactly
  one request is up AND A0 is low (INIT property, true in every state).
* `arbiter_exclusion`: under h1, h2, h3, never g1.g2 and never A1.A2 (reachable
  set of 114 ghost states / 56 circuit states, closure certificate `R3_cert`
  checked by kernel evaluation, then induction on reachability).
* `arbiter_alternates`: under h1, h2, h3, if a client was waiting when the
  server ended the other's transaction, the next grant goes to it.
* `need_h1`: without h1 (h2, h3 on), g1.g2 is reachable: g1 slow to fall,
  server completes, q flips, g2 rises.
* `need_h3`: without h3 (h1, h2 on), A1.A2 is reachable: A1 slow to fall,
  server serves client 2 while A1 still holds.
* `need_h2`: without h2 (h1, h3 on), **alternation fails**: client 2 waiting,
  server ends client 1's transaction (q excited to hand over), A1 falls, client
  1 re-raises r1 before q fires, the tie holds q, client 1 is granted again.
  `need_h2_q_disabled`: in that run q's excitation was withdrawn by the r1
  rise. In silicon that withdrawal is a runt, the header's "request coincident
  with A0-fall".
* `no_hyp_fails`: with no hypotheses both exclusion failures are reachable.

So: "Because q only ever moves while exactly one request is up, sustained
contention forces alternation" is false as an unconditional (delay-insensitive)
claim; the premise is true (proved), the conclusion needs H_Q_BEFORE_REREQ,
which is exactly the "one arc of margin" the header admits further down. More
notably, the header's tier 2 "during handover: structural WITH THE HOLD" is
also not structural in the delay-insensitive sense: it needs h1 and h3 (grant
and ack fall arcs shorter than a server round trip). The margins are large,
but they are timing hypotheses, and the theorem names them.

## What did not work / not done
* No request-routing skew between the state LUT's and the grant LUT's pins,
  and no separate rise/fall arcs (the header's 124 ps fall vs 56+52 ps rise
  race). The overlap mechanism in the runt trace is O5/O6 skew; rise/fall
  asymmetry would be a second mechanism (probe 7d territory).
* The bounded-delay model uses one constant delay per trace, not a delay
  varying per edge inside an interval. Counterexamples transfer; the positive
  theorem `exclusion_transport` is proved only for constant delays (per-edge
  varying transport delay can reorder edges and would need a different proof).
* The inertial result is proved for one instance (`δ = 1, W = 3`), not for
  all δ, W.
* The interleaving model has atomic gates; it locates runts (disabled
  excitations) but cannot say what they do.
* `H_REQ_SEP` is stronger than needed: it also separates opposite-sense pairs,
  which are clean anyway. A sharper hypothesis (only same-sense pairs and
  single-signal pulses) was not attempted.

## Verdict
**Works.** Binary model of tie, runt, and alternation done with the real INITs,
about 3 h. What it buys: (a) machine-checked statements of exactly which
timing hypotheses each of the header's three exclusion tiers and the
alternation claim rest on; (b) two corrections to the prose: the runt is a
SAME-sense near-coincidence (the "plain tie" is safe only at exactly zero
gap), and the tie goes to the previous winner; (c) tier 2 for `bd_arbiter` is a
large-margin timing property (h1, h3), not structural. Remaining effort to
extend: per-edge varying delays (1-2 days), rise/fall arcs with request skew
(1-2 days), general inertial lemma (half a day).

## Fidelity per primitive
* **LUT (state, grant):** Boolean function of the real INIT via `lutB`, plus a
  transport (or, in one instance, inertial) delay. Not the mux tree: no glitch
  or intermediate values (the Kleene remark is the only exception). Fidelity:
  exact for settled Boolean inputs; a runt is represented as a short binary
  pulse that circulates unchanged, which silicon does not do.
* **Feedback wire:** folded into one loop delay `L` shared by the state LUT and
  the grant LUT read of q (one net, no branch skew). W separate only in the
  inertial instance.
* **Grant LUT O5/O6:** separate constant delays `d5`, `d6`, same for rise and
  fall.
* **C-elements A1, A2 (`bd_c2`):** atomic Boolean gates (interleaving model);
  their own feedback-loop timing is assumed (track 5).
* **Clients, server:** idealised four-phase environments with unbounded delay;
  the timing hypotheses h1-h3 are where their speeds enter.
