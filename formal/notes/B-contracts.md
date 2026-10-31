# B-contracts (probe Cc): one contract shape between B's timed cells and C's composition

Shard B, Phase 3, for shard C's composition of the gcd_hw graph. 2026-10-27.
Core Lean, no Mathlib. Files (all CLAIMED, all check clean):

| file | lines | content |
|---|---|---|
| `formal/lean/Formal/Cells/Contracts.lean` | 440 | `Port` (the uniform port contract), bridge to C (`Port.protocol`, `Port.held`, `Port.offAt_iff`, `Port.offer_val`, `Port.offered`), `OpSpec`, `EarlierDet`, `opSpec_of_ports`, `net_refines_ports`, a concrete port (`Witness.port`, `Witness.offers`) |
| `formal/lean/Formal/Cells/ContractsOps.lean` | 226 | one event contract per operator, in C's equations verbatim: `ForkEv`, `JoinEv`, `LinkEv`, `SrcEv`, sink, `SteerEv`, `MuxEv`, `MuxNEv`, `AMergeEv`; `*_det` (⇒ `EarlierDet`) and `*_spec` (⇒ C's `OpProto ∧ OpData`) |
| `formal/lean/Formal/Cells/ContractsB.lean` | 273 | B's `steer_ok_static` ⇒ the steer's half of the ports + `SteerEv` (`steer_contract`); generic helpers `tok_from0`, `enum_cnt`, `fst_mono`, `rx_min` |

## Check

    cd /home/user/asyncfpga3/formal/lean
    for f in Contracts ContractsOps ContractsB; do
      PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/$f.lean \
        -o .lake/build/lib/lean/Formal/Cells/$f.olean; done
    python3 ../scan.py Formal/Cells/Contracts.lean Formal/Cells/ContractsOps.lean Formal/Cells/ContractsB.lean

- All three: no output (clean), a few seconds each. Order matters (each imports the previous olean).
- `scan.py`: clean. No `sorry`/`admit`/`axiom`/`native_decide`.
- `#print axioms` (scratch file importing `ContractsB`) on `Port.protocol`, `Port.held`,
  `Port.offAt_iff`, `opSpec_of_ports`, `net_refines_ports`, all nine `*_spec`, `steer_contract`,
  `enum_cnt`, `Witness.offers`: `[propext, Classical.choice, Quot.sound]` only.
- Imports (read-only): `Formal.Net.Ops`, `OpsFork/Join/Steer/Mux/MuxNOp/CM/Link`, `CapstoneSrc`
  (C's equations), `Formal.Cells.OpsTimed`, `OpsTimed2` (B's `Tok`, `Enum`, `rx`, `steer_ok_static`).
  No shared definitions changed. The lead must add the three modules to `Formal.lean`.

## What C's composition expects (read from `Formal/Net/Ops*.lean`, C-8f/8i/8j/8n)

C composes with `net_refines` (`Ops.lean`). Its per-operator input is exactly

    OpProto ch (ins o) (outs o) ∧ OpData ch (ins o) (outs o) (E o)      -- here: OpSpec

on C's `Chan` (`req ack : Nat → Bool`, `dat : Nat → Nat`): a causal step-wise
assume-guarantee four-phase rule (`SendStep`/`RecvStep`, reset `Init`), H_BUNDLE as
`Held`, tokens counted at the offer (`OffAt c k r` = k-th `req↑` at `r → r+1`), and the
token equations `forkEq`, `joinEq`, `linkEq`, `srcEq`, sink `True`, `steerEq`, `muxEq`,
`muxnEq`, `amergeEq ω` (ω = the emitted index bit, `winner`). C currently gets these from
hand-written SI gate relations (`Fork`, `Join`, `Steer`, `Mux`, `MuxN`, `AMerge`, `Link`,
`Src`, `Sink`), which `OpsGen` (C-8n) ties to the generated INITs under H_FB_FIRST.
So "C's interface" = `OpSpec`; not token traces, not B's `Tok`.

## The uniform shape

**Per channel: `Port c ρ α v`.** `c.req` is B's `Tok 0 … ρ (fun _ => true)`, `c.ack`
is `Tok 0 … α true`, `0 < ρ 0`, `ρ j < α j < ρ (j+1)` (strict interleaving), and
`c.dat t = v k` on `[ρ (2k), α (2k+1))` (H_BUNDLE, req-rise to ack-fall, zero margins).
Each field is directly GLS-testable on one channel's pins (edge times, interleaving,
data window).

**Per operator: an event contract `…Ev`** over the ports' `ρ` and `v`: (causality)
each output token is offered strictly after the input tokens its value is made of;
(value) its value is the token equation applied to those input values. All of them
reduce to one property, `EarlierDet ρ v outs E`: every σ satisfying `E` and agreeing
with `v` on every token offered strictly earlier gives the output token the value `v`.

| theorem | statement |
|---|---|
| `Port.protocol` | a port is a C channel obeying C's `Protocol` (Init + Send/RecvStep at every step) |
| `Port.held` | a port satisfies C's `Held` (H_BUNDLE) |
| `Port.offAt_iff` | `OffAt c k r ↔ r + 1 = ρ (2k)`; `offer_val`: then `c.dat (r+1) = v k`; `offered`: every token is offered |
| `opSpec_of_ports` | ports on every channel + `EarlierDet` ⇒ `OpProto ∧ OpData` (C's `OpSpec`) |
| `net_refines_ports` | all channels ports + every operator `EarlierDet` ⇒ every solution `ref` of C's equations equals `v` on every channel (via C's `net_refines`) |
| `fork_det/_spec` | `ForkEv` (ρ_a(2k) < ρ_o(2k), v_o k = v_a k) ⇒ `forkEq` |
| `join_det/_spec` | `JoinEv` (all operands earlier, v_o k = g (map v k)) ⇒ `joinEq` (also every compute unit) |
| `link_det/_spec` | `LinkEv` ⇒ `linkEq` (link WITHOUT an initial token) |
| `src_det/_spec`, `sink_det/_spec` | `SrcEv` (constant value) ⇒ `srcEq`; sink trivially |
| `steer_det/_spec` | `SteerEv` (output b's token m is input token i with sel = b and `cnt … i = m`, offered after it, value `f (v_j i)`) ⇒ `steerEq` |
| `mux_det/_spec` | `MuxEv` (after control token k and after the selected input's `cnt`-th token; its value) ⇒ `muxEq` |
| `muxn_det/_spec` | `MuxNEv` (same, 3-way, with H_S_RANGE `sel < 3`) ⇒ `muxnEq` |
| `amerge_det/_spec` | `AMergeEv ω` (relative to the arbitration outcome ω) ⇒ `amergeEq ω` |
| `Witness.port`, `Witness.offers` | non-vacuity: a concrete period-8 port, token k offered at 8k with value k |

`SteerEv`/`MuxEv`/`MuxNEv` carry `Strict (ρ select-input)` because C's equations read
earlier select tokens (`cnt … k`); every `Port` provides it (`Port.strictR`).

## B's theorem ⇒ the uniform contract: the steer (`ContractsB.lean`)

`steer_contract`: from exactly `steer_ok_static`'s hypotheses (`SteerGates` with the real
INITs `0x8888888822222222`/`4'hE`, FIFO arcs; partner traces; `SteerCausal`;
`SteerStatic` = `bd_steer.bundled_s_setup` (S_S_SETUP), `bd_steer.bundled_s_hold`
(S_S_HOLD), and S_ACK), plus the named hypotheses below, it proves:
1. the sender-side ack is `Tok 0` on `K` (input port's ack half);
2. each branch request, re-indexed on its own tokens (B's `Enum`, `Tok.reindex`), is
   `Tok 0` on `rx R_b κ_b` (output port's req half);
3. strict interleaving `ρ j < K j < ρ (j+1)` and, per branch, on its tokens,
   `R < A < R(next)`;
4. `SteerEv ρ v sel f cj cout` (routing index via `enum_cnt : cnt g (κ m) = m`,
   causality via B's `steer_R_ge`).
With the partners' halves (sender's req, receivers' acks, data windows) that is `Port`
on all three channels, and `steer_spec` gives C's `OpProto ∧ OpData (steerEq …)`.

Named hypotheses added (each a fact about the routed design):
- `H_QUIET_ACK`, `H_QUIET_FWD`: steer-driven wires are low before B's clean window
  (`T2`, `T1`); `H_T1`, `H_T2`: that window starts before the first edge. Reset facts;
  `ResetGcd` proves all control nets settle low under reset, but not tied to these traces.
  GLS: wire is 0 from power-up to its first edge.
- `H_ER, H_ES ≥ 1`, `H_FWD_POS : 1 ≤ Wq.lo + Lm`: positive minimum delays (prjxray SDF minima).
- `H_SEL_VAL`: B's select bit `sv i` = C's `sel (v_j i)`.
- `H_STEER_DATA`: branch token value = `f` of the input token value (the data wire beside
  `bd_steer`; B has no data theorem for it because the cell has no data path; this is C's
  H_STEER_DATA).
- the identification of the port edges with B's derived edges (`hρj`, `hρo`).

Finding: `OpsTimed2.SteerStatic.S_ACK` cites `bd_steer.ack_or_skew`, which does NOT exist in
`formal/out/cell_constraints.json` (only `bd_steer.bundled_s_setup`/`_hold` do). Missing entry.

## What C's interface needs that B has not proved (precise list)

**G1 (main, blocks real composition): time-truncated (causal) B theorems.** `opSpec_of_ports`
takes ports on ALL channels for the whole run. B's theorems give a cell's driven wires from its
partners' wires for all time. In a closed graph this is circular (op A's output port needs op B's
ack, which needs A's output). C closes its circle with `OpProto`'s step-wise form (rules up to
`t-1` ⇒ rule at `t`). The needed B form: "if every partner wire is a clean `Tok` up to time t
(edges ≤ t) with the causality latencies, the cell's driven wires are clean up to t + min delay".
None of B's timed theorems (`steer_ok`, `mux_ok`, `merge_ok`, `muxn3_ok`, `ctl_phases`,
`ctree*_timed`) is stated that way. Without it, `net_refines_ports` is a statement about runs in
which all ports are GIVEN, i.e. B's results are consistency checks, not a derivation.
Estimated effort: per cell, re-prove with edges truncated at t (proof structure unchanged:
each derivation is per edge and only looks backward), then a generic event-induction lemma;
1-2 days for steer/mux/muxn3, more for the link (phase-time `CtlEnv`).

**G2: observation points.** C's `Chan` has ONE `req` and ONE `ack` trace. B's cells place them
at different ends: the steer reads its input `req` at the sender's port (wire `Wq` inside the
steer) and drives its outputs at the receivers' pins (wires `W0`, `W1` inside). If the next cell's
theorem also includes its input wire, the wire is counted twice and the traces do not match.
A convention is needed (e.g. "every channel is observed at the consumer's LUT pins; each cell
contains its OUTPUT wires only") and each B theorem re-stated to it.

**G3: data window (mux, merge, muxn3).** `Port.dat` (= C's `Held`) needs the bus stable from
req↑ to ack↓. B's `mux_data_ok`/`merge_data_ok`/muxn3 data theorems prove it on
`[Z(2k) - Mz, ζ(2k) + holdM]`: until ack↑ plus a margin, not to ack↓. Either C weakens `Held`
to the receiver latch's real hold window (8a's `SetupHold`), or B extends the data hold to ack↓
(plausible: each input sender holds until its own ack falls, after z_ack falls).

**G4: finite token streams.** `Port` (like B's `Tok`) has infinitely many edges. A branch that
receives finitely many tokens (e.g. a steer branch never taken, or a run with one invocation)
has no `Enum` and no `Port`. Needs a `Port` variant with a token count `n ≤ ∞` (edges beyond n
at "never"). C's sources repeat forever, so gcd with repeated invocation is fine; a single run
is not.

**G5: per operator, the B instantiation is not done except for the steer.**
- link/pipe (`LinkTimed`, `PipeTimedN`): conclusions are in environment phase times `cph j`
  (`CtlEnv`), node windows and latch capture (`stage_token`). Missing: the map from `cph` to the
  two ports' `ρ`/`α` and `LinkEv` (causality `ρ_in(2k) < ρ_out(2k)`, value = latched). Also a
  link WITH an initial token (bdc's reset-token buffers): C's `linkEq` does not cover it; needs
  `v_out 0 = init`, `v_out (k+1) = v_in k`.
- fork/join (`CTreeTimed`): C-tree output windows only (`= V k` on per-phase windows); no `Tok`
  form at the ports, and no fork req-wire / join data theorems (H_FORK_DATA, H_COMPUTE_DELAY
  stay C's hypotheses).
- mux (`mux_value_ok_static`) and 3-way mux (`muxn3_ok`): closest to done. Gated `Tok` traces,
  enumerations, `idx`. Missing: `idx κ0 k = cnt (!sv) k` (an `enum_cnt` variant), G3, then
  `MuxEv`/`MuxNEv` as for the steer. About half a day each.
- merge / control_merge: B has the SI checker results (`AMerge*`, `MergeMuxSI`) and the timed
  arc forms of the index bundling (`AMergeTimed*`), not an event-form operator theorem with
  ports. `AMergeEv ω` (each output token = next token of the winner, offered after it, index
  bit packed) is unproved on B's side. The 2-input `bd_merge` (`merge_ok`, `merge_data_ok`) is
  deterministic-by-assumption (`MergeEnv` presupposes exclusive inputs) and maps to C's `merge`
  only for exclusive inputs.
- src/snk: no B timed theorem (trivial cells); `SrcEv` is only the constant value.
- `ResetGcd`: proves the reset-quiet state of all 3322 control nets; not yet linked to the
  per-wire `H_QUIET_*` hypotheses above (needs the net names of each port).

## Verdict

**Works with effort.** The uniform contract exists and is proved to be exactly C's interface:
`Port` per channel + `EarlierDet` per operator ⇒ `OpProto ∧ OpData` ⇒ `net_refines`, with an event
contract for every operator C composes, in C's equations verbatim. For the steer, B's existing
timed theorem is proved to deliver its half of the contract under its static obligations. The
composition is NOT yet a derivation from B's cell theorems: it needs G1 (time-truncated B
theorems; 1-2 days for steer/mux/muxn3), the observation-point convention G2, and the data-hold
window G3; then the remaining instantiations (mux, muxn3 ~0.5 day each; link ~1 day; amerge open).

What it buys: one interface (`Port` + `…Ev`) that both shards can target, with every hypothesis a
per-channel or per-cell fact that GLS can check; and a precise list of what B must restate for
C's gcd composition to rest on gate-level timed proofs instead of SI gate relations.

## Fidelity per primitive

- No primitive is modelled in `Contracts.lean`/`ContractsOps.lean`: they are pure interface
  (wires are abstract traces).
- `ContractsB.lean` inherits B's steer model unchanged: `u` is the real LUT6_2 INIT
  `0x8888888822222222` (O5/O6 via `lutB`), `uack` the real `4'hE`, every LUT and wire a FIFO
  bounded-delay arc (`Ret`, H_LUT_FIFO/H_WIRE_FIFO: no glitch, no runt, no inertial filtering), no
  isochronic fork. The data wire beside the steer is not modelled (H_STEER_DATA).
- The `Port` data field is C's `Held` with zero margins; the receiving latch's own setup/hold is
  not in it (8a's `SetupHold`, B's `Bundling`).
