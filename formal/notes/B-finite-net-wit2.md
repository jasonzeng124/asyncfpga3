# B-finite-net-wit2 (probe Bfin3): a joint witness of `FGcdNetOK` on C's terminating run; tsrc; what chW cannot carry

2026-10-29. Continues Bfin2 (`notes/B-finite-net.md`): `FiniteNetMixed.gcd_hw_safe_fin_net`
(one gate-level network, links + forks N <= 4 + 2-input joins + steer branches + the 38
steer acknowledge ORs gate-modelled, finite edge counts) was proved but had no witness.
The lead's update during the probe: Bmn delivered the truncated `tmuxa` (`AssumeGuaranteeMuxNFin`)
and `gcd_hw_safe_fin_net3` (`AssumeGuaranteeMuxNNet`), so this probe did NOT write its own
tmuxa; the scope became tsrc and the witnesses.

## Files (all checked with `/tmp/claude-0/btools/bcheck.py`, core Lean only)

| file | result | content |
|---|---|---|
| `formal/lean/Formal/Cells/FiniteNetWit2Lib.lean` | **OK** | checkers + soundness: `celB_spec` (n-pin C-element), `stB_spec` (steer branch), `orB_spec` (acknowledge OR), `linkB_spec` (Bfin's `linkB` gives `FLinkSpec` + `LinkOut`); token tables `σT`/`κT` (H_KAPPA*), `nt11`, `step_win` |
| `formal/lean/Formal/Cells/FiniteNetWit2Data.lean` | **OK** | GENERATED (untrusted) node event lists per operator (`faL`, `jrL`, `sbTL`, `sbFL`, `aoL`) and steer select tables (`tabL`) |
| `formal/lean/Formal/Cells/FiniteNetWit2Chk.lean` | **OK** | `decide +kernel` on every operator (6 chunks) and every channel list (about 2 min) |
| `formal/lean/Formal/Cells/FiniteNetWit2.lean` | **OK** | the network `NW`, `fgcdNetOK_chW`, `gcd_hw_fin_net_witness`, `gcd_hw_fin_net_consistent` |
| `formal/lean/Formal/Cells/FiniteNetSrc.lean` | **OK** | `tsrc` (truncated `bd_src`) + `WitS.tsrc_witness`; `chW_src_unwired`; `chW_steer_unwired` + `steer_fires` |

Scratch (untrusted): `/tmp/claude-0/probes/Bfin3/gen.py` (imports C's `formal/tools/capwit/sim.py`
read-only, asserts its channel rows equal C's committed `CapstoneWitnessData`, simulates the
node traces, mirrors every checker, emits the Data file), `sim2.py` + `sim2.out` (non-unit
delays), `negctl.py`, `Ax.lean` (axiom printout).

## (2) The joint witness of `FGcdNetOK` on chW (a = 12, b = 18, quiet after 476 ticks)

`fgcdNetOK_chW : FGcdNetOK chW NW LW nW`. The network `NW` (cell type `Cl`):

* one contract cell per channel signal (`rq c`, `ak c`, 930 cells): node = the signal one tick
  earlier, no pins; every pin in the network is a channel signal driven by one of them
  through a unit `Wire`;
* 175 links `lk o`: Bfin's controller node, pins `req_i`, `ack_o'` (Bfin's `lk_all` reused);
* 41 fork acknowledge C-elements (N = 2, 3, 4: real `bd_c2`, `bd_ctree` N=3, `bd_c4` via
  `c2_gen`/`c3_gen`/`c4_gen`), 47 join request C-elements, 76 steer branches (real `bd_steer`
  `u`; select = bit 0 of the input bus; `σ`/`κ` = the token table, alternating past its end),
  38 steer acknowledge ORs (real `uack`, pins the two branch acknowledges): pins = C's channel
  traces, node SIMULATED with the real LUT at unit LUT delay, unit feedback wire, `R = 2`, and
  kernel-checked at every tick (constant after 480), with H_SND (`E = 1`), H_CNT, H_SEL_STABLE,
  H_ORD/H_DOWN, sortedness;
* every other cell (non-tied indices of `lk/fa/jr/sb/ao`) has an empty node.

`gcd_hw_fin_net_witness`: chW meets `FGcdNetOK` and C's H_OTHER (`w_cells`), H_BUNDLE (`w_held`),
H_CM_FORCED jointly, and out0 latches a token carrying 6; `gcd_hw_fin_net_consistent` applies
`gcd_hw_safe_fin_net`. So the gate-level finite-run network theorem is non-vacuous, on the real
terminating gcd run, with the 377 tied cells' LUT relations checked on real traces.

Degenerate parts, stated (do not read more into the witness):
1. **The gate-modelled fork/join/steer/OR nodes drive nothing.** `FGcdNetOK` ties these cells'
   PINS to channel traces but not their NODES (only links have `LinkOut`), and `H_SOR` does not
   even tie the OR's pins. In `NW` every channel signal is driven by a contract cell whose truncated
   contract holds because its conclusion does. No tied cell's guarantee feeds another tied cell's
   assumption, and links do not feed links either (Bfin2's chain witness had the same END
   contracts). Finding for the spec: `FGcdNetOK` could be strengthened to require
   `Wire (O (fa o)) (ch i).ack` etc.; but see 3.
2. Unit delays, every window met at width 0; `R = 2` chosen.
3. **This cannot be fixed on chW**: `FiniteNetSrc.chW_steer_unwired`: for a steer branch whose
   first request comes one tick after the input's first request (38 of the 53 branches that
   fire, by the pre-check; `steer_fires` exhibits one), NO node of the real `bd_steer` LUT
   (any `Win lo hi`, `1 <= lo`, H_PWR, ANY select trace) drives that branch request through ANY
   `Wire`. C's operator takes one tick channel-to-channel, B's LUT + wire at least two.

## (1) tsrc and the sources

`FiniteNetSrc.tsrc`: the real `bd_src` (`¬ack`, `src_gate`, H_PWR_SRC, no reset), truncated:
acknowledge clean on `[0, T)` (edge set `La`, downward closed) ⇒ node clean on `[0, T + lo)`
with edges `srcE`, node edge `k+1` iff acknowledge edge `k`; H_SPACE only for existing edges.
Proof via a new `phase_hold` (a `Win` LUT holds its phase to `b + lo` with no spacing).
`WitS.tsrc_witness`: all hypotheses on a one-handshake finite run, and the node is high
forever after the acknowledge falls.

`chW_src_unwired`: for each of the 3 sources and ANY `Win lo hi`/`Wire wl wh`, no node of the real
source LUT drives chW's source request (chW's acknowledge ends low, so the excitation is 1
forever; chW's request ends low). **A gate-modelled source and a terminating gcd run are
incompatible**: the real `bd_src` re-requests, so with gate-level sources the run is infinite
(gcd recomputed again and again). Therefore no `gcd_hw_safe_fin_net'` with sources tied is
witnessable on a terminating run, and I did not build that net theorem (tsrc is ready to plug in;
the witness would need an infinite-run version of `FEnv1`, which Bseg's `PhysLink` already is).

## (3) Non-unit delays (Python only, untrusted)

`sim2.py`: gcd_hw re-simulated with B's gate structure (links `bd_c2n` + wires; fork ack
C-element + request wires; join C-element; steer AND + OR; mux `j0/j1` C-elements + `uor` +
`uxa/uya`; muxn; amerge grants as nodes; sinks as wires), every LUT a transport delay `dL`,
every channel signal its driver through its own random wire delay, C-element feedback 1.
NOT gate-level (as in C): sources (one token then wait), data buses (combinational: bundling
trivially holds), the muxes' delay buffers.

| dL | wires | seed | quiet after | out0 values | C's unit-step cell checks (`sim.check`) |
|---|---|---|---|---|---|
| 1 | 1 | 1 | 696 | [6] | 0 violations |
| 2 | [1,3] | 1 | 1388 | [6] | 0 violations |
| 2 | [1,3] | 2 | 1385 | [6] | 0 violations |
| 2 | [1,3] | 3 | 1367 | [6] | 0 violations |

out0 = gcd(12, 18) = 6 in every run, and C's own step-form cell models, Held and
H_START_ONCE pass on the non-unit channel traces (negative control `negctl.py`: holding one fork
output request 3 ticks too long is flagged). So a connected (nodes wired to channels) Lean
witness at non-unit delays looks feasible; NOT done (no Lean for it). It would need the
net3 cell checkers too.

## NOT done / open

* No witness of `gcd_hw_safe_fin_net3` (`FGcdNetOK3`): it needs further checkers for the mux
  joins/acks/delay buffers/`uor`, the muxn decoders/joins/acks/line buffers/ANDs and the fork
  trees N = 5, 6. The checker pattern here (event lists, `decide +kernel`, soundness
  lemma per spec) carries over; estimate 2-3 h.
* The non-unit-delay network in Lean (the step that would make tied nodes actually drive
  the channels).
* `gcd_hw_safe_fin_net'` with sources tied: not built, because it is unwitnessable on any
  terminating run (`chW_src_unwired` is the reason on chW).

## Axioms

`#print axioms` (`/tmp/claude-0/probes/Bfin3/Ax.lean`): `fgcdNetOK_chW`, `gcd_hw_fin_net_witness`,
`gcd_hw_fin_net_consistent`, `celB_spec`, `stB_spec`, `orB_spec`, `linkB_spec`, `tsrc`,
`tsrc_witness`, `chW_steer_unwired`: propext, Classical.choice, Quot.sound; `op_all`,
`chW_src_unwired`: propext, Quot.sound; `steer_fires`: propext. No sorry, admit, native_decide.
