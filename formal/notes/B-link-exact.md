# B-link-exact: one exact contract for one bd_link stage (probe Blink)

File: `formal/lean/Formal/Cells/LinkExact.lean` (core Lean, ~1040 lines).
Check: `/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/LinkExact.lean`
-> `[bchk] OK`. `#print axioms` of every headline theorem: only
`propext`, `Classical.choice`, `Quot.sound`. No sorry/admit/native_decide/axiom.

## Problem statement

One `bd_link` stage (`cells/rtl/bd_link.v`): the `bd_c2n` controller (real INIT
`00B2…`, pins I0 = req_in, I1 = ack_out, I2 = own feedback, I3 = rst) and one
latch bit (`bd_latch`, enable = the controller node), one token.

**Assumed** (named in the Lean):
- H_CTL_READ / H_PIN_READ: every LUT output is its real INIT in Kleene
  semantics of its pins, each pin read through its OWN read map (window
  `[t-hi, t-lo]`, non-monotone allowed: no FIFO). Power-up arbitrary.
- H_BOX: seven windows (req, ack, controller loop `Qlo>=1`, rst, data, enable
  branch, latch loop `Flo>=1`).
- H_ENV (open loop, one token): rst, req, ack, data definite on stated
  intervals, ARBITRARY (glitches, X) in every gap. Event times are parameters.
- Scope `Wf`: ordered windows; H_RST_EARLY / H_RST_EARLY_ACK (rst surely read
  low before req/ack can be read moved); H_ACK_ORDER (`V1 <= Fb + Blo`,
  implied by H_RACE_DN). Necessity only: H_REL_SPLIT (`Fa+Alo != Rb+Blo`).

**Spec** (`Spec`): node = window token (0 on `[Rhi,U0)`, 1 on nonempty
`[U1,V0)`, 0 on `[V1,inf)`), latch captures (`LibGapLatch.Capt`, B = V0) and
outputs `v` from `max(U1+pe.hi, Td+pd.hi)` on. With `U0=Ra+Alo`, `U1=Ra1+Ahi`,
`Rel=min(Fa+Alo, Rb+Blo)`, `V0=max(Fa+Alo, Rb+Blo)`, `V1=max(Fa1+Ahi, Rb1+Bhi)`.

**Proved**:
- `sufficient`: Conj => Spec for every behaviour in the box.
- `exact` (headline): under Wf and Split, (every behaviour meets Spec) IFF
  - H_RST_WIDTH   `Rhi + Qhi <= W + Rlo`            (NecessityReset, bd_c2n)
  - H_RACE_UP     `Ra1+Ahi + Qhi <= min(Fa+Alo, Rb+Blo)`  (CElemStrict, rise)
  - H_RACE_DN     `max(Fa1+Ahi, Rb1+Bhi) + Qhi <= Fb+Blo` (CElemStrict, fall)
  - H_SETUP_PULSE `U1 + Ehi + Fhi <= V0 + Elo`      (LibGapLatch, A,B = U1,V0)
  - H_SETUP_DATA  `Td + Dhi + Fhi <= V0 + Elo`
  - H_HOLD        `V1 + Ehi <= Tn + Dlo`            (C = V1)
  Necessity: `need_rst/up/dn/pulse/data/hold`, each an explicit simulated run
  (controller + latch, read maps constant or two-phase, adversarial fills of
  the env windows) breaking the spec. Proof order: each `need_*` assumes the
  earlier conjuncts (the run that realises the latch witnesses needs the
  controller races, `rpulse_eq`/`rhold_eq` make the node exactly
  `eAdv U1 V0 V0` / `eAdv U1 V1 V1`, LibGapLatch's adversarial enables).
- `no_cross`: the same iff with the per-cell theorems' own left-hand sides
  (`NecessityReset.c2n_box_exact`, `LibGapLatch.SafeBox` at
  `A,B,C := U1,V0,V1`). **Finding: composition adds no cross-cell
  condition.** The only coupling is substitution: the latch's enable times are
  the controller's input read windows. Consequences worth knowing:
  the controller's req-pin spread `Ahi-Alo` enters the latch's pulse budget
  (`Ra1+Ahi+Ehi+Fhi <= max(Fa+Alo, Rb+Blo)+Elo`); the latch hold window
  closes at the controller's SLOW reads `V1`; and latch hold correctness
  (enable 0 forever after V1) rests on the controller's fall race.
- `strict_edges`: with one tick of X before each binary edge (CElemStrict's
  convention) all six are strict; definite-window form above is `<=`.
- `witness` (non-vacuity): P0, slow-corner-scale illustrative numbers in ps
  (one corner; req [400,520], ack [380,500], loop [300,420], rst [600,900],
  data [350,480], enable [450,700], latch loop [280,400]; rst to 2000, req
  3000/4500, ack 4300/6000, data [2500,7000)); margins 1280 / 739 / 939 / 729 /
  1970 / 1629 ps. A simulated run exists and meets the spec. NOT route numbers.
- `Pv_one_tick` + `Pv_breaks`: six parameter sets, each violating exactly one
  conjunct by exactly 1 ps (all others and the scope met, by `decide`), each
  with a behaviour that breaks the stage (rst W=719; ack Rb=3560; ack fall
  Fb=5060; enable Ehi=1430; data Td=4471; next datum Tn=5370).
- C's interface: `rout_definite` (receiver's request pin DERIVED definite
  outside the node's windows through any window wire) and `out_port`
  (`Contracts.PortUpTo` of the output channel for one token, from Spec plus
  named H_ROUT (clean pin, as ContractsLink), H_ACK, H_ORDER, H_X_LEAD).

**NOT covered**: closed loop (races are about env event times; composing the
partners turns them into latency inequalities); the release tie
`Fa+Alo = Rb+Blo` (sketch: both inputs move together, no race needed, but
NOT proved); more than one token; a W-bit bus (per bit, shared node: not
stated as one theorem); the input port (Port => Env/DStab: one-token PortUpTo
cannot say "req low forever"); cleanliness of the request wire (not derivable
for window wires, WinFifo); correlated corners (box: pins independent).
