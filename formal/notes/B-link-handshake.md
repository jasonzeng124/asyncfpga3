# B probe 6b: link controller, four-phase handshake (`bd_link`, `bd_pipe`, `bd_link_dctl`)

File: `formal/lean/Formal/Cells/LinkHandshake.lean` (core Lean, imports only
`Formal.Cells.Prelim`, ~1150 lines). Checks clean: no `sorry`, no extra axioms,
no native evaluation. `#print axioms` on every main theorem gives only a
subset of `propext, Classical.choice, Quot.sound`.

Check command (about 10 s; nearly all of it is the N = 3 finite check in Section 3):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/LinkHandshake.lean

No new shared definitions. Everything is local to namespace
`Formal.Cells.LinkHandshake`. Prelim is unchanged.

## Cells and INITs used (verbatim from cells/rtl)

* `bd_link_ctl` = `bd_c2n`: INIT `0x00B200B200B200B2`, `I0=req_in I1=c_next I2=c (fed back) I3=rst I4=I5=0`.
  `ctlB_eq`: with rst=0 the INIT equals `req·¬cnext + c·(req + ¬cnext)` = C(req, ¬c_next). `ctlB_rst`: rst=1 forces 0.
* `bd_latch` odd bit: `0xB8B8B8B8B8B8B8B8`, `I0=d I1=en I2=q`. Pair: LUT6_2 `0xFF33CC00B8B8B8B8`,
  `I0=d_i I1=en I2=q_i I3=d_j I4=q_j I5=1`, `O5=q_i O6=q_j`. `lat_eq` and `pair_eq` prove each is `en ? d : q`.
* `bd_link_dctl` (LDN=0 so `s=1`; BROAD 0/1): `ub 0x0000F3200000F320`, `ua 0x0000FA800000FA80`,
  `uld 0x00000F0800000F08`, `ult 0x0101010101010101`. `dctl_eqs` proves they equal the header's set/reset equations.

## Theorems (all proved)

### Item (1): one stage refines four-phase (interleaving, atomic gates)
Model (Section 2): state `x : Nat → Bool`, `x 0 = req_in`, `x (i+1) = C_i`,
`x (N+1) = ack_out`. Transitions: the sender toggles `req_in` when `ack_in = C_0` equals it;
gate `i` fires when its LUT output (`ctlB`, from the INIT) differs from the node;
the receiver copies `req_out` into `ack_out`. A compliant environment *may* move.
It is never forced to, so this covers every four-phase environment.

* `link1_four_phase`: in a one-stage link, `C_0` (= `req_out` = `ack_in`) rises only while
  `req_in = 1` and `ack_out = 0`, and falls only while `req_in = 0` and `ack_out = 1`. So both
  channel pairs are four-phase.
* `node_moves` (any N, any stage): the same at every internal boundary. `env_moves`: the
  environment wires move only by their owners, and by the four-phase rules.
* `persist` (any N): **speed independence.** An enabled transition (gate, sender or receiver)
  stays enabled when any other transition fires. So the controller LUT has no hazard
  and the circuit never withdraws a request or acknowledge.

Hypotheses this model hides. They are named and treated below:
* **H_ISO_FORK**: node `C_i` reaches its readers (next stage's `I0` / `req_out`,
  previous stage's `I1` / `ack_in`, the latch enables) at the same instant.
  Section 3 discharges it for the control (N ≤ 3). It matters only on the latch-enable
  branch, which is Section 5.
* **H_FB_FAST** (fundamental mode of the controller loop): the LUT's own `O -> I2`
  feedback wire settles before any neighbour can respond to the new value.
  `fb_refines` proves it sufficient (any N). `fb_hazard` proves it needed (N = 1: the sender
  drops `req_in` after seeing `ack_in` high, the stale feedback pin makes the LUT compute 0,
  and `C_0` falls with `ack_out` still low, giving a runt on `req_out` and a four-phase violation).
  Test: compare the feedback-net max delay with the min of `C_i -> neighbour -> pin of C_i`
  on GLS/prjxray timing.

### Item (2): pipe of N stages (general N, plus N = 2, 3)
Token picture: `d x j = x j xor x (j+1)` for `j = 0..N` is a half token on boundary `j`
(boundary 0 = input wire, boundary `i+1` = stage `i`). A gate moves a half token one
boundary forward (`d_gate`), the sender creates one at boundary 0 and the receiver removes
one at boundary N. This is an exclusion process with injection and ejection.

* `conservation`: for every state reachable from reset after `s` sender and `r` receiver
  transitions, (half tokens in flight) + r = s. **No token is lost or duplicated.**
* `bounded`: `r ≤ s ≤ r + N + 1`. This is at most one half token per stage plus one on the input
  wire, i.e. "half a token per stage". `pipe2_full`: the bound is attained (N = 2, 3 half tokens,
  receiver stalled).
* `deadlock_free`: in every state, reachable or not, some transition is enabled.
* `send_progress` / `recv_progress`: any run that avoids the sender (resp. receiver)
  has at most `Phi` (resp. `Psi`) ≤ (N+1)(N+2)/2 transitions. With a greedy environment every
  run is infinite, and sends and receives each recur within every window of
  (N+1)(N+2)/2 + 1 transitions. So there is no starvation and no livelock.
* N = 2, 3 instances: `pipe2_bounded`, `pipe3_bounded`, `pipe2_live`, `pipe3_live`
  (window bounds 6 and 10 evaluated).
* Section 3, `di_pipe1/2/3` (finite, kernel `decide`): the same control with **a separate
  unbounded delay on every fork branch** (`C_i -> next stage`, `C_i -> previous stage`, and
  `req_in`/`ack_out` wires). In every reachable state there is no hazard on any gate or wire
  (persistence) and no deadlock. Reachable sets have 32/128/512 states. The bitmask
  is computed outside Lean, and the kernel checks that it contains reset, is closed, and
  satisfies the properties (`g_sound`, `g_props`, a generic checker).

### Item (3): data path, latch enable = C_i, bundling as a derived condition
* Latch LUT, Kleene (`latK_*`, `pairK_keep`): open passes D, shut holds Q, and **closing is
  glitch-free when D = Q at the pins whatever the enable does (X included)**. If D ≠ Q while
  the enable is in transit, the loop goes to X (`latK_race`). For the pair, the other
  bit's pins cannot disturb this bit even at X.
* `latch_capture` (timed, `Nat` time, hypothesis **H_LUT_TRANSPORT**: `Q(t+L)` is the
  Kleene LUT of the pins at `t`, with the feedback pin seeing `Q(t-F)`). Suppose the enable at this bit
  is high on `[a,c)`, any value on `[c,c+h)` and low on `[c+h,z)`. Then
  **SETUP `a + L + F ≤ c`** and **HOLD (D = v on `[a, c+h)`)** give `Q = v` on `[a+L, z+L)`.
* `setup_needed`: concrete counterexample with L = F = 1. D arrives one tick too late
  (`a+L+F = c+1`), and the loop captures X, which then circulates as a 1/X pattern.
* `pipe_data` (any N, one bit, one token; **H_WIRE_TRANSPORT**: data wire `Q_i -> D_{i+1}` is a
  pure delay `w(i+1)`). With the data wave `arr 0 = max(o0, a0)`,
  `arr(i+1) = max(o(i+1), arr i + L + w(i+1))`, the conditions
  SETUP_i: `arr i + L + F ≤ c i` and
  HOLD_{i+1}: `c(i+1) + h ≤ z i + L + w(i+1)`, plus a source that holds `v` on
  `[a0, c0 + h)`, give that every stage latches `v` and holds it until its next opening.
* `setup_iff`: **the exact bundling condition**. SETUP_i holds iff for the source and for
  every upstream stage `j ≤ i`:
  `o_j + Σ_{m=j+1..i}(L + w_m) + L + F ≤ c_i` (and `a0 + Σ_{m=1..i}(L+w_m) + L + F ≤ c_i`).
  Here `o_j = t(C_j↑) + e_j(bit)` and `c_i = t(C_i↓) + e_i(bit)`, with `e` the enable-wire delay to that bit.
  The `j = i` term is a minimum enable pulse width at the pin. The `j < i` terms are
  the header's fill race ("the closing wave gains on the data wave", rule I): the data opened
  by `C_j` must cross `i-j` latch arcs and data wires before `C_i` falls at this bit.
  **The timing inequality compares data arrival with C_i's FALL at latch i, not with
  C_{i+1}'s rise.**
* `arr_classical`: the classical "request after data" (`o_i + L + w_{i+1} ≤ o_{i+1}`, i.e.
  `C_{i+1}↑` at the latch at least one latch arc plus one data wire after `C_i↑`) is sufficient. It makes
  the data wave equal to the enable wave, so only the pulse-width term remains.
  It is NOT necessary, and the Muller stage does not provide it on its own (56 ps controller arc
  against a 152 ps latch arc), which is why the exact form above is what the route must meet,
  with SDELAY as the adjustment.
* HOLD in control terms (derived by hand, not in Lean): `z_i = t(C_i↑ next) + e_i`, and
  `C_i↑ next` cannot happen before `C_{i+1}↓` reaches `C_i`'s `I1` through the ack wire and
  DACK and then one controller arc. Sufficient:
  `e_{i+1}(bit) + h ≤ d_ackwire + d_DACK + d_ctl + e_i(bit) + L + w_{i+1}`: the enable fan-out
  skew of stage i+1 against the round trip back through stage i. This is rule H and the reason DACK
  holds back the ack's FALL. At the pipe input, `hsrc` (`D_0` held until `c_0 + h`) is the same
  condition for the sender: it must not release data until `C_0`'s fall has reached the latest
  latch bit (the 1125 ps fan-out of the header).

### bd_link_dctl (Section 6, one stage)
* `dctl_eqs`: the four INITs equal the header's equations.
* `dctl_ok1` / `dctl_ok0` (BROAD = 1 / 0): against a four-phase sender and receiver, under
  **H_LT_FIRST** (as a schedule: no neighbour fires while `lt` is excited; physically, `lt` settles,
  one LUT arc, before a neighbour can respond to `b`/`a` through wire, LUTs and wire back), every
  reachable state is hazard-free and deadlock-free (29 / 32 states).
* `dctl_si_hazard`: without H_LT_FIRST there is a reachable state (a 9-step trace) where `lt` is
  still the stale 1 after a whole handshake and firing `a` withdraws its excitation, i.e. a hazard on
  the latch enable. This matches the header's report of `verify/decoupled_si.py`.
* Four-phase compliance of dctl's channels follows directly from `dctl_eqs` (b sets only with
  `¬ack_out`, resets only with `ack_out`; a sets only with `req_in`, resets only with `¬req_in`).
  It is not stated as a separate Lean theorem.

## What did not work / is not done (unproved goals)
* The fork-branch-delay model (Section 3) is checked only for N = 1, 2, 3, not for general N.
  A general proof needs an inductive invariant on wire ends (each branch lags its driver by at most
  one transition, plus the d-picture). Not attempted. Estimate: 1 day.
* The timed model (Section 5) is not linked to the untimed models. The event times `o, c, z` are
  free parameters, not derived from the controller and wire delays. The hold condition in control
  terms is a hand derivation (above), not a theorem.
* Delays are fixed pure (transport) delays per arc and per bit, not ranges. The bounded-delay
  relational model of Track 3 should replace H_LUT_TRANSPORT / H_WIRE_TRANSPORT.
* Data correctness is one bit and one token at a time. Multi-token FIFO ("the k-th value out is the k-th
  value in") is not stated as a single theorem. Conservation plus exclusion gives the order in the
  untimed model, and `pipe_data` applies per token with that token's times, but the two are not joined.
* `bd_link_dctl` is checked as a single stage only (no `bd_pipe_dc`), with LDN = 0 (no `s` line), and
  without its `bd_delay` lines. Its setup rule K (data vs capture on the request) is not formalised.
* Reset is not modelled as a transition. Every run starts at the reset values.

## Verdict
**Works.** Item (1) and item (2) are proved for general N in the isochronic-fork interleaving model,
and for N ≤ 3 with independent delays on every fork branch. Item (3) has an exact, machine-checked
bundling condition (`setup_iff`), proved sufficient (`pipe_data`) and shown necessary by a
counterexample (`setup_needed`). `bd_link_dctl` is done for one stage.
Effort to finish:
* General-N branch-delay theorem: about 1 day.
* Delay ranges on top of Track 3's bounded-delay channel: 1-2 days.
* Deriving `o/c/z` from controller and wire delays, turning the rule-H derivation into a
  theorem, and multi-token data: 3-5 days.

What it buys: rules I (fill race) and H (hold / DACK) become exact, proved inequalities instead of
heuristics. The isochronic-fork assumption is shown to be needed only on the latch-enable branch.
The feedback-loop fundamental-mode assumption (H_FB_FAST) is pinned down as the one place where
the controller is not speed-independent, and the dctl header's single-assumption claim is confirmed.

## Fidelity per primitive
* **Controller LUT (`bd_c2n`)**: real INIT and pins, evaluated with binary `lutB`. A firing is atomic
  (an interleaving step). A hazard shows up as a withdrawn excitation, which the persistence theorems
  rule out. The mux-tree / Kleene behaviour during a firing is not used here (probe 5a/CElemFn covers
  it). Its feedback wire is either instantaneous (H_FB_FAST, Sections 2-3) or a separate
  unbounded-delay variable (Section 4).
* **Routing wires (control)**: Section 2 is zero delay (H_ISO_FORK). Section 3 gives one unbounded-delay
  variable per fork branch. Because persistence holds, no pending transition on a wire is ever
  withdrawn, so inertial vs transport makes no difference there. There is no R/C or prjxray delay data.
* **Latch LUT (`bd_latch`, odd bit and LUT6_2 pair)**: real INITs, Kleene `lutK` (H_KLEENE_LUT), fixed
  transport delay `L` for the arc and `F` for the feedback wire (H_LUT_TRANSPORT). The enable's transit
  is modelled as an arbitrary K3 window of length `h`.
* **Data wires**: fixed pure delay per bit and boundary (H_WIRE_TRANSPORT).
* **Delay lines (`bd_delay`: DELAY, DACK, SDELAY)**: not modelled as gates. For the control they are
  extra delay on one fork branch, which Section 3 already covers. For timing they appear only as terms
  of `e`, `w` and the hold derivation.
* **`bd_link_dctl` LUTs**: real INITs (LDN = 0, BROAD 0/1), binary, atomic firings, `lt` timing as the
  schedule H_LT_FIRST.
* **Environment**: an abstract four-phase sender and receiver.
