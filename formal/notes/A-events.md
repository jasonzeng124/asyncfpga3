# A-events: an event-count (counter) domain that stays precise on self-timed loops (shard A)

## Verdict

**It works for closed Muller networks of `bd_c2n`/`bd_c2n_set` stages, ring3 included.**

- The domain abstracts each C-element node by a **count** `M t j`, the number of times it has
  fired. It drops the per-time `K3` value. It is proved sound for every Discrete-transport
  behaviour.
- On ring3, which `xaudit`/XSim reports UNRESOLVED after about one lap, the result is now a
  theorem about every behaviour of the **parsed netlist**:
  - **no X and no glitch at any time, for ever;**
  - every hop takes between 45 and 57 steps (450..570 ps);
  - the node period lies in [2700, 3420] ps, and this window does **not** widen with the
    number of laps.
- 200 random concrete transport runs agree: the observed hop gap is [450, 560] ps and the
  observed node event spacing is [1350, 1550] ps.
- **Open networks (pipe3) are not covered yet.** They need an environment model (E2 below) and
  buffer chains on pins (E1). `xevents` refuses pipe3 and says why.
- **gcd_hw's loops are only partly unblocked** (see the gcd_hw section).

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Events.lean` | proved. Domain, `Beh`, counts `M`, `M_mono`, `pin_le_q`, **`safe`** |
| `formal/lean/Formal/Core/XAudit/EventsRing.lean` | proved. ring3 for **any** bands: `ring_inv`, `hops_upper/lower`, `node_period`, `ring3_safe` |
| `formal/lean/Formal/Core/XAudit/EventsDesign.lean` | proved. Link to the parsed `Design`: `Recog`, `design_beh`, **`design_safe`**, and `Ring3D.ring3_design` on the `--emit-lean` literal of `designs/ring3.json` |
| `formal/lean/Formal/Core/XAudit/EventsMain.lean` | compiles. Executable `xevents`; TRUSTED parser (a verbatim copy of Main's) and report |
| `formal/lean/Wip/Events.lean` | 3 open shapes (`sorry`): E1 buffer chains, E2 open nets, E3 general period bounds |
| `formal/tools-A/xaudit/events/run.sh` | builds the oleans privately (via `../lean.sh`), runs `xevents` and the simulation |
| `formal/tools-A/xaudit/events/ring3_sim.py` | random concrete transport simulation of the same gate-level model (evidence only) |
| `formal/tools-A/xaudit/events/*.txt` | the results quoted here |

### Check

From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Events.lean Formal/Core/XAudit/EventsRing.lean \
      Formal/Core/XAudit/EventsDesign.lean Formal/Core/XAudit/EventsMain.lean
    # -> [audit] 890 declarations checked, [check] OK   (about 25 s)

- There is no sorry, admit, axiom, native_decide or bv_decide.
- The only axioms used are `propext`, `Classical.choice` (`axiomOfChoice`, to pick the warps
  of every gate in `design_beh`) and `Quot.sound`.
- The ring3 instance facts use kernel `decide +kernel`: `Ring3D.recog`, `race`, `bands_lo`,
  `bands_hi`, `rst_hi`.

### Lakefile stanza (for the lead; I did not edit the lakefile)

```toml
[[lean_exe]]
name = "xevents"
root = "Formal.Core.XAudit.EventsMain"
```

Usage: `xevents NETLIST.json [--top T] [--bands B.json]`.

Until the stanza exists, run `formal/tools-A/xaudit/events/run.sh`. It uses the interpreter,
`lean --run`, against private oleans in `/tmp/events/olean`.

## The domain and why it does not lose phase

**Why XSim loses phase.**
- XSim keeps one `K3` per wire per step, so the X window of every event is absolute.
- The windows widen by Σ(hi−lo) per hop. That widening is real: the delays of successive laps
  are independent.
- After about one lap, the window of a C-element's own feedback overlaps the window of its
  neighbour's next request. At that point no per-time abstraction can tell that the feedback
  arrives first.
- That ordering is a **relation between two causally linked events**, and it holds in every
  behaviour (`win_exact` shows each single gate is already exact, so the loss is entirely in
  composition).

**The counter domain.**
- It keeps the relation and drops absolute time. Each node is `c j t = ph (v j) (M t j)`: its
  reset value, flipped `M t j` times.
- The counts follow the min-plus (counter) recursion of a timed marked graph, evaluated over
  the behaviour's own warps (`Beh.M`, defined by well-founded recursion):

      M t j = 0                                                   if the reset pin is high at F j t
            = min_p ( M (G j p (F j t)) (src j p) + off j p )     otherwise

  Here `F` is the LUT's monotone warp, `G j p` is the route warp of pin `p`, and `off ∈ {0,1}`
  is the token on that arc. `off` is computed from the reset values and the pin polarity.
- Monotone warps compose into monotone functions, which is the FIFO fact the window channel
  lacks. Counts may jump by more than 1 (an annihilated pulse), and nothing assumes they do
  not.

**The two hypotheses** (both decidable and checked):
- **`Pairing`**: every pin of `j` reads a stage `k` that reads `j` back through a pin, and the
  two tokens sum to 1. This is the Muller handshake structure. It holds for rings and pipes.
- **`Race`**: `hiQ j ≤ loG j p + loF k + loG k p'`. Own feedback must be no slower than the
  fastest round trip through any neighbour. This is A-xaudit's relative-timing obligation for
  the LUT C-element, now a stated and checked hypothesis.

**The proof of `safe`** is a strong induction on time. It uses three facts, and there is no
case analysis on the network:
1. `M` is monotone (`M_mono`).
2. The neighbour bound `P j p s ≤ M (Q j s) j + 1` (`pin_le_q`, from `M_le_pin`, `Pairing`
   and `Race`): a pin is at most one phase ahead of the stage's own fed-back count.
3. The four-case lemma `maj_ph`: if `mq ≤ pa, pb ≤ mq+1`, then
   `maj(ph pa, ph pb, ph mq) = ph (min pa pb)`.

## Theorems

| name | statement |
|---|---|
| `Events.maj_ph` | the C-element as a counter (above) |
| `Beh.M_eq`, `Beh.M_mono`, `Beh.E_mono` | unfolding; counts are monotone in time |
| `Beh.M_le_pin` | `M u k ≤ M (G k p' (F k u)) (src k p') + off k p'` (min-plus upper bound) |
| `Beh.pin_le_q` | `Pairing ∧ Race ⇒` each pin phase ≤ own feedback count + 1 |
| **`Beh.safe`** | `Pairing ∧ Race ⇒ ∀ t j, c j t = ph (v j) (M t j)` for every behaviour |
| `Ring3.pairing` | ring3's `MNet` satisfies `Pairing` (decide) |
| `Ring3.ring_inv` | at every t: `M2 ≤ M0 ≤ M1 ≤ M2 + 1`, so the firings are strictly sequential c1, c0, c2, … (no Race needed) |
| `Ring3.state_of_hops` | `M1 = (H+2)/3`, `M0 = (H+1)/3`, `M2 = H/3` with `H = ΣM`: the whole state is a function of the hop count |
| `Ring3.hops_upper` | `d ≤ loF+loG` on every pin ⇒ `H (t + k·d) ≤ H t + k` |
| `Ring3.hops_lower` | `hiF+hiG ≤ D`, reset pins low from `R` ⇒ `∀ t ≥ R, H t + k ≤ H (t + k·D)` |
| `Ring3.node_period` | each node fires at most once per `3d` steps and, after `R`, at least once per `3D` steps |
| `Ring3.ring3_safe` | with Race, the three node waveforms are `ph v (f(H t))` at every t |
| `Events.c2nInit_eval` | the real INITs `0x00B2…`, `0xFFB2…` on `[a,b,q,rst,0,0]` are `lutF` (all 32 cases, decide) |
| `Events.design_beh` | `Recog d net sm` ⇒ every `Circuit.Sat (toCircuit (build d)) x` (with const-0 = 0 and the reset port falling once at T ≥ 1) is a `Beh`, node signals = LUT output wires, reset pins low from `T + hi` |
| **`Events.design_safe`** | `Recog ∧ Pairing ∧ Race` ⇒ every LUT-output wire of every behaviour of the parsed design is `ph v (M t j)` at every t, with `M` monotone |
| **`Ring3D.ring3_design`** | for the parsed ring3 netlist (slow-corner bands, 1 step = 10 ps), every behaviour: wires 5/7/3 are fixed functions of `H` at every t; `H 0 = 0`; `H (t + 45k) ≤ H t + k`; `∀ t ≥ T+44, H t + k ≤ H (t + 57k)` |

## Precision achieved

### ring3, slow-corner bands (`designs/slow_corner.bands.json`, ILLUSTRATIVE ±10 %)

The bands in steps are:
- LUT [9, 13], with lo rounded down and hi up from [99, 121] ps;
- route [36, 44];
- feedback [27, 33].

| | XSim / xaudit (A-xaudit) | counter domain (this probe, proved) | 200 random concrete runs |
|---|---|---|---|
| node values | X from about 5.2 ns, UNRESOLVED to the horizon | binary at **every** time, for ever | — |
| hop gap | — | [45, 57] steps = [450, 570] ps, **every** hop | [450, 560] ps |
| node event spacing | — | [1350, 1710] ps | [1350, 1550] ps |
| node period | — | [2700, 3420] ps | — |
| Race margin | — | round trip ≥ 810 ps vs feedback ≤ 330 ps: margin 480 ps | — |

- **The intervals stay bounded per lap.** The proved bound for hop `n+1` relative to hop `n` is
  the same for every n.
- The absolute time of hop `n` is uncertain by about `n·(D−d)`. This is real, not imprecision:
  the delays of different laps are independent warps.
- **Lower bound.** The lower bounds 45 steps per hop and 135 per node event are attained by the
  random runs, so they are tight.
- **Upper bound.** The proved upper bound of 57 steps per hop was not reached by the random
  walks (the maximum observed was 56).
  - 57 = LUT_hi + route_hi, which is the delay of a hop whose LUT and route both sit at their
    maximum.
  - The bound is therefore attainable by a behaviour with every delay at hi. Random walks
    rarely sit at hi for a whole hop.

### Negative controls

- **`slowfb.bands.json`** (feedback [1300, 1500] ps):
  - `xevents` reports Race false (margin −690 ps) and VERDICT NOT PROVED.
  - The concrete simulation with feedback [130, 150] steps breaks the protocol in **100 of 100**
    runs. For example c1 rises at 245 and falls back at 337 before c2 ever rose: the C-element
    race of A-xaudit.
- **Tightness of `Race` on ring3.**
  - Race allows a feedback delay up to 81 steps (36 + 9 + 36).
  - A fixed feedback of 81 steps is clean in 40 of 40 runs.
  - A fixed feedback of 85 steps fails in 40 of 40 runs.
  - So the hypothesis is not just sufficient, it is essentially at the boundary here.
- **pipe3.** `xevents` refuses it because it is not closed: stage 0 reads `req_in`, stage 2
  reads `ack_out`, and stages 1 and 2 read `r[i]` through a `bd_delay` LUT1. It exits with
  code 3 and a reason, so the tool does not over-claim.

### Comparison with shard C's ring results

C's `Ring.lean` is untimed. It proves, among other things:
- the wavefront invariant `D = 2`;
- `persistent`;
- `ring_three`;
- `fair_window`: every N(N−1)+1 firings fire every stage, under any interleaving.

`Ring3.ring_inv` is the gate-level, timed counterpart for N = 3, and it is sharper:
- **Gate level and timed.** It is proved for the LUT C-element with its routed own feedback
  under transport delays, not for an atomic C-element under `H_SI`.
- **Fewer hypotheses.** It needs no H_SI assumption and no `H_RESET_CLEAN`.
- **Exact sequencing.** The interleaving is forced to be exactly c1, c0, c2. That matches C's
  token picture: two wavefronts, one stage between them, so at most one stage is excited at a
  time.
- **Race is now explicit.** C's H_SI silently assumed the C-element race away
  (`H_FB_SETTLED`). Here it is the explicit `Race` hypothesis, checked per pin.

**Cycle time against "period = Σ delays".**
- The proved node event spacing is `[3d, 3D] = [N·(LUT+route)_lo, N·(LUT+route)_hi]`. So the
  node period, two events, is `2·Σ_stages (LUT + route)`, as an interval.
- This is the max cycle ratio of the counter graph. `xevents` prints it as computed for other
  nets: the backward cycle (b-pins) carries 1 token over N hops.
- The n = 128 board/GLS ring measurements read period as a sum of stage delays. The proved
  interval is that statement with both corners, for N = 3.
- I did not re-derive the n = 128 numbers. That needs the general period theorem (E3) and the
  real per-arc bands.

## Fidelity

| item | model | status | test |
|---|---|---|---|
| LUT function | real INIT of `bd_c2n`/`bd_c2n_set` (`c2nInit_eval`, all 32 cases), Boolean pins | exact (UG474) | GLS with unisim LUT6 |
| LUT and route delay | Discrete transport: monotone warp, delay in `[lo,hi]`, varying per event | the FIFO channel. **Not** proved for the weaker non-FIFO `WinCh`; there a route could replay old/new trains and a C-element could glitch, so the precision gain *depends on* the FIFO hypothesis | GLS: per-arc SDF delays are pure/transport (`cells/gls`); board: a TDC on a route would show non-FIFO behaviour as runts |
| pin sampling | all pins sampled at one instant, then the LUT warp (same as XSim) | hypothesis | per-pin IOPATH in GLS |
| inertial filtering | not modelled | sound only for transport; an inertial LUT that swallows a pulse is not a warp. In a ring no pulse is shorter than a hop (≥ 450 ps), so it is moot there but not in general | GLS at both corners |
| reset | the reset port falls once at T ≥ 1; each reset arc is a warp | hypothesis (`hrst`) | the reset sequencing of the rig |
| power-up | arbitrary; reset at time 0 forces the LUT | sound | — |
| bands | from the parsed band file; here ILLUSTRATIVE ±10 % one-corner numbers | the numbers are not measured | prjxray per-arc bands per corner (A-xaudit item 3) |
| metastability, runts | none (binary) | out of scope; `Race` excludes the C-element's own runt mechanism | B's CElemTiming runt results |

## What it does not do, and the next steps

| item | what | estimate |
|---|---|---|
| E1 | buffer **chains** on pins (bdc `bd_delay` lines, pipe3 `r[i]`): compose warps with `transport_comp`, extend `Recog` | 0.5 day |
| E2 | **open nets** (pipes): environment pins with a count and two hypotheses (never more than one phase ahead through a round trip; answers within a bound). Only `pin_le_q` changes. The stimulus discharges them by `decide` | 1 day |
| E3 | period bounds for **every** recognised net, from max-cycle-ratio arguments on the same counter inequalities (today proved for ring3 only, and computed for others) | 1-2 days |
| E4 | other stage kinds: n-input C-elements (fork/join, `bd_c3`/`bd_c4`): `maj_ph` generalises to "all inputs equal phase ⇒ follow, else hold" | 0.5 day |
| E5 | data-dependent control (mux/steer/merge) and the arbiter. A count per *channel*, with choice. No longer a marked graph | research, 3-5 days |
| E6 | **bundling inside loops**: data valid before the latch-enable event, as a separation from the req event. Per hop, re-run XSim in time *relative* to the hop, which the counter result now justifies (the state at each hop is a function of `H`) | 2-3 days |

## gcd_hw: does this unblock its loops?

**Partly.** It removes the reason A-xaudit gave for "UNRESOLVED everywhere", which was the phase
loss of free-running control rings. Where the loop control is a Muller ring/pipeline of `bd_c2n`
links, the counter domain proves it hazard-free for ever, with a per-pin Race margin. gcd's
1-stage control ring is padded to 3 stages (C-9b), which is exactly the ring3 shape.

gcd_hw also needs:
- **E1 and E2**: delay lines on req, and the entry/exit of the loop.
- **E4/E5**: the loop header mux and steer, which are data-dependent, plus forks and joins.
- **E6**: the datapath latches inside the loop.
- A-xaudit's blockers 1–3: the routed netlist, CARRY4/MUXF, and per-arc bands.

E5 is the hard one. The counter domain needs a per-channel count, and the token's path depends
on data.

A realistic order: E1, E2 and E4 (2 days) cover the bdc control skeleton without choice; E6
(2-3 days) adds bundling; E5 stays research.

## What it buys

- **The first sound check that stays precise on free-running self-timed loops.** It holds for
  every delay in the bands and for all time, and it rests on a decidable hypothesis (`Race`)
  whose margin is printed per pin.
- **Cycle time and per-hop bounds proved on the parsed netlist** for ring3.
- **The LUT C-element's relative-timing obligation** ("own feedback ≤ fastest neighbour round
  trip") is a single checked inequality per (pin, back-pin). It should become a bdc/route gate
  on real per-corner arcs (A-xaudit recommended this). The concrete simulation shows the
  inequality is tight on ring3.
