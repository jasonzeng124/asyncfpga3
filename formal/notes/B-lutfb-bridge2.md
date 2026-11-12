# B-lutfb-bridge2 (probe Bfb2): the rest of C's LUT premises, the environment from the neighbours, and the link class on `CapstoneNet`

Lean (core only, no Mathlib in the closure):

- `formal/lean/Formal/Cells/LutFbBridge2.lean`, which imports `LutFbBridge`;
- `formal/lean/Formal/Cells/LutFbBridge2Env.lean`, which imports `LutFbBridge2` and C's
  `Formal.Net.CapstoneSafe`.

Both check OK with `/tmp/claude-0/btools/bcheck.py` (autoImplicit=false), with no warnings
and no sorry, axiom or native_decide. `#print axioms` (collected in a companion file, since
removed) on all 31 headline theorems gives `[propext, Classical.choice, Quot.sound]`, or
less for the kernel-`decide` counts.

## The question

Bfb (`B-lutfb-bridge.md`) derived C's `LutFb`/`FbFirst` for `bd_c2n` and every 2-input
`bd_c2`. It assumed B's physical model (a `Win` LUT, H_NO_REVERT and a `WinDelay` feedback
wire) plus a four-phase environment (`Env1`/`EnvC`). It left three things open:

- (a) `bd_mux` `uj0`/`uj1`, `bd_c3`, C-trees, and the `LutSI` premises of steer and src;
- (b) the environment hypotheses, which were not derived from the neighbouring cells;
- (c) the bridge was not used on C's `CapstoneNet`.

## Answers

### (a) Every remaining LUT premise of C's bindings except the C-trees is derived

| theorem | cell (generated LUT, real `rst` pin) | C premise delivered | extra hypotheses |
|---|---|---|---|
| `celG_lutFb` | any C-element LUT `G` on any pin set (`CelLaw G`: reset gives 0; all pins `v` gives `v`; feedback `v` and some pin `v` holds `v`) | `LutFb`, `FbFirst` | `CelG` (= Bfb's channels), `EnvG` (n-pin `EnvC`: last-arrival `c j`), H_RST_LONG, H_LAT, H_PWR |
| `join3_lutFb`, `join3_cel_phys` | `bd_join` N=3 `u.genblk1.genblk1.g3.u.u` (`bd_c3`, 5-pin) | `join3_cel`'s premises; `Join.cel` | as `celG_lutFb`; `CelLaw` proved by `decide +kernel` |
| `muxJ0_lutFb`, `muxJ1_lutFb` | `bd_mux` `uj0`/`uj1` (5 pins incl. `s`, `rst`) | `mux_bound`'s `h0,f0` / `h1,f1` | `EnvG` on the effective pins `(x_req, ctl_req ∧ ¬s)` |
| `steer_lutSI`, `steer_ack_lutSI` | `bd_steer` `u` O5/O6, `uack` | `steer_bound`'s `hL`, `hA` | the excitation's phases (`Phases`) and spacing, named |
| `src_lutSI` | `bd_src` `u` (LUT1 `¬ack`) | `src_bound`'s premise | ack phases; **H_PWR_SRC** (see below) |
| `gated_phases` | — | the gated request `r ∧ (s == b)` has phases | `r`'s phases, **H_SEL_STABLE** (select constant while `r` is high), an enumeration of the tokens steered to `b` |

- **New findings.**
  - The generic n-pin proof needs only three laws of the LUT function, so `bd_c3` and the
    mux joins need no new timing argument. Each instance proves the laws on the real
    generated INIT.
  - The source cannot satisfy Bfb's H_PWR (output 0 until `hi`): its excitation `¬ack` is 1
    from power-up. `src_lutSI` replaces H_PWR with H_PWR_SRC: inside the power-up window
    `t < hi`, where `Win` says nothing, the output may only rise. The proof reads the
    complemented node, forced to 0 on that window.
- **Witnesses with nonzero delays.**
  - `join3_witness`: the real `bd_c3` loop, LUT band `[1,2]`, wire 1. The pins disagree on
    `[4,5)` and `[8,9)`.
  - `muxJ0_witness`: the real `uj0` loop.
  - `steer_witness`.
  - `src_witness`: the source rises at 1, inside the window, so H_PWR_SRC is actually used.
- **Counter-run `sel_glitch_breaks_uj0`.** It uses the real `uj0` LUT, a fixed transport
  LUT delay 2 and wire 1 (every channel hypothesis, H_LUT_POS, H_PWR), with
  `x_req = ctl_req = 1` and a select that glitches for one tick. C's `LutFb muxJ0F` fails.
  So for `uj0` the request protocols are not enough: H_SEL_STABLE (or C's H_SEL_PIN) is
  needed.

### (b) The environment of a cell follows from its neighbours, one channel at a time (assume-guarantee)

- **Wire model.** H_WIRE (`Wire`): `Win wl wh` + H_NO_REVERT, `1 ≤ wl`, power-up 0.
  - `wire_steps`: a clean step signal stays clean through such a wire, with edges in
    `[τ+wl, τ+wh]`.
  - `wire_di`: C's DI wire relation (`H_REQ_DI`/`H_ACK_DI` form) holds.
- **A neighbour's guarantee.** This is a property of the neighbour's own trace: its node is a
  clean step signal, and edge `j` comes at least `lo` after the pin it waits for. Two lemmas
  prove it from B's cell models plus the cell's own environment:
  - `link_guar`, for a link controller, from `Stage`/`Env1`/`Timing1`;
  - `celG_guar`, for a C-element.
- **Link-to-link channel (`link_link_env`).** Given both controllers' guarantees and both
  wires, plus two timing conditions:
  - H_WIRE_R: wires shorter than reset;
  - H_RT: each wire's maximum is below the round trip `wl_ab + lo_B + wl_ba + lo_A`.

  The lemma proves:
  - B's request-side `Env1` fields, with `Es = wl_ba + lo_A + wl_ab`;
  - A's acknowledge-side fields, with `Ea = wl_ab + lo_B + wl_ba`;
  - both DI wires.

  `env1_of_neighbours` assembles B's **whole** `Env1` when both its neighbours are links.
- **2-way fork (`fork_env`).** It covers an upstream node `U`, the fork C-element (edges
  defined from its node, as in `EnvC`), two consumer links and five wires. It proves:
  - Bfb's **whole `EnvC`** of the fork C-element, with `Es`/`Ea` the two branch cycles minus
    the C-element's own delay;
  - the consumers' request-side `Env1` fields;
  - U's acknowledge-side bounds;
  - all five DI wires.

  The only timing condition is H_CYC: each wire's maximum is below the shorter branch
  cycle's minimum.
- **Witnesses.**
  - `link_link_witness`: B's two-stage pipe run `Wx.gates_w` (the real `bd_c2n`
    controllers, all delays 1). The derived `Es = Ea = 3` are met **with equality**.
  - `fork_witness`: phases of 7 ticks, request wires of delay 1 and 2. Branch 1 is one tick
    slower, so the C-element's pins disagree for a tick each phase. The upstream guarantee
    is met with equality, and the theorem's `EnvC` holds.

### (c) `CapstoneNet`: the link class end to end, modulo `Env1`

- **`gcd_hw_safe_phys_links`.** This is C's `gcd_hw_circuit_safe` with `H_CELLS` for all 175
  link operators replaced by B's physical link model `PhysLink`. `PhysLink` consists of:
  - `Stage` + `Env1` + `Timing1` + H_LUT_POS + H_PWR;
  - two `Wire`s, to the neighbours' `i.ack` and `o.req`, shorter than reset and than the
    controller's minimum cycle (H_WIRE_SPREAD);
  - the latch data fields.
- **What `link_of_phys` derives.** It derives C's `Link` fields `H_CEL_SI`, `H_ACK_DI`,
  `H_REQ_DI`, `ic`, `ii` and `io`. Only the two `H_LATCH_*` data fields pass through.
- **Kernel-checked counts.** These are by `decide +kernel` over C's `opAt`/`prodOf`/`consOf`:
  - 175 links (`link_count`);
  - 75 link-to-link channels (`ll_count`, with `ll_ends`);
  - only 12 links whose input and output channels are both link-to-link
    (`interior_count`);
  - no 2-way fork fed by a link (`fork_from_link_count`).

## What blocks the rest (precisely)

- **The loop is not closed.** `link_guar` gives a cell's guarantee from its own `Env1`, and
  `link_link_env`/`env1_of_neighbours` give `Env1` from the neighbours' guarantees. A
  network-wide `Env1` needs the causal induction on edge index, interleaved across cells.
  That induction is done in Lean only for the two-stage pipe (`WinFifoCausal.pipe_fifo`).
  So **no gcd_hw link's `PhysLink`/`Env1` is derived.** `gcd_hw_safe_phys_links` still
  assumes `Env1` per link.
- **Coverage of link neighbours.** The 75 link-to-link channels cover 150 of the 350 link
  channel ends. The other 200 meet forks (N = 2..4; N ≥ 3 is the C-tree), joins
  (N = 1, 2), steers, muxes, muxn and arbiters. No guarantee lemma is packaged for these
  classes: `link_guar` covers links and `celG_guar` covers C-element nodes only. Also,
  `fork_env`'s upstream `U` is never a link on gcd_hw (`fork_from_link_count`).
- **C-trees** (fork/join N ≥ 4, two LUT levels): the inner node's environment is a
  `fork_env`-style composition, not done.
- **Infinite runs only.** `EnvG`, `Phases`, `Env1` and `EnvC` all describe an infinitely
  alternating run. A mux or steer branch that stops being selected is not covered.
- **Channel model.** C has one trace per channel, so the physical pin trace is identified
  with C's channel trace and the routed delay lives in C's DI step. The data path is C's
  (zero-delay H_DATA_COMB).
- **Not proved weakest.** H_WIRE_R, H_RT, H_CYC and H_WIRE_SPREAD are sufficient. Only the
  link-link witness shows the derived `Es`/`Ea` are attained.
