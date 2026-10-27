# B-on-netlist-timed (probe Bt): shard B's timed cell theorems on the routed bits

Shard B x shard C. 2026-10-27. File: `formal/lean/Formal/Cells/OnNetlistTimed.lean` (core Lean, no Mathlib).

## Verdict

**Works** for the C-element family (CElemTiming) and for the Latch family (`holds_value`). It is
done for the link C node and for latch bit q0 of the four routed `link_arb` bitstreams. These are
C-11c's `Formal.Net.FasmLink.S1..S4`, with nextpnr sha256 9c732bc6303458df and `toolchain.sh` ok,
as stamped by `fasm2lean2/check.sh`. Nothing was re-routed here, so this probe adds no new routed
numbers. Every delay comes from C's committed, generated `pinDelay`, or from prjxray-db's CLB SDF.

The chain on each seed:
- C's per-pin physical gate relations `Behaves` hold on the bits (named hypotheses H_LUT,
  H_ROUTE, H_TIE).
- From them, B's `CElemTiming.Loop INIT_c2` holds for the physical C node, with:
  - `a` = the req pin;
  - `b` = the negated ack_out pin;
  - LUT window = the O6 arc;
  - feedback window = the routed feedback pin's own `pinDelay`.
- Then B's `c2_follow_hold` and `c2_four_phase` apply, with concrete ps numbers.
- For the latch, `Behaves` gives B's `Latch.LatchBit (dlmax + dwmax)` for the O5 bit of the
  physical pair LUT6_2, and B's `Latch.holds_value` applies.

## Check command

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OnNetlistTimed.lean

Result:
- **Clean**, with no output, in about 3 s.
- Imports use only existing oleans: `Formal.Cells.{Prelim,CElemTiming,Latch}`,
  `Formal.Net.Fasm.Basic` and `Formal.Net.FasmLink.S1..S4`. `OnNetlist` is not imported, because
  it has no olean and is not needed.
- `formal/scan.py` is clean.
- `#print axioms` was run on a scratch copy:
  - `c_follow_hold_s*`, `cloop_s*` and `c_follow_hold_ports_s*` give `[propext, Quot.sound]`;
  - `c_four_phase_s*` and `latch_q0_s*` give `[propext, Classical.choice, Quot.sound]`;
  - the decided facts and the negative controls give `[propext]`.
- There is no `sorry`, `admit`, `axiom` or `native_decide`. Only plain `decide` is used.

## Concrete per-seed bounds used (ps)

These are the LUT windows (hypothesis `H_DL`):
- **O6 [45, 124].** This is the envelope of the min-of-fast and max-of-slow corners over all 144
  `IOPATH A* O6` entries in prjxray-db `timings/CLB{LL,LM}_{L,R}.sdf`; every entry is
  (0.045::0.056)(0.100::0.124). It is the same figure as C-11b. The C node is a LUT6 with O6
  only.
- **O5 [42, 157].** This is the same envelope over all 120 `A* O5` entries. In `Behaves` one `dl`
  covers the whole site, so the fractured latch-pair LUT6_2 takes the O5 envelope, which contains
  the O6 one.

The feedback windows (hypothesis `H_DW`) are tied to C's `pinDelay` by `rfl`
(`cfb_s*`, `lfb_s*`). The C node is physical LUT 0 / O6 on every seed (C's `rho[0]`, checked in
`cnode_rho`). The latch q0 bit is O5 of the pair LUT (`rho[1][0]`).

| seed | C fb pin | C fb dw | nextpnr SDF | Dmin = 45+lo | **Dmax = 124+hi** | **E ≥ Dmax−45** | latch fb pin | latch dw | nextpnr SDF | **latch L = 157+hi** |
|---|---|---|---|---|---|---|---|---|---|---|
| 1 | A4 | [125, 445] | 295 | 170 | 569 | 524 | A2 | [261, 872] | 508 | 1029 |
| 2 | A1 | [211, 714] | 295 | 256 | 838 | 793 | A2 | [261, 872] | 508 | 1029 |
| 3 | A4 | [206, 836] | 649 | 251 | 960 | 915 | A5 | [123, 444] | 444 | 601 |
| 4 | A4 | [124, 466] | 295 | 169 | 590 | 545 | A5 | [123, 447] | 444 | 604 |
| **mean** | | | | 211.5 | **739.25** | **694.25** | | | | **815.75** |
| **range** | | | | 169–256 | **569–960** | **524–915** | | | | **601–1029** |

### What these numbers mean

**Dmax** is B's minimum pulse width, from `c2_follow_hold`. When `req = v`, `ack_out = !v` and
`rst = 0` are held at the physical LUT pins for Dmax ps, the C node output is `v` from 124 ps on.
It then holds while the inputs are not both at the opposite value. `runt_oscillates` in B shows
this bound is exact under fixed transport delays. That result was not re-instantiated on the bits.

**E** is B's `H_ENV_LATENCY` for `c2_four_phase`, after the four-phase discipline hypotheses.
It is the environment's minimum ack-to-input latency, measured at the pins. Under it, the C node
output equals `V k` on `[c k + 124, c(k+1) − 1 + 45]` for every phase `k`.

**latch L** is `holds_value`'s loop bound. On `[s, T]`, suppose two things:
- the enable pin goes low only after `s + L`, so the latch has been open for a full loop delay;
- the data pin is `v` whenever the enable pin is high.

Then the physical O5 output is `v` on `[s + 157, T + 42]`.

**Port-level forms** come from `c_follow_hold_ports_s*`, which run through the routed input pins
using C's `pinDelay` for every pin of the C node. The ports must hold for 1646 / 2083 / 2137 / 1745
ps (mean 1902.75, range 1646–2137). The excess over Dmax is the skew between the IOB-to-LUT
input routes of this test harness. In a real link, `req`/`ack` come from neighbouring LUTs, not
IOBs, so the pin-level figures are the cell's.

**For comparison:** the routed `ce_pair` seed 1 in C-11b has Dmax = 833.

**With the CLAUDE.md guardband** (informational, not in Lean): `GUARD_HI` = 1.155 is applied to
the maxima and `GUARD_LO` = 0.772 to the LUT minimum. The theorems are generic in the bounds, so
these numbers just go into the same statements.

| | seed 1 | seed 2 | seed 3 | seed 4 | mean |
|---|---|---|---|---|---|
| Dmax | 658 | 968 | 1109 | 682 | 854.25 |
| E | 623 | 934 | 1075 | 647 | 819.75 |
| latch L | 1189 | 1189 | 695 | 698 | 942.75 |

The guardband is arguably double counting here, since the windows are already corner envelopes.
It is shown because the H_DW upper ends are unvalidated (see below).

## Theorems (namespace `Formal.Cells.OnNetlistTimed`)

### Generic

| name | statement |
|---|---|
| `c2n_as_c2` | `exc INIT_c2n a b q r = exc INIT_c2 a (!b) q r` (the real INITs, decided) |
| `cnode_loop` | **bridge, C family.** It holds for any `PNet` and LUT `i` that satisfy two conditions: the LUT's physical function on its physical pins is `bd_c2n(pin ia, pin ib, pin iq, pin ir)` (`hfn`), and pin `iq` is routed from the LUT's own O6. Then `Behaves` gives `Loop INIT_c2 (pin ia) (¬pin ib) (pin ir) (out i O6) (pin iq) (dl i) (dw i iq)`, given B's `H_LOOP_POS` |
| `c2n_follow_hold`, `c2n_four_phase` | B's `c2_follow_hold` and `c2_four_phase`, restated for `C(a, ~b)` (targets `a = V k`, `b = !V k`) |
| `winDelay_held`, `c2n_follow_hold_ports` | Port-level form. Routed inputs with windows `[lo_k, hi_k]` hold the inputs on `[P, P+W]`, with `W + m + 1 ≥ M + Dmax` (`M` ≥ every `hi_k`, `m` ≤ every `lo_k`). Then `O = v` on `[P+M+dhi, P+W+m+dlo]` |
| `loop_k` | A LUT window followed by a wire window gives, at each `t`, a loop delay `k t ∈ [1, dhi+whi]` with `p t = exc (t − k t)` once `k t ≤ t` (via B's `winDelay_comp`) |
| `latch_holds_bits` | **bridge, Latch family, plus `holds_value`.** Take any Bool output `out` that is a window copy of `bmux en d p`, with `p` a window copy of `out`. A `Latch.LatchBit (dhi+whi)` is built from these traces: its `k t` is chosen with `Classical.choose`; `d1, p1` are the other bit's real pins; `q` is the zero-delay `o5K PAIR`; and `hloop` follows from `pair_o5_kleene`. Under `H_EN_OPEN` and `H_DATA`, B's `Latch.holds_value` gives the excitation `= v` on `[s, T]`, and so `out = v` on `[s+dhi, T+dlo]` |

### Per seed (s1..s4)

| name | statement |
|---|---|
| `ports_same`, `cnode_rho`, `cnode_pins`, `latch_rho`, `latch_pins` | The wiring facts used, read from C's generated data: port 7 = `req_in`, port 1 = `ack_out`, port 8 = `rst` on every seed; the C node is LUT 0/O6; the latch q0 is O5 of LUT 1 (LUT 2 on seed 3); the physical pin sources |
| `c_fn_s*`, `l_fn_s*` | Physical INIT on physical pins (ties substituted) = `exc INIT_c2n` and `bmux` on the right pins (16 and 32 cases, decided) |
| `cfb_s*`, `lfb_s*` | Feedback `pinDelay` values (`rfl`) |
| `cloop_s*` | `Loop INIT_c2 … 45 124 dwlo dwhi` on the bits, given `Behaves`, `H_DL` and `H_DW` |
| `c_follow_hold_s*` | B's (a) on the bits, with the numbers above |
| `c_four_phase_s*` | B's (c) on the bits, with `H_ENV_LATENCY` as `524/793/915/545 ≤ E` |
| `c_follow_hold_ports_s*` | (a) from the ports, with `H_DWALL` (C's `pinDelay` for every pin of the C node) |
| `latch_q0_s*` | `holds_value` for the physical latch bit q0, with `L` = 1029/1029/601/604 |
| `c_fn_unpermuted_fails_s1`, `l_fn_swap_fails_s1` | **Negative controls.** The function checks can fail: the logical pin order on the physical LUT is not the C node, and the latch with d0/d1 swapped is not q0 |

### Hypotheses

All are named:
- C's `Behaves`:
  - **H_LUT:** a per-LUT window on the physical INIT and the physical pins;
  - **H_ROUTE:** a per-pin window from the routed source;
  - **H_TIE:** constant ties.
- **H_DL:** the numbers of the LUT window.
- **H_DW / H_DWALL:** the routed pin windows equal C's `pinDelay`.
- B's own environment hypotheses, unchanged:
  - follow-and-hold: H_PULSE, H_NORST, H_NOT_BOTH;
  - four-phase: H_ALT, H_ORDER, H_BOTH, H_NEXT, H_ACK, H_ENV_LATENCY, H_RESET_DONE;
  - latch: H_EN_OPEN, H_DATA.

  These are stated on the physical pin traces.

B's `H_LOOP_POS` is discharged from the numbers.

## What did not work / limits / not done

1. **H_DW upper ends are not validated, and are tight against nextpnr in one case.** C's
   `pinDelay` is (fast-min intrinsic) to (slow-max intrinsic plus Elmore). It has not been
   cross-checked against `prjxray/timing.py` or the board (C-11b notes).
   - nextpnr's SDF numbers sit inside every window used here (column "nextpnr SDF").
   - But on **seed 3 the latch q0 feedback is exactly at the upper end (444 = 444)**, and on
     seed 4 it is 3 ps below (444 vs 447).

   nextpnr's figure is a single-corner number. A max that equals it is suspicious as a
   slow-corner bound. Per CLAUDE.md ("take the longer number"), the latch L for seeds 3 and 4
   should be treated as provisional until the H_DW maxima are validated. The theorems take any
   bound, so a corrected `pinDelay` only changes the numbers.
2. **The OUTMUX arc is missing.** The latch O5 leaves the slice through `?OUTMUX.O5 → ?MUX`.
   prjxray-db's CLB SDF has no arc for that mux, and C's `pinDelay` starts at the `?MUX` site
   pin. So the latch loop may be short by the OUTMUX delay; the O6-only C node is not affected.
   This should be checked against nextpnr's or Vivado's model of the CLB output mux.
3. **Kleene / X is not exercised.** `Behaves` is Boolean. The latch bridge builds a K3
   `LatchBit` from `ofBool` traces, so `holds_value`'s `en = x` (edge-in-flight) case is never
   used. B's Kleene power, X on the other bit not leaking, is used only through
   `pair_o5_kleene` in `hloop`. A Kleene `Behaves` (K3 pins, X during transitions) would be
   needed to port B's edge semantics. That is about 1 day for C's semantics plus re-doing the
   bridges.
4. **Only latch bit q0 (O5) is covered.** `LatchBit` is stated for O5 of `PAIR`. q1 (O6 of the
   pair, `pair_o6_kleene`) and the odd bit q2 (`odd_kleene`, a separate LUT) need a `LatchBit`
   variant, or the generic `latch_holds_bits` with `bmux` from O6 or ODD. That is mechanical:
   about 1 h each, since `latch_holds_bits` only needs `bmux`; only `hloop`'s
   `pair_o5_kleene` step changes.
5. **Not ported:**
   - `runt_oscillates` on the bits. This needs a whole-net `Behaves` witness: traces for all 7
     LUTs and all pins, with fixed delays.
   - `c2_reset` (straightforward, same pattern as `c2n_follow_hold`).
   - `inertial_runt_lost` (`Behaves` has no inertial channel).
   - `link_latch_holds` / rule H (`hold_of_dack`). This needs the en-fanout and ack windows,
     which are available from `pinDelay` (`en` = LUT 0 O6 routed to the latch pins, `ack_in`
     = the same net to the port), so it is the natural next step at about 0.5 day.
   - LinkTimed / PipeTimed.
6. **One `dl` per site.** `Behaves` gives one LUT window per site, not per (pin, output) arc. The
   per-arc prjxray data is flat for O6 (all 45/124), but varies for O5 (42 to 157). Per-arc
   windows would tighten the latch numbers slightly.
7. **Pin-level environment hypotheses.** B's four-phase hypotheses are stated on LUT pin traces.
   Discharging them from a neighbouring stage's output, through its route, is the per-link work
   of LinkTimed. Only follow-and-hold was lifted to the ports.

## Fidelity per primitive

- **LUT6 (C node).**
  - C's H_LUT: a window channel `[45, 124]` ps of the PHYSICAL INIT on the PHYSICAL pins A1..A6,
    with binary values and a per-tick varying delay, so glitches are admitted.
  - The function equals B's `exc INIT_c2n` on the routed pins (decided).
  - Mux-tree internals, X and inertial filtering are not modelled.
- **LUT6_2 (latch pair).** The same, with O5 = `o5B` (INIT[31:0] over A1..A5, with A6 tied to
  VCC, as read from the bits). The window is `[42, 157]` ps. The OUTMUX arc is missing (limit 2).
- **Feedback.** The routed wire from the LUT output back to its own pin is a window channel with
  that pin's own `pinDelay` bounds (H_ROUTE per sink), as B's `Loop.H_FB`. For the latch, the
  LUT window and the wire window compose into B's lumped `LoopDelay` (`loop_k`). This is
  faithful to the "LUT whose output feeds back to its own input pin" picture.
- **Input routes.** These are per-pin window channels from the ports (IOB I through the ILOGIC
  bypass, C's H_IMPLICIT). The IBUF delay is not included.
- **Ties.** Constant (H_TIE).

## Effort to finish and what it buys

- **Bits q1 and q2, `c2_reset`, and rule H (`link_latch_holds`) with `pinDelay` en-fanout
  windows:** about 1 day.
- **The arbiter family (`ArbHeldTimed*`, `ArbHandover`, `exclusion_transport`):** this needs a
  routed `bd_arbcell` design first (B-on-netlist item 2), then the same bridge pattern. Estimate
  2–3 days.
- **Validating `pinDelay` maxima and adding the OUTMUX arc:** this is C/research work. Until it is
  done, every number above is conditional on `H_DW` and `H_DL`.

**What it buys.** B's C-element timing results (minimum pulse width, four-phase correctness with
its isochronic-fork latency condition) and the latch hold theorem now hold for the cells as the
four real bitstreams wire them. That covers the placer's pin permutation, the re-encoded INITs,
the routed feedback pins and their seed-dependent delays.

The seed-to-seed spread is large:
- C node Dmax 569–960 ps (×1.7);
- latch L 601–1029 ps;
- the environment-latency obligation E 524–915 ps.

So a single route is not representative (CLAUDE.md "one route is a sample"). The obligation a
link controller must meet depends on which feedback pin and route the router picked, and on
nothing visible in the netlist.
