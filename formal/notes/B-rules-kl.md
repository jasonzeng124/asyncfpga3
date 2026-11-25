# B-rules-kl (probe Bk): tighten.py rules K and L against a derivation

File: `formal/lean/Formal/Cells/RulesKL.lean` (core Lean, imports only
`Formal.Cells.Bundling`, 468 lines, checks in about 2 s). It contains no sorry
and no native_decide, and it declares no axioms. `#print axioms` on
`setup_of_KL`, `dc_capture`, `counter_K`, `counter_L`, `coded_K_covered`,
`coded_L_covered` and `ub_eq` gives a subset of {propext, Classical.choice,
Quot.sound}.

Check command:

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/RulesKL.lean

Status: checks clean, with no warnings. No olean was written into `.lake`.
The axiom check used a scratch copy.

## What the rules guard (tighten.py, line numbers as of this probe)

Rule L is at l.1969-2022 and rule K at l.2024-2118. Helpers:
- `latch_enables`, l.1054-1076
- `latch_data_pins`, l.1079-1089
- `loop_wire`, l.1092-1100
- `req_guard`, l.1103-1106

Both rules guard the same latch: `<link>.lat` of a `bd_link_dc`, which is the
ordinary `bd_latch` (odd LUT6 `B8B8..`, pair LUT6_2 `FF33_CC00_B8B8_B8B8`).
Its enable is `lt`, the output of `bd_link_dctl.ult` (`0101..`,
`lt = ~b & ~a & ~ack_out`). There is no mlink involved.

The latch is transparent between tokens and closes when `b` rises. `ub`
(`0000F320..`) sets on `req_in & ld & ~ack_out`. So the close needs both the
request and `ld`, and each rule times one of the two causes:

- **K** (l.2084-2103) covers the close caused by the request. Its quantities:
  - `t_close = early(req_src -> b) + (b -> ult -> en pin) + min en-pin arc`
  - `t_data = data wire + max D-pin arc + loop_wire(inst)`
  - The data is taken as launched together with the request from the sender's outputs.
- **L** (l.1994-2015) covers the close caused by `ld`, when the request was already up. Its quantities:
  - `t_close = early(lt -> ld) + early(ld -> b) + min_p(b -> ult -> p + min arc p)`
  - `t_follow = max_p(late(lt -> p) + max arc p + loop_wire)`

The derived condition is Bundling's H_SETUP,
`max(Ton + ehi, Td + dhi) + fhi <= Toff + elo`, where `fhi` = loop wire
**plus the feedback-pin arc** (I2 for O5/odd, I4 for O6). In those terms, K is
the data part `Td + dhi + fhi <= Toff + elo` and L is the pulse part
`Ton + ehi + fhi <= Toff + elo`.

**Finding: the catalogue's reading of the code is correct.** Both `t_data`
(K, l.2096-2099) and `t_follow` (L, l.2009-2011) add `loop_wire` and not the
feedback pin's arc. This is the same omission as rule I (l.1875-1878). Neither
rule adds the site-pin (SP) terms either, as noted in B-obligations L1.

## Theorems (all proved)

- **`ub_eq`, `ua_eq`, `uld_eq`, `ult_eq`.** The four real `bd_link_dctl` INITs equal the header's set/reset equations, with rst = 0, s = 1 (LDN = 0), and I5 (plus ult's I3..I5) tied to 0. Proved by `decide`.
- **`RuleK n g` and `RuleL n g`.** Each rule's inequality, written exactly as the code computes it.
  - `RuleK` is per (enable pin, data pin, driver) triple. The code takes the worst margin, so passing rule K means every triple passes.
  - `RuleL` is the pairwise form of `max_p follow + g <= tLd + tB + min_p' close`.
  - "Passes" means `data + guard <= close`, which is the code's `margin >= 0`.
  - `RuleK'` and `RuleL'` are the corrected rules, with the feedback-pin arc added to the data/follow side.
- **`coded_K_covered` and `coded_L_covered`.** If the guard is at least the feedback arc, the coded rule implies the corrected one, with the guard reduced by that arc.
- **`setup_of_KL`.** `RuleK'` plus `RuleL'` (any guard) imply H_SETUP for the bit, under these named hypotheses:
  - **H_LAUNCH `Td <= T0`.** Data is settled at the sender's driver by the time the request leaves its source. This is K's "launched together", which is conservative by the sender's rule A.
  - **H_LT_FALL_K `T0 + tReq + dCtl <= Toff`.** `lt` cannot fall before the request has set `b` and `b` has crossed `ult`. Reason: ub's set needs req_in, and `a`/`ack_out` rise only after `b`.
  - **H_LT_FALL_L `Ton + tLd + tB + dCtl <= Toff`.** ub's set needs `ld`, and uld's set needs `lt`.
  - **H_ELO, H_EHI, H_DHI, H_FHI.** The latch pin windows are bounded by the SDF wire and arc numbers the code reads: en wire + I1 arc min/max, D wire + D arc max, loop wire + feedback arc max.
  - Each hypothesis is testable as SDF-min/max path delays at the routed GLS slow and fast corners.
- **`dc_capture`.** The same hypotheses plus rule H's H_HOLD give, through `Bundling.capture`, `q = v` from settling until the enable can next reach the bit.
- **`counter_K`.** A transport trace of a whole `bd_link_dc` stage that passes both coded rules and corrupts the token.
  - Stage: W = 1 (odd bit), BROAD = 1, LDN = 0, DELAY = DACK = 0. ub, ua, uld and ult use their real INITs and the latch is the odd LUT6. Every LUT is a fixed transport delay.
  - Delays: req -> b is 1, every other controller pin is 1, D is wire 0 + arc 1, en is wire 0 + arc 1, and the loop is wire 2 + **I2 arc 1**.
  - Environment: four-phase legal. ack_out = 0, and req and data both rise at 8.
  - Rule K: close 3, data 3, margin 0. Rule L: follow 3, close 4, margin 1. Both pass at zero guard.
  - Corrected K fails, and H_SETUP fails (`8+1+3 > 10+1`).
  - Result: D = 1 from 8 and lt = 0 from 10, but `q (11 + 3k) = 0` for every k. The loop circulates 1,1,0 for ever.
  - The latch part reuses Bundling's `caQ` (enable = `caEn`, data = `caD`).
- **`counter_L`.** The same stage reopening for a new token while the request is already up.
  - Environment: four-phase legal. A token is held initially. `ack_out` is high on [2,4). req_in is withdrawn at 2, the data changes to 1 at 3, and req_in rises again at 5.
  - Delays: req -> b is 2, and the loop is wire 3 + **I2 arc 1**.
  - Sequence: lt rises at 5, ld at 6, b at 7, and lt falls at 8.
  - Rule L: follow 4, close 4, margin 0. Rule K: close 4, data 4, margin 0. Both pass at zero guard.
  - Corrected L fails, and the pulse part of H_SETUP fails (`5+1+4 > 8+1`).
  - Result: D = 1 from 3 and lt = 0 from 8, but `q (9 + 4k) = 0` for every k. The pattern is 1,1,1,0 for ever.

Both traces were also cross-checked by a 60-tick Python simulation of the
INITs before the proof (scratchpad only).

## Verdict per rule

| derived (per bit) | rule as coded | verdict |
|---|---|---|
| data part: `Td + dWire + dArc + loopWire + fbArc <= Toff + dFan + enArcMin`, with Toff >= T0 + tReq + dCtl | **K**: `dWire + dArcMax + loopWire + guard <= tReq + dCtl + dFan + enArcMin` | **K is weaker** by one feedback-pin arc. `counter_K` passes K (and L) at zero guard and corrupts. |
| pulse part: `Ton + lateWire + enArcMax + loopWire + fbArc <= Toff + dFan + enArcMin`, with Toff >= Ton + tLd + tB + dCtl | **L**: `max_p(lateWire + enArcMax + loopWire) + guard <= tLd + tB + min_p(dCtl + dFan + enArcMin)` | **L is weaker** by one feedback-pin arc. `counter_L` passes L (and K) at zero guard and corrupts. |
| K' and L' together | — | Sufficient (`setup_of_KL`, `dc_capture`). |

Numerically, with nextpnr's flat 124 ps arcs, the 200 ps floor of
`req_guard` covers the missing arc (`coded_*_covered`). It does so by using
up 124 of the guardband's 200 ps, which is meant for route scatter. It does
not cover arc plus site pin; see B-obligations L1 for the SP term of up to
about 0.49 ns.

**Suggested fix, same as for rule I.** Add `max IOPATH(fb pin -> O)` to
`t_data` (l.2096-2099) and `t_follow` (l.2009-2011). For a pair LUT the
feedback pin is I2 for bit i and I4 for bit i+1, so take the max of the two,
as `loop_wire` already does for the wire.

Practical weight: low. The rtl header (bd_link.v l.157-166) already calls
`bd_link_dc` a failed experiment that is "not a production option". Rule K
already fails on most xorshift_round dc routes, by 100-900 ps.

## What did not work / not done

- **Causal hypotheses are not derived.** H_LT_FALL_K and H_LT_FALL_L are
  stated, not derived from the controller's Gate relations. Deriving them
  would need a Gate-level argument that `b` cannot rise while its req or ld
  window still reads 0, and that `lt` cannot fall without `b`/`a`/`ack_out`.
  This is straightforward with `ub_eq`/`ult_eq` lifted to Kleene, but it is
  not done.
- **No hold side.** The hold side of the dc latch (rule H on the dc ack) is
  not re-examined here. H_HOLD stays a hypothesis.
- **Single pin per trace.** The traces use one enable pin and one odd bit.
  The pair LUT (I4 feedback for O6) is covered by `Bundling.pair_o6_latch`
  in the soundness direction, but no pair counter-trace is written.
- **Guard modelled as a free parameter.** `int(0.2 t)` is not modelled.

## Verdict

**Works.** Both rules have been checked against a gate-level derivation:

- **Sound direction.** The corrected rules K' and L' are proved sufficient.
- **Rules as coded.** Rules K and L as written are shown insufficient by
  complete, four-phase-legal transport traces of a whole `bd_link_dc` stage
  with real INITs.
- **Size of the gap.** It is exactly one feedback-pin arc, the same as rule I.

Effort to finish: about half a day. That would derive H_LT_FALL_K/L from the
controller gates and add a pair (O6/I4) trace.

What it buys: it confirms the catalogue's code reading (P7 / L1) with
theorems, and it gives the one-line fix for both rules. Because dc is not a
production option, the main value is completeness of the rule audit.

## Fidelity per primitive

- **LUT.** The real INIT under transport delay (`Transport`), turned into
  Bundling's Kleene `Gate`/`LatchRel` window relation via `transport_gate`
  and `odd_latch`. The soundness theorems hold for every trace satisfying
  `LatchRel` (H_KLEENE_LUT). The counter-traces are concrete transport
  traces, which is the sound instance.
- **Routing wire.** Folded into the per-pin delay or window, as wire + arc.
- **Feedback loop.** A routed wire plus the feedback pin's own arc, with
  H_LOOP_POS.
- **Controller (ub/ua/uld/ult).** Real INITs with transport delay in the
  counter-traces. In the soundness theorem it appears only through H_LT_FALL_K/L.
- **Discrete time.** One tick is an arbitrary quantum.
