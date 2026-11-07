# B-lib-gap-latch: bd_latch setup_data, setup_pulse and hold, per pin, exact (probe Blp)

File: `formal/lean/Formal/Cells/LibGapLatch.lean` (core Lean; imports `Latch`,
`LibGapMux`). Check:
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/bchk.sh formal/lean/Formal/Cells/LibGapLatch.lean` prints `[bchk] OK`.
Axioms of every theorem below: a subset of `propext`, `Classical.choice`,
`Quot.sound`. No sorry, native_decide or axiom. The draft JSON rows are in
`/tmp/claude-0/-home-user-asyncfpga3/2410103a-6b9c-55d0-893c-8f5f867f7a22/scratchpad/Blp/draft_entries.py` (output `draft_entries.json`). They replace the
nine rows `bd_latch[odd|pair.O5|pair.O6].{setup_data,setup_pulse,hold}`.
`cell_constraints.validate.py` reports no error on the merged copy apart from
"untracked file".

## Verdict

**Works.** For all three bits, the bits' three rows are **exact (iff)** over the
per-pin delay box. The three bits are the odd LUT6 (INIT B8B8..), pair O5 and
pair O6 (INIT FF33_CC00_B8B8_B8B8), all on their real INITs. Each pin (d, en,
own feedback q) is read through its own window, and the read maps do not have
to be monotone. Before this probe, setup_pulse was sufficient only and was not
checked by any rule. setup_data and hold were sufficient, plus tight at the
boundary.

## Model (named hypotheses)

- **H_PIN_READ** (`LutEq`). For t >= 0, the output is
  `latM (d(pd.σ t)) (en(pe.σ t)) (q(pq.σ t))`, with `pq.lo >= 1`.
  - Each read map lies in `[t - hi, t - lo]`. The window covers the wire, the
    site pin and that pin's arc to THIS output.
  - `latM` is the Kleene mux. `Latch.odd_kleene/pair_o5_kleene/pair_o6_kleene`
    prove it equal to the real INITs for all 3^5 inputs. So the neighbour pins
    of a pair never matter, X included. `o5_box_exact` and `o6_box_exact`
    quantify over the neighbour traces and their read maps.
  - Before 0 the output is arbitrary (power-up: the latch has no reset).
- **H_EN_TOKEN**. The enable at its driver is definite 1 on `[A, B)` and
  definite 0 from `C` on. It is **arbitrary** (X included) before `A` and on the
  closing window `[B, C)`.
- **H_D_STABLE**. `d` is definite `v` on `[Td, Tn)` and arbitrary elsewhere.
- **H_T0**: `0 <= A + Elo`.
- **Spec `Capt`**. `q t = v`, definite, at every t at which the enable pin reads
  `>= B`. That is: from the instant the enable starts to close, for ever (one
  token). This is CElemStrict's one-clean-edge `Spec` for the latch.

## Results

The headline is `box_exact` and its three per-bit instances, `odd_box_exact`,
`o5_box_exact` and `o6_box_exact`. Over `pd in [Dlo,Dhi]`, `pe in [Elo,Ehi]`
and `pq in [Qlo,Qhi]`, Capt holds for every trace if and only if all three of
these hold:

    setup_pulse  A  + Ehi + Qhi <= B  + Elo
    setup_data   Td + Dhi + Qhi <= B  + Elo
    hold         C  + Ehi       <= Tn + Dlo

Which pin windows enter each condition, and which drop out:
- The feedback pin appears at its **max** in setup_pulse and setup_data. It
  drops out of hold.
- The data pin drops out of setup_pulse.
- The enable's rise is read slow and its fall fast. So its spread `Ehi - Elo`
  is part of setup_pulse.
- Under **H_RF_SYM**, where every arc has one delay for both edges
  (`sym_exact`, `cells_sym_exact`), setup_pulse becomes `A + Qhi <= B` and the
  enable term cancels.

**Binary-edge form and strictness** (`box_exact_edges`, `strict_edges`,
`atomic_edges`). Write `A = Ton`, `B = Toff - we`, `C = Toff` and
`Tn = Tnew - wd`. Here `we` and `wd` are the X windows that come before the
binary edge, which is CElemStrict's convention:

    Ton + Ehi + Qhi + we <= Toff + Elo
    Td  + Dhi + Qhi + we <= Toff + Elo
    Toff + Ehi + wd      <= Tnew + Dlo

- Under H_MUX_KLEENE, which gives one tick of X (`we = wd = 1`), **all three are
  strict**.
- With instantaneous selects, all three are `<=`.
- setup_data at fixed delays is `CElemStrict.latch_facts`' race,
  `tb + D + wb <= s`, with `c = Td + dd`, `D = dq` and `s = Toff - we + de`.
  The two results agree.
- **Hold's `strict_pending` is resolved: it is strict.** The cause is the next
  datum's X window. `ct_hold_x` shows the X at 1 ps past the boundary.

**Necessity.** These lemmas build real traces satisfying H_PIN_READ for all
t >= 0: `need_pulse_two` (box: rise read at Ehi, fall at Elo), `need_pulse_sym`,
`need_data` and `need_hold`.

**1 ps counter-traces.** Each holds for EVERY trace that obeys the
hypotheses. The box used is data [300,700], enable [400,800], feedback [300,900],
v = 1, power-up 0.
- With an X window: `ct_pulse_x`, `ct_data_x` and `ct_hold_x` each capture X.
- With an instantaneous select: `ct_pulse_wrong` keeps the power-up value 0,
  `ct_data_wrong` captures the old datum 0, and `ct_hold_wrong` captures the
  new datum 0 and feeds it back.
- `ct_numbers` shows that each setup violates exactly one row by 1 ps.

**Non-vacuity.** `witness_hyps` and `witness_run` give a run at the boundary
(B = 3300, with equality in setup_pulse and hold). It satisfies every
hypothesis, writes 0 -> 1, and Capt holds on a non-empty set.

## What rules I and H miss, in terms of the exact form

- **Rule I (setup_data).** All of rule I's missing terms appear, at max:
  - the feedback-pin arc `u.I2/I4 -> O`;
  - `SP[fb]`;
  - `SP[d]`;
  - the `+1` (strict).
  For O5, the feedback wire also includes the LUT->AMUX output hop, which is
  not in the prjxray SDF.
  `SP[en]` and the en arc appear at min on the right, so leaving them out is
  conservative. The enable's hi does not appear.
- **Rule H (hold).** The exact form contains `SP[u.I1].hi` and the data pin's
  `SP.lo`, which are rule H's missing site-pin term. It also contains the D-pin
  arc at min (rule H omits it, which is conservative) and the `+1`, which rule H
  is missing. The feedback does not appear.
- **setup_pulse.** No rule checks it. Proposed rule P, per latch bit and per
  corner: `Won >= en spread at the bit + fhi + 1`, with site pins taken from
  the FASM pin.

## setup_pulse in prjxray terms (one consistent corner c)

    Won >= (w_en.c_max - w_en.c_min) + (SP[en].c_max - SP[en].c_min)
           + (arc_en->O.c_max - arc_en->O.c_min)
           + w_fb.c_max + SP[fb].c_max + arc_fb->O.c_max + 1

`Won` is the enable's high width at its driver, between binary edges. Under
H_RF_SYM the first three terms drop.

Instance for the odd bit (O6 arc SLOW 100::124, FAST 45::56), with en on A2
(SP SLOW 409::507, FAST 170::212) and fb on A1 (SP SLOW 516, FAST 214):

| corner | box form | H_RF_SYM form |
|---|---|---|
| SLOW | Won >= 763 ps + en wire spread + w_fb | Won >= 641 ps + w_fb |
| FAST | Won >= 324 ps + en wire spread + w_fb | Won >= 271 ps + w_fb |

Wire terms are route data and were not measured here. For the pair O5, use the
O5 arcs (I0/I1 122::152, I2 121::150 at SLOW) and add the O5 output hop.

## NOT covered

- Multi-token packaging (apply per token).
- Where Ton, Toff, Td and Tnew come from (LinkTimed, ForkData).
- The physical X width: 1 ps is the grid minimum, not a measured slew.
- A mid-rail select beyond H_KLEENE_LUT (grade B).
- Box necessity treats the pins as independent. Use the per-realisation
  `sym_exact` under a corner model.
- No route was evaluated.
