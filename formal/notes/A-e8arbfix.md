# A-e8arbfix (probe E8ArbFix, shard A): corrected virtual arbiter core

STATUS (2026-10-29, started): in progress. Nothing claimed yet.

Plan
1. Corrected virtual core (E8Arb §4): ctl lower band lo_c - 2 (D2); R0 = merge of two shadow
   grants (ustate O5 stage band, ustate's request arcs, same ctl·σ pins; taps (1,1)) (D1).
   In events4/model.py + cert6/cert8 generators, old behaviour behind a flag.
2. Lean: Events9Arb.lean with HARB7' and a verdict reusing Events9's (HDsub stays discharged).
3. Sufficiency theorem (ArbOK + Unc W + RT1/RT1b => exists cv, HARB7'), or the exact gap.
4. Re-run xevents9 on E8Mux corrected bands, 4 seeds x slow/fast/gb/indep; wchk.py on new bands;
   negative control: old core shown wrong on a recorded run.
