# A-e8arbfix (probe E8ArbFix, shard A): corrected virtual arbiter core

STATUS (2026-10-29 ~09:55, in progress): tools change done (model.py `build_arb_fix`, old core
behind `XA_ARB=old` / `--arb-old`); pipeline runs started; Lean not yet written. Nothing claimed.

## Findings so far (untrusted scripts; to be confirmed by the runs)

1. **E8Arb §4's proposed fix does not fix D1.** Shadow grants reading the SAME ctl through a
   `(1,1)` pin with the ustate O5 stage band make the virtual R0-minus-grant delay of a q-caused
   edge lie in `[loF' + 2 − hiF, hiF' + 2 − loF]` (a few tens of ps), but the real one is
   `Dq(R0) − Dq(g)` (q arc to ustate vs q arc to ugrant), e.g. merge4 d slow `[−622, −348]` ps.
   The q-arc difference has to sit in a PER-READER ctl pin band.
2. **A common stage band cannot factor two per-pin reads.** In A's per-pin model a reader X reads
   its request and q through independent warps, each with band arc + LUT. A virtual node with a
   stage warp `F` (LUT band) and pin warps (arc bands) can match both only if one `F t` lies in
   the intersection of three intervals, which is empty when the request is read fast and q slow
   (LUT band width > 0). So the corrected core gives every virtual node `F = (1,1)` and puts the
   whole read (arc + LUT − 1, minus the merge/tap steps for R0) into the pins.
3. **Neither orientation of the old structure is sound.** `arbfix/orient.py`: per grant, R0-term
   minus grant over the bands, for q-caused and request-caused edges. "R0 downstream of the grant"
   (the old core, any tap band) needs both lower ends ≥ 1: 0 of 11 grants (d slow), 0/11 (d fast),
   0/13 (3 slow, 3 fast). "Grant downstream of R0" needs both upper ends ≤ −1: 2/11 (d), 0/13 (3).
   Every other grant straddles 0: the R0 term and the grant are two parallel readers.
4. **The certificate rules cannot certify the corrected core.** The old certificates used the
   count link `R0 ← g_b` (R0 a merge of the grants): (a) Back of the grant's ctl pin
   (walk ctl ← A0 ← R0 ←SUB g_b), (b) the guard G walk at `A_b = C(g_b, A0)`
   (labelled walk A0 → g_b, no token, i.e. `filt_b(M A0) ≤ M g_b` earlier). With R0 a merge
   of shadows, (a) and (b) have no walk, nor does (c) Back of the shadow's request pin
   (the only path back to the shadow is through A_b's GUARDED A0 pin). cert9 on d slow:
   54 items uncertified (18 + 18 + 18). (b) is not just underivable: on a run where A0 rises
   before g_b (R0 first by 350–620 ps, server faster than that), `filt_b(M A0) ≤ M g_b` is FALSE.

## Corrected core (as implemented, events4/model.py `build_arb_fix`)
Readers X of q: g1, g2 (ugrant O5/O6), R0 (ustate O5). `Dq(X)` = arc(q→X) + lut(X),
`Dr_b(X)` = request leaf path + arc(r_b→X) + lut(X), `DA0` = arc(A0→ustate) + lut(ustate).
- `K = min(Dq(g1)lo, Dq(g2)lo, Dq(R0)lo − 2) − 2`;
- `vctl`: F (1,1), Q (1,1), pin ¬A0 `[DA0lo + K − 1, 10^12]`;
- `arb:g_b`: F (1,1), Q (1,1), request pin `Dr_b(g_b) − 1`, ctl pin (filtered, label (ctl, b)) `Dq(g_b) − K − 1`;
- `vsh:R0/b` (shadow, no wire): F (1,1), Q (1,1), request pin `Dr_b(R0) − 3`, ctl pin `Dq(R0) − K − 3`;
- `arb:R0`: merge of the two shadows, F (1,1), taps (1,1).
A q flip at tq that reaches X at tq + Dq(X) is the virtual edge of X from one ctl edge at tq + K;
the A0 → X lower end equals the real one (D2 gone).
