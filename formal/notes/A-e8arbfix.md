# A-e8arbfix (probe E8ArbFix, shard A): the corrected virtual arbiter core

STATUS (2026-10-29 ~10:25): tools DONE (corrected core in events4/model.py, old core behind a
flag, 16-row rerun, wchk, recorded-run membership + negative controls); Lean DONE for the
cell-level corrected core and a sufficiency theorem modulo three per-reader timing conditions
(`Events9Arb.core_of_settle`, non-vacuous instance `ho3_fix`); `Events9ArbBeh` (HARB7',
design_verdict9arb) check.sh OK (§7).
Headline NEGATIVE: with the corrected core, the Events7 log rules cannot certify 54 items per
row, so **no gcd_hw row is CLEAN any more** (11 CLEAN rows → RESIDUAL 54). Prefix-by-prefix
verdict (to discharge Unc and the protocol): NOT attempted (out of scope).

## 1. Plain statement

- Assumed (Lean, `core_of_settle`): the real `bd_arbiter` core in A's per-pin model (real INITs
  `ARB_ST`/`GRANT`; every LUT output reads every pin through its own monotone warp in the per-pin
  band), outputs low on an initial settled segment, band side conditions (K ≥ 2 etc., true at ps
  scale), (hstall) every ustate time is within H of an "ok" time (ustate reads A0 high, or q has
  settled for the rest of the A0-low phase), and per reader (g1, g2, R0's two terms) the three
  conditions `RdOK`: (B1) with the request read high, losing the state term only if the output was
  already low [RT1/RT1b]; (B2) a reader rises only from a settled q-read [corrected P-rise];
  (C) a request fall is read only at unsettled times [P-fall].
- Proved: the real cell is a behaviour of the corrected core `CoreOf B` (bands computed from the
  real per-pin bands by exactly model.py's formulas), with an EXPLICIT ctl (`ctlc`: ustate's A0
  read shifted by K, stalled until q settles) and σ = q.
- NOT covered: deriving hstall / B1 / B2 / C from Unc W + B's RT1/RT1b + the environment
  protocol (each is one edge-time inequality; not discharged for gcd_hw); the link from the
  cell-level `CoreOf` to `Events7.HARB7` over the parsed `Net4` (ND7 per virtual node, SelOK of
  σ); B's ArbOK (a decidable "virtual triple = real cell" check) — not built; certificates.

## 2. Why E8Arb's §4 fix had to change (untrusted analysis, `arbfix/orient.py`, member.py)

1. **Shadow grants reading the same ctl through `(1,1)` do not fix D1.** The q-caused
   R0-minus-grant delay is the difference of the two q arcs (ustate vs ugrant: merge4 d slow
   `[−622, −348]` ps); a common `(1,1)` ctl pin gives a few tens of ps. Mutation control
   `member.py --mut=samectl` (every reader reads ctl with the grant's lag): NOT MEMBER on 31 of
   576 arbiter-runs (all those with a q-caused edge). So each reader gets its OWN ctl pin band.
2. **A common stage band cannot factor two per-pin reads.** A reader reads request and q through
   independent warps (band arc + LUT each); a node with stage warp F (LUT band) and pin warps
   needs one F t in the intersection of three intervals, empty when the request is read fast and
   q slow. So every virtual node has F = Q = (1,1) and the whole read sits in the pin bands.
3. **Neither orientation of the old structure is sound** (`orient.py`): "R0 downstream of the
   grant" (the old core, ANY tap band) needs both relative lower ends ≥ 1: 0/11 grants d slow,
   0/11 d fast, 0/13 seed 3 slow and fast. "Grant downstream of R0": 2/11 (d), 0/13 (3).

## 3. The corrected core (events4/model.py `build_arb_fix`; Lean `Events9Arb.CoreOf`)
Readers X of q: g1, g2 (ugrant O5/O6), R0 (ustate O5). `Dq(X)` = arc(q→X) + lut(X),
`Dr_b(X)` = leaf path + arc(r_b→X) + lut(X), `DA0` = arc(A0→ustate) + lut(ustate).
- `K = min(Dq(g1)lo, Dq(g2)lo, Dq(R0)lo − 2) − 2`;
- `vctl:`: F (1,1), Q (1,1), pin ¬A0 `[DA0lo + K − 1, 10^12]`;
- `arb:g_b`: F (1,1), Q (1,1), request `Dr_b(g_b) − 1`, ctl pin (filtered, label (ctl, b)) `Dq(g_b) − K − 1`;
- `vsh:R0/b` (shadow, no wire): F (1,1), Q (1,1), request `Dr_b(R0) − 3`, ctl pin `Dq(R0) − K − 3`;
- `arb:R0`: merge of the two shadows, F (1,1), taps (1,1).
A q flip at tq reaching X at tq + Dq(X) is the virtual edge of X from ONE ctl edge at tq + K, for
all readers at once (D1 gone); the A0 → X lower end equals the real one (D2 gone; `wchk.py`:
equality on all 18 pairs d slow, e.g. merge4 g2 1450 ≤ 1450, the value sim1 observed).
Old core: `XA_ARB=old` or `--arb-old` (any generator using model.py: cert6/7/8/9, ana);
`ARB=old arbfix/run.sh` reproduces events9/xe9_d_slow_new.txt BYTE-IDENTICALLY. Every cert JSON
records `arb_core`; every generator prints `model: virtual arbiter core = …`.
Cost of item 2: on 5 gb two delay-line request pins (merge12.uarb2 g2 and its shadow) become
Line residuals (−90 / −70 ps), because the reader's LUT band now widens each copy's window.

## 4. The certificate gap (the headline negative)
The old certificates used the count link "R0 is a merge of the grants". With R0 a merge of the
shadows, cert9 finds no walk for, per arbiter (×9):
(a) Back of each grant's ctl pin (walk ctl ← A0 ← R0 ←SUB g_b) — 18;
(b) Back of each shadow's request pin (the only way back to a shadow is through A_b's GUARDED A0
    pin, which walks skip) — 18;
(c) the guard G walk at A_b = C(g_b, A0) (labelled A0 → g_b, no token) — 18 guard pins.
These are not search failures: (a)/(c) need a LOWER bound on the grant's count from the
shadow's (two parallel C-elements on the same inputs), which no upper-bound log rule (r1, fpin,
r3, sub, …) can give; it needs a liveness rule inside the verdict induction (a C-element whose
inputs have both advanced, read with bounded delay, has advanced), i.e. a new Events9-level
rule with its own soundness proof. (c)'s judgement `filt_b(M A0) ≤ M g_b` is false on any run
where A0 rises before g_b; on the recorded runs below it never did (N3 = 0), so it is
underivable, not observed false.

## 5. Pipeline (xevents9 on E8Mux corrected bands; `arbfix/run.sh`, `arbfix/table.sh`)
Inputs: E8Mux's `w/<seed>/new/` skeletons and band files (each passes e8mux/checkbands.py),
overlay = HDsub's `ov` (oleans of the committed Events9 sources). Outputs
`arbfix/results/xe9_<s>_<c>_fix.txt`, table `arbfix/results/table.txt`.

| seed corner | OLD (events9 *_new) | FIX: Back cert, guards cert | FIX residual = structural + other |
|---|---|---|---|
| d slow / fast | CLEAN / CLEAN | 830/866, 45/63 | 54 = 54 + 0 |
| d indep | RESIDUAL 21 | 824/866, 43/63 | 67 = 54 + 13 |
| d gb | RESIDUAL 2 | 830/866, 45/63 | 54 = 54 + 0 (the 2 ENTRY guards are among the 18) |
| 3 slow / fast / gb | CLEAN ×3 | 830/866, 45/63 | 54 = 54 + 0 |
| 3 indep | RESIDUAL 30 | 824/866, 45/63 | 69 = 54 + 15 |
| 4 slow / fast / gb | CLEAN ×3 | 830/866, 45/63 | 54 = 54 + 0 |
| 4 indep | RESIDUAL 19 | 822/866, 44/63 | 67 = 54 + 13 |
| 5 slow / fast | CLEAN / CLEAN | 830/866, 45/63 | 54 = 54 + 0 |
| 5 indep | RESIDUAL 22 | 824/866, 45/63 | 66 = 54 + 12 |
| 5 gb | RESIDUAL 1 (uenv1) | 829/866, 45/63 | 57 = 54 + 3 (uenv1 −61, two Line −90/−70) |

The 830 real-node Back pins are certified exactly as before, with the same minimum margins on
every slow/fast/gb row (d 937/423/526, 3 748/332/416, 4 919/400/553, 5 186/107/−61): nothing real
got worse. Every row: log accepted, all 90 dsub lines carry a valid wS (HDsub stays discharged).

## 6. Recorded runs: the old core is wrong, the corrected one fits (untrusted)
`arbfix/sim.py` (= Wip/E8Arb/sim1.py + `--delay lo|hi|rand:N` per-pin fixed delays in band, a
SatPin behaviour; `--json`), `arbfix/member.py`, `arbfix/members.sh`: 4 seeds × slow/fast ×
{lo, hi, rand:1, rand:2} × selects {0,1} = 64 runs, 9 arbiters each (576 arbiter-runs), all with
grant exclusion and no free contest (weak: ≤ 2 A0 rounds per arbiter, 160 grant rises in all;
the runs deadlock with frozen selects).
- OLD core, N1 (= Lean `Events8Arb.vmerge_needs_grant`: at R0's first rise some grant must have
  been high F_lo + tap_lo earlier): VIOLATED in 54/64 runs (82 arbiter-runs). N2 (per-round
  D2, old ctl band): violated in 8 runs (the lo-delay ones, e.g. d slow merge4: g2 rises 1450
  after A0 falls, old core needs ≥ 1452). So the old core is shown wrong on recorded runs.
- FIX core: member.py BUILDS the virtual signals (ctl edges = Lean's `ctlc`: rise at
  max(a_k + lo_ctl + 1, tq + K), fall at b_k + lo_ctl + 1; σ = round winner; every lag = the
  run's per-pin delay minus the core offsets, checked in band) and compares at every ps: 576/576
  MEMBER. Controls of the check itself: `--mut=samectl` 31/576 NOT MEMBER, `--mut=noshift`
  (drop the shadows' 2 steps) 128/576 NOT MEMBER.
- `Wip/E8Arb/wchk.py` on a fix cert: 18/18 q-caused R0/grant relations covered, lower ends equal
  (d slow); on the old cert unchanged: 14/18 disjoint.

## 7. Lean

Claimed candidates (Mathlib-free, no sorry/axiom/native_decide):
- `Formal/Core/XAudit/Events9Arb.lean` (imports Events8Arb): `VRd`, `RdB`, `CoreFix`, `kOf`,
  `loCtl`, `rdG`, `rdS`, `CoreOf`; `cel2_eval`, `En`, `EnOK`, **`and_cel`** (an AND term read
  through two warps is a `VRd` node under EnOK), **`core_of_en`** (sufficiency modulo the
  enable); §4 `ho2_pin`, `ho2_unc`, `ho2_not_old`, `ctl2_v`, **`ho2_fix`**, `fix_not_old`;
  §5 `Settled`, `Ok`, `Gc`, `rc`, `ctlc`, `settled_step`, `gc_ok`, `gc_le`, `gc_step`,
  `mono_of_step`, `rc_succ_false`, `gc_stall`, `ctlc_iff`, **`ctlc_vctl`**, `RdOK`,
  `enOK_of_rd`, **`core_of_settle`**; §6 `ho3_pin`, `settled3`, **`ho3_fix`** (every hypothesis
  of core_of_settle holds on an uncontested handover with R0 12 steps before g2), `ho3_not_old`,
  **`settle_not_old`**. Uses `Classical.propDecidable` locally (Classical.choice only).
- `Formal/Core/XAudit/Events9ArbBeh.lean` (imports Events9Beh): `FixShape` (corrected-core
  shape of a certificate: virtual F = (1,1), non-merge Q = (1,1), R0 taps (1,1) from wireless
  virtual nodes), `HARB7' := HARB7 ∧ FixShape`, `design_verdict9arb` (design_verdict9 under
  HARB7'; a projection — the content is in the certificate and in Events9Arb). Existing
  statements unchanged.

Check (2026-10-29, lead's .lake/build had XAudit oleans only up to Events3):

    formal/check.sh Formal/Core/XAudit/Events8Arb.lean Formal/Core/XAudit/Events9Arb.lean
    ... [audit] 976 declarations checked
    [check] OK

    formal/check.sh Formal/Core/XAudit/Events2PinDesign.lean Formal/Core/XAudit/Events4.lean Formal/Core/XAudit/Events5Line.lean Formal/Core/XAudit/Events5.lean Formal/Core/XAudit/Events6Gate.lean Formal/Core/XAudit/Events6Cert.lean Formal/Core/XAudit/Events6Design.lean Formal/Core/XAudit/Events6Beh.lean Formal/Core/XAudit/Events7Core.lean Formal/Core/XAudit/Events7Excl.lean Formal/Core/XAudit/Events7Cert.lean Formal/Core/XAudit/Events7Beh.lean Formal/Core/XAudit/Events8Core.lean Formal/Core/XAudit/Events8Cert.lean Formal/Core/XAudit/Events8Beh.lean Formal/Core/XAudit/Events9Cert.lean Formal/Core/XAudit/Events9Beh.lean Formal/Core/XAudit/Events9ArbBeh.lean
    ... [audit] 2538 declarations checked
    [check] OK

(the second is the not-yet-built XAudit closure of Events9ArbBeh, ending with it). Once lake has
built Events9Beh: `formal/check.sh Formal/Core/XAudit/Events9ArbBeh.lean`. Lakefile/Formal.lean
untouched; root imports if wanted: `Formal.Core.XAudit.Events9Arb`, `…Events9ArbBeh`.

## 8. For the lead
- Default of events4/model.py is now the corrected core. Any probe rerunning events5–9 / K3 /
  kapres through model.py gets it; `XA_ARB=old` restores the old one (byte-identical).
- The 11 CLEAN rows of A-events9/A-e8mux rest on a refuted H_ARB; with the corrected core they
  are RESIDUAL 54 (structural, §4). FEASIBILITY / gcd_hw_hypotheses should say so.
- Next probe (suggested, "E9Par"): a liveness rule for parallel virtual C-elements (shadow vs
  grant) in the verdict induction, to re-certify (a)–(c); then discharge hstall/RdOK per arbiter
  from routed edge-time inequalities (each is one ENTRY-like margin), and the prefix verdict.
