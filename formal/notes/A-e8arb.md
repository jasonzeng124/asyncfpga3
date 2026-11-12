# A-e8arb (probe E8Arb, shard A): H_ARB (HARB7) against the real bd_arbiter

STATUS (2026-10-29): done as a REFUTATION, partial on the rest. One claimed Lean file,
`formal/lean/Formal/Core/XAudit/Events8Arb.lean` (check.sh: 879 declarations, [check] OK, §7).

Headline
1. **HARB7, as events4/model.py and cert8 encode it, is false on uncontested runs of the real
   cell.** Proved at cell level in Lean (`unc_not_harb`): a behaviour of the real `bd_arbiter`
   core (real INITs, A's per-pin semantics), uncontested for every window, with exclusive
   grants, that no virtual core matches, for two independent reasons:
   - **D1 (R0)**: the virtual `R0` is the OR of the two grants read AFTER them (stage band plus
     tap band, lower ends ≥ 1). The real `R0 = r1·q + r2·¬q` is computed in `ustate` from its
     own reads of `q`, so when `q` flips (every handover, and every first request on input 2)
     `R0` moves on its own path and can rise BEFORE the grant. cert8's tap bands come from the
     request arcs only (events4/model.py, the `R0 = merge of the two grants` block) and do not cover q-caused edges.
   - **D2 (ctl, 2 steps)**: the virtual ctl's lower band `lo_c` = A0 pin + state LUT + q pin (of
     the first grant) lower ends, but ctl's own stage band `(1,1)` and the filtered pin's band `(1,1)` add 2
     steps, so the virtual grant rises at least `lo_c + loF + 2` after A0 falls while the real
     one can rise `lo_c + loF` after it.
   Untrusted numbers on gcd_hw (§3): D1's q-caused R0 relation is DISJOINT from the virtual
   band (violated for every delay choice in the bands) on 14/18 grant→R0 pairs (seed d slow),
   18/18 (d fast), 11/18 (3 slow), 15/18 (3 fast); D2 and D1 both occur in E8Hyp's own sim0
   SatPin behaviour (merge4, seed d slow: R0 rises 453 ps before g2; g2 rises 1450 ps after A0
   falls, the virtual needs ≥ 1452). So on such behaviours `design_verdict8`'s H_ARB premise is
   false and the verdict says nothing about them.
2. **Necessity of a window** (Lean, `noFree_not_harb`): C's instantaneous "no free contention"
   (both requests high ⇒ a grant held; the conclusion of `gcd_hw_arbiters_uncontended'`), read
   on A's wires, does not imply HARB7: a contested runt behaviour of the real cell satisfies it
   at every instant, has exclusive grants, and its `g2` pulses for ever under a steady `r2`,
   which no virtual grant can do (`vgrant_hold`).
3. "Uncontested" is defined on A's traces (`Unc W`, §2); `Unc 0` = C's predicate
   (`unc0_iff_noFree`); the runt trace violates `Unc 1` (`ct_not_unc1`).
4. NOT proved: the sufficiency direction (uncontested + B's conditions ⇒ a corrected virtual
   core). Target statement and missing pieces: §4, `Wip/E8Arb/Sufficiency.lean` (open, sorry).
5. Discharging "uncontested" for gcd_hw (§5): not via C (C's predicate is instantaneous and
   lives in an SI tick model with no time scale; even with a perfect channel map it gives only
   `Unc 0`, which is insufficient by 2). Route: an A certificate (count walks with band delays)
   inside a prefix-closed verdict; not built. No contested schedule found (weak evidence).

## 1. What HARB7 says (read in the Lean and in model.py)

`Events7.HARB7 net b rn x cv`: every virtual node has an `ND7` in the certificate's bands, the
grant and R0 wires equal the virtual signals, the virtual R0 is low at 0. The virtual nodes per
arbiter (events4/model.py:250-291, cert6.py:384-424; values from `cert8` on seed d slow):

| node | ND7 shape | bands (cert8) |
|---|---|---|
| `vctl:` | non-merge, ONE pin: `¬(A0 source)`, plain, inverted; reset value 0 | F (1,1), Q (1,1), pin `[lo_c, 10^12]`, `lo_c` = arc(A0→ustate) + lut(ustate) + arc(q→first grant) lower ends (e.g. 1350 for merge4) |
| `arb:g_b` | non-merge, pin 0 = request (plain, filtered or multi, as the request's source is), pin 1 = `ctl·[σ = b]` (filt) | F = grant LUT band (e.g. [100,124]), Q (1,1), request pin = the real request arc, ctl pin (1,1) |
| `arb:R0` | merge of the two virtual grants | F = ustate O5 band, taps `[max(1, R(r) lo − g(r) hi − lut_g hi), …]` from the REQUEST arcs |

## 2. "Uncontested" on A's traces (Lean: `Pend`, `Unc`)

`Pend r g t := r t = true ∧ g t = false` (request pending). **`Unc W r1 r2 g1 g2`**: whenever `r1`
is pending at `u` and `r2` at `v`, `u + W < v ∨ v + W < u` — the two requests are never both
pending within `W` steps. Over the real wires (the request source wires, the grant wires).

- `Unc 0` ⇔ "both requests high ⇒ some grant high" (`unc0_iff_noFree`): C's predicate.
- `unc_mono`: antitone in `W`.
- The window B derives: `ArbBinary.H_REQ_SEP` (cell_constraints `bd_arbcell.req_separation`):
  same-sense request edges more than `L` apart, `L` = state LUT arc + q feedback. For
  `bd_arbiter` (A0 hold) the race moves to A0's fall (bd_arb.v header, "WHAT THE HOLD DOES NOT
  DO"); B has no windowed statement for the held cell (its `ArbHeldTimed` / `OnGcdArb*` are
  handover-exclusion conditions RT1/RT2, not a contest window). Proposed (NOT derived in Lean):
  `W_arb = L + S` with `L` = the ustate q pin's upper band and `S` = the spread of the request
  reads over the four LUT outputs (`Wip/E8Arb/wchk.py`): seed d slow, per arbiter, W from 808
  (merge12.uarb2) to 2901 ps (merge6, S = 2491 from a delay-line request).
- Why a window is needed: `ct` (below) satisfies `Unc 0` and is contested within 1 step.

## 3. The Lean results (`Events8Arb.lean`)

Cell model. `ArbPin B r1 r2 rs a q R0 g1 g2`: `ustate` O6 / O5 and `ugrant` O5 / O6, each output
reading each of its pins through its own monotone warp in the per-pin band (`Events2Pin.PinRel`
specialised; bands composite route + site pin + LUT arc from the source signal). INITs are B's
constants `ArbBinary.ARB_ST`, `GRANT`, decoded by `cases` (`st_eq`: `q = rst + (A0 ? q :
C(r1,¬r2))`, `r0_eq`, `g1_eq`, `g2_eq`). Virtual nodes `VCtl`, `VGrant`, `VMerge`: the `ND7`
equations of the three node kinds, specialised to one-copy plain pins (the ctl pin and a plain
request pin; a filtered or delay-line request pin is not covered by `VGrant`).

| theorem | plain statement |
|---|---|
| `vgrant_hold` | a virtual grant high on `[t0, t0+hiF]` with its request high on `[t0−hiF−hiR, t1]` stays high on `[t0, t1]`, whatever ctl and σ do |
| `ct_pin` | the contested runt `ct` is a behaviour of the real cell: `r2` rises at 10, `r1` at 18 (reset excitation of 8 steps < the q loop of 10), A0 = rst = 0; q then carries a low pulse of width 8, period 10, for ever |
| `ct_excl`, `ct_noFree`, `ct_unc0` | `ct`'s grants are exclusive; at every time both requests high ⇒ a grant high |
| `ct_g2_osc` | `g2` high on `[22+10k, 29+10k]`, low at `30+10k`, for every k, with `r2` high from 10 |
| `ct_not_virtual` | no `VGrant` with `hiF ≤ 7`, `hiF + hiR ≤ 12` (any ctl, σ, branch) is `ct`'s `g2` |
| `ct_not_unc1`, `noFree_not_harb` | `ct` violates `Unc 1`; packaged: C's predicate does not give a virtual grant |
| `vmerge_needs_grant` | virtual R0 high at `t` ⇒ a grant high at a time `≤ t − (loF + lo_tap)` |
| `vgrant_rise_ctl` | a virtual grant's first rise at `t` needs A0's source low at some time `≤ t − (loF + lo + 2)` |
| `ho_pin`, `ho_unc` | the handover `ho`: r2 waiting, r1 never, A0 falls at 10; every read 1 step except ugrant's q pin for g2 (3); q falls at 11, R0 rises at 12, g2 at 14. A real-cell behaviour, uncontested for every W |
| `ho_not_vmerge` | no `VMerge` with stage + tap lower ends ≥ 1 is `ho`'s R0 (D1) |
| `ho_not_vctl` | with cert8's split (`loF + lo` = the real lower path, 1 + 3), no `VCtl`/`VGrant` pair is `ho`'s g2 (D2) |
| **`unc_not_harb`** | packaged: a real-cell behaviour, `Unc W` for all W, exclusive grants, matching neither the virtual R0 nor the virtual grant over cert8's ctl split |

Scale: the traces use steps (1, 3, 8, 10); the theorems quantify over the virtual bands but the
real bands are concrete. The gcd_hw-scale versions are the untrusted numbers below.

What the Lean does NOT cover: the link from these cell-level relations to `ND7` over a parsed
`Net4` (no `Events7` import: the virtual node shapes are restated, not imported; a filtered or
multi-copy request pin is not covered); the sufficiency direction; D1/D2 on the gcd_hw netlist
(untrusted scripts only).

### Untrusted gcd_hw numbers (`Wip/E8Arb/*.py`, `python3 -I`; inputs regenerated with
`tools-A/xaudit/events7/rerun/prep.sh` (skeleton md5 d af88a1eb97c8, 3 080423e23154) and
`tools-A/xaudit/events8/cert8.py`, unchanged)

- `wchk.py`: per grant→R0 pair, the real q-caused relative delay
  `(q→R0 pin+lut) − (q→g pin+lut)` over the bands vs the virtual need `[F_lo + tap_lo, F_hi + tap_hi]`.
  Disjoint (violated by every delay choice): **14/18** d slow, **18/18** d fast, 11/18 3 slow,
  15/18 3 fast. Typical: merge4 g2 relation `[-622, -348]` ps vs need `[94, 241]`: the real R0
  rises 0.35-0.62 ns BEFORE g2. merge11's is late instead (`[228, 613]` vs `[96, 183]`).
- `sim1.py` (= E8Hyp's sim0.py plus an event dump; every pin read with its fixed lower band end,
  rst released at 20 ns, selects 0, seed d slow): merge4: A0 falls 177243, q 177907, **R0 rises
  178240, g2 178693** (R0 first, by 453 ps = wchk's lower-end value), and g2 − A0fall = 1450 ps
  while the virtual needs ≥ lo_c + F_lo + 2 = 1350 + 100 + 2 = 1452 (D2). Pending distance
  between the two requests in that run: r1 pending [73806, 75445), r2 pending [114150, 178693):
  38.7 ns apart, so `Unc W` holds for any W < 38 ns there. No free contest in either run (as E8Hyp).
- So the behaviour E8Hyp used as its (weak) joint witness violates HARB7.

## 4. Sufficiency (OPEN)

Target (`Wip/E8Arb/Sufficiency.lean`, statement incomplete by design): an uncontested
(`Unc W_arb`) real core, settled at reset with q = 1, under B's handover conditions RT1 / RT1b
(cell_constraints `bd_arbiter.rt1`, `.rt1b`: the falling grant's request read beats the q
flip at the other grant) and a port protocol (A0 rises only with R0 high, falls only with R0
low; grant edges at least `lo_c + loF + 2` after the A0 edge that enables them), is a behaviour
of a CORRECTED virtual core:
- ctl band `lo_c − 2` (fixes D2), σ_k = the winner of ctl round k (SelOK at the virtual pins
  then holds by construction);
- grants as now;
- R0 = merge of two SHADOW grants `g'_b` (virtual C-elements like `g_b` with ustate O5's stage
  band and ustate's request arcs, reading the same ctl·σ) with taps (1,1), instead of the OR of
  the grants (fixes D1).
Proof plan (not done): (i) under `Unc W` every q move is a single clean transition (the
excitation outlives the loop: B's `fix_at_redge` / `qedge_cause` in the transport model are the
model); (ii) per grant, the real `g = R ∧ Q_b` equals `cel(R, E)(g(F t − 1))` iff three enable
conditions hold (E high at a rise, low while R waits on a q flip, low within `loF+1` after a
fall); (iii) build ctl as `¬A0` through a warp that holds back ctl's rise in each round until
the winner's q flip has reached its grant (bounded by the flip time, ≤ 10^12) — the
`Warp`-existence part is the main Lean work; (iv) the warp factorisation of each real read
`w ∈ [loR+loF, hiR+hiF]` into `G ∘ F`. Estimate 1-2 days.

Circularity: the port protocol is what the verdict proves (counts), using H_ARB. A discharge
needs a prefix-closed verdict (HARB on `[0, t)` ⇒ counts on `[0, t + δ)` ⇒ protocol and `Unc`
there ⇒ HARB on `[0, t + δ')`). Nothing in Events7/8 is stated per prefix today.

## 5. Discharging "uncontested" for gcd_hw

- **From C** (`CapstoneCut.gcd_hw_arbiters_uncontended'`, `CapstoneLiveArb.Contested`): its
  conclusion is `Unc 0` on C's Ops channels. Gaps: (a) no map from C's channels `ch x`, `ch u`
  and grant traces `g1 g2` to A's wires (C's `Ops` traces are SI tick relations, unbounded
  delay, no ps scale); (b) even with an exact map it yields only `Unc 0`, and
  `noFree_not_harb` shows `Unc 0` does not give HARB7 (nor any virtual grant). A windowed
  version cannot come from an untimed model. So this route is closed, not just unlinked.
- **A certificate** (proposed, not built): an UNC row per arbiter checked by xevents: "r_b
  pending at `u` ⇒ r_b' not pending on `[u − W, u + W]`", from count facts the verdict already
  certifies with delays: `pending_b` ⇔ `M(r_b)` odd ∧ `M(g_b)` even; a labelled walk from `g_b`'s
  grant to `r_b'`'s next request (the spine token of C-8r: one token in the loop) with a Back-
  style lower band `≥ W` gives the separation. Needs (i) the prefix-closed verdict above and
  (ii) the corrected virtual core of §4 (else the counts are of a false model).
- **Counterexample**: none found. In the untrusted runs no two requests are pending within
  38 ns; each gcd_hw control_merge joins an entry with a loop back edge or two branches of one
  steer, both separated by a token walk much longer than W (≈ 1-3 ns). Weak evidence: the runs
  deadlock early with frozen selects.

## 6. design_verdict8 with H_ARB replaced

Not writable soundly today: H_ARB cannot be replaced by "uncontested + B's conditions" because
the virtual core it names is refuted by uncontested real behaviours (`unc_not_harb`). The
replacement needs, in order: (1) the corrected virtual core in model.py / cert6.py / cert8.py
(ctl lower band −2; R0 as a merge of shadow grants) and a re-run of xevents8 (the Back margins at
the servers' C-elements change); (2) `ArbOK`, a decidable check that each virtual triple matches a
real `bd_arbiter` in `d` (INITs `ARB_ST`/`GRANT`, pin wiring, bands = the real per-pin bands);
(3) the sufficiency theorem of §4. The variant would then read:

    design_verdict8_arb : (as design_verdict8, minus harb) →
      ArbOK d net b rn → (∀ arbiter k, Unc (W k) (r1 k) (r2 k) (g1 k) (g2 k) on x) →
      (B's RT1/RT1b at the routed bands) → ∃ cv, HARB7' net b rn x cv ∧ …

with `Unc` itself discharged by the UNC certificate inside a prefix induction (§5). None of
(1)-(3) is done.

## 7. Check

    cd formal/lean && ../check.sh Formal/Core/XAudit/Events.lean Formal/Core/XAudit/Events2.lean \
        Formal/Core/XAudit/Events8Arb.lean
    ...
    [audit] 879 declarations checked
    [check] OK

Imports: `Formal.Core.XAudit.Events2` (A; `cel`), `Formal.Cells.ArbBinary` (B, read-only: the INIT
constants and `o5B`/`o6B`). Mathlib-free. No sorry / admit / axiom / native_decide.
`Wip/E8Arb/Sufficiency.lean` contains `sorry` and is not claimed.

## 8. For the lead
- E8Hyp's notes §5 call sim0's run a (weak) joint witness; that run violates HARB7 (D1, D2).
- `gcd_hw_hypotheses.md`'s H_ARB row should say: refuted in its current encoding on uncontested
  handovers (D1, D2); the corrected core of §4 is the hypothesis to grade.
- tools-A/xaudit/events4/model.py (ctl `lo`, R0 taps) is the place to fix; not mine to edit.
- Next probe: E8ArbFix — implement the corrected virtual core in model.py/cert8, re-run xevents8
  (4 seeds × 4 corners), and check with `wchk.py` that every q-caused R0 relation lies in the new
  bands; then the sufficiency proof of §4.
