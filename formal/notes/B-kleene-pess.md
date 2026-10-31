# Probe Bpess: a pessimistic bracket below H_KLEENE_LUT

File: `formal/lean/Formal/Cells/KleenePess.lean`. Core Lean only. It imports MuxTree, ArbKleene,
Latch and KleeneBox, which are all core.
Check: `/tmp/claude-0/btools/bcheck.py Formal/Cells/KleenePess.lean`. Result: OK, 0 warnings,
about 25 s. No sorry, admit, axiom, native_decide, implemented_by, extern or unsafe.
`#print axioms` was run from a companion file that has since been removed. Every headline
theorem uses at most `[propext, Classical.choice, Quot.sound]`. The `decide` tables use
`[propext]` only.

Origin: audit row 88, `audit/findings/P8.md` section 2. `lutK` is the exact
hazard-free ternary closure. It is the OPTIMISTIC LUT model, for example `C2(1,1,X) = 1`.

## 1. Models (one 2:1 pass-transistor mux with an `x` select)

A policy `Pol = <p0, p1>` says which equal-leg value an x-select mux passes. Values are
output-referred: an inverting output stage is folded into the policy.

| model | p0 p1 | physical reading |
|---|---|---|
| `kle` | 1 1 | H_KLEENE_LUT. `muxP_kle` proves it is `K3.mux`. |
| `weak1` (P2) | 1 0 | An NMOS-only tree. An NMOS passes 1 only up to V_G - V_t, so equal-1 legs under a moving or mid-rail select can produce a runt or an intermediate level (charge sharing; the "legs rise while select mid-rail" case of `B-muxtree-fidelity.md` section 3). Equal-0 legs pass strongly. |
| `weak0` (P2') | 0 1 | The same tree behind an inverting output buffer, so the weak level is the output's 0. Which of P2 and P2' applies to 7-series silicon is not public. |
| `strict` (P1) | 0 0 | Any x select gives x. This is the extreme. |
| `lutR` (H_RETAIN) | any + retention | A LUT output that already shows the closure value keeps it: the level restorer holds an undriven node ("legs 1, node already 1"). It is modelled at the LUT output only, not at the internal nodes. |

The policy is per pin (`pol : Nat -> Pol`). Each input buffer drives one level, and
re-buffering may flip the polarity between levels. The tree may split on the pins in any
order (`MuxTree.build`; silicon has A6 at the output mux).

## 2. General theorems

- `bracket`: for every permutation order and every per-pin policy,
  `lutP strict ⊑ lutP pol ⊑ lutK`. `evalP_mono` adds that it is also monotone in the inputs.
- `lutP_definite` (exactness): the model output is a definite `v` iff two things hold. The
  Kleene closure is `v`, and every pin that reads x sits on a level that passes `v`.
  `lutP_eq_lutM` follows: the model depends only on the set of (pin, value) pairs that pass.
  It does not depend on the tree order or the pin order. So the A6-root question is moot here too.
- `strict_iff`: under strict, the output is definite iff no pin reads x at all.
- `transfer`: a definite model value equals the Kleene value. `lutR_between` gives
  `lutM ⊑ lutR ⊑ lutK`.
- `arb_run_le`: under any LUT semantics below Kleene (all the models above, retention
  included), the `bd_arbiter` ternary simulation stays below the Kleene simulation at every
  step. `arb_acks_safe` follows from it.

Reading: every result that says "never a definite wrong value" or "never both 1" survives
every model. Every x in a Kleene run stays x. A result that says "this output is definite `v`"
survives iff every pin that reads x at that moment passes `v`. That is the precise dependence
on H_KLEENE_LUT.

## 3. Cell results (uniform policy `p`; each theorem is over all four `p`)

| result (Kleene) | under the models | Lean |
|---|---|---|
| C2 hold with x on its own feedback: definite iff `a = b ≠ x` | **changes**: also needs `pass a`. `C2(1,1,X) = 1` iff p1; `C2(0,0,X) = 0` iff p0. weak1 loses the restore and hold of 1, weak0 loses those of 0, strict loses both. | `c2M_restore`, `c2M_11x` |
| C2 with x on one input keeps `q` iff `q = b` | **changes**: also needs `pass q` | `c2M_hold_xin` |
| C2 reset forces 0 whatever is x | **changes**: needs p0, or no x pin | `c2M_rst` |
| bd_c2n (00B2) restore iff `a = ~b ≠ x` | **changes**: also needs `pass a` | `c2nM_restore` |
| latch ODD hold (en=0, x on d) keeps q | **changes**: needs `pass q` | `oddM_hold` |
| latch transparent (en=1, x on q) passes d | **changes**: needs `pass d` | `oddM_transp` |
| latch x on en with d = q | **changes**: needs `pass d` | `oddM_enx` |
| bd_latch_rst RST0/RST1 reset under x | **changes**: RST0 needs p0, RST1 needs p1 (or no x pin) | `rstM_reset` |
| arbiter exclusion (never g1 = g2 = 1) | **survives**, for any per-pin model | `excl_M` |
| arbiter q = x is held on every hold input | **survives** (any model) | `arb_x_held_M` |
| g1 with q = x is 0 iff r1 = 0 | **changes**: iff r1 = 0 and p0 | `g1M_qx` |
| hold_shields (A0 = 1, x requests) | **changes**: needs both requests definite, or `pass q` | `hold_shields_M` |
| arb_restore_iff | **changes**: restoring to 1 needs p1, restoring to 0 needs p0 | `arb_restore_M` |
| network: acks never both definite 1 | **survives** (any LUT semantics below Kleene) | `arb_run_le`, `arb_acks_safe` |

The nine `ArbKleene` scenarios use the same input sequences. The end state is listed as
`q g1 g2 R0 A1 A2`. Lean: `scen_*`. `scen_kle` reproduces ArbKleene, and `scen_kle_matches`
checks this.

| scenario | kle | weak1 | weak0 | strict | weak1+R | weak0+R | strict+R |
|---|---|---|---|---|---|---|---|
| reset from all-x | tfffff | **x**fffff | tfff**xx** | xxxxxx | xfffff | tfffxx | xxxxxx |
| runt_opposite, window | xxxxff | xxxxff | xxxx**xx** | xxxxxx | xxxxff | xxxxff | xxxxff |
| runt_opposite, after | ffttff | ffttff | **xxxxxx** | xxxxxx | ffttff | xxxxff | xxxxff |
| runt_held | txfxtf | **xxxxxx** | txxxtx | xxxxxx | txfxtf | txfxtf | txfxtf |
| tie_rising | xxxtff | xxx**x**ff | xxxt**xx** | xxxxxx | xxxxff | xxxtff | xxxxff |
| tie_acked | xxxtxx | xxx**x**xx | xxxtxx | xxxxxx | xxxxxx | xxxtxx | xxxxxx |
| a0_fall_skewed | ffttfx | ffttfx | xxxxxx | xxxxxx | ffttfx | xfxxxx | xfxxxx |
| a0_fall_ordered | ffttff | ffttff | **xxxxxx** | xxxxxx | ffttff | xfxxxf | xfxxxf |
| a0_fall_runt | xxxtff | xxxxff | xxxtxx | xxxxxx | xxxxff | xxxtxf | xxxxxf |

Two of these matter for the arbiter claims:
- Under weak0, a held-0 ack C-element whose grant input reads x (A0 = 0) is itself x. Kleene
  masks this case; weak0 shows it as a possible spurious ack runt (runt_opposite, a0_fall_ordered).
- Under weak1, the A0 = 1 hold shield does not protect q = 1 (runt_held). The tie's definite
  R0 = 1 is also lost (tie_rising).

Exclusion of definite acks holds in every column.

KleeneBox `+w` (setup and hold in binary-edge times, H_X_UNIFORM):

| result | weak1 | weak0, strict |
|---|---|---|
| steer `steer_edges_K` (+w iff) | **survives verbatim** (`steer_edges_weak1`). Every definite spec value that is reached with an x pin is 0. | **fails** (`steer_fails_M`). The run is steer_witness_K's own traces, which Kleene accepts. At t = 1299 the unselected O5 reads x: the request is in its rise window and the select is a definite 1. |
| join `join_edges_K` (+w iff) | **fails** (`join_fails_weak1`). The right side holds and the Kleene left side holds. In the counter-run, uj1 is selected, x_req is waiting and ctl_req rises (1-tick x). The C-element must then restore 1 with its own feedback reading x, which is `C2(1,1,X)`. Run: `jW` = 0, then x from t = 999. | **fails** (`join_fails_weak0`). uj0 is unselected and spec 0, and the ctl_req rise window puts x on its pin at t = 999. |
| latch `latch_edges_uniform` / `box_exact` | token 0: the sufficient half **survives** (`latch_pin_ok_M`). Token 1 **fails** (`latch_fails_M`): the run `q ≡ x` is a model run at A=0, B=2, C=3, Td=0, Tn=3, where Kleene's box is safe. | weak0: the mirror case (token 1 survives, token 0 fails). strict: both fail. |

The C-element results, the join, and the latch hold at the non-passing level fail
unconditionally under the matching P2 model. Any input edge during a hold at the weak level
can produce a runt. No timing inequality excludes this, because the inputs do move during the
hold. The "new condition" is therefore that the (pin, value) pair must pass. It is not a margin.

## 4. Which results depend on H_KLEENE_LUT being hazard-free

- **Independent of it** (true in every model): every exclusion and safety result of the form
  "never a definite wrong or double value". Stated here: `excl_M` (kleene_exclusion), `arb_acks_safe` (network ack exclusion) and
  `arb_x_held_M` ("x stays x"). Others, such as `steer_excl_K`, follow from `transfer` in the
  same way but are not stated.
- **Needs pass-0 only** (true under weak1): the steer `+w` iff, every unselected-branch-0
  claim, a C-element or latch holding or capturing 0, RST0 reset, and g1/g2 masked by a 0
  request.
- **Needs pass-1** (true under weak0): C2(1,1,X) = 1, the join hold of 1, a latch holding or
  capturing 1, RST1 and the arbiter reset to q = 1, and the A0 hold shield for q = 1.
- **Needs both**: the join `+w` iff, the latch box for both tokens, KleeneBox overall, and every
  definite end state in the arbiter scenarios. Only H_KLEENE_LUT (both levels hazard-free under
  a single moving select) gives all of them.

Per pin: `lutP_definite` makes the requirement a finite list of (cell, pin level, value)
pairs. For example, the bd_c2 hold of 1 needs the level of I2 (q), and of whichever input
moves, to pass 1.

## 5. Experiments that distinguish the models

1. **Board, pass matrix (decisive).** Build 12 configurations, one per pin j in A1..A6 and
   value v in {0, 1}. Each is a `(* keep *) LUT6` with INIT all-v (or O6 = A_k with A_k static
   at v, k ≠ j, which tests unequal SRAM cells), LOC-pinned, with pin j toggled by a ring
   oscillator and the other pins tied. O6 drives the asynchronous PRE/CLR of an FDCE that
   software clears. Any runt above that pin's threshold sets the FDCE. Run 1e10 toggles per
   configuration, at 2 V_CCINT points and with heating if possible.
   - No flag in any configuration: consistent with `kle`.
   - Flags only for v = 1: weak1. Flags only for v = 0: weak0.
   - Flags only on some pins: the per-pin model, and the requirement list of section 4 then
     names the cells and pins at risk.

   Repeat with the select driven from bd_arb's grant near a tie (the MTBF rig in
   `cells/hw/arb_mtbf_measure.py`). This tests a truly mid-rail select, and it separates
   retention (legs static) from rising legs.
2. **GLS (model dependence, not silicon truth).** Replace the bitwise x-merge of
   `cells/gls/prims.v` SLICE_LUTX (on claude/research) with the weak1, weak0 or strict rule
   (x select: pass only if the legs are equal and equal to the passing value). Then rerun the
   power-up-x and reset regressions. The models predict different reset outcomes (table above):
   the ustate q stays x under weak1, the acks stay x under weak0, and everything stays x under
   strict. The GLS has no x during ordinary transitions, so this checks only reset and
   metastability paths. Only experiment 1 can tell which model the silicon follows.

## 6. Not done / open

- The latch `box_exact` necessity half under a model, when the token value passes. Only the
  sufficient half (`latch_pin_ok_M`) is proved, with a non-vacuity witness.
- The join and steer non-passing failures are proved by single counter-runs, not as iffs. The
  failures are unconditional in kind: an x on any pin of a non-passing level during a definite
  output.
- H_RETAIN is at the LUT output only. Internal-node state is not modelled.
- `bdc_muxn` and the CTree, Link and Ops cells were not re-run. By `lutP_definite`, their
  dependence follows the same (pin, value) rule.
- Grade: the bracket and exactness are proved. Which point of the bracket silicon sits at is
  untested (experiment 1).
