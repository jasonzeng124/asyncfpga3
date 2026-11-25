# A-lut-audit: function-hazard audit of every LUT in the cell library

Files:
- `formal/tools-A/lut_extract.py`: extracts every LUT1..LUT6/LUT6_2 instance from
  `cells/rtl/*.v` (INIT, I0..Ik-1 connections, outputs, `file:line`) and generates
  the Lean file. With `--audit` it is also an independent brute-force cross-check
  of the audit counts (Python vertex enumeration).
- `formal/lean/Formal/Core/LutCells.lean`: GENERATED, definitions only. There are 43 instances
  (41 source instances; the 2 parametrised INITs `INITB` and `SIDE_INIT` are emitted as both
  variants, `_t`/`_f`). A pin is `c0`/`c1` (tied), `fb o` (the instance's own output `o`,
  i.e. the feedback) or `sig "<net>"`.
- `formal/lean/Formal/Core/LutAudit.lean`: proved (namespace `Formal.Core.LutAudit`). It imports
  `Formal.Core.LutTree` and `Formal.Core.LutCells` and does not copy anything.
- `formal/lean/Wip/LutAudit.lean`: one open conjecture, written as a comment.

## How to check

`LutCells` has no olean yet (no `lake build` allowed), so compile it to a scratch path first:

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    python3 ../tools-A/lut_extract.py            # regenerate (idempotent; output identical)
    mkdir -p /tmp/lut-audit/olean/Formal/Core
    ln -sf $PWD/.lake/build/lib/lean/Formal/Core/LutTree.olean /tmp/lut-audit/olean/Formal/Core/
    ../slot.sh lake env lean -o /tmp/lut-audit/olean/Formal/Core/LutCells.olean Formal/Core/LutCells.lean
    ../slot.sh lake env bash -c 'LEAN_PATH=/tmp/lut-audit/olean:$LEAN_PATH lean Formal/Core/LutAudit.lean'

After the lead's `lake build` the last line is just `../slot.sh lake env lean Formal/Core/LutAudit.lean`.
The check is clean: no output, about 50 s wall, peak RSS about 1.1 GB. There is no `sorry`, `admit`,
`axiom`, `native_decide` or `bv_decide`. The computations use `decide +kernel`, which is the kernel
evaluating `Decidable.decide` and produces no `ofReduceBool`. `#print axioms`: the audit and protocol
theorems use `[propext]` only; the general theorems use `propext, Quot.sound` and
(`sic_hazardFree`) `Classical.choice`.
Cross-check: `python3 formal/tools-A/lut_extract.py --audit` prints the same 51 count rows that
the `audit_*` theorems prove.

## Definitions (which hazard notion)

Fix a LUT output `o`. Its function is taken over the FREE pins: tied pins are filled in, and for O5 of
a LUT6_2 I5 is dropped. Vectors are root first (`[I5..I0]` restricted to free pins). The tree
order only affects delays (`LutTree.evalTree_swap`). A transition is `old → new` on the free pins.
- **Static** (Eichelberger 1965): `f old = f new = c`. It is hazard-free iff every vertex
  of the cube `[old,new]` gives `c`. `staticHF_iff_kleene` shows this is the same as the Kleene value of
  the merged vector (changing pins = X) being `c`.
- **Dynamic** (Unger 1969; Nowick & Dill 1995): `f old ≠ f new`. It is hazard-free iff there are
  no `C ∈ [old,new]` and `D ∈ [C,new]` with `f C = f new` and `f D = f old`. Equivalently, every
  monotone vertex path changes the output exactly once. `dynHF_iff_kleene` gives the Kleene form:
  every vertex `C` with `f C = f new` has Kleene(`merge C new`) = `f new`.
- Feedback pins are held in the audit (fundamental mode): the inputs move, and the loop
  responds afterwards with a single change on its own pin, which `sic_hazardFree` covers.

## Theorems that check

General results (proved once for all LUTs):
- `outK_kv`, `outK_eq_ofBool_iff`: on a free-pin vector, the Kleene value of a sub-cube is `c`
  iff every vertex gives `c`. This rests on `consistent_fill` and on LutTree's
  `evalTree_eq_tableEval`.
- `staticHF_iff_kleene`, `dynHF_iff_kleene`, and the Bool checkers `sHFk_iff`, `dHFk_iff`,
  `classify_sHF/sHZ/dHF/dHZ`.
- `sic_hazardFree`: every single-input change is function-hazard-free, static or dynamic.
- `lut_static_glitch_free`: a static hazard-free transition gives a physical output (`PhysTree`
  under `H_sram`, `H_mux_kleene`) that is constant for any delays.
- `dyn_stays_new`, `dyn_never_back`, `dyn_single_window`: for a dynamic hazard-free transition,
  under any monotone progress of the pins (any order, skew or overlap), the Kleene output goes
  old → X → new and never back. With `root_sound`, the physical output is `old` before one window
  and `new` after it. Inside the window `H_mux_kleene` says nothing; see the Wip conjecture.

Audit results (`decide +kernel` on the generated terms):
- `audit_<inst>_<out>`: 51 theorems, one per LUT output. Each gives the counts
  `(sHF, sHZ, dHF, dHZ)` over all multi-input changes. Selected rows:

  | output | free pins | sHF | sHZ | dHF | dHZ |
  |---|---|---|---|---|---|
  | bd_c2 / c2_set / c2n / c2n_set .O | 4 | 16 | 20 | 24 | 4 |
  | bd_c3 .O | 5 | 148 | 76 | 104 | 24 |
  | bd_c4 .O | 6 | 880 | 260 | 424 | 100 |
  | bd_latch pair .O5/.O6 | 5 | 32 | 32 | 64 | 0 |
  | bd_arbiter ustate .O6 (q) | 5 | 148 | 76 | 104 | 24 |
  | bd_arbiter ustate .O5 (R0) | 5 | 128 | 0 | 224 | 0 |
  | ugrant .O5/.O6 | 3 | 8 | 8 | 16 | 0 |
  | bd_datamux pair | 5 | 176 | 192 | 400 | 64 |
  | bd_mlink uz | 4 | 36 | 44 | 60 | 36 |

  Every LUT has hazardous multi-input changes except the 1-input ones. The counts by themselves
  mean little. What matters is which changes the protocol can produce, listed below.
- `c4_tree_eq_table_3pow6`: on all 729 Kleene vectors of bd_c4's real INIT and pin map, the mux
  tree and the table semantics agree.

## Protocol: which multi-input changes reach each LUT

Free-pin orders: c2 family `[rst,q,b,a]`, latch pair `[q1,d1,q0,en,d0]`, ustate
`[A0,rst,q,r2,r1]`, ugrant `[q,r2,r1]`.

**bd_ce (C-elements).** `celem_same_direction_hazard_free` covers all 8 cells. From a settled state, any
set of data inputs moving together in one logical direction is hazard-free, with rst held at either value.
That covers the four-phase join and fork: all requests rise before any falls. For `bd_c2n` the logical
direction counts `~b`. `celem_reset_dominates`: while rst is held, any change at all is
static hazard-free. `c2_opposite_direction_hazard`: on a 2-input C-element, an opposite-direction change is
always a static hazard. As the merge acknowledge `C(x_req, z_ack)`, that is x_req rising while z_ack is still
falling from y's transaction, which bd_merge's precondition forbids. So the precondition is
needed at LUT-function level too, not only for protocol bookkeeping. bd_ctree's header ("all of them rise
before any falls") is exactly the same-direction class.

**bd_link (Muller stage, `bd_c2n` with a = req_in, b = c_next).** With c = 0, c_next cannot rise and
req_in cannot fall, because both need c = 1. With c = 1 the reverse holds. So the only possible multi-input changes are
`req_in↑ ∥ c_next↓` (c = 0) and `req_in↓ ∥ c_next↑` (c = 1). Both are dynamic hazard-free
(`link_mic_hazard_free`). The hazardous change `req_in↑ ∥ c_next↑` cannot occur
(`link_unreachable_mic_hazard`). Result: hazard-free.

**bd_latch.** `latch_closed_data_free`: data may move freely while en = 0. `latch_bit_isolation`: changes on the
other bit's pins never disturb this bit, even when several move together. en↑ or en↓ with D steady is a single-input change, and
closing with D = Q is covered by the consensus term. Two hazardous changes:
`latch_close_while_d_moves` (D moves during en↓, the hold side, rule H / DACK) and
`latch_close_while_q_settles` (en↓ before the own feedback has followed D, the setup side,
rule L). The protocol presents both exactly when those timing rules fail. They are timing obligations
that the routed audit already checks, not new defects. Opening while D still ripples
(req_out leads data_out) can glitch Q while transparent. That is harmless, because Q is only used after
close.

**bd_arbiter / bd_arbcell.**
- **FINDING: `arb_tie_from_idle_hazard`.** r1 and r2 rising together from idle with A0 = 0 is a
  static function hazard on q, for BOTH held values of q. The same holds for bd_arbcell's `bd_c2n_set`. The cube
  contains r1·¬r2 (set) and ¬r1·r2 (reset). Whichever request reaches the active muxes first drives
  set or reset for the length of the skew. The header (bd_arb.v, "A plain tie (both requests rising
  together from idle) is resolved deterministically … What remains is a runt … r1 and r2 moving in
  OPPOSITE senses") is therefore wrong as stated. A same-sense near-tie, with the
  non-favoured request leading by less than a loop delay, produces the same runt on set or reset, and so the same metastability
  exposure. Only exactly simultaneous arrival at every mux copy holds, and per LutTree that is not a
  physical notion (per-copy select skew). This does not change the design decision ("trust the arbiter").
  It changes the header's characterisation of the MTBF window: verify/MTBF.md should drive same-sense near-ties too, not only
  opposite-sense ones.
- `arb_frozen_while_A0`: while A0 = 1, any request change is static hazard-free on q. The hold
  works as claimed. `arb_A0_rise_with_competitor`: a competing request arriving with A0↑ is hazard-free.
- `arb_A0_fall_with_rerequest`: A0↓ together with the winner re-requesting is a static hazard. This
  is the race the header already acknowledges ("a request arriving coincident with that edge").
- **FINDING (digital): `arb_grant_near_tie_runt`.** On ugrant, `q↑ ∥ r2↑` is a static-0 hazard on
  g2 = r2·¬q. The near-tie can resolve cleanly at ustate, because its feedback branch of q already
  holds, while r2 reaches ugrant before ugrant's branch of q does. g2 then pulses with no
  metastability involved. The window is the routing skew between the two branches of the q net plus the r2
  skew. This is a fourth exclusion tier, not one of the header's three. `arb_runt_absorbed`: `ua2 = C(g2, A0)` holds 0 through
  it while A0 = 0. R0 reads the feedback branch and is unaffected. There IS a direct reader:
  `bdc/emit.py` (n-way arbitrated merge, around line 420) emits `assign won[k] = g2[k] | in_k_ack`
  and derives the `index` output from it. So the runt reaches `index`, which is data bundled with
  the request R0. It is harmless only if the pulse ends, at the latest when q arrives at ugrant, before
  anything samples `index` behind R0's matched delay. That is a bundling margin which should be named and
  checked post-route. It is not shown to fail here.

Other cells (not asked, from the audit). bd_mlink's XNOR (`ux`/`uz`) is hazardous on `done ∥ ack`.
MOUSETRAP never produces that change: done can toggle only while done = ack, and ack only while done ≠ ack.
bd_ctl steer/bd2dr `req ∥ s` is hazardous, so it is the bundling constraint (s before req). bd_link_dctl (status: failed
experiment) is in the audit table only.

## Scaling of `decide`

Kernel `decide +kernel` handles everything directly, so no reflection layer was needed. Measured
(one slot):
- one LUT6, all 3^6 = 729 Kleene vectors (tree = table): 6-8 s.
- bd_c4 full audit (64×32 pairs, dynamic cube enumeration up to 3^5 per pair): 8-19 s.
- whole file (51 audits + protocol sweeps + general proofs): about 46 s kernel and 50 s wall, 1.1 GB.
- elaborator `decide` (without `+kernel`) also works: bd_c2 audit 0.9 s, bd_c3 audit 3.3 s total.
If 8-input structures or cross-LUT products are needed later, the next step is the
proved-once checker already in place: `sHFk_iff`/`dHFk_iff` reduce the semantics to Bool
functions, and those can be evaluated on bitmask encodings.

## Verdict

**It works.** Extraction from Verilog, general hazard theory tied to the mux-tree model, a full audit
of all 43 instances / 51 outputs, and protocol classification for bd_ce, bd_link, bd_latch and
bd_arb are all proved. Two findings on bd_arb are reported above. Effort to finish:
(a) a mechanised environment model, so that "which multi-input changes can occur" is derived instead of argued: about 1-2 days
(a small speed-independent state-graph explorer over LUT next-state functions plus four-phase environments, in
Lean with `decide`); (b) the Wip conjecture (one edge inside the window, exact model): about 1-2 days.

What it buys: every LUT's hazard behaviour is computed from the exact INIT in the RTL. A changed INIT
regenerates `LutCells.lean`, and any changed count breaks the build. Every place where the cells rely on
"these pins never move together" is now a named theorem.

## Fidelity

- Primitive: the LutTree mux tree under `H_sram` and `H_mux_kleene`. The static results transfer to
  silicon through `lut_static_glitch_free` for any delays. The dynamic results give one switching window,
  not one edge. A hazard result is existential: some arrival order at the active muxes gives the
  glitch (cf. LutTree `and_glitch`). It does not say every routing does.
- Explicit modelling assumptions: (1) tied pins are truly constant; (2) fundamental mode for
  feedback, so the inputs of a change finish before the loop responds; (3) the protocol argument for
  each multi-input change is prose plus a named Lean case, not a mechanised environment.
- Tests: GLS of bd_arbiter with r1/r2 skew swept through ±1 loop delay in the same sense. Count
  ustate output edges and look for an X or a runt on q. Separately, delay ugrant's q branch relative to
  ustate's feedback branch and look for g2 pulses (A0 = 0). On the board, use the verify/MTBF.md
  setup with same-sense request pairs.
