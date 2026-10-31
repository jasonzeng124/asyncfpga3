# C-8x4: physical gcd_hw capstone with the data fields derived (phys5); composing lemmas for every cell kind; H_FN checked against the generated cells

Shard C, probe 8x4, 2026-10-29. About 3 h. Follows C-8x3 (`notes/C-8x3-refine.md`), C-8x2 and
C-8x.

STATUS: DONE for (1) and (2). Five new Lean files pass `./check.sh` (log at the end). No existing
file was edited.

## Correction (2026-10-31, audit P12a rows 18-19)

- **phys4/phys5 rows were unusable on any terminating run.** The `TxWin` of `CapstoneRefine`
  demanded a `k`-th transaction for EVERY `k` (`count : ∀ k, ...`), so a channel with a TxWin is
  offered infinitely often (auditor's `txwin_inf`). On a single-start gcd run every channel is
  offered finitely often, so the `dag`/`cert` certificates and every `Row`/`RowG` were impossible,
  `BCert` reduced to `exempt` (assumed bundling), and `phys5_cls`/`phys5_gen` were vacuous on
  every real gcd run (auditor's `phys5cls_out0_inf`, `chW_not_cls`). The statement "26 root
  certificates, all with tcheck A rows" below could not be realised.
- **Fixed** (2026-10-31): `TxWin` now quantifies only over transactions that occur (`HasOff P k`):
  `idle`, `count` and `win` need a `k`-th offer, and the last transaction's window is unbounded on
  the right. Every theorem built on `TxWin` re-checks unchanged in statement. Non-vacuity on a
  FINITE channel: `CapstoneRefineFinWit.fin_witness` (a channel offered exactly twice, idle
  forever after, certified by a real tcheck DAG row, not `exempt`). On the REAL gcd_hw witness run
  (C-8t's `chW`): `CapstoneRefineOut0Wit.out0_dag_witness` -- out0 (offered once, closes at 473)
  carries a `BCert.dag` (`out0_dag_cert`: the dag hypotheses, stated as an existential), and from
  that row alone out0 is `Held` and every in-transaction sample is `6 = Nat.gcd 12 18`. Its
  obligation netlist is hand-made (5 nodes, fixed delays, 3 bus bits), NOT the routed one. Still
  NOT shown: tcheck's real rows meeting `TxWin` on a gcd_hw run; the other 25 roots; phys5's
  `Row` hypotheses on any gcd_hw run; the phys4/phys5 witnesses still use exempt/ghost.
- **"H_FN decided against Formal.Gen on 176/221" overstated.** `fnOK` returns `true` for `.wire`
  (43 forks) and `.shift` (37 steerD var 0) without consulting `Formal.Gen`. Only 96 (87 latches,
  9 data muxes) are checked against generated cells, at W = 3 only, with each bit pair assumed to
  use `pair[0].u`. H_FN is reduced to H_ZD_BITS + H_WIDTH, which are assumed.

## Verdict

- **(1) Composing lemmas for every kind.** `fieldOf_row`: a cell's handshake half, the protocol
  and bundling of every channel, and a tcheck `Row` for output `c` (row + H_TXWIN, H_FN, H_LAUNCH)
  give `c`'s relaxed data field. It covers every kind: fork, join/bjoin, steer, **link** (open and
  hold fields), **mux**, **3-input mux** and **arbiter stage**.
  - New kernel-checked facts: `mux_busy` (8f's 132-state `tbl`: while `z` is busy, the select and
    the selected input are busy) and `muxn_busy` (8l's state code, 4 × 8192 states, the same for
    select < 3).
  - New proved lemma: `link_open_stable` (8l's table: an open-latch stretch inside an output
    transaction goes back to the offer).
- **(2) phys5.** `gcd_hw_circuit_safe_phys5`: every out0 latch is `Nat.gcd a b`. The
  hypotheses:
  - per operator, `CellP`: the HANDSHAKE half of the relaxed gate model, and per output EITHER
    its data field (a ghost) OR a `Row`;
  - H_START_ONCE;
  - `BCert` on the 26 roots.

  Data fields of sampled channels are no longer assumed. `gcd_hw_joint5` derives protocol and
  bundling without them (joint induction over time, C-8x3's); `fieldOf_row` then derives them.
  - `gcd_hw_circuit_safe_phys5_cls` fixes the classification of `classes.tsv`: rows on exactly
    the 221 sampled channels, fields on the 244 ghosts.
  - `gcd_hw_circuit_safe_phys5_gen` also discharges H_FN by a decidable check against
    `Formal.Gen`'s generated cells, for 176 of the 221 sampled channels. It is replaced by a
    bit-level netlist correspondence (H_ZD_BITS) plus H_WIDTH.
  - H_FN stays assumed on 45 sampled channels: 38 bjoin, 4 compute join, the extui steer's 2
    branches, and out0.
- **Witnesses.**
  - 8t's run meets every hypothesis of phys5, with all outputs as ghosts
    (`gcd_hw_phys5_witness`). So does C-8x2's `chS`, on which the OLD models fail.
  - The sampled branch is exercised end to end only on a toy fork (C-8x3's `wI → wQ`, DAG row
    `wcheck`): `toy_cellP`, `toy_field`, `toy_rowG`. On that same run the old all-time field fails
    (`toy_old_fails`).
  - **No run of gcd_hw carries real rows**, so phys5_cls and phys5_gen are not witnessed on
    gcd_hw.

## Files

| file | what |
|---|---|
| `formal/lean/Formal/Net/OpsBusy3.lean` | `CellW` (`CellB` with explicit witnesses), `cellB_iff`; `wonOf`, `fnOf`, `fval`, `fcond`, **`FieldOf`** (one output's data field), `zdD` (zero-delay output bus); `fnOf_congr`, `fieldOf_modC_out`, `field_zd`; `reb`, **`HS`** (handshake half), **`cellW_reb`** (the one transfer lemma), `hs_of_cellW`, **`cellW_of_hs`**, `cellW_modS`; **`hs_protoT`**, **`hs_heldT_one`** |
| `formal/lean/Formal/Net/OpsBusy3Fn.lean` | `field_of_tx` (generic), `const_busy`; `stab_fork`, `stab_join`, `stab_steer`; **`mux_busy`** (kernel decide), `stab_mux`; `BusyN`, `busyN0..3`, **`muxn_busy`** (kernel decide), `stab_muxn`; `stab_amerge`; **`link_open_stable`**; **`Row`**, `Row.heldStep`, `field_fin`, **`fieldOf_row`** |
| `formal/lean/Formal/Net/CapstoneRefine4.lean` | `CellP`, `fieldOf_of_cellW`, `cellP_of_cellB`, `cellB_of_cellP`; **`gcd_hw_joint5`**, **`gcd_hw_cells_of_phys`**, **`gcd_hw_circuit_safe_phys5`**; `sampIds` (221), `isSampled`, `CellPcls`, **`gcd_hw_circuit_safe_phys5_cls`**, `samp_count`, `phys5_hyps_of_phys4`; `gcd_hw_phys5_witness`, `strict_phys5_hyps` |
| `formal/lean/Formal/Net/CapstoneRefine4Fn.lean` | `bitN`, `bv_bitN`; `genOut`, `muxBit`, `latBit`, **`dmCheck`/`latCheck`** (+ `_ok`, kernel decide against `Formal.Gen.Cells.bd_datamux_W3` / `bd_latch_W3`), `muxBit_ok`, `latBit_ok`; `DP`, `dpOf`, **`fnOK`**, `genBit`, `genBit_ok`, **`hfn_of_bits`**, `RowG`, `row_of_rowG`; `openIds`, **`fnOK_census`**, `fnOK_ops`, `CellPgen`, **`gcd_hw_circuit_safe_phys5_gen`** |
| `formal/lean/Formal/Net/CapstoneRefine4Wit.lean` | toy network `chT`/`kT` (C-8x3's `wI`, `wQ`): `toy_hs`, `toy_row`, `toy_cellP`, **`toy_field`**, `toy_cellB`, `toy_old_fails`, `toy_rowG`, `toy_fnOK`, `toy_row'` |
| `formal/lean/Wip/C8x4/sampled.py` | the sampled/ghost split from `Wip/C8x2/classes.tsv` (prints `sampIds`) |
| `formal/lean/Wip/C8x4/axioms.lean` | `#print axioms` of the headline theorems |

## The Lean, in plain words

### The two halves of a relaxed cell (`OpsBusy3`)

C-8x2's `CellB` holds two kinds of facts:
- the handshake fields (wires, C-elements, select LUTs). They read handshake wires and INPUT
  buses only.
- one data field per output.

To derive a field per channel, the two had to be separated.

- **`HS ch sv k w`** (handshake half) is `CellW` on the trace whose OUTPUT buses are replaced by
  their zero-delay values (`modC ch k.outsC (zdD ..)`). No handshake field reads an output bus, so
  for a `Disj` cell this says exactly "the handshake fields hold", and it needs no new structure
  per kind.
- **`FieldOf ch sv k w c`** is output `c`'s data field alone:
  - for a link, the open and hold fields;
  - for the arbiter stage, it reads the grant witness `w 1`, so the witnesses are explicit
    (`CellW`).
- **`cellW_reb`** is the single transfer lemma. The handshake fields survive any bus re-labelling
  that keeps the input buses, and the data fields are supplied per output. From it:
  - `cellW_of_hs`: half + all fields ⇒ relaxed cell;
  - `hs_of_cellW`: relaxed cell ⇒ half;
  - `cellW_modS`: half + the fields outside `S` ⇒ relaxed cell with `S` re-labelled.
- **`hs_protoT`**: the bounded protocol spec `OpProtoT` from the half alone (via C-8x3's
  `cell_protoT_B` on the re-labelled trace).
- **`hs_heldT_one`**: bounded structural bundling of ONE output from its own field. The other
  outputs of the same fork or steer may have no field: they are re-labelled to their zero-delay
  value, and C-8x3's `cellB_heldT` is applied.

### Composing lemmas (`OpsBusy3Fn`), piece (1)

`field_of_tx` (generic) takes:
- the row;
- "`zdBus` of transaction `m` = `F (r+1)` at its offer `r`" (H_FN + H_LAUNCH);
- "`F` constant over the transaction".

It concludes: the observed bus equals `F t` at every busy instant. Constancy per kind:

| kind | why the inputs (as the field reads them) are constant over an output transaction |
|---|---|
| fork, join, steer | 8w's FInv/JInv/SInv (input busy while output busy) + input `Held` |
| mux | **`mux_busy`** (decide, 8f's `tbl`): select busy and selected input busy while `z` busy; the select bus is `Held`, so the selection does not move; the selected input is `Held` |
| 3-input mux | **`muxn_busy`** (decide, 4 × 8192 states of 8l's code): same, under the field's own premise select < 3 |
| arbiter stage | C-8x3's `amerge_busy` + `amerge_won_stable`: `won` constant, the input it names busy and `Held` |
| link (open field) | **`link_open_stable`**: if the enable is high at `t` inside an output transaction, it was high all the way back to the offer and the input was busy (8l's table via `link_stepT`), so the input bus at `t` is the one at the offer. Hold field: the row's own `Held` (`heldStep_of_txwin`) |
| source, steerC | the function is a constant |

`Row ch sv k w c` packages, for a sampled output `c`:
- the tcheck row: `TxWin` + separation (a DAG or cert verdict);
- the launch values (`vin` = input buses, `vb` = index bit);
- **H_FN**: `zdBus m = fnOf sv k (vin m) (vb m)`;
- **H_LAUNCH**: the launch values are the input buses (index bit) at `r+1`, where `r` is the
  output's offer.

**`fieldOf_row`** dispatches over all 12 kinds; `sink` has no output.

### phys5, piece (2)

Why the field need not enter the joint induction:
- bundling of a SAMPLED channel comes straight from its own row (`Row.heldStep`, receiver rule
  up to `t`);
- bundling of a GHOST channel comes from its (by-construction) field and its inputs;
- the 26 roots use their certificate.

So **`gcd_hw_joint5`** (C-8x3's `net_joint` with these three rules, inner induction on
`rankL3`) gives protocol and `Held` everywhere without any sampled field. After that, every
sampled field follows from `fieldOf_row` at all times (**`gcd_hw_cells_of_phys`**). That is
H_CELLS_B, and C-8x3's `gcd_hw_circuit_safe_phys4` finishes.

The task suggested putting the field at step `t` inside the induction. It turned out
unnecessary: no step of the induction reads a sampled field.

- `CellP` (any channel may be ghost or sampled) is the most general form.
- `CellPcls` fixes the split of `classes.tsv`: `sampIds` = consumer is a latch D with data pins,
  a steer / mux / 3-input-mux select, or the environment reading out0, 221 channels
  (`Wip/C8x4/sampled.py`). The other 244 are ghosts: combinational consumer, sink, or a W = 0
  stage.
- `phys5_hyps_of_phys4`: phys4's hypotheses imply phys5's. phys5 assumes strictly less, but only
  the `cls`/`gen` forms force rows on sampled channels.

### H_FN against the generated cells (`CapstoneRefine4Fn`)

H_FN mixes "the routed data path is the library cell" (a correspondence) with "the library cell
computes the Ops function". The second part is now a checked fact.

- **`dmCheck`** reads `Formal.Gen.Cells.bd_datamux_W3`:
  - the pin maps and INITs (`lutIs`) of `pair[0].u` (LUT6_2, bits 0/1 on O5/O6) and `odd.u`
    (LUT3);
  - exhaustively, that their tables give `s ? b : a`.
- **`latCheck`** does the same for `bd_latch_W3`: transparent when enabled (for every stored bit),
  opaque otherwise. Both are proved by kernel `decide` (`dmCheck_ok`, `latCheck_ok`).
- **`fnOK k`** (per operator, by datapath class `dpOf`):
  - wire for fork branches;
  - wire minus the cond bit for a data steer with `fd = var 0`;
  - `latCheck` for links;
  - `dmCheck` for muxes;
  - `false` otherwise.
- **`genBit`** evaluates bit `j` of a `W`-bit instance with those generated tables. Bits pair
  into LUT6_2 O5/O6, and an odd last bit uses the single LUT, as the W=3 instance does.
- **`hfn_of_bits`**: `fnOK k` + **H_ZD_BITS** + **H_WIDTH** ⇒ H_FN. Here H_ZD_BITS says the
  obligation's zero-delay data bit `j` = `genBit`, and H_WIDTH says the value fits `data.length`
  bits.
- **`fnOK_census`** (kernel `decide`) runs `fnOK` on the producer of every sampled channel. It
  passes on 176 of 221; `openIds` lists the 45 others:
  - 38 `bjoin` (compare+data);
  - 4 compute `join` (51, 116, 344, 410);
  - chans 71/74, the one data steer whose projection is `extui`;
  - out0 = 416 (the 3-input mux, `bdc_muxn3`, has no generated netlist in `Formal.Gen`).
- **`fnOK_ops`**: over all 367 operators it passes on 268.
- `RowG` is `Row` with H_FN replaced by H_ZD_BITS + H_WIDTH; `row_of_rowG` converts it.
- **`gcd_hw_circuit_safe_phys5_gen`**: `RowG` on the 176 checked sampled channels, `Row` on the
  45 open ones, fields on the ghosts.

## Hypotheses and non-vacuity

| name | where | content | non-vacuity |
|---|---|---|---|
| H_CELLS_P (handshake half `HS`) | phys5 / cls / gen | relaxed handshake fields per operator, on the observed run | 8t's run (`gcd_hw_phys5_witness`), `chS` (`strict_phys5_hyps`); toy fork (`toy_hs`) |
| ghost field (`FieldOf`) | per ghost channel | the observed bus of a channel no gate samples IS the zero-delay value (a definition of the observation, not a measurement) | 8t's run (all 465 channels as ghosts) |
| `Row` = tcheck row + H_TXWIN + H_FN + H_LAUNCH | per sampled channel (cls: all 221; gen: the 45 open) | as above | toy only (`toy_row`, C-8x's `wrun`/`wcheck`); **none on gcd_hw** |
| `RowG` = row + H_TXWIN + H_ZD_BITS + H_WIDTH + H_LAUNCH | gen: 176 sampled channels | H_FN replaced by a bit-level netlist correspondence | toy only (`toy_rowG`); **none on gcd_hw** |
| H_START_ONCE | all | as 8s | 8t (`w_start_once`) |
| H_TCHECK_ROOT (`BCert`, 26 roots) | all | as phys4 | 8t with `exempt` (as 8x/8x2/8x3); `dag` constructor on the toy (`wQ_bcert`) |
| `Disj` | per operator | no self-loop | checked (`disj_ok`) |

Which run would witness phys5_cls on gcd_hw: a run with real per-channel tcheck rows (a routed
build, its obligations as `Netlist`s with `TxWin` windows). 8t's run is zero-delay and has no
rows. Building it is the next step; it needs 10m/10n's obligation import.

## Not covered

- **No gcd_hw run is shown to meet phys5_cls / phys5_gen.** The `Row` branch is exercised on a
  2-channel toy only. phys5 itself is witnessed on gcd_hw only with every channel a ghost, which
  is the old H_CELLS_B in another form.
- **H_ZD_BITS is the remaining correspondence.** It says the obligation netlist's zero-delay data
  bits are the library slice evaluated on the launch bits, and it is not checked against the
  routed netlist. `genBit`'s bit pairing for W > 3 is modelled on the generated W=3 instance; no
  generated instance of the full bus width is checked.
- **H_FN stays assumed on 45 sampled channels.** These are bjoin/join arithmetic, extui, and the
  muxn on out0. Doing them needs a generated netlist of bdc's arithmetic: the comparators and
  subtractors are CARRY4 chains. Formal.Gen has CARRY4 semantics but no gcd_hw datapath netlist.
- **H_WIDTH** (Ops values fit the bus) is stated per row and not derived. It follows from 32-bit
  values plus the cond bit, but that is not proved here.
- **The ghost classification is data.** `sampIds` comes from C-8x2's `classes.tsv` (consumer
  type). It is not re-derived from the netlist in Lean.
- Unchanged from phys4: 4 arbiter-stage roots and the muxn select (chan 415) need rows (415's row
  is now a sampled-channel row, still missing on every route: 8w). Liveness and timing are not
  covered. Every root certificate in every gcd witness is `exempt`.

## Fidelity

| model | grade | why |
|---|---|---|
| `HS` + `FieldOf` split, `cellW_reb` | A (proved) | `CellB ↔ ∃ w, HS ∧ fields` for `Disj` cells (`cellW_of_hs`, `hs_of_cellW`, `fieldOf_of_cellW`) |
| `fieldOf_row` (all kinds) | A (proved) | from 8f/8j/8l's reachable sets (re-checked by kernel decide) and C-8x's `sampled_eq_zd` |
| `gcd_hw_joint5`, phys5 | A (proved) | given its hypotheses |
| ghost field | B | a definition of the unobserved bus, per channel; legitimate only if no gate samples it (`classes.tsv`, not re-derived) |
| `dmCheck`, `latCheck` | A (decided) | against yosys's output for `cells/rtl` at W=3 (`Formal.Gen.Cells`) |
| H_ZD_BITS, H_WIDTH, H_LAUNCH, H_TXWIN | C | stated; toy witness only |

## Check log (2026-10-29)

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/OpsBusy3.lean Formal/Net/OpsBusy3Fn.lean Formal/Net/CapstoneRefine4.lean \
      Formal/Net/CapstoneRefine4Wit.lean Formal/Net/CapstoneRefine4Fn.lean
    [check] textual scan
    [check] lean Formal/Net/OpsBusy3.lean
    [check] lean Formal/Net/OpsBusy3Fn.lean
    [check] lean Formal/Net/CapstoneRefine4.lean
    [check] lean Formal/Net/CapstoneRefine4Wit.lean
    [check] lean Formal/Net/CapstoneRefine4Fn.lean
    [check] axiom audit
    [audit] 5061 declarations checked
    [check] OK

`Wip/C8x4/axioms.lean`:
- phys5, phys5_cls, phys5_gen, `gcd_hw_joint5`, the witnesses, `fieldOf_row`, `toy_field` ⊆
  {propext, Classical.choice, Quot.sound};
- `fnOK_census`, `dmCheck_ok`, `latCheck_ok`: {propext};
- `muxn_busy`: {propext, Quot.sound};
- `mux_busy`: none.

No sorry, no native_decide. All table checks are `decide +kernel`.

Oleans needed before `check.sh` (targeted builds, Mathlib-free closure; `Formal.Gen` imports
only `Formal.Core.Lut`/`Kleene`):

    ./slot.sh lake build Formal.Net.CapstoneRefine3 Formal.Net.CapstoneRefine3FnWit Formal.Gen.Cells

`OpsBusy3Fn` takes about 35 s (the `muxn_busy` decides); the others take a few seconds each, and
`CapstoneRefine4Fn` about 10 s.
