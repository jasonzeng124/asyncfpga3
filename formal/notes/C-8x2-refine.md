# C-8x2: busy-gated gate models; the physical gcd_hw capstone without H_ZD_AGREE; H_DERIVED made structural

Shard C, probe 8x2, 2026-10-29. About 3.5 h. Follows C-8x (`notes/C-8x-refine.md`).

STATUS: DONE for the two asks, with one new named hypothesis (H_SEND) for the H_DERIVED part.
All six new Lean files pass `./check.sh` (log at the end). No existing file was edited.

## Verdict

- **H_ZD_AGREE is gone.** Every cell data field is now required only while the cell's OUTPUT
  channel is mid-transaction (`OpsBusy.CellB`, implied by the old `Cell`: `cell_relax`). On these
  relaxed models the capstone still holds with the same token equations (`cell_op_B`), so the
  physical observation itself is the Ops trace: `gcd_hw_circuit_safe_phys2` assumes H_CELLS_B on
  the observed run, H_START_ONCE, H_RECV and a `BCert` per channel. There is no second
  (zero-delay) trace and no agreement hypothesis.
- **H_DERIVED, structural part: proved.** On the relaxed fields, bundled inputs give a bundled
  output for fork, join/compute, steer, link and source (`*B_held`). The 434 channels produced by
  those kinds form a ranked dependency graph (kernel `decide`) whose 31 roots are the outputs of
  the muxes, the 3-input mux and the arbiter stages. `gcd_hw_circuit_safe_phys3` needs
  certificates on those 31 roots only, plus **H_SEND** (sender rule on every channel).
- **New tcheck rows needed: exactly 2 channels** (data below): chan 463 (`ucontrol_merge12.uarb1`,
  the 3-input merge's stage-1 bus, a root with no row) and chan 415 (umux21's select, sampled by
  the muxn select LUT, no E row on any route). Every other sampled channel is backed by an
  existing I/H, E or A row; 223 channels are ghosts (their consumer never samples the bus).
- **What carries the timing now:** the relaxed field of each cell whose output is SAMPLED
  (253 channels) is a physical claim: "while the output is busy, its sampled bus equals the cell
  function of its inputs". It is C-8x's `sampled_eq_zd` (proved, from the tcheck row) plus H_FN
  (LUT function of the obligation netlist = the Ops cell function) plus the inputs' own
  agreement. H_FN is open (not a tcheck question).

## Files

| file | what | |
|---|---|---|
| `formal/lean/Formal/Net/OpsBusy.lean` | relaxed structures `ForkB JoinB SteerB MuxB MuxNB AMergeB LinkB SrcB`, `CellB`, `Disj`, **`cell_relax`**, `modC`, `AgrOut`, `winner_congr`, **`proto_of_mod`**, **`data_of_mod`**, `eqn_mod` | |
| `formal/lean/Formal/Net/OpsBusyLoc.lean` | `loc_fork loc_join loc_steer loc_mux loc_muxn loc_amerge loc_link loc_src`, `latchD`, `forced_mod_amerge`, **`cellB_loc`** | |
| `formal/lean/Formal/Net/OpsBusyHeld.lean` | **`cell_proto_B`**, **`cell_op_B`**, `rel`, `*.toOld`, `AMergeB.winner_eq`, **`amerge_data_upto_B`**, **`forkB_held joinB_held steerB_held linkB_held srcB_held`**, `StructK`, **`cellB_held`** | |
| `formal/lean/Formal/Net/CapstoneRefine2Cut.lean` | `disj_ok` (kernel decide), `gcd_hw_init_B`, `gcd_hw_protocol_B`, `forc_atB agr_atB rise_curB mainB`, `gcd_hw_forcedB`, `gcd_hw_circuit_safeB`, **`gcd_hw_circuit_safe3B`** | |
| `formal/lean/Formal/Net/CapstoneRefine2.lean` | **`gcd_hw_circuit_safe_phys2`**, `rootIds`, `rankL`, `struct_chk` (kernel decide), **`held_struct`**, **`gcd_hw_circuit_safe_phys3`**, `gcd_hw_phys2_witness`, `gcd_hw_phys3_witness` | |
| `formal/lean/Formal/Net/CapstoneRefine2Strict.lean` | `cellB_congr`, `chS` (8t's run with chan 3's idle bus garbled), **`strict_old_fails`**, `cells_S`, `held_S`, **`strict_phys2_hyps`**, `strict_out0` | |
| `formal/lean/Wip/C8x2/classify.py` | channel classification (Held class, rank, what the consumer does with the bus, row needed); writes `classes.tsv`; `--lean` prints the Lean tables | |
| `formal/lean/Wip/C8x2/classes.tsv`, `lean_tables.txt` | its output (465 rows) | |


## The Lean, in plain words

### 1. The relaxed gate models (`OpsBusy`)

Each old data field becomes "when the output channel is mid-transaction (`inTx`)":

| cell | old field (every `t`) | relaxed field |
|---|---|---|
| fork | `o.dat t = a.dat t` | `inTx o t → o.dat t = a.dat t` |
| join / compute | `o.dat t = g (ins at t)` | `inTx o t → ...` |
| steer | `(out b).dat t = f (j.dat t)` | `inTx (out b) t → ...` |
| mux / muxn / arbiter stage | `z.dat t = ...` | `inTx z t → ...` |
| link | `c t → o.dat t = i.dat t`; `¬c (t+1) → o.dat (t+1) = o.dat t` | `c t → inTx o t → ...`; `¬c (t+1) → inTx o t → inTx o (t+1) → ...` |
| source | `z.dat t = v` | `inTx z t → z.dat t = v` |

The handshake fields are unchanged. Fields that read an INPUT bus (steer `lut`, mux `cj0/cj1`,
muxn `cj`) are unchanged too; they read the select only while the select's request is high.

- `cell_relax`: old ⇒ relaxed, for every kind. So every theorem below has a WEAKER cell hypothesis
  than its C-8m/8s/8x counterpart.
- `Disj k`: no channel is both an input and an output of operator `k`. `disj_ok` checks it for
  all 367 gcd_hw operators (kernel `decide`).

### 2. Relaxed cells are Ops operators (`cellB_loc`, `cell_op_B`)

- **`cellB_loc`.** Take a relaxed cell and re-label its OUTPUT buses with the zero-delay value of
  the cell (`modC`; the handshake wires and the input buses are untouched). The re-labelled trace
  satisfies the OLD gate model, and the re-labelling equals the real bus at every busy instant of
  the output (`AgrOut`). For the link the zero-delay value is the latch content `latchD`, and
  `AgrOut` needs the four-phase protocol on its two channels: an output offer happens only with
  the latch enable high (8l's table), so a busy stretch of the output starts with the latch open.
- **`proto_of_mod`, `data_of_mod`.** `OpProto` and `OpData` of the re-labelled trace transfer
  back to the real one. The reason: an Ops operator reads an output bus only at `r+1` for an offer
  `r`, which is a busy instant, and reads its input buses only through `Held` and the offer
  values, which the re-labelling does not touch.
- **`cell_op_B`.** Relaxed cell, `Forced`, `Dist`, `Disj` ⇒ `OpProto ∧ OpData` with the SAME token
  equations `Eqn` as 8m's `cell_op`. **`cell_proto_B`**: the protocol half needs no forcing.
- **`amerge_data_upto_B`.** 8r's arbiter data spec up to an offer, for a relaxed stage. The
  winner stream is unchanged by the re-labelling (`winner_congr`, `AMergeB.winner_eq`).

### 3. The capstone on relaxed cells (`CapstoneRefine2Cut`)

- **`gcd_hw_circuit_safe3B`.** For `a, b < 2^31`, every run of the 465-channel network whose
  operators meet `CellB`, whose channels are `Held` and whose `start` is offered at most once,
  latches only `Nat.gcd a b` on `out0` (both conclusions of `gcd_hw_circuit_safe3`).
- The proof is 8r's `main` induction re-run:
  - `cell_op_B` replaces `cell_op` for the operator data;
  - `amerge_data_upto_B` replaces the arbiter's data spec;
  - the old-structure views `*.toOld` (output bus replaced, wires unchanged) feed the
    handshake-only lemmas `fork_strict`, `join_strict`, `link_strict`, `steer_strict` and
    `offer_pending`.
  - 8s's token-level `gcd_hw_walk` is reused as is.

### 4. The physical capstone without H_ZD_AGREE (`CapstoneRefine2`)

**`gcd_hw_circuit_safe_phys2`.** The Ops trace `ch` IS the observation: per channel, the
handshake wires and the observed bus. The hypotheses are:
- **H_CELLS_B**: the relaxed gate models on `ch`;
- **H_START_ONCE**: as in 8s;
- **H_RECV**: the receiver rule, as in 8x;
- **H_TCHECK**: `∀ c, BCert (ch c)`, C-8x's certificate: a tcheck DAG row with H_TXWIN, a cert
  row with H_TXWIN, or `exempt`.

It concludes the same as `gcd_hw_circuit_safe3`. Compared with 8x's `gcd_hw_circuit_safe_phys`:
- H_ZD_AGREE is gone, and so is the pair (`ch`, `pdat`);
- H_CELLS is weakened to H_CELLS_B.

### 5. H_DERIVED made structural (`held_struct`, `gcd_hw_circuit_safe_phys3`)

- **`cellB_held`** (generic). Take an operator of kind fork, join/bjoin, steer, link or source,
  with the protocol on its channels and its inputs `Held`. Then its outputs are `Held`. The
  proofs:
  - fork, join, steer: 8w's handshake invariants FInv/JInv/SInv ("output busy ⇒ input busy")
    plus the relaxed field;
  - link: 8l's table (a busy step with the latch open had it open one step earlier, and the
    input busy at both instants) plus the relaxed open/hold fields;
  - source: the relaxed constant field.

  No all-time field is needed. 8w's `*_held` were proved only for the old fields.
- **`struct_chk`** (kernel `decide`). Every channel not in `rootIds` (31 ids) has a structural
  producer, and every input of that producer has a smaller rank (`rankL`, max rank 25).
- **`held_struct`.** Given H_CELLS_B, the protocol on every channel and `Held` on the 31 roots,
  every channel is `Held`. Strong induction on the rank.
- **`gcd_hw_circuit_safe_phys3`.** The hypotheses are H_CELLS_B, H_START_ONCE, H_RECV, **H_SEND**
  (`∀ c t, SendStep (ch c) t`) and `BCert` on the 31 roots only. The conclusion is again
  gcd-only on `out0`.

**Why H_SEND appears.** The structural step needs the protocol on all channels.
- The capstone derives the protocol from `Held` (`net_protocol`; the steer/mux/muxn select
  invariants need their input `Held`).
- Using that derivation here would be circular.
- 8x already assumed H_RECV for the same reason; H_SEND is its sender-side twin.

Removing both needs a time-bounded `net_protocol` ("Held before t ⇒ protocol up to t"), which
would mean re-proving the steer/mux/muxn invariants with `Held` up to `t`. Not done.

## Hypotheses and non-vacuity

| name | where | content | non-vacuity |
|---|---|---|---|
| H_CELLS_B | phys2, phys3, safe3B | relaxed gate models on the observed run | 8t's run (`cell_relax w_cells`) in `gcd_hw_phys2_witness` / `phys3_witness` |
| H_START_ONCE | all | as 8s | 8t (`w_start_once`) |
| H_RECV | phys2, phys3 | receiver rule on every channel | 8t, via `gcd_hw_protocol` |
| H_SEND | phys3 | sender rule on every channel | 8t, via `gcd_hw_protocol` |
| H_TCHECK (`BCert`) | phys2: all 465; phys3: 31 roots | C-8x certificates | 8t with `exempt` only (as in 8x); the `dag` constructor on one channel: 8x's `refine_witness` |
| `Disj` | per operator | no self-loop | checked (`disj_ok`) |

**Strictness (`CapstoneRefine2Strict`).** The joint witnesses above use 8t's zero-delay run,
which already meets the OLD models. To check that the relaxation actually matters, `chS` is 8t's
run with one change: while channel 3 (`ufork0` → sink) is idle, its bus shows `start`'s bus + 1.
- `strict_old_fails`: `¬ ∀ o, Cell chS ..`. Fork 0's all-time field breaks at `t = 0`.
- `strict_phys2_hyps`: every hypothesis of `gcd_hw_circuit_safe_phys2` holds on `chS`
  (certificates `exempt`).
- `strict_out0`: so the relaxed theorem applies to `chS`. The old capstone could only take it
  through a separate zero-delay trace plus H_ZD_AGREE.

The garbled channel is a sink branch, so this shows strictness, not a physically interesting run.
The roots' certificates in all witnesses are `exempt`; tcheck's `dag` constructor is exercised
only by 8x's one-channel `refine_witness`.

## H_DERIVED: the classification (data)

`Wip/C8x2/classify.py` reads `CapstoneNet.lean` (the 367 operators) and 8w's
`tools/oblgen/out/obligations.tsv`, and writes `Wip/C8x2/classes.tsv`, one row per channel. The
columns are: producer, consumer, bdc instance, 8w expectation, Held class, rank, what the consumer
does with the bus, and which row backs it.

**Held class** (what `held_struct` / `phys3` needs):

| class | n | how `Held` is obtained |
|---|---|---|
| structural: link output | 175 | `linkB_held` from the link input |
| structural: fork branch (forkG 52, forkH 70) | 122 | `forkB_held` from the parent |
| structural: steer output (steerD 58, steerC 18) | 76 | `steerB_held` from the joined input |
| structural: join / bjoin output | 58 | `joinB_held` from the inputs |
| structural: source | 3 | `srcB_held` |
| **root (BCert)**: mux 21, muxn 1, arbiter stage 9 | 31 | tcheck row: A exists for 30; **chan 463 has none** |

All 376 channels that 8w classed derived/ghost are structural. So are 20 of 8w's 50 A-class
channels (compute outputs: chans 8, 26, 51, 54, 107, 111, 115, 116, 118, 188, 194, 244, 250, 263,
297, 298, 344, 386, 393, 410). In the relaxed model their `Held` follows from their inputs. Their
A row is still needed, but for the relaxed FIELD (below), not for `Held`.

**What the consumer does with the bus**:
- 253 channels are sampled:
  - 175 by a latch D;
  - 38 by a steer select;
  - 21 by a mux select;
  - 1 by the muxn select;
  - 18 go to the environment, of which only out0 (chan 416) is read.
- 212 channels go to combinational consumers (bjoin 76, mux data 45, join 29, forkH 22,
  forkG 22, amerge 18).

**Which row backs each channel**:

| row need | n |
|---|---|
| ghost: the consumer never samples the bus, so the observed bus is the zero-delay value by definition and the producer's relaxed field holds by construction | 208 |
| ghost: W = 0 control link stage, no data pins (8w's `vacuous:W=0`) | 15 |
| field backed by the stage's I/H rows (exist) | 151 |
| field backed by the steer select's E row (exists) | 38 |
| field backed by the mux select's E row (exists; 8w: band-only failures on some routes) | 21 |
| root: `Held` from an A row (exists; 8w: seed 3 `ushrsi1` fails fastG, and some F/Fd drains fail band-only) | 30 |
| **NEW ROW NEEDED** | **2** |

**The two channels that need new tcheck rows** (for 10m; this probe does not touch
`formal/tools/tcheck`):

| chan | bdc instance | why |
|---|---|---|
| 463 | `ucontrol_merge12.uarb1` (stage 1 of the 3-input control merge, bus `acc251`) | a root: its `Held` needs a certificate, and no rule covers it (C-8l: no matched delay between R0 and acc_req). Alternative: prove an `amergeB_held` on the relaxed fields (stage-1 grant stable while `acc` is busy), which would make it structural |
| 415 | `ulink_n_index_97.many.stage[1].u` → umux21 select | sampled by the muxn select LUT; the muxn's relaxed field `cj`/`dat` reads it; no E row exists on any route (8w) |

## How the timing reaches the relaxed fields (what remains open)

For a SAMPLED channel `o`, the relaxed field of its producer says that at every busy instant
`t` of `o`, the sampled bus `P.dat t` equals `F (input buses at t)`. It decomposes into three
pieces:
1. **`P.dat t = zdBus runs data k`.** C-8x's `sampled_eq_zd` (proved), given `o`'s tcheck row
   (DAG or cert) and H_TXWIN.
2. **`zdBus = F (launch values of transaction k)`.** This is H_FN: the obligation netlist's LUT
   functions compute the Ops cell function. It is a per-cell-type functional check against the
   netlist tcheck analysed. It is NOT a timing question. Open.
3. **Launch values of transaction `k` = input buses at `t`.** The inputs are busy while `o` is
   busy (JInv/FInv/SInv, the link table), and they are `Held`, so they show their offer values.
   The offer values are the launch values of `o`'s obligation when the inputs are themselves
   sampled channels (piece 1 for them) or ghosts (by construction). That is C-8x's R3 (latch)
   and R4 (select) in this setting. Not mechanised: no lemma composes 1-3 into a `CellB` field.

So the remaining refinement content is H_FN (per cell type) plus H_TXWIN per sampled channel. Both
are precise and local. The cross-channel ordering argument that C-8x's H_ZD_AGREE needed (a
zero-delay trace whose buses change only when no downstream channel is busy) is gone. It is
replaced by the structural `held_struct` plus each channel's own row.

## Fidelity

| model | grade | why |
|---|---|---|
| relaxed fields `CellB` | B | strictly weaker than 8f/8j/8l's (`cell_relax`); they say nothing at idle instants, matching what `sampled_eq_zd` can deliver |
| observed bus of a ghost channel | B | a definition (zero-delay value), not a measurement; legitimate because no gate samples it, but it must be stated per channel (`classes.tsv`) |
| `held_struct` | A (proved) | given H_SEND/H_RECV and the 31 root certificates |
| H_SEND, H_RECV | C | protocol facts the old capstone derives; here they are assumed to break the circularity |

## Check log (2026-10-29)

Output of the six-file run below:

    [check] lean ... (all 6 files, no error; only deprecation warnings)
    [audit] 4273 declarations checked
    [check] OK

Axioms ⊆ {propext, Classical.choice, Quot.sound}. No sorry, no native_decide; the table checks are
kernel `decide +kernel`. Commands:

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/OpsBusy.lean Formal/Net/OpsBusyLoc.lean Formal/Net/OpsBusyHeld.lean \
      Formal/Net/CapstoneRefine2Cut.lean Formal/Net/CapstoneRefine2.lean \
      Formal/Net/CapstoneRefine2Strict.lean
    python3 lean/Wip/C8x2/classify.py          # summary + classes.tsv
    python3 lean/Wip/C8x2/classify.py --lean   # the rootL / rankL tables used in CapstoneRefine2

`CapstoneRefine2` imports `CapstoneRefineNet` (8x), `CapstoneWalk` and `CapstoneWitness3`. Their
oleans were built with targeted `./slot.sh lake build Formal.Net.<module>`. The kernel `decide`s
(`disj_all1..3`, `struct_all`) dominate the build time (`CapstoneRefine2Cut` ≈ 220 s).
