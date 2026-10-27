# C-11c: bitstream import scaled to a bd_link stage + a bd_arbiter

Track 11, probe c. Shard C. 2026-10-27.

## Verdict

**Works.** 11b's bitstream import scales from the C-element pair to a design with
one `bd_link #(.W(3))` stage and one `bd_arbiter`, sharing `rst`. That is 7 LUT sites,
3 of them fractured LUT6_2 with live O5 and O6, 9 inputs, 10 outputs, and internal
state nets that no port shows. The design was routed on 4 seeds. For each seed, Lean
proves by `decide` that the physical netlist read back from the `.bit` equals 11a's
yosys-imported netlists of the same cells (`Formal/Net/Import/Cells.lean`, used
unchanged) up to a renaming of state nets. Each proof enumerates only 16 + 128 + 128 = 272
cases, because the check is split per instance over a proved support bound. Lean time is
about 100 s user for the 4 seeds plus a negative control, with plain `decide` (no `+kernel`).

**Primitives that appeared:** LUT6 (O6 only), and LUT6_2 with **O5 out through `?OUTMUX.O5` →
`?MUX`** next to O6 through the direct `A..D` pin. The site-feature census also shows
`COUTMUX.O6`, the CMUX output mux selecting O6 (not CARRY4). **No MUXF7/F8, CARRY4, FF,
LUTRAM, DSP or clocking** appeared on any seed. The importer now refuses all of these
loudly, by category (see below). Constant pins: A6 = VCC on every fractured LUT6_2. The
router also ties some unused pins to VCC instead of GND (e.g. ugrant A4 = 1 on seeds 3
and 4). The physical INIT accounts for this, and the proof covers it.

## What checks (run it)

    formal/tools/fasm2lean2/check.sh          # 2 min 24 s wall (2 min 5 s user) from the committed fixtures
    formal/tools/fasm2lean2/route.sh SEED     # re-route one seed (~13 s), then check.sh

Last run of `check.sh`: **PASS** (log excerpt at the end). It does the following:
0. Checks the stamps: `cells/verify/toolchain.sh` ok, **nextpnr sha256 9c732bc6303458df**,
   and `fasm_audit.py` PASS on every seed.
1. Seeds 1..4: the netlist from nextpnr's FASM equals the netlist from the FASM read back
   from the `.bit` (xc7frames2bit → bitread → bit2fasm). The committed
   `Formal/Net/FasmLink/S<n>.lean` equals what `gen.py` regenerates from the read-back
   (drift check).
2. `compose.py`: the Lean composition `LinkArb.insts` (11a's per-cell netlists plus the
   wiring) equals yosys's own flattening of `link_arb`. That means the same 7 LUT cells,
   INITs and type, and the same canonical source on every pin and output, seen through
   IBUF/OBUF. A wrong binding fails here (tested: en bound to `req_in` → 2 DIFFs, exit 1).
3. Lean: `Formal/Net/FasmLink/{Basic,LinkArb,S1..S4,Proofs}.lean` compile with core Lean
   only (no Mathlib), `scan.py` is clean, and `#print axioms` shows only `propext`
   (+ `Quot.sound`/`Classical.choice` from core list lemmas).
4. Negative controls, injected in the BITS of seed 1 by `mutate2.py` and extracted the same
   way into `Wip/C11c/`:
   - **MutInit**: one INIT bit of `ugrant`'s LUT6_2 flipped (bit 36, the lowest address
     consistent with its tied pins and A6 = 1, so it changes O6 = g2). Result: `¬ Correct`
     proved (`Design.not_correct` + `decide`).
   - **MutPips**: the INT pip `INT_R_X29Y95.IMUX7.NW2END_S0_0` (ugrant pin A1 = r1) is
     re-pointed to `IMUX7.FAN_BOUNCE_S3_4`. That is a legal pip whose node carries `A0`, a
     different signal net. Result: `¬ Correct` proved. The physical LUT now reads a signal
     that the logical ugrant does not read, and the support argument catches it.
   - **MutShort** (second driver on IMUX7), **MutFF** (`AFF.ZINI` in that slice),
     **MutCarry** (`CARRY4.ACY0`): fasm2lean2 refuses the FASM with the category named.
   - `wrong_rho_caught` (in `Proofs.lean`): seed 1's renaming with arbiter `q` ↔ `ua1.q`
     swapped is rejected. The renaming is checked, not trusted.

## Theorems (namespace `Formal.Net.FasmLink`)

| name | statement |
|---|---|
| `Design.check_sound` | `D.check = true → D.Correct` (generic, any design) |
| `Design.check_complete`, `Design.not_correct` | `D.Correct → D.check = true`; so `check = false` (decided) proves `¬ Correct` |
| `Design.peval_congr` | physical evaluation reads only `psupp` (the lemma that makes per-instance enumeration sound) |
| `LinkArb.seed1_correct` .. `seed4_correct` | `(design S<n>.net S<n>.ports S<n>.rho).Correct` |
| `LinkArb.wrong_rho_caught` | negative control on the witness |
| `LinkArb.grant_exclusion`, `grant_exclusion_s1..s4` | transferred through 11a's `bd_arbiter_outs_spec`: for every route whose bits are `Correct`, the grant PORTS g1, g2 that the bitstream drives are never both 1 (binary, any state, any inputs) |
| `LinkArb.c2n_iface`, `latch_iface`, `arbiter_iface` | pin the imported port and state order that the binding relies on |

`Design.Correct` (see `Basic.lean`) holds for every valuation `val : Sig → Bool` of the
top-level inputs and of every logical state net (bd_link: `c`, `q[0..2]`; bd_arbiter:
`ua1.q`, `ua2.q`, `q`). It requires:
- **next**: 11a's `Netlist.next boolSem` of each imported cell netlist equals, state by
  state, the excitation of the physical LUT output `rho[k][j]`. That is its physical INIT
  on its physical pins A1..A6. Each pin reads a port, a tie, a renamed state, or any other
  physical LUT recursively (combinational: ugrant's g1/g2 feeding `ua1`/`ua2`, ustate's R0).
- **outs**: 11a's `Netlist.outs` equals, port by port, the value of the output port the
  bits drive. `c` drives both `req_out` and `ack_in`.
- **structure**: `rho` is injective, names only existing LUT outputs, and has one entry
  per logical state. The physical output ports are exactly the logical ones. There are as
  many physical LUT sites as logical LUT cells (7). Every physical input port is a
  logical one.

**Decide size.** Per instance, the check enumerates the dedup'd support (logical inputs and
states plus the physical support of every compared source): **4 signals for `lnk.ctl.u`
(16 cases), 7 for `lnk.lat` (128), 7 for `arb` (128)**, the same on all four seeds.
Without the per-instance split, a global enumeration would need 2^16. Before dedup, the
support list had repeats and gave about 2^30, which would never finish. That was the
first attempt; it was killed and fixed. Runtime: `Proofs.lean` takes **~95 s user** for the
4 seed proofs, `wrong_rho_caught` and the transfer theorems (4 min wall with slot waits).
One seed alone takes ~20 s user with plain `decide` and ~11 s with `decide +kernel`. Plain
`decide` was kept: it is not `native_decide`, and nothing needed `+kernel`.

## Files

- `formal/tools/fasm2lean2/`
  - `link_arb.v`, `link_arb.xdc`: the design (cells verbatim from `cells/rtl/`) and 19 bank-35 pins.
  - `route.sh SEED`: the 11b flow (toolchain.sh first; `synth_xilinx -flatten -nosrl
    -nolutram -nobram -noclkbuf`; nextpnr `--ignore-loops --freq 100 --seed`; fasm_audit;
    frames → bit → bitread/bit2fasm). It also writes `fixture/link_arb_s<n>.bels` (cell →
    BEL from the routed JSON: the renaming hint) and `fixture/link_arb.synth.json` (the
    top module of the yosys netlist, trimmed from 10 MB to 9 kB).
  - `fasm2lean2.py`: a copy of 11b's `fasm2lean.py`, extended (see below).
  - `gen.py`: fasm2lean2 plus `rho` from the hint and `Cells.lean`'s state nets → `S<n>.lean`.
  - `compose.py`, `mutate2.py`, `check.sh`.
  - `fixture/`: FASM, read-back FASM, toolchain stamp, audit, SDF, bit sha256 and bels per seed.
  - `build/`: large outputs, ignored by the repo's `.gitignore` pattern `build/` (checked
    with `git check-ignore`).
- `formal/lean/Formal/Net/FasmLink/Basic.lean` (generic semantics, check, soundness and
  completeness), `LinkArb.lean` (the logical composition), `S1..S4.lean` (GENERATED),
  `Proofs.lean`.
- `formal/lean/Wip/C11c/Mut*.lean`: written by check.sh (negative controls; they are not claims).

## Importer extensions over 11b (fasm2lean2.py)

- **Every site feature is classified.** A whitelist (`SITE_OK`) covers what the model
  handles or what is a printed default for a used site (NOCLKINV, PRECYINIT.C0,
  SLICEM DI1MUX, `?OUTMUX.O5/O6`, IOB standard/drive/slew/pull/termination, IOI bypasses,
  and the unused IDELAY/ISERDES/IFF/OSERDES defaults bit2fasm prints). Anything else is
  refused with its category: FF/latch, CARRY4, MUXF7/F8, LUTRAM/SRL, other OUTMUX, a
  registered/inverted IOI path, clocking, DSP/BRAM, or "unclassified". 11b only refused
  these when they appeared as a pin's SOURCE. A configured but bypassed FF or carry was
  invisible there.
- **IOI bypass inversion is checked.** The ILOGIC D→O pseudo pip is taken only with
  `ZINV_D` set (Z-sense: D not inverted). The OLOGIC D1→OQ pseudo pip is taken only with
  `OMUX.D1` and without `IS_D1_INVERTED`. 11b took the OLOGIC bypass unconditionally and
  ignored ILOGIC inversion. Both were right on its fixtures, but the 11b code did not check them.
- XDC port names with brackets (`{data_in[0]}`): 11b's regex would have read `data_in[0`.
- `--ns` takes a full namespace. Generic LUT6_2 support needed no change: 11b's `o5B`
  (INIT[31:0] on A1..A5) and the `?OUTMUX.O5` source decoding already covered it.

## What does not work / limits

- **The state cut and the unit-step reading are 11a's.** `Correct` is a statement about
  next-state functions with every logical feedback net as an independent state variable.
  It is not a statement about traces. Lifting it to 11b's `Behaves` (bounded-delay channels
  per routed pin) was not done here. For the routed q1 cell, 11b's `q1_loop_s1` shows the
  pattern; doing it per instance is mechanical.
- **Binary only.** A Kleene version (`kleeneSem` vs a Kleene physical evaluation) needs
  `lutK` on the physical side and a 3-valued `forallBits`. It is estimated at 1 day. The
  supports are small (3^7 = 2187 per instance), so `decide +kernel` should handle it, as in 11a.
- **The renaming hint comes from nextpnr's routed JSON.** It is not a trust issue (the
  proof fails on a wrong hint), but without nextpnr's JSON one would need a search
  (≤ 14 LUT outputs here; for whole designs, match by port reachability first).
- **Functional, not structural.** `Correct` does not say "physical LUT i IS logical cell
  c". Two netlists computing the same next-state and output functions from the same
  states pass. That is the right notion under pin permutation and VCC/GND re-tying (11a
  notes item 3). A per-LUT structural statement is a possible add-on: every logical LUT
  output, combinational ones included, would get a `rho` entry.
- **Not covered by the model, and now refused**: FFs (CK→Q, setup/hold, SR), CARRY4,
  MUXF7/F8, LUTRAM/SRL, clocking, DSP/BRAM. None appeared, so nothing about them is proved.
- `PULLTYPE.PULLDOWN` appears on some IOBs. It is accepted as electrical (a weak pull).
  IOB/IBUF/OBUF delays are not modelled.
- `untraced pip` warnings (active pips on no traced path) are reported, not refused. In
  MutPips the old route's dangling pips show up this way. A dangling stub adds load
  (capacitance) but has no logical effect.

## Effort to finish

- Kleene version: ~1 day. Lift to traces (`Behaves`, per-pin delay bounds already emitted
  by fasm2lean as `pinDelay`): 1-2 days.
- FFs / CARRY4 / F7-F8: the refusal hooks are in place. Each needs a source decoder (FFMUX,
  CARRY4 O/CO, F7/F8 select) and a semantics with timing. That is 3-5 days in total, as
  11b estimated.
- Whole shipped designs: the per-instance support split is what scales. Cost is
  Σ_instances 2^|supp|, and |supp| ≤ ~8 for library cells, so it is linear in the number
  of cells, not exponential in the design. A gcd_hw-sized design (~1-2k LUTs, ~500
  instances × ≤ 256 cases) is estimated at minutes of `decide`. The cost then shifts to
  emitting the `insts` binding automatically from the flat yosys JSON (compose.py already
  does the matching) and to Lean elaboration of big generated terms. Estimate 1 week.

## What it buys the project

- The cell theorems of 11a / shard B now apply to the cells as the board runs them inside
  a design, after flattening, placement, pin permutation and routing. The internal nets
  are included (the arbiter `q` and the link node that feeds the latch enables). The
  arbiter's grant exclusion is proved for the PORTS of four real bitstreams.
- The importer cannot silently read an unmodelled primitive as a wire. That was a real gap
  in 11b, where only sources were checked.
- The negative controls show that a one-bit INIT change and a single legal re-pointed pip
  are both caught. The pip case is the mis-route that netlist, routed JSON and
  `fasm_audit.py` would all still agree on.

## Fidelity of every primitive model used

- **LUT6 / LUT6_2**: shard B's `o6B` / `o5B` (`Formal.Cells.Prelim`, via 11b's `PLut.fn`)
  on the physical INIT and pin order. O5 = INIT[31:0] over A1..A5, which is exact for
  7-series. The A6 = VCC requirement of a fractured LUT is not assumed: it is read from the
  bits as a tie, and the proof uses it. Binary only. A real LUT's mux-tree glitch and X
  behaviour are not used here.
- **Routing**: a pure connection (source → pin) in this statement. The per-pin delay data
  of 11b is still emitted (`pinDelay`) but unused by these theorems.
- **Ties**: constant (VCC_WIRE/GND_WIRE through GFAN or direct). The tool checks that each
  tie node has a single driver.
- **IOB/ILOGIC/OLOGIC**: identity bypass, accepted only with the non-inverting
  configuration features (above). The pads' delays are not modelled. The logical side's
  IBUF/OBUF are 11a's H_PAD_IDENTITY.
- **Logical side**: 11a's interpreter (`Netlist.next`/`outs`, `boolSem`), unchanged.

## Surprises

- The 11b code needed almost nothing for LUT6_2. The real gaps were elsewhere: XDC
  bracket names, the unchecked IOI inversion features, and the fact that a configured but
  bypassed FF or carry feature would have been accepted silently.
- The naive support (with repeats) made the decide 2^30. Dedup brought it to 2^7. The
  per-instance split is the scaling lever, not the solver.
- Placement differs a lot across seeds. ugrant shares a slice with ua2 (s1) or ua1 (s4),
  or sits 4 rows from ustate (s3). The pin orders all differ. Some unused pins are tied
  to VCC, others to GND.
- yosys keeps the non-`keep` `ugrant` intact in the flattened design (same INIT, its own
  LUT6_2), so 11a's per-cell import matches the in-context cell here.
- `xc7frames2bit` header bytes vary between runs (as 11b noted). The bit sha256 in
  `fixture/` changes on each re-route, but the FASM does not.

## Last check.sh run (2026-10-27)

```
    == 0. toolchain ==
      seed 1: nextpnr 9c732bc6303458df, toolchain.sh ok, fasm_audit PASS
      seed 2: nextpnr 9c732bc6303458df, toolchain.sh ok, fasm_audit PASS
      seed 3: nextpnr 9c732bc6303458df, toolchain.sh ok, fasm_audit PASS
      seed 4: nextpnr 9c732bc6303458df, toolchain.sh ok, fasm_audit PASS
    == 1. FASM vs bitstream read-back, Lean data drift ==
      seed 1: same netlist from FASM and from .bit  (7 LUTs, 10 outputs, inputs ['A0', 'ack_out', 'data_in[0]', 'data_in[1]', 'data_in[2]', 'r1', 'r2'
      seed 1: Formal/Net/FasmLink/S1.lean up to date
      seed 2: same netlist from FASM and from .bit  (7 LUTs, 10 outputs, inputs ['A0', 'ack_out', 'data_in[0]', 'data_in[1]', 'data_in[2]', 'r1', 'r2'
      seed 2: Formal/Net/FasmLink/S2.lean up to date
      seed 3: same netlist from FASM and from .bit  (7 LUTs, 10 outputs, inputs ['A0', 'ack_out', 'data_in[0]', 'data_in[1]', 'data_in[2]', 'r1', 'r2'
      seed 3: Formal/Net/FasmLink/S3.lean up to date
      seed 4: same netlist from FASM and from .bit  (7 LUTs, 10 outputs, inputs ['A0', 'ack_out', 'data_in[0]', 'data_in[1]', 'data_in[2]', 'r1', 'r2'
      seed 4: Formal/Net/FasmLink/S4.lean up to date
    == 2. composition vs yosys flattening ==
      compose: LinkArb.insts = yosys flattening of link_arb (7 LUT cells, 10 outputs, same INITs and pin sources)
    == 3. Lean ==
      ok  Formal/Net/FasmLink/Basic.lean  (2 s wall incl. slot wait)
      ok  Formal/Net/FasmLink/LinkArb.lean  (1 s wall incl. slot wait)
      ok  Formal/Net/FasmLink/S1.lean  (0 s wall incl. slot wait)
      ok  Formal/Net/FasmLink/S2.lean  (1 s wall incl. slot wait)
      ok  Formal/Net/FasmLink/S3.lean  (0 s wall incl. slot wait)
      ok  Formal/Net/FasmLink/S4.lean  (1 s wall incl. slot wait)
      ok  Formal/Net/FasmLink/Proofs.lean  (99 s wall incl. slot wait)
      'Formal.Net.FasmLink.Design.check_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
      'Formal.Net.FasmLink.Design.not_correct' depends on axioms: [propext]
      'Formal.Net.FasmLink.LinkArb.seed1_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
      'Formal.Net.FasmLink.LinkArb.seed2_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
      'Formal.Net.FasmLink.LinkArb.seed3_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
      'Formal.Net.FasmLink.LinkArb.seed4_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
      'Formal.Net.FasmLink.LinkArb.wrong_rho_caught' depends on axioms: [propext]
      'Formal.Net.FasmLink.LinkArb.grant_exclusion_s1' depends on axioms: [propext, Classical.choice, Quot.sound]
      'Formal.Net.FasmLink.LinkArb.grant_exclusion_s4' depends on axioms: [propext, Classical.choice, Quot.sound]
    == 4. negative controls in the bits (seed 1) ==
      MutInit: caught (not Correct, proved by decide)  [CLBLM_R_X29Y95.SLICEM_X0.ALUT INIT bit 36 flipped]
      MutPips: caught (not Correct, proved by decide)  [pin A1 (was {'k': 'port', 'name': 'r1', 'site': 'IOB_X0Y91'}): INT_R_X29Y95.IMUX7.NW2END_S0_0 
      MutShort: refused by fasm2lean2: fasm2lean: CLBLM_R_X29Y95.SLICEM_X0.ALUT pin A1: node ('CLBLM_R_X29Y95', 'CLBLM_IMUX7') has 2 active
      MutFF: refused by fasm2lean2: CLBLM_R_X29Y95.SLICEM_X0.AFF.ZINI  [flip-flop / latch]
      MutCarry: refused by fasm2lean2: CLBLM_R_X29Y95.SLICEM_X0.CARRY4.ACY0  [carry chain (CARRY4)]
    fasm2lean2 check PASS
```

Note: `formal/lean/Wip/C11c/` was removed by something outside this probe during one run (another agent's cleanup?); check.sh now recreates it. Its contents are regenerated each run and are not claims.
