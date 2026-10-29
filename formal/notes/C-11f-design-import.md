# C-11f: the whole routed gcd_hw imported from its bitstream

STATUS: SEE "Last run" AT THE END (DONE for route d in Lean if the last run says PASS; routes 2, 3
(and 4 if listed) are checked by the Python mirror only).

Track 11, probe f. Shard C. 2026-10-27.

## Verdict

**Works for the whole design.** The routed gcd_hw (kernel + rig, 9623 logical cells) is read back
from its `.bit`, every used primitive is decoded with a stated digital model, and Lean proves, for
route d, that the physical netlist equals the yosys netlist nextpnr was given, gate by gate, up to a
checked renaming of nets (H_NETLIST for that route). It also proves that every library-cell LUT of
the design (5645 of them) has the kind and INIT of the `Formal.Gen.Cells` cell generated from the
same line of `cells/rtl/*.v` (the INIT half of H_CELLS). Routes 2 and 3 (and 4, see the last run)
were routed, read back and pass the same check in a Python mirror of the Lean check. They are not
in Lean: the time box allowed one 43-chunk build, about 1.5 h of CPU on this loaded machine.

Two findings. (1) nextpnr adds 1130 LUT outputs that are not in the yosys netlist: route-through
LUTs for carry-chain inputs and `$PACKER_GND/VCC` constant LUTs. Each is proved to pass exactly its
renamed input, or to be the constant. (2) A first flattening bug of mine (nets joined through a
pass-through port of a bdc wrapper module got two ids) made 438 instances fail. The check caught
it. It did not pass vacuously. The fix is a union-find in `gen3.py` (49 nets joined).

## What checks

    formal/tools/fasm2lean3/check.sh            # everything from fixtures (Lean part ~1-2 h CPU when unbuilt)
    formal/tools/fasm2lean3/check.sh --no-lean  # steps 0-2 + the Python half of the negative controls (~15 min)
    formal/tools/fasm2lean3/route.sh SEED && python3 formal/tools/fasm2lean3/trim.py SEED   # re-route a seed (~9 min)
    cd formal && ./check.sh Formal/Net/FasmDesign/Basic.lean Formal/Net/FasmDesign/GcdD/All.lean Formal/Net/FasmGcd.lean

check.sh does the following:
0. Checks the stamp of each fixture seed: nextpnr 9c732bc6303458df, `cells/verify/toolchain.sh` ok,
   the 4 clocks PASS at `--freq 100`, and fasm_audit PASS.
1. For each seed, the physical netlist that `fasm2lean3.py` extracts from the FASM read back from
   the `.bit` (xc7frames2bit → bitread → bit2fasm) must be the one extracted from nextpnr's FASM
   (it is, on d, 2 and 3). Then `gen3.py` pairs it with the yosys netlist, and `check3.py` (a
   Python mirror of `Inst.check`) passes every instance.
2. Drift: `Formal/Net/FasmDesign/GcdD/*.lean` must equal what gen3 regenerates from the fixtures.
3. Lean build and the axiom audit.
4. Negative controls, injected in the BITS of seed d (`mutate3.py`):
   - **init**: one INIT bit of the bd_link C-element LUT at SLICE_X0Y63.ALUT is flipped.
   - **pips**: the IMUX pip of its pin A2 is re-pointed to another legal source that carries a
     different signal.
   - **ffinit**: ZINI of SLICE_X22Y62.AFF is toggled.
   - **clkinv**: CLKINV is added to that slice.

   Each one is caught by check3 at exactly the mutated instance. The Lean files
   `Wip/C11f/Mut{Init,Pips,Ffinit,Clkinv}.lean` prove `checkAll rho insts = false` for the mutated
   chunk with `decide +kernel` (all four compiled, 47-73 s each).

## Theorems

`Formal/Net/FasmDesign/Basic.lean` (hand-written, generic):

| name | statement |
|---|---|
| `Trie.find`, `ren` | the renaming (a Nat-keyed binary trie, so each lookup is about 14 steps in the kernel) |
| `fastSem_eq` | the `testBit` table reading used by `decide` is `Formal.Gen.boolSem` (Core `Lut.eval`) |
| `forallEnv_sound` | enumerating the support nets covers every valuation |
| `Inst.check_sound` | `i.check rho = true → i.Sound rho` |
| `checkAll_sound` | the same, for a list of instances |
| `bindsOk_sound` | a bound logical LUT has the Gen cell's kind and INIT |

`Inst.Sound rho i` has three forms:
- **Logical cell `l`, non-opaque.** `kindOk`: a non-LUT physical primitive has `l`'s kind, a
  buffer is any buffer, and a flip-flop also has `l`'s INIT. For every corresponding output pair,
  the physical output net renames to `l`'s output net, and for **every** `env : Nat → Bool`, the
  physical output (Gen semantics, its own pins renamed) is defined and equals `l`'s output.
- **Route-through** (`l = none`). The output net renames to some source `s`, and the output equals
  `s` under every env.
- **Opaque** (BSCAN). Every pin renames to `l`'s pin net.

`Formal/Net/FasmDesign/GcdD/` is GENERATED: `Rho.lean` (`rho`, `ports`, `ports_ok`),
`C000..C042.lean` (250 instances each, `ok` and `binds_ok` by `decide +kernel`) and `All.lean`
(`all_ok`, `sound`, `cells_init`).

`Formal/Net/FasmGcd.lean` restates the results:
- `gcd_hw_d_netlist : ∀ i ∈ GcdD.insts, i.Sound GcdD.rho`
- `gcd_hw_d_ports`
- `gcd_hw_d_count`: 10629 instances, 9622 of them carrying a logical cell.

## Coverage (route d; routes 2 and 3 give the same logical counts)

| | count | status |
|---|---|---|
| LUT sites (LUT6 / LUT6_2, O6 and O5) | 8925 sites | imported: physical INIT plus pip-walked pins; 0 floating pins; 0 reads of an all-zero LUT on d (1 on seed 3, read as constant 0) |
| slice FFs | 306 FDRE + 20 FDSE (FF and 5FF) | imported: kind from FFSYNC/ZRST, INIT from ZINI, CE/SR from CEUSEDMUX/SRUSEDMUX, CLKINV, D from ?FFMUX |
| CARRY4 | 59 | imported: PRECYINIT (C0/C1/AX/CIN), ?CY0 (DI = O5 or ?X), S = O6, O/CO through ?OUTMUX/?FFMUX/COUT |
| MUXF7 / MUXF8 | 857 / 343 | imported: F7AMUX = AX ? A6 : B6, F7BMUX = CX ? C6 : D6, F8MUX = BX ? F7A : F7B |
| BUFGCTRL | 5 | identity, accepted only with exactly {IN_USE, IS_IGNORE1_INVERTED, ZINV_CE0, ZINV_S0} |
| BUFHCE | 9 (d), 13 (2), 11 (3) | identity, accepted only with {IN_USE, ZINV_CE}; route-throughs in the check |
| BSCAN | 1 | **opaque**: pins only, no semantics |
| IOB/OLOGIC (2 LED outputs) | 2 | 11c's checked non-inverting bypass; pads electrical |
| logical cells matched | 9622 / 9623 | the missing one is a MUXF7 whose output nothing reads (`ucontrol_merge12 ... mux7`, net `z_data`); gen3 checks that it is unread. Its select route is 4 of the 31 untraced pips |
| nextpnr-added outputs | 1130 LUT + 9 BUFHCE | proved route-throughs / constants |
| untraced active pips | 31 | 27 are BUFGCTRL I0/I1 input muxes of unused or I1-unused BUFGCTRLs; 4 are the dangling MUXF7 select stub |
| site features | all classified | consumed by the decoder, or a known default (6016), clock-spine enable (75), IOB electrical (14), IOI bypass (8); anything else is refused |

Decide size: max support 9 nets per instance (CARRY4). Chunks take 110-200 s wall each on a machine
at load ~14, ~0.8 GB each; Rho takes 64-93 s.

## Primitive models and their fidelity

All semantics are Formal.Gen's (11d), `boolSem` = shard A's Core `Lut.eval`. **No new primitive
model is introduced.** What is new is the decoding of the site bits into those models.

- **LUT6_2.** O6 = INIT over A1..A6; O5 = INIT[31:0] over A1..A5. Exact for 7-series. Binary only.
- **FF** (H_FF_MS, Gen): a master-slave pair with a synthetic master net. It is an ideal edge
  flop. CK→Q, setup/hold and metastability are not modelled. The decode follows prjxray fuzzer
  011: FFSYNC=1 → FDRE/FDSE, else FDCE/FDPE; ZRST set → reset value 0; ZINI set → INIT 0; CLKINV →
  clock read inverted. **LATCH mode is refused** (none present). The decode is H_SITE_DECODE (from
  prjxray's documentation). The ZINI and CLKINV negative controls show that the bits it reads
  matter.
- **CARRY4** (H_CARRY4_SIM, Gen): `c0 = CI | CYINIT`. Physically there is one PRECYINIT mux; it is
  decoded as CI = CIN (CYINIT 0), or CYINIT = AX/0/1 (CI 0). So the OR is exact here, because one
  side is always 0. DI is O5 when `CARRY4.?CY0` is set, else ?X (fuzzer 013). S is O6.
- **MUXF7/F8**: `S ? I1 : I0`, with the A/C side as I1. That matches nextpnr's SELMUX2_1 pin use
  (A6LUT → input 1). The check would fail on 343 F8 and 857 F7 instances if the order were wrong
  relative to nextpnr. It is not checked against silicon.
- **BUFG/BUFHCE**: identity (H_BUF_IDENTITY). The ns insertion delay is not modelled.
- **INV** (logical, 37 cells): read as LUT1 INIT 1, which is the same function as `NOT`.
- **Floating pins** would be FREE inputs (the check must hold for both values). On these routes
  there are none, once bidirectional long-line pips (LV/LVB, `<<->>` in prjxray-db) are walked in
  both directions. 11c's walker did not do this. Here it mattered: 1 pin looked floating.

## What this does NOT show

- **No timing.** These are Boolean gate functions only: no delays, glitches, setup/hold, X. The
  timing layer (tcheck) still assumes its graph is this netlist; what is discharged is H_NETLIST's
  *connectivity and function* half, for this route. tcheck's SDF arcs are not tied to these pins
  yet. Next step: emit tcheck's graph from these instances.
- **The logical netlist is yosys's.** It is not proved equal to the RTL, except that the 5645
  library LUT INITs equal Gen's. The wiring inside each library-cell instance is not compared with
  Gen's per-module netlist: that is the "structure" half of H_CELLS. The ~3500 abc-mapped LUTs of
  the fused compute regions and the rig are yosys's word, not tied to any spec.
- **`rho` is a function but not proved injective.** Merging two drivers would still have to pass
  every gate check of both. A statement "the physical graph IS the logical graph" (a bijection up
  to route-throughs) is not stated.
- **The decoders are trusted**: FASM → site semantics (prjxray fuzzer docs, H_SITE_DECODE), and the
  yosys JSON flattening. Both are tested only by the agreement itself (a decoding error makes
  instances fail, as the flattening bug did) and by the negative controls.
- **Only route d is in Lean.** 2 and 3 (and 4 if listed below) pass in the Python mirror (check3),
  which is not a proof.
- **BSCAN is opaque**, and the rig's JTAG logic is checked only as gates.
- These routes use `--freq 100` (CLAUDE.md). tcheck's 4 routes (formal/tools/tcheck/route.sh) did
  not pass `--freq`, so these are not the same bitstreams as C-10h's verdicts.

## Files

- `formal/tools/fasm2lean3/`:
  - `route.sh`: tcheck's flow plus `--freq 100`, the .bit and its read-back.
  - `fasm2lean3.py`: the whole-design extractor; it imports 11c's fasm2lean2.py read-only.
  - `gen3.py`: flatten, pairing, renaming, route-throughs, Gen binding, Lean emission.
  - `check3.py`: the Python mirror of the check.
  - `trim.py`, `mutate3.py`, `mkmut.sh`, `check.sh`.
  - `fixture/gcd_hw_{d,2,3[,4]}.*`: xz FASM, xz read-back FASM, xz trimmed synth JSON, xz
    placement hint, xdc, toolchain/audit/pnr stamps, sha256. About 1 MB per seed.
- `formal/lean/Formal/Net/FasmDesign/Basic.lean` (hand-written).
- `formal/lean/Formal/Net/FasmDesign/GcdD/{Rho,C000..C042,All}.lean` (generated, ~6 MB).
- `formal/lean/Formal/Net/FasmGcd.lean`.
- `formal/lean/Wip/C11f/Mut*.lean` (negative controls, written by check.sh; not claims).

No pre-existing file was edited.

## Surprises

- nextpnr places logical MUXF8s in 343 slices and pairs them with F7s. The read-back shows
  `BOUTMUX.F8` in slices that have only route-through LUTs. 11c's "F7/F8 never appear" holds only
  for small designs.
- bit2fasm prints a LUT INIT with a single 1 bit as `...INIT[k]`, not as a vector. 11c's reader
  would have read such a LUT as all-zero.
- The bidirectional long lines (LV/LVB) are stored once in prjxray-db. The FASM uses the reverse
  direction for some routes.
- The design's yosys JSON keeps the bdc wrapper modules as hierarchy (`bdc_fused_*`,
  `bdc_amerge*`, `bdc_muxn3_*`) and has pass-through ports. Flattening needs a union-find.

## Last run
(filled in below)

### 2026-10-29 rebuild (in progress)
- The tools under formal/tools/fasm2lean3/ were NOT lost (they were in the lead's WIP snapshot,
  commits e4b7998..bef1849); the Lean was. Rebuilt: Formal/Net/FasmDesign/Basic.lean (compiles,
  hand-written from the data format gen3 emits and the statements above), FasmGcd.lean.
- gen3 regenerates route d exactly as recorded: 10629 insts / 43 chunks, rho 13907, 9622/9623
  logical matched, 1139 route-through outputs (1130 LUT + 9 BUFHCE), 5645/5645 bound, max supp 9.
- toolchain restored by the lead: cells/verify/toolchain.sh ok, nextpnr sha256 9c732bc6303458df.

