# C-11g: the bitstream import on all four gcd_hw routes, rho as a bijection, and xorshift

STATUS: SEE "Last run" AT THE END.

Track 11, probe g. Shard C. 2026-10-29. Builds on C-11f (formal/notes/C-11f-design-import.md),
whose Lean covered gcd_hw route d only.

## Verdict

**The import holds on every route tried, in Lean.** For gcd_hw routes d, 2, 3 and 4 (all
`--freq 100`, nextpnr 9c732bc6303458df), Lean proves that every physical instance decoded from the
bitstream read-back computes its yosys cell under the checked renaming `rho` (10629 / 10633 /
10631 / 10632 instances), and that the 5645 library LUTs have the generated INITs. New: for each of
the four routes, Lean also proves that `rho` is a **bijection on nets** outside route-throughs:
12768 physical nets, one per logical net used by a logical cell, and no two physical nets merged
except a nextpnr route-through output with the net it passes on. A second kernel, **xorshift**
(standalone soak top, 4 seeds), passes the same import in Lean on all 4 seeds (1043 instances,
988 logical cells, 832 library LUTs each) with the same bijection. It needed one extension: an
input pad (IBUF), read as identity (H_IBUF). **ipow** is refused: its 6 DSP48E1 sites have no model
(the decoder stops on 92 DSP features; it would need DSP48E1 as an opaque cell, not done).

## What was done

1. **Seeds 2, 3, 4 of gcd_hw in Lean.** gen3.py was run, unchanged in what it emits for gcd_hw,
   on the committed fixtures of seeds 2, 3, 4 with namespaces `Gcd2`, `Gcd3`, `Gcd4` (gen3 already
   took the namespace as an argument; no seed/prefix extension was needed). The regenerated `GcdD`
   is byte-identical to the committed one (drift check), before and after the IBUF change below.
   `Formal/Net/FasmGcd{2,3,4}.lean` restate FasmGcd.lean's five theorems per route
   (`gcd_hw_N_netlist`, `_ports`, `_count`, `_cells_init`, `_chunks`).
   Built one module at a time (`formal/tools/fasm2lean3/build.sh Gcd2` etc.: Rho, C000..C042,
   All in sequence, stop on the first error, each under a probe-wide `flock` so that no two Lean
   processes of this probe ever run together). Peak RSS per chunk 0.8-1.54 GB.
2. **`rho` is a bijection (outside route-throughs)**, all four gcd_hw routes and all four
   xorshift routes. `Formal/Net/FasmRho.lean` (hand-written, generic) and per route generated
   certificates (`rhoinj.py`).
3. **xorshift**, 4 seeds, standalone (`kroute.sh`, the C-10n recipe plus the `.bit` read-back),
   imported, checked by the Python mirror and in Lean.
4. **ipow**, seed 1, routed and refused by the decoder (DSP48E1).

## The bijection theorem

`Formal/Net/FasmRho.lean` defines, for the instance list `insts` and renaming `rho` of a design:

- `IsRtOut insts k`: physical net `k` is on an output pin of an instance with no logical cell
  (a route-through or constant LUT/buffer added by nextpnr).
- `NonRt insts rho k v`: `rho.find k = some (.net v)` and `¬ IsRtOut insts k`.
- `LNet insts v`: `v` is on some pin of some instance's logical cell.

`bij_of_checks`: if four Boolean checks hold, then
1. `NonRt k v → NonRt k' v → k = k'` (injective);
2. `NonRt k v → LNet v` (into the used logical nets);
3. `LNet v → ∃ k, NonRt k v` (onto them).

The checks run on generated certificates, which are hints and are not trusted: `inv` (logical net
→ physical net), `occ` (logical net → index of an instance whose logical cell has it), `mark`
(route-through output → index of its instance; index = 1000·chunk + position). `markOk` (each mark
points at a real route-through output), `coverOk` (every route-through output is marked, every
logical pin net has an `inv` entry), `keysOk` (every `rho` entry to a net is marked or is `inv`'s
preimage), `invOk` (each `inv` entry is a `rho` entry, unmarked, and occurs on a logical cell).
To bound the kernel's memory each trie walk is cut at depth 6 into 64 `decide`s, assembled with
`kvAll_node` (otherwise one `decide` over `rho` peaked at 4.25 GB).

Per route: `Formal/Net/FasmRho<R>.lean` states `rho_bij` for `<NS>.insts` and `<NS>.rho`, with
`<R>` = D, 2, 3, 4 (gcd_hw) and Xorshift1..4. Inputs: `FasmRho<R>{Inv,Occ,Mark}.lean` (one trie
each, ~1 GB to elaborate) and `FasmRho<R>Data.lean` (`keysOk`, which needs only `Rho`).

What the routes give (rhoinj.py, then proved):

| route | rho entries | route-through outputs | bijection on | constants |
|---|---|---|---|---|
| gcd_hw d | 13907 | 1139 | 12768 nets | the rest map to constants |
| gcd_hw 2 | 13911 | 1143 | 12768 | |
| gcd_hw 3 | 13909 | 1141 | 12768 | |
| gcd_hw 4 | 13910 | 1142 | 12768 | |
| xorshift 1-4 | 1735 each | 108 | 1627 | |

Together with `Inst.Sound` this is the statement "the physical gate graph is the logical gate
graph": one physical net per used logical net, plus nextpnr's route-throughs, each proved to pass
its source (or a constant). The 6 physical nets that are no instance output are BSCAN's outputs
(opaque, pins renamed one to one).

Not covered by `rho_bij`: logical nets that no logical cell in `insts` touches (on gcd_hw the
dangling MUXF7's output, which nothing reads, see C-11f); the OBUF's own pins (the OBUF is not an
instance; `ports_ok` covers its input).

## xorshift

- **Route.** `kroute.sh xorshift SEED`: C-10n's kcheck/route.sh recipe (git-archive copy of
  cells/ and bdc/, bdc/emit.py's soak top `bdc_xorshift_top`, research's `xorshift_sizes_T3.vh`,
  cells/flow.sh with its own gates, `--freq 100 --timing-allow-fail` patched into the copy's
  nextpnr line), then the `.bit` and its read-back as route.sh (11f). Outputs under
  build/k_xorshift/ (ignored), fixtures `fixture/xorshift_{1,2,3,4}.*` (trimmed by
  `trim.py --kernel`, ~180 kB per seed). Seeds 1-4: flow.sh exit 0, fasm_audit PASS, toolchain.sh
  9/9 ok, nextpnr 9c732bc6303458df. The 4 FASMs differ (sha256 in the fixtures); the yosys JSON is
  the same for all 4. Seed 1's FASM is byte-identical to C-10n's seed-1 route
  (268245f15e43e7cf).
- **The soak top has no clock** and no FF: 1019 LUT6_2, 14 CARRY4, 5 MUXF7, 2 MUXF8, one input
  pad, one output pad. `--freq 100` therefore constrains nothing.
- **One extension, the input pad.** gen3.py now accepts a logical IBUF (dropped like the OBUF)
  and renames the physical net `port:<p>` (fasm2lean3 already named a fabric pin reached from an
  input IOB that way) to the IBUF's output. That rename is part of `rho` and so part of the
  bijection. What is assumed (**H_IBUF**): the input path pad → IBUF → ILOGIC bypass → fabric is
  the identity. The IOB/ILOGIC features are classified by fasm2lean3's existing "IOB electrical /
  IOI bypass" lists; nothing else on that path is decoded. This changes nothing for gcd_hw (no
  input pad; regenerated GcdD/Gcd2-4 byte-identical).
- **Result.** For every seed: the physical netlist from the `.bit` equals the one from nextpnr's
  FASM; 1043 instances, all 988 logical cells matched (no dangling cell), 55 route-through /
  constant instances (108 outputs), max support 9, check3 0 failures; in Lean
  `Formal/Net/FasmXorshift<N>.lean` (`xorshift_N_netlist`, `_ports`, `_count`, `_cells_init` for
  832 library LUTs, `_chunks`) and `FasmRhoXorshift<N>.rho_bij`.
- **Negative controls (Python mirror only, seed 1, `kcheck.sh` step 1b):** an INIT bit of
  SLICE_X17Y53.BLUT flipped in the bits, and its pin B1's IMUX pip re-pointed to another legal
  source carrying a different signal. Each is caught by check3 at exactly that instance (C001[0],
  `uut.ulink_n_trueResult_8.lat.pair[18].u`). The Lean versions of these controls exist only for
  gcd_hw route d (C-11f's Mut*.lean).

## ipow (refused)

`kroute.sh ipow 1` routes (flow.sh exit 0, fasm_audit PASS: 1484 LUT sites, 6 DSP48E1, sha256 of
the FASM 27e7d88a8f148ccc). `fasm2lean3.py` on the read-back stops with "site features the model
does not cover": 92 DSP48E1 features at DSP_L_X22Y{25,30,65,70}. So ipow uses DSP48E1 and the
import has no model for it. Importing it would mean an opaque DSP48E1 cell (pins walked, no
semantics, as BSCAN), so the multiplies would be unchecked: not done here. The fixture was not
kept.

## What this does NOT show

- Everything C-11f lists still holds: no timing, glitches or X; the logical netlist is yosys's,
  not the RTL; the decoders (FASM → site semantics, yosys JSON flattening) are trusted and tested
  only by agreement and negative controls; BSCAN opaque.
- New trust: H_IBUF (xorshift's input pad is the identity).
- xorshift is imported in its **soak** top, not in a rig or the PS7 bench measured on the board.
  The theorem is about gate functions; the kernel is made of combinational loops (C-elements,
  latches as LUT feedback), and nothing here says anything about its asynchronous behaviour.
- `rho_bij` is about nets that logical cells use. It does not say the OBUF/IBUF pins are
  instances.
- The negative controls in Lean are route d only; seeds 2-4 and xorshift rely on the same code
  (same `Inst.check`, same decoder) and on the Python controls.

## Files

- `formal/tools/fasm2lean3/`: `gen3.py` (IBUF), `trim.py` (`--kernel`), `check.sh` (seeds 2-4 drift,
  rho drift, Lean build via build.sh), new `build.sh`, `rhoinj.py`, `kroute.sh`, `kcheck.sh`,
  `fixture/xorshift_{1,2,3,4}.*`.
- `formal/lean/Formal/Net/FasmDesign/{Gcd2,Gcd3,Gcd4,Xorshift1,Xorshift2,Xorshift3,Xorshift4}/`
  (generated by gen3.py).
- `formal/lean/Formal/Net/FasmGcd{2,3,4}.lean`, `FasmXorshift{1,2,3,4}.lean` (theorem files).
- `formal/lean/Formal/Net/FasmRho.lean` (hand-written), `FasmRho{D,2,3,4,Xorshift1..4}{,Inv,Occ,Mark,Data}.lean`
  (generated by rhoinj.py).

## Reproduce

    formal/tools/fasm2lean3/check.sh            # gcd_hw d,2,3,4 + rho + negative controls (Lean: hours of CPU when unbuilt)
    formal/tools/fasm2lean3/check.sh --no-lean
    formal/tools/fasm2lean3/kcheck.sh xorshift  # xorshift 1-4 (Lean ~20 min)
    formal/tools/fasm2lean3/kroute.sh xorshift N   # re-route one seed (~5 min)

## Last run
(filled in below)
