# The target: the file THE theorem is about

Chosen 2026-11-01 by shard A (formal/PROGRAM.md, "THE goal"): BOARD-QUEUE #1 on
`claude/research` (gcd_hw, fusion on, cloud toolchain, v4 placement, converged select pads),
build_hw.sh's default seed. The theorem is about **these bytes**. A later research design is a
new target, journaled as a new decision.

| file | what | md5 | sha256 |
|---|---|---|---|
| `gcd_hw_03e82630.bit` | the bitstream, copied from `research/board/gcd_hw_03e82630.bit` (research 1a97b739) | 594bd861e6b86c9e278802a4e06d5158 | 03e82630dcf5c453b40121cdaf86eae0cc79c6c65a69ba1bfa0c83e402141196 |
| `gcd_hw_03e82630.fasm.xz` | nextpnr's FASM the `.bit` was made from (rebuild, see below) | 1a3909f6bd7395df0ae764875d289f00 (uncompressed) | b73e1ba0...221b (uncompressed) |
| `gcd_hw_03e82630.fromBit.fasm.xz` | the `.bit` read back by prjxray (`bitread` + `bit2fasm.py`): the decoder's input | 418f36ae52359790e9120e8f4c55fa03 (uncompressed) | a93664d1...598b (uncompressed) |
| `gcd_hw_03e82630.sdf.xz` | nextpnr's SDF of the rebuild (cross-checks only, never an input of the theorem) | 6f8b99e6c49bb7ef8855c881cecabe5c (uncompressed) | |
| `gcd_hw_03e82630.json.xz` | yosys netlist of the rebuild (to name the boundary nodes; not trusted) | ff7c6997eb31f2ffa8a89af52dc0ab28 (uncompressed) | |
| `gcd_hw_03e82630.toolchain.txt`, `.pnr.txt` | toolchain stamp and nextpnr clock lines of the rebuild | | |

## How the `.fasm` is tied to the `.bit` (checked 2026-11-01 07:20 UTC)

1. Rebuild in the cloud toolchain (nextpnr 9c732bc6303458df, patches as in
   `gcd_hw_03e82630.toolchain.txt`, `cells/verify/toolchain.sh` all ok, yosys v0.62, fasm via the
   textX parser), from `git archive` of research 1a97b739, with BOARD-QUEUE #1's recipe exactly
   (`NEXTPNR_SEED`, `NEXTPNR_FREQ`, `BD_SIZES` unset):

       cd cells && BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 ./hw/build_hw.sh gcd_hw

   SDF md5 6f8b99e6c49bb7ef8855c881cecabe5c = BOARD-QUEUE #1's recorded SDF md5.
   (No `--freq`: this reproduces the committed file; nextpnr's "PASS at 12.00 MHz" lines mean
   nothing, and no timing claim is made from them.)
2. The rebuilt `.bit` (made by `fasm2frames.py` + `xc7frames2bit` from this `.fasm`) differs from
   the target in exactly 8 bytes, offsets 99-114: the header's date and time strings
   (`2026/10/25 20:44:55` in the target). Every configuration byte is identical. So the target is
   `fasm2frames(this .fasm)` with another date.
3. `bit2fasm` of the target gives 355126 canonical features; the nextpnr FASM gives 401642. The
   differences are expected and are not a decoding claim yet: 52547 nextpnr-only lines are
   features with no bits (e.g. `BRKH_INT_*_SLOW` pseudo-pips), 6031 read-back-only lines are
   zero-encoded defaults (e.g. `PRECYINIT.C0`) and configuration-tile constants. The decoder
   (Spec part II) reads the **read-back** FASM plus prjxray's always-on pseudo-pips, so that its
   input is what the bits say, not what nextpnr intended.

## What is trusted here (H_DECODE)

`bitread` + `bit2fasm.py` with prjxray-db (`$TC/openxc7/share/nextpnr/prjxray-db/zynq7`, part
xc7z010clg400-1): the map from frame bits to FASM features. The decoder from features to the
Lean netlist will be Lean code with a re-encoding round trip (Spec.lean section 7).
