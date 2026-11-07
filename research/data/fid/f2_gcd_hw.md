# F2: gcd_hw simulated from its bitstream (2026-10-27)

**Route.** gcd_hw R5 with fast fall, the default seed, from the wtFF_sd build.

| file | md5 |
|---|---|
| `gcd_hw.bit` | b40e4e41ed234fc57c6ecc13c895c0c3 |
| `gcd_hw_routed.json` | f9c4597dd8168d5e59fcf1eaaf617426 |
| `gcd_hw.sdf` | 61e147559e2c6112aa19d8e431ee14f1 |
| `gcd_hw.fasm` | 04657de73d1b88597856d081ea7f8319 |

**Toolchain.** nextpnr 9c732bc6303458df, with all patches `ok` per toolchain.txt.

**prjxray-db.** `$TC/openxc7/share/nextpnr/prjxray-db/zynq7`, the database
`build_hw.sh` encodes with.

**Re-encoding check.** fasm2frames followed by xc7frames2bit on `gcd_hw.fasm`
gives a byte-identical `.frames` and a byte-identical bit payload. Only the
`.bit` header's file name and date differ.

## 1. Equivalence: `fasm_equiv.py` compares the routed JSON with the netlist decoded from the `.bit`

| check | result |
|---|---|
| cells | 11732 bels in JSON, 11731 in the bits. The one missing is SLICE_X22Y94/F7BMUX, which has no loads in JSON (dead) |
| config | 326 FF, 59 CARRY4, 5 BUFGCTRL, 1 BSCAN: 0 differences |
| pin drivers | 34975/34975 JSON driver-to-sink pairs present in the bits. The bits have 15k more pairs: pins JSON leaves unconnected are a constant on the die (see below) |
| LUT functions | 10136/10136 identical over every assignment of their input nets. JSON is read through gen.py's X_ORIG_PORT expansion, the bits through the physical INIT |
| routing | 12092/12092 non-constant nets: identical pip set as (src node, dst node) pairs. One net has 3 more pips in the bits; they reach only the dead F7BMUX's CX pin (stubs.tsv). The 2 constant nets are compared per sink, not per pip, because a "default" ppip has no bits |
| benign, listed | 11304 LUT pins that JSON leaves unconnected (gen.py ties 0) are VCC on the die, through the IMUX default ppip. They are harmless because the functions are identical. 5 BUFGCTRL I1 inputs are connected on the die by the input mux's all-zero encoding but deselected (S1/CE1 inverted, checked) |
| verdict | EQUIVALENT. The same check on nextpnr's FASM instead of the `.bit` is also EQUIVALENT |

## 2. GLS: the same tb_run, 16 vectors, TEND=150000 ns, nominal delays

| vector | routed-JSON GLS | FASM-built GLS (from `.bit`) |
|---|---|---|
| 0..15 | 16/16 errs=0 | 16/16 errs=0 |
| laps | 4834 3177 316 271 665 236 51 180 157 128 665 72 42 60 246 156 | identical |

The acceptance gate on the FASM-built netlist passes: `vvp gate.vvp` printed ANNOTATE_DONE, with zero SDF WARNING/ERROR lines, over 110855 IOPATHs including 66284 ICBUFs.

All 16 SUMMARY lines are byte-identical, down to t_first_lap and t_last_lap in
ps.

The netlist differs from the routed-JSON one: 66284 ICBUFs against 50154, and
16k extra constant sinks at 0 ps. It still produces the same event times.

## 3. Negative controls

**(a) The genuine unpatched writer** (`fasm_audit.py --write-unpatched pinmap`)
changes 58 LUT INITs. fasm_audit FAILS on it. Assembled to a `.bit` and decoded
back, fasm_equiv finds 0 LUT FUNCTION differences.

The reason: every run-together X_ORIG_PORT pin on this route is tied to GND, so
the corrupted half of each table is never addressed. The same holds on 19
distinct gcd_hw routes in the scratch area: 63 run-together pins each, all on
GND. On today's flow the bug is functionally invisible.

One cell drops out: SLICE_X22Y94/D6LUT, whose only load is the dead F7BMUX.
The checker reports it as "HAS LOADS" because that load is dead in JSON too.
GLS was not run on this one; equivalence covers it.

**(b) The August signature on live pins** (`inject_pinmap.py`):
- For every LUT under `urig.udut.ucmpi*`, one live pin's name is made unknown
  to the emulated unpatched writer, so it is read as I0.
- 97 pins mis-mapped, 81 LUT sites changed. Assembled to a `.bit`.
- fasm_audit FAILS: 81 sites.
- fasm_equiv: NOT EQUIVALENT, 81 LUT FUNCTION DIFFERS, everything else as in 1.

GLS on that `.bit`:

| | routed-JSON GLS (unchanged) | FASM-built GLS |
|---|---|---|
| vectors | 16/16 errs=0 (table 2) | 0/16: laps=0 errs=0 oks=0 on every vector. Reset released at 467 ns, housekeeping ring running (hk=8435), no gcd completes in 150 us |

This is the August "absent result" signature: errs=0 with no answer. Whether
it is a wedge or a spin was not checked.

## What this does not show

- Delay accuracy. The delays are nextpnr's SDF, re-keyed onto bels.
- Anything prjxray-db cannot decode, or its ppip semantics. These are trusted,
  not measured.
- Designs outside the decoded subset: DSP, latch, LUTRAM, async SR and CLKINV
  are refused.
- One route and one design (gcd_hw), at nominal delays only. No scatter or
  corner runs on the FASM-built netlist.
- The negative control (b) is an injection of the bug's mechanism. It is not
  the August bitstream, which is not archived.
