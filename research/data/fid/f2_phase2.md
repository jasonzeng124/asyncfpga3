# F2 phase 2: DSP48E1 and latches from the bits, DSP bitstream controls (2026-10-27)

All results: nextpnr 9c732bc6303458df (all patches `ok`), prjxray-db
`$TC/openxc7/share/nextpnr/prjxray-db/zynq7`. Each `.bit` was assembled from its
FASM with the build's own fasm2frames + xc7frames2bit; for gcd_hw that path was
shown in phase 1 to reproduce the shipped payload byte for byte.

## ipow, BD_DSP=1: `wt_coll/build/fresh7_ipow/seed13`

Route: 6 DSP48E1, 2069 LUTs.

The audits record **tighten exit 1 with 8 violations**, as on all 8 of its
seeds. The route is not "clean" in the rules' sense. Its routed GLS passed when
it was built.

**Equivalence: routed JSON against the netlist decoded from the `.bit`.**
EQUIVALENT:
- 2270/2270 bels;
- 6/6 DSPs with the same decoded control words and data-pin drivers:
  - OPMODE head 0000101, middle 1010101 with A_INPUT CASCADE, tail 0010101;
  - INMODE, ALUMODE, CARRYINSEL and CARRYIN all 0;
  - all registers 0;
- 2069/2069 LUT functions identical;
- 2877/2877 nets with the same pip set. 60 always-on DSP cascade ppips appear
  only in the bits, and are listed as benign.

**GLS** (`soak_fid.py`, the stalled and fast harnesses of fusion_bench):

| harness | routed JSON | from the .fasm | from the .bit |
|---|---|---|---|
| stalled | PASS, lat = 27355 76608 313581 228299 158402 238931 308035 309012 315736 310966 235138 389725 390702 313966 381909 312012 162126 | identical | identical |
| fast | PASS, lat = 27355 75631 312535 236115 159310 236115 312920 312920 312920 312920 236115 389725 389725 312920 389725 312920 159310 | identical | identical |

The routed-JSON latencies also equal the `results.json` entry for seed 13.
`gate.vvp` on the FASM-built netlist printed ANNOTATE_DONE with no warnings.

## DSP controls on that route (`bit_control.py ... --gls`)

| kind | writer | decoded from the buggy .bit | equivalence | GLS |
|---|---|---|---|---|
| `dsp_constpins` | real unpatched packer writer (48 lines) | INMODE 00000 -> 11111, ALUMODE 0000 -> 1100, OPMODE[6] 0 -> 1 on all 6 DSPs | NOT EQUIVALENT (DSP CONFIGURATION DIFFERS) | FAIL: REFUSED, "INMODE[1]=1: the multiplier's A input is GATED TO ZERO" |
| `dsp_constpins_inv` | real unpatched inversion writer (92 lines) | same words, read from explicit DSP_VCC bits | NOT EQUIVALENT | FAIL: REFUSED |
| `dsp_areg` | real writer is HARMLESS here: no bit differs, because ACASCREG=0 everywhere. Injected instead: every Z[AB]REG_2_[AB]CASCREG_1 cleared | AREG=0 with the bit clear, an undefined combination | NOT EQUIVALENT (REFUSED) | FAIL: REFUSED |

The decoded `dsp_constpins` words are the patch README's board measurement
exactly: INMODE 00000 -> 11111, OPMODE[6:4] 000 -> 100, ALUMODE[3:2] 00 -> 11.
- The packer variant gets there only through the assumption that a pin with
  neither DSP_GND nor DSP_VCC bit reads 1. That is the tile default the board
  showed, so for this variant the agreement is partly circular.
- The inversion variant gets there from explicit bits and does not depend on
  that assumption.

**What the GLS does with these.** It fails closed: the decoder names the decoded
mode and refuses it. It does not simulate the corrupted DSP, so it cannot show
the product going to zero. INMODE[1]=1 gates the multiplier's A input to zero
(UG479 Table 1-11), and ALUMODE=1100 is a logic-unit mode. The model would have
to grow to show the board's numbers, and no data exists to check that growth
against.

## The lut-pinmap control on a second design: xorshift `fresh_xorshift/seed9`

| | equivalence | GLS (stalled / fast) |
|---|---|---|
| good `.bit` | EQUIVALENT | PASS / PASS. Latencies identical to the routed JSON (stalled 24648 60894 ...; fast 24648 59628 ...) |
| `lut_pinmap`, real unpatched writer | NOT EQUIVALENT: 1 LUT FUNCTION DIFFERS (`upipe.many.stage[3].u.ctl.u.u`, a soak-harness pipeline C-element, on 1 of 8 input assignments) | **PASS / PASS, identical latencies.** The vectors never reach the corrupted entry |
| `lut_pinmap_live`, injection: 88 pins on 86 `uut.ucmpi*` LUT sites | NOT EQUIVALENT: 86 LUT FUNCTION DIFFERS | FAIL / FAIL: "timeout on vector 0", no result. The same absent-result signature as gcd_hw |

Unlike gcd_hw (where every run-together pin is GND-tied), the real unpatched
writer does produce a reachable function change on this route. Only the
equivalence check catches it; the GLS vectors do not.

## Latches: a three-latch test design (`fid/f2work/lat/lat_t`, built here)

The design has LDCE, LDPE, and an LDCE with IS_G_INVERTED, each fed through
LUTs from pads.
- fasm2net decodes 3 latches (LATCH, CLKINV/NOCLKINV, ZRST). Equivalence:
  EQUIVALENT, with latch mode and gate sense compared.
- In GLS with `gen.py`'s new `SLICE_LATX`, the routed-JSON netlist and the
  bitstream-built netlist give identical results against expected values
  derived from `lat_t.v`. Before this change, `gen.py` simulated LDCE as an
  edge-triggered flop.
- The LDCE and the LDPE match the source.

**Finding.** The LDCE written with `.CLR(1'b0)` (l3) is held in clear in BOTH
simulations, and the bits say the same.
- nextpnr's packer turned the constant-0 CLR into `$PACKER_VCC_NET` with
  IS_CLR_INVERTED=1.
- fasm.cc then set SRUSEDMUX and routed VCC to SR.
- A slice has no SR inverter, so on silicon that latch would be stuck at 0.
- This is a toolchain defect candidate, not a simulation artefact. It is not
  checked on the board, and no current design instantiates LDCE.

## What this does not show

- **A simulated DSP failure.** The corrupted DSP modes are refused, not
  simulated.
- **Sequential DSP modes.** One DSP configuration only; registered modes are
  untested.
- **Latches on a real design.** Latches were checked only on the 3-latch design,
  and the D->Q/SR->Q delays of `SLICE_LATX` take nextpnr's CK->Q number,
  which is an assumption.
- **The "no bit = 1" tile default.** It is used for the dsp_constpins decode and
  comes from the board via the patch README, not from prjxray-db.
- **Breadth.** One ipow route and one xorshift route; nominal delays only.
