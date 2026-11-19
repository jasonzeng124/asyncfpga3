# tools-B/auto: formal's simx on research's automatic (BDC_AUTO=1) bench builds (shard B, UNTRUSTED simulation)

Everything here simulates the circuit decoded from the bitstream (prjxray `bit2fasm` read-back of the build's `.bit`,
C's decoder in `formal/tools/margin/run.sh`, RC_TREE=1 arcs) with research's draw model K. Results: formal/FOR-RESEARCH.md
B8-B11. Needs: the FPGA toolchain in `$TC` (cells/verify/toolchain.sh passing), a research checkout in `$RS` with
`build/frontend` copied from `cloud/fixtures/frontend`, python packages textx / simplejson / intervaltree, g++.

## One command per route

    RS=/path/to/research/checkout KERNEL=collatz bash formal/tools-B/auto/coltask.sh SIZES.vh SEED OUT/

KERNEL = collatz (default) | collatz64 | xorshift | ipow. It builds `BDC_AUTO=1 NEXTPNR_SEED=SEED BD_DSP=1 BD_NO_TIGHTEN=1
BD_SIZES_GATE=0 BD_SIZES=SIZES.vh ./hw/build_bench.sh KERNEL` in `$RS/cells`, reads the bits back, decodes, and runs:
research's gate vectors (col18 / c6419 / xor19 / ipow17) on 32 draws from research's board-item K and 32 slow-carry draws
(CARRY4 / F7F8 / FF at 0.8-1.0 of the band), with NEARMISS sums (storage-LUT output pulses < 200 ps) and the mean last-answer
time; then the kernel's long paths: collatz / collatz64 full-range values (vec/c32hi, c64hi) and the steps counter
preloaded at 0x3ffffff0 with two carry slacks (`cchecks.sh`); xorshift the counter preloaded and a +20 ns carry control
(`xorchecks.sh`, `../preload/carryslack.sh`); ipow 8 draws with the DSP48 at >= SLOW_MAX (`dsp_slow.py`). Summary in
OUT/summary.txt. 20-45 min on 4 cores. The sdf md5 in the summary says which route was built; a `.bit` md5 does not
(xc7frames2bit stamps the date into the header).

Suite kernels (any kernel with research's `kernels/K/vec.hex` and `research/tools/suite/oracle.sh`):

    RS=... bash formal/tools-B/auto/suite/task.sh K SEED SIZES.vh SDF8 OUT/ [NDRAWS]

(rebuild, sdf check against SDF8, decode, NDRAWS + NDRAWS slow-carry draws with research's C oracle via `xdraws.py`), and
`suite/preload.sh OUT K LINK I0 "a,n ..." N K0` for the counted loops (countloop / horner / brhash / varshift, `ploracle.py`).

## Pieces
- `decode.sh DIR K`: decode a bench build's files in DIR into DIR/m. `fasm_bits.py`: split bit2fasm's DSP inverter vectors.
- `kdraws.sh DIR K HEX K0 N`: research's draws on a decode. `xdraws.py` / `xsteer.py`: C's draws.py / steermargin.py for
  kernels C's kernels.py does not know (an expected-value file instead).
- `linescale.sh DIR K LINE [STEPS]`: the smallest fraction of one matched-delay line's length that still passes every probe
  on the SAME placement (what-if, not a buildable circuit; STRICT=1 also refuses NEARMISS pulses; PRE= scales other lines
  first). A linescale minimum is an edge on one placement: shipping it failed (B9). Use it to find lines with room.
- `capslack.py RUNDIR CELLREGEX EXP ...`: capture slack of matched latches (data pin's last flip to the enable's closing
  flip) in one draw's dump.
- `dsp_slow.py NET OUT [T]`: an injection putting every DSP48 arc at band >= T (the draw models never draw the DSP slow).
- `sizes/`: the shortened size sets of B9 / B10.

## Added 2026-11-19 (FOR-RESEARCH B12-B14)
- `suite/task.sh K SEED SIZES.vh SDF8|- OUT [NDRAWS] [K0]`: SDF8 `-` builds a what-if route (no research route to match);
  a 64-bit argument takes both bench words; writes OUT/pairs.txt; gcd uses suite_one's gcd8 + gcd_oracle.sh.
- `boundary_bench.py`: resolves a port's driver through the yosys hierarchy (nested operator modules, pass-through ports
  such as test_divui's start_ack = p_end_ack, nextpnr's LUT6_2 -> $LUT6 / $LUT5), CARRY4 outputs, DUTs without
  parameters, part-select connections.
- `suite/linescale_x.sh OUT LINE [STEPS] [ND]`: linescale for suite kernels (any line prefix, e.g. udivui0.udly).
- `pulses.py RUNDIR CELLREGEX EXP ...`: output pulses of ANY LUT (combinational too) matching a cell regex, one draw.
- `suite/pulrun.sh K SEED SIZES SDF8 OUT DRAWS...`: rebuild + pulses.py on the udut.umux* LUTs.
- `lutreaders.py ROUTED NAME...`: which cells read a LUT (decode LUTs are read by the joins .uj<k>.u).
- `decslack.py RUNDIR EXP ...`: the N-way mux decode race in ps per mux (request pin rise vs last index pin flip).
- `divchain.py MDIR`: the divider's enable-chain floor (sum of FAST_MIN over 256 hops) and the request chain's ceiling
  (sum of SLOW_MAX joined -> out0_req), the numbers for Lean's ChainHold.chain_hold_const / chain_hold_side.
- `../select/muxn_rows.py NET ROUTED OUT.lean NS`: decode LUTs of a route as Lean forcing facts (MuxNRowsCmp.lean).
