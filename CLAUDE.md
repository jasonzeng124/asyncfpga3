# asyncfpga3: rules for any agent working here

Bundled-data asynchronous circuits on a Xilinx xc7z010 (Zynq-7010), built with
openXC7 (yosys and a *patched* nextpnr-xilinx). `bdc/` is a Dynamatic backend:
it reads Dynamatic's handshake MLIR and emits Verilog built from the frozen
cells in `cells/rtl/`. Start with `README.md`, `cells/README.md`,
`cells/docs/TOOLING.md`, `patches/README.md` and `bdc/AUDIT.md`.

Each rule below is here because breaking it once produced a number that looked
right and was wrong.

## The toolchain is part of the measurement
- There is ONE toolchain, under `$TC` (default `~/dev2/lib/fpgatoolchain`).
  Run `cells/verify/toolchain.sh` before every build. If it fails, nothing
  routed by that build is a result. Three of the four worst bugs here were in
  the bitstream: the netlist, the SDF and every simulation were correct.
- Write down which nextpnr (patch set, fingerprint) produced every routed
  number you report.
- A new nextpnr patch goes in `patches/`, with a fingerprint in `toolchain.sh`
  that has been CHECKED to fail on an unpatched binary. A check that cannot
  fail is worse than no check.
- nextpnr's default target is 12 MHz, so "PASS at 12.00 MHz" means nothing.
  Always pass `--freq`.
- `pnr.log` is buffered. Before calling a process hung, check `/proc/<pid>/stat`:
  state R with rising utime means it is making progress.

## One route is a sample
- Routing scatter (hundreds of ps) is bigger than most margins. Never report a
  single route. Use at least 4 placer seeds and give mean and range.
- Pin `NEXTPNR_SEED` for any A/B comparison, and check that both arms really
  used it (compare the bitstreams with `cmp`).
- Rebuilds of the shipped xorshift violate rule A 2 times in 8. The audit gates
  carry real weight: never skip them, never set `BD_SIZES_GATE=0` and then read
  `tighten_gate.log` (it will be stale).

## Delays
- The only legitimate delay makes a request arrive after its data. Before
  adding one, ask why the two signals diverge and whether they can share one
  request (a join), or whether the value is already registered somewhere.
- A delay that is too long only costs time. One that is too short corrupts data
  silently under PVT, which simulation cannot show. When a measurement is
  ambiguous, take the longer number. Quote margins with the guardband applied
  (`GUARD_LO`/`GUARD_HI` in `cells/verify/skew.py`). Never shorten a delay to hit
  a speed target.
- 8.5% is the median ring scatter, not a guardband.

## Simulation is not silicon
- Zero-delay RTL sim proves very little here. The strongest evidence available
  without the board is `cells/gls/`: the routed design, simulated with its
  routed delays. It must print `ANNOTATE_DONE` with no SDF warning or error.
  iverilog silently ignores `INTERCONNECT`, which is why `gen.py` rewrites it.
- iverilog cannot see yosys memory inference: a sync read inside a clocked block
  passes sim and reads garbage on the board.
- Derive expected values from the C source in `kernels/`. Never paste what a run
  printed into a check. Avoid degenerate vectors, where the right answer equals
  the failure value (for example 0).
- A negative control must be able to fail: make the injected defect larger than
  anything the harness can hide.

## Design decisions already made (do not reopen them)
- Trust the arbiter: emit `bd_arbiter` unconditionally. Don't build analyses
  whose purpose is to avoid one.
- Anything that is true once at startup is a reset polarity (`_set`,
  `RESET_VALUE`), not a missing primitive.
- `cells/rtl/` is frozen. Change it only with a stated reason and a routed-GLS
  result showing the change.
- Never edit `dynamatic/` or `circt/`. They are vendored and used as data.
  Reuse their graph construction, but none of their clock-based timing
  reasoning.
- A ring needs three storage stages per simple cycle.
- An async signal entering a clocked FSM needs a synchronizer, not a delay.

## Git
- Commit messages say what was measured and what it does not show. Read
  `git log` for the house style.
- Never push to `main`. Never force-push a branch someone else is working on.
- Never run `git stash` in a shared tree. Use a worktree.
