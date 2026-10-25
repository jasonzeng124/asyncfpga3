# Board queue

Experiments that have passed every check possible without the board, most
valuable first. Each one: branch/commit, exact commands, pass criterion
(self-reporting, never "read the scope"), and what a failure would mean.

(empty of board experiments: as of 2026-10-25 19:45 `cells/check.sh` passes on claude/research,
but no cloud-built kernel bitstream has been through routed GLS yet; a gcd bench build is in
progress, see JOURNAL.md.)

## Owner-side check, not a board experiment (cheap, still useful)
ANSWERED in the cloud on 2026-10-25: the failure was the netlist, not the patch or the chipdb.
yosys 0.62 maps soak_top's two 8-input functions to MUXF7/MUXF8, and rloc_stamp gave their LUTs
slots no placement can honour (fixed in 77b20a8). The check below still tells whether the local
yosys makes MUXF7/F8 here (`grep -c MUXF build/pnr/synth.log`); if it does not, the two
toolchains produce different netlists from the same source, which is worth knowing.
On the owner's machine, with the local toolchain rebuilt from this branch's
patches/ (the local one has only main's patches, see the first journal entry):

    cd cells && BD_NO_TIGHTEN=1 ./flow.sh; echo "exit $?"

Pass: `flow.sh PASS`, exit 0. If it passes there and fails in the cloud
(`Unable to find legal placement ... rdly_chain`), the difference is the chipdb
or the build, not the patch. If it fails there too, the committed
nextpnr-xilinx-rloc-group.patch is not the one PR #1's routed numbers came from.
