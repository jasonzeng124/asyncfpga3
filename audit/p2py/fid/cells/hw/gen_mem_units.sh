#!/usr/bin/env bash
# Generate the memory units cells/tb/tb_bdc_mem.v needs.
#
# Cheap, deterministic, and needs no toolchain -- but it does need to exist
# before run_sim.sh will run that bench, and run_sim.sh SKIPs rather than fails
# when a declared requirement is missing.  A skip is not a pass; run this.
set -eu
cd "$(dirname "$0")/.."
mkdir -p build/gen
# The :seq variants carry a program-order token as one more join input, and
# cells/tb/tb_bdc_memseq.v uses them to check that the token actually orders
# the accesses.  They cost nothing when unused -- a station without :seq is
# byte-identical to what this script emitted before they existed.
python3 ../bdc/mem.py port:10:32:2 store:10:32 load:10:32 \
        store:10:32:seq load:10:32:seq portarb:10:32:2 \
        -o build/gen/bdc_mem_units.v
echo "wrote build/gen/bdc_mem_units.v"
