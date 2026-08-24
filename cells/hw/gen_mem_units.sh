#!/usr/bin/env bash
# Generate the memory units cells/tb/tb_bdc_mem.v needs.
#
# Cheap, deterministic, and needs no toolchain -- but it does need to exist
# before run_sim.sh will run that bench, and run_sim.sh SKIPs rather than fails
# when a declared requirement is missing.  A skip is not a pass; run this.
set -eu
cd "$(dirname "$0")/.."
mkdir -p build/gen
python3 ../bdc/mem.py port:10:32:2 store:10:32 load:10:32 \
        -o build/gen/bdc_mem_units.v
echo "wrote build/gen/bdc_mem_units.v"
