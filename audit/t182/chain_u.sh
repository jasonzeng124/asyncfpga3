#!/usr/bin/env bash
# T182 queue for the unpadded half after its fastmin run: the split replay first, then its other 4 corners one at a time
A=/home/user/asyncfpga3/audit/t182
until grep -q GLSDONE $A/unpadded_gls.log; do sleep 60; done
./split.sh unpadded split_c1_r0 1.0 0.0

bash ./gls_rest.sh unpadded
