#!/bin/bash
cd /tmp/claude-0/bsub1/tocc812 && python3 sim.py 1 8 12 > sim_c1.log 2>&1 && python3 data.py 1 > data_c1.log 2>&1
cd /tmp/claude-0/bsub1/tocc1071 && python3 sim.py 1 1071 462 > sim_c1.log 2>&1 && python3 data.py 1 > data_c1.log 2>&1
echo done > /tmp/claude-0/bsub1/prep.done
