# Quiet start at reset: coverage of the timed certificate's exact nodes (shard C, 2026-11-08; untrusted Python)

These scripts read /tmp/claude-0/tocc/model.pkl (built by formal/tools/tocc/build.py). Node ids are Lean's.
- tern.py: ternary fixpoint under reset (rst=1, requests/acks 0, buses free). It reports Q1 counts and blockers.
- island2.py: the same with data nodes banned as forcing sources. rst is the only environment node needed.
- arb.py: the 9 arbiter states are forced to 1 by rst=1 together with their k=0 VCC pin.
- rho.py: the forcing ranks. It writes reset_island.txt, a list of 3,224 members with value and ρ ≤ 14.
- mbound.py: the pin bound M over the members, 4,636 ps (c=1) and 2,234 ps (c=0).
- simcheck.py: agreement with the tocc transport simulation at R-1.
Result: all 3,217 exact nodes are forced during reset by rst alone. Each storage self-pin was tried at both values.
