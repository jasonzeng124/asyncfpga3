# C-witgen: an ACTIVE witness for the generated-cell capstones (O4, O4b)

Shard C, probe witgen, 2026-10-29. Status: IN PROGRESS (draft saved early).

## Verdict (draft)

- gcd_hw (a = 12, b = 18): one unit-delay run of the concrete 465-channel network at the
  generated-netlist level satisfies every hypothesis of O4's `gcd_hw_circuit_safe_gen`, O4b's
  `gcd_hw_circuit_safe_genK` and the PersistK `gcd_hw_circuit_safe_genP` together, with every
  internal node (bd_ctree nodes, bd_join nodes, `uor`, `|j`, R0, every delay-chain stage) and
  closes out0 with 6 at tick 1147. `Formal/Net/GenWit.lean`, `gcd_hw_gen_all_witness`.
  check.sh: 6638 declarations, OK.
