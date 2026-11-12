# THE target's datapath units vs Net/Compute's yosys cells (shard C, 2026-11-09; UNTRUSTED Python)
Inputs (not committed, large): ps.json = `xz -dc formal/target/gcd_ps_e6bb4aec.json.xz`, ps.routed.json =
`xz -dc formal/target/gcd_ps_e6bb4aec.routed.json.xz`, net.json = tools-B/target/lean2json.py on Formal/Target/NetPS.
`check_unit.py` maps each yosys cell of a `bdc_fused_<u>` unit to its placed site (NEXTPNR_BEL, X_ORIG_PORT_*), and checks
the DECODED gates there compute the cell for every input (pin permutation, route-through LUT1 hops, constant pins and O5
packing folded). `run_all.sh` -> run_all.out: 20 units, 2,840 cells, 3,050 outputs, 0 failures. `negctl.py`: a flipped INIT
bit, a re-pointed pip, a flipped CARRY4 half are each caught. `extract_cmp.sh`: tools/compute/extract.py on gcd_ps gives
Lean byte-identical to Gen/Compute/GcdD/* for 19 of 20 units; uori4 differs (abc chose other LUTs, same op).

## Timed units (2026-11-10)
`psmapT.py UNIT` writes the timed certificate `Gen/Compute/PSMap/<Unit>T` (topological gate order picked from decoded
chunks, slow-max depth SN, D = max); the held inputs are now every node of the untimed certificate's input map
(`maps.psi`; uselect1's 2026-11-09 certificate used the two 32-bit inputs, `KNOWN_E01=1` reproduces it).
`psunitT.py UNIT` writes `Net/Compute/PS/<Unit>T.lean` (`<unit>_settled`, `<unit>_timed`, and the `_circ` versions over
`circuit net boundary`) from a template of Uselect1T.lean. Both untrusted; the kernel checks every gate, order and bound.
