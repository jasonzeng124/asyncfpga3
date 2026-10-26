// Rule E padding for ipow (BD_DSP=1), from skew.py "fix:" asks on placeholder seeds 1-4:
// placeholder + worst ask + 2.  Only lengthens.
`define BD_SZ_UUT_ULINK_N17__2 30
`define BD_SZ_UUT_ULINK_N17__1 10
`define BD_SZ_UUT_ULINK_N_INDEX_15 12
// Round 2: umux0 asks on fresh seeds 7 (10) and 8 (3) -> ulink_n17__0 placeholder 8 + 10 + 2.
`define BD_SZ_UUT_ULINK_N17__0 20
// Round 3: fresh seed 12 (round 2) asked 2 more on ulink_n17__2 (at 26) -> 26 + 2 + 2 = 30 (edited above).
