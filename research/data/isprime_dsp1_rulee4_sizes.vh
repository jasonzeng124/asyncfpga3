// Rule E padding for isprime BD_DSP=1, from skew.py "fix:" asks on placeholder seeds 1-4:
// placeholder + worst ask + 2.  Only lengthens.
`define BD_SZ_UUT_ULINK_N29__0 14
`define BD_SZ_UUT_ULINK_N29__1 21
`define BD_SZ_UUT_ULINK_N44__0 13
`define BD_SZ_UUT_ULINK_N44__1 12
`define BD_SZ_UUT_ULINK_N44__3 13
`define BD_SZ_UUT_ULINK_N66__0 15
`define BD_SZ_UUT_ULINK_N66__1 11
`define BD_SZ_UUT_ULINK_N66__2 17
`define BD_SZ_UUT_ULINK_N66__3 18
`define BD_SZ_UUT_ULINK_N79__0 10
`define BD_SZ_UUT_ULINK_N79__1 14
`define BD_SZ_UUT_ULINK_N79__2 11
// Round 2 (asks on fresh seeds 5-8, worst + 2): n66__1 7->11, n66__0 9->15, n44__0 10->13, n29__0 10->14 (edited above); rule I seed 6: SDELAY 3 -> 4 + 2.
`define BD_SZ_UUT_ULINK_N_TRUERESULT_62_SDELAY 6
// Round 3: fresh seed 11 (round 2) asked 1 more on ulink_n66__3 (at 15) -> 15 + 1 + 2 = 18 (edited above).  ucond_br16 has no attributable knob (skew.py: reported, not padded).
// Round 4: fresh seeds 13-16 asked n29__1 +9 (at 10) -> 21 and n66__2 +5 (at 10) -> 17 (edited above).  ucond_br16 unattributable; rule J placement-only.
