# Full-stack GLS: bits-decoded netlist + prjxray SDF + GLS_MODEL=fid (session 2026-10-27 10:12)

cells/gls/fid/build_fid.sh HWDIR WORK bit with GLS_SDF=<xray_delay.py SDF> GLS_SDF_FIELD=<col> GLS_MODEL=fid, then
run_fid.sh (16 vectors, 150 us each). Laps = completed gcd results in 150 us; errs = wrong results. Toolchain nextpnr
9c732bc6303458df, patches 789a7120c912d393, prjxray-db 0a0added. Column: min = FAST_MIN, max = SLOW_MAX, band = FAST_MIN +
0.38 (SLOW_MAX - FAST_MIN).

| run | route / bits | col | bits vs JSON | vectors done | errs | laps v6/v12/v13 | never complete |
|---|---|---|---|---|---|---|---|
| bq3_max | BQ#3 route (sdf 61e14755) | max | EQUIVALENT (only the benign kinds above) | 16/16 | 0 | 33/27/39 | - |
| bq3_min | BQ#3 | min | EQUIVALENT (only the benign kinds above) | 16/16 | 0 | 91/75/108 | - |
| bq3_band | BQ#3 | band | EQUIVALENT (only the benign kinds above) | 16/16 | 0 | 55/45/64 | - |
| nf_good_max | nofuse route (sdf c647eb1a), patched bits | max | EQUIVALENT (only the benign kinds above) | 16/16 | 0 | 17/13/20 | - |
| nf_bug_max | nofuse route, UNPATCHED lut-pinmap bits | max | NOT EQUIVALENT | 9/16 | 0 | 0/0/0 | 5,6,7,8,11,12,13 |
| bq1_max | bq1_max |  | EQUIVALENT (only the benign kinds above) | 16/16 | 0 | 16/12/18 | - |
