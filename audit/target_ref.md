# Reference md5s for auditing formal/target/ (the bitstream theorem's target)

Owner priority (audit/PROGRAM.md, 2026-10-31): the target must be the BOARD-QUEUE #1 build on claude/research, one seed.
These are the auditor's own rebuild values (research checkout 4b922e9b, toolchain fingerprint nextpnr 9c732bc6303458df),
BOARD-QUEUE #1 command at the default seed (audit/r23/route_bq1.sh), rebuilt three times on 2026-10-31 with the same sdf.

| file | md5 | note |
|---|---|---|
| gcd_hw.sdf | 6f8b99e6c49bb7ef8855c881cecabe5c | = BOARD-QUEUE #1's recorded sdf md5 |
| gcd_hw_xray.sdf | 357f17cb33a6ae47bd8653fa47eb99a2 | = research bq1_fullstack_8seed.tsv row d |
| gcd_hw.fasm | 1a3909f6bd7395df0ae764875d289f00 | own build (copy in /root/bq1ref, not committed) |
| gcd_hw.bit | f7f3450081353e2a7c368f068184d440 | whole-file md5 is not reproducible (header date) |
| bit payload from sync word AA995566 | 2181bd85... (2083692 bytes) | IDENTICAL to research/board/gcd_hw_03e82630.bit's payload (whole file 594bd861) |
| gcd_hw_routed.json | 9f6f3583fdc3457c5914f14887d121b3 | routed.json md5 known not reproducible (BOARD-QUEUE #1 note) |

Seed-9 BQ#1 route (if the target picks seed 9): sdf 81d27cf3, xray 7a495c31 (both reproduced, audit/r23/route_bq1_9.log).
Check for the target: README md5s == files; .fasm == the above (or the named seed's rebuild); .bit payload == the above.
