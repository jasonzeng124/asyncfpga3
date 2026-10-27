# Audit report

Auditor: independent audit session (see JOURNAL.md). Verdicts: CONFIRMED / REFUTED / OVERSTATED / UNVERIFIED.
Audited commits (this pass): claude/formal 71ee3e86, claude/research 19a93c1.
Toolchain for Lean: Lean 4.35.0 release zip (sha256 of bin/lean bf8d54e4...), installed by audit/tools/install_lean.sh; Mathlib per their lake-manifest (rev 56a00585), built from source.

## REFUTED / OVERSTATED
| branch | commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|---|
| research | 19a93c1 | BOARD-QUEUE #3 title "~9% more laps than #2"; body "Laps vec 6 mean 50.0 (46-52) vs 45.75 for #2 on the same 4 seeds" | OVERSTATED | audit/findings/research-stats.md (their own JOURNAL tables, recomputed) | 50.0 is an 8-route mean (d,3-9), 45.75 is #2's 4-seed mean (d,3,4,5). Same 8 routes: vec6 50.0/47.25=+5.8%, vec12 +6.0%, vec13 +5.8%. ~9% exists only in the 4-seed A/B (+8.2%). Per-seed FF values not in journal: 50.0 itself UNVERIFIED |

## CONFIRMED / UNVERIFIED
| branch | commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|---|
| research | 19a93c1 | BOARD-QUEUE #2 "vec 6 ... mean 47.3, vs 24-26 unsized" (~1.9x), vec12 38.1, vec13 55.4 | CONFIRMED (arithmetic only) | audit/findings/research-stats.md | means recomputed from per-seed table; per-seed laps themselves not yet reproduced |
| research | 19a93c1 | gcd_rig.v: "Every expected value here was produced by bdc/simcheck.py's ref_gcd" (oracle for BQ#1-#3) | CONFIRMED | audit/oracle/ (dynamatic gcd.c compiled by the auditor, 16/16 equal) | oracle is derived from the C, not recorded from a run |
| research | 19a93c1 | toolchain: nextpnr sha256 9c732bc6303458df with all 9 patch fingerprints | CONFIRMED | ~/audit-tc rebuilt by cloud/setup-toolchain.sh (cache), own sha256sum 9c732bc6303458dfed29...; yosys 4726b5a4... | matches research/board/gcd_hw_03e82630.toolchain.txt |
| research | 19a93c1 | BOARD-QUEUE #1 "sha256 03e82630dcf5...41196" of research/board/gcd_hw_03e82630.bit | CONFIRMED | `sha256sum research/board/gcd_hw_03e82630.bit` | file integrity only; route reproduction pending |
| formal | 71ee3e86 | no sorry/admit/native_decide/axiom/opaque/extern/implemented_by/unsafe/csimp in Formal/ | CONFIRMED (textual) | grep in JOURNAL 03:4x; only 2 hits, both in doc comments | kernel-level axiom audit pending (audit/tools/axiom_audit.sh) |
