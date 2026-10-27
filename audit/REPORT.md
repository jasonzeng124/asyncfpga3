# Audit report

Auditor: independent audit session (see JOURNAL.md). Verdicts: CONFIRMED / REFUTED / OVERSTATED / UNVERIFIED.
Audited commits (this pass): claude/formal 71ee3e86, claude/research 19a93c1.
Toolchain for Lean: Lean 4.35.0 release zip (sha256 of bin/lean bf8d54e4...), installed by audit/tools/install_lean.sh; Mathlib per their lake-manifest (rev 56a00585), built from source.

## REFUTED / OVERSTATED
| branch | commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|---|
| (pending) | | | | | |

## CONFIRMED / UNVERIFIED
| branch | commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|---|
| research | 19a93c1 | BOARD-QUEUE #1 "sha256 03e82630dcf5...41196" of research/board/gcd_hw_03e82630.bit | CONFIRMED | `sha256sum research/board/gcd_hw_03e82630.bit` | file integrity only; route reproduction pending |
| formal | 71ee3e86 | no sorry/admit/native_decide/axiom/opaque/extern/implemented_by/unsafe/csimp in Formal/ | CONFIRMED (textual) | grep in JOURNAL 03:4x; only 2 hits, both in doc comments | kernel-level axiom audit pending (audit/tools/axiom_audit.sh) |
