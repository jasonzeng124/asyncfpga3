# Audit journal

## 2026-10-27 -- branch created
Program in audit/PROGRAM.md.

## Session Tue Oct 27 03:27:09 UTC 2026
Session session_01HC49FyHr5QA8JKjiqPQGZv. Lock was free (epoch placeholder).
Audited heads: formal=71ee3e8 research=19a93c1.

### progress 03:32
Lean 4.35.0 from GitHub zip (audit/tools/install_lean.sh, no elan). Clean worktrees of
origin/claude/formal 71ee3e86 and origin/claude/research 19a93c1. `lake build` of formal running
(Cells built quickly; Mathlib from source in progress). Research toolchain restoring via
cloud/setup-toolchain.sh into ~/audit-tc (cache hit). Textual sorry/axiom grep clean (2 hits in
comments). Wrote audit/tools/axiom_audit.sh (own collectAxioms over every Formal.* constant).
Subagents running: A/B/C statement+witness+mutation audits, transcription fidelity, GLS
sample-at-fire reproduction, rules J/I/F reproduction. #1 bitstream sha256 matches.

### progress 03:33
Toolchain restored (nextpnr sha256 9c732bc6303458df = committed toolchain.txt). BQ#1 route rebuild started in
clean worktree wt-rb1 (19a93c1). BQ#3 "~9%" found OVERSTATED from their own tables (8-seed vs 4-seed mean);
see audit/findings/research-stats.md.

### progress 03:41
Subagent results in: GLS findings (4 CONFIRMED, research prims.v "identical timestamps" comment OVERSTATED),
rules J/I/F (shard B's "68-161 ps wrong way" REFUTED: fast/slow corners misread as rise/fall; I verified in
prjxray makesdf.py; research bd_prims_sim.v has the same misreading -> REFUTED), shard C (3 OVERSTATED, rest
CONFIRMED, 10/10 mutants break), transcription (0 mismatches). BQ#1 rebuilt from clean: sdf md5 and bit payload
identical; routed.json md5 not reproducible (embedded paths). Still running: shard A and B statement audits;
formal lake build (Mathlib).
