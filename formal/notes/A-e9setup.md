# A-e9setup (probe E9Setup, shard A): select rows on the corrected arbiter core, setup rows, design_verdict9_full

STATUS (2026-10-31, lead): Events9Setup / Events9Full / Events9FullMain CLAIMED as left on 2026-10-29
(checked 2026-10-31 by the lead, Lean 4.35.0, autoImplicit=false, scratch overlay; axioms standard). The
statement is `Events9Full.design_verdict9_full` (header of Events9Full.lean: one realisation for the
corrected arbiter core, the junction select rows and the setup rows; HARB7', HRst, H_BUNDLE, H_SEL_FN
remain hypotheses). No run table from the full verdict was committed; the plan below was not finished.
Earlier status line (2026-10-29 12:25 UTC): IN PROGRESS. Events9Setup.lean compiles in my overlay (not yet
check.sh). Map regenerated on the corrected-core certificates (identical content, 126/126 per seed).
Early finding (untrusted Python estimate, old core, d): with O = the request wire's rise (the earliest
time C's H_BUNDLE holds the bus), the junction-anchored setup row passes 81/126 literals at slow,
77 fast, 39 gb, 11 indep; the source-anchored form fails ~all (−15 ns: common-path pessimism on the
request delay line).

## Plan
1. Regenerate the select channel map (copy of selhold/mkmap.py, selrun/certsel.py into
   tools-A/xaudit/setup/) against the corrected-arbiter-core certificate (cert9p, E9Par), and
   rerun selT/selJ (xselL) on the 16 rows on top of the Events9Par log.
2. H_SEL_SETUP / H_SEL_O as checked rows: read C's tcheck rule E (formal/tools/tcheck,
   Formal/Timing/Rules.lean, notes/C-*.md, read-only); import or write A's own row + soundness.
3. Events9Full*.lean: design_verdict9_full = Events9Par verdict + selJ rows + setup rows; exact
   remaining hypothesis list; table of CLEAN rows.
