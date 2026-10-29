# A-e9setup (probe E9Setup, shard A): select rows on the corrected arbiter core, setup rows, design_verdict9_full

STATUS (2026-10-29 12:25 UTC): IN PROGRESS. Events9Setup.lean compiles in my overlay (not yet
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
