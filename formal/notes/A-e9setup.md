# A-e9setup (probe E9Setup, shard A): select rows on the corrected arbiter core, setup rows, design_verdict9_full

STATUS (2026-10-29, start): IN PROGRESS. Nothing claimed yet.

## Plan
1. Regenerate the select channel map (copy of selhold/mkmap.py, selrun/certsel.py into
   tools-A/xaudit/setup/) against the corrected-arbiter-core certificate (cert9p, E9Par), and
   rerun selT/selJ (xselL) on the 16 rows on top of the Events9Par log.
2. H_SEL_SETUP / H_SEL_O as checked rows: read C's tcheck rule E (formal/tools/tcheck,
   Formal/Timing/Rules.lean, notes/C-*.md, read-only); import or write A's own row + soundness.
3. Events9Full*.lean: design_verdict9_full = Events9Par verdict + selJ rows + setup rows; exact
   remaining hypothesis list; table of CLEAN rows.
