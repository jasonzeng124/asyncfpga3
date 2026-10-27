# Research statistics recomputed from the research journal's own tables (claude/research 19a93c1)

Raw GLS logs are not committed (they live in build/), so recomputation is from the per-seed tables in
research/JOURNAL.md. Arithmetic by hand / python, recorded here.

## BOARD-QUEUE #2 (R5): JOURNAL 20:38 table
vec 6: 47 42 45 49 50 48 49 48 -> sum 378, mean 47.25 (claim 47.3) OK
vec 12: 38 34 37 39 41 39 39 38 -> 305/8 = 38.125 (claim 38.1) OK
vec 13: 56 49 53 57 59 56 57 56 -> 443/8 = 55.375 (claim 55.4) OK
"~1.9x laps": 47.25 / 25 (midpoint of unsized 24-26) = 1.89 OK. "Worst seed (3) 1.6x best unsized": 42/26 = 1.62 OK.

## BOARD-QUEUE #3 (R5 + link fast fall): OVERSTATED
Headline: "~9% more laps than #2". Body: "Laps vec 6 mean 50.0 (46-52) vs 45.75 for #2 on the same 4 seeds;
vec 12 40.4, vec 13 58.6".
- 50.0 is a mean over the 8 routes d,3-9 (commit 65881ee: "on 8 routes ... vec 6 50.0 laps (46-52)").
- 45.75 is #2's mean over 4 seeds d,3,4,5 only: (47+42+45+49)/4 = 45.75.
- So the sentence compares an 8-seed mean with a 4-seed mean while saying "on the same 4 seeds".
- Same 8 seeds (#2 table above): vec 6 50.0/47.25 = +5.8%; vec 12 40.4/38.125 = +6.0%; vec 13 58.6/55.375 = +5.8%.
- The only ~8-9% figure is the 4-seed A/B (JOURNAL 22:10: 45.75 -> 49.5, +8.2%).
- "Routed GLS predicts ~0.92x of #2" -> 8-seed data give 47.25/50.0 = 0.945x.
Verdict: OVERSTATED. On their own 8-route data the gain is ~6%, not ~9%. Per-seed FF values for 8 routes are not in
the journal, so 50.0 itself is UNVERIFIED until reproduced.
