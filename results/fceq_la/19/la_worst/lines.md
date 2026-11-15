## eventgraph, corner worst

- c0 critical: 36741 ps, 88 arcs, stages ulink_n13 1632/1632, ulink_n14__1 14441/14441, umux1 3195/1400; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 13416 (382) | 13841/13841 | E depends | 13193 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A5 | 0 / 68 / 171 / 307 / 0 |  | 14181 / 340 / 340 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A5 307 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1821 (440) | 2240/445 | A own | 2190 | umux1.uj1 -> umux1.uya.u/O6 | 0 / 0 / 0 / 479 / 68 |  | 2787 / 547 / 479 | 50 | 1 | 0 | 5 | umux1.uj1/O6 -> umux1.uya.u/A2 479 | F (own flush) margin 3159; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj1; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (376) | 774/774 | H own | 1930 |  ->  |  /  /  /  /  | 198-883 (32 bits) | 2938 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
