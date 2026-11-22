# The search's structure, built as modelled: AUTO_SEARCH_KEEPDEPTH (2026-11-22)

Research bot, session cluster-research-29671222-2. nextpnr 6e5d224472232d5d (cells/verify/toolchain.sh all ok).

## The miss

The sizing loop's search phase (research/tools/auto/auto_size.sh search_phase, research/tools/eventgraph/search.py
--all-sites) predicts the period of each candidate storage structure on the base route's timed event graph
(research/tools/eventgraph/whatif.py) and builds the best one. Over every flow v10 / v11 search route, built P over
predicted P was 0.88-1.22, except quadrec: 1.96-2.17 on all three seeds whose search route was built (predicted
18.2-20.4 ns, built 39.4-41.0 ns).

## The cause

quadrec rotates four values (a <- b <- c <- d <- t). bdc's token floor (bdc/emit.py ring_depths, "THE MODEL" and
"WHAT THAT SAYS": two stages on each rotation back edge) builds the three rotation back edges as 2-stage pipes
(ulink_n_trueResult_16 / _18 / _20). The search chose latches on three fork outputs (BDC_FORK_OUT_LINK=n20__0, n23__0,
n25__0, with rule F's n27__0). whatif.py priced them with every other link at its depth on the base route. bdc, emitting
the new structure, counted the new links as storage on the same rings and lowered the three pipes to 1-stage links:
the build held exactly the floor's storage, as before, and the critical cycle still threaded all four rings with one
token (quadrec_s3/links_10.txt vs links_11.txt).

## The check (flow v10's quadrec seed 3, farm suite13t_s5a_v10_3a task 14, rebuilt here; files in quadrec_s3/)

| route | structure | sdf | P untrimmed |
|---|---|---|---|
| it 10 (base) | the loop's | 0ed89d69 (= farm) | 42568 ps |
| it 11 (search, as the flow built it) | + 3 fork-output links; the three pipes lowered to 1 stage | 961c94c6 (= farm) | 43402 ps |
| it 11 with the base depths kept | + 3 fork-output links; BDC_LINK_DEPTHS=ulink_n_trueResult_16=2,_18=2,_20=2 | 61636315 | **21199 ps** |

search.py on the rebuilt base graph with the same edits: 20924 ps. Same sizes (sizes_11.vh), seed 3, EQUIVALENT. One
route, not rule-checked, no draws: it measures the structure.

## The knob

auto_size.sh AUTO_SEARCH_KEEPDEPTH=1 (opt-in, e8e2349a7): after the search's structure is emitted, every link it would
make shallower than on the base route keeps its base depth (merged into BDC_LINK_DEPTHS, which may only raise a depth
above the floor), and the structure is emitted again; the log names each pin (kd_pins.py is its helper, as a script).

census_v10.tsv (census_run.sh): for each of flow v10's 89 (kernel, seed) search structures, the base and the search
structure emitted by bdc and compared. 85: nothing to pin. quadrec s1-s4: the same three pipes. So on v10's structures
the knob changes quadrec's search builds and nothing else.

## Not shown yet

The knob in a full loop (local: quadrec s1-s3 under flow v13's environment, research/JOURNAL.md 2026-11-22); whether a
search on a later flow's routes picks structures elsewhere that bdc would lower.
