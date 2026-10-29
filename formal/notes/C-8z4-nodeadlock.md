# C-8z4: H_NO_DEADLOCK'' by route B -- (in progress)

Shard C, probe 8z4, 2026-10-29.

Status: IN PROGRESS. Working notes; the final version replaces this file.

- Route B (walk simulation) assessed: the data-arrival and return-to-zero capacity parts are a
  multi-day proof; not attempted in full.
- Instead: exhaustive interleaving search with stubborn-set reduction (`Wip/C8z4/explore.py`),
  concrete vectors and an abstract-data mode that covers every input.
- First run found a "deadlock" that was a late-binding bug in the explorer (grant guard read
  the wrong `z`); caught by the independent replay (`Wip/C8z4/replay.py`, 8z2's gate encoding).
