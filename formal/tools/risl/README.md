# Reset island over the timed certificate's exact nodes (shard C, 2026-11-08)
`gen.py` writes `Formal/Net/CViewPS/RIslData.lean` from `formal/tools/quiet/reset_island.txt`: 3,224 members
(node, value, forcing pins, ρ ≤ 14) in 62 blocks, routed by a search tree.
The check and the theorem (`rEntryOK`, `reset_quiet_PS`) are in `formal/lean/Wip/RIsl/`. They are not compiled
yet, because the modules they import (BoundaryReset) had no oleans in this session. To finish: compile RIslDefs,
time RIslChk00, generate the remaining chunk files and RIslChk.lean, compile RIslPS, then move all of them into
Formal/Net/CViewPS and run check.sh.
