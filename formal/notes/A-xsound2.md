# A-xsound2: xaudit's timed verdict is sound for continuous-time transport/inertial channels (probe XSound2, shard A)

STATUS: in progress (session 2026-10-29, restarted from the 2026-10-28 WIP snapshot
Wip/_snapA; nothing claimed yet). Plan:
1. `Formal/Core/XSimChan.lean` (Mathlib-free): XSim soundness for an ARBITRARY time type
   with a cell map `c : τ → ℕ` (abstract step k covers every instant of cell k), for any
   channel satisfying the step-level property `ChanCells`.
2. `Formal/Core/XSimChanReal.lean` (Mathlib): `ℝ`-time channels; `Follows L Lo Hi`;
   transport `Chan` and (bounded) inertial channels are instances; cells of width q.
   Counterexample: inertial with rejection window wider than the abstract window is NOT
   covered by xaudit.
3. `Formal/Core/XAudit/SoundCells.lean`, `SoundPhys.lean`: end-to-end statements for
   `auditF` / `noXF`.
4. `Formal/Core/XAudit/SoundChain.lean`: covered-window sound_postfix under Stale; W1 chaining.
