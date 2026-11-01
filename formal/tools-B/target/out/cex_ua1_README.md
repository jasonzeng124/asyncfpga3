# Candidate counterexample (simulation, UNTRUSTED): arbiter 0's acknowledge C-element latches a runt

Netlist: the decoded target as committed in Lean (formal/lean/Formal/Target/Net/*.lean, generator md5
of A's net 7c41591d), rebuilt as JSON by `tools-B/target/lean2json.py`. Simulator: shard A's sim.py
(copied as `tools-B/target/simb.py`, + `--posmap`/`--kappa`). Transport, one fixed delay per pin arc.

Delay assignment (Spec `Adm` with g = 1, κ = KAPPA, corner c = 0.5): every arc at the middle of its
corner window, except the gates in `cex_ua1_posmap.json` (value -1: fast end
max((1-κ)·lerp(FAST_MIN, SLOW_MIN, c), FAST_MIN); value 2: slow end min((1+κ)·lerp(FAST_MAX, SLOW_MAX, c),
SLOW_MAX)): the causal path from ua1's rise to its g-pin fall (fast) and ua1's feedback route + ua1
itself (slow). ua1 = SLICE_X2Y18.DLUT.O6 (table = C(A0, g) with reset).

Reproduce (sequential env, rig vector (12, 18)):

    python3 tools-B/target/lean2json.py formal/lean/Formal/Target/Net net.json arbs.json
    python3 tools-B/target/simb.py net.json formal/tools-A/target/out/boundary_03e82630.json \
        --pairs 0xC,0x12 --corner 0.5 --kappa 0.215 --tmax 620000 \
        --posmap formal/tools-B/target/out/cex_ua1_posmap.json --dump d.json

Observed: κ <= 0.21: ua1 rises once at ~600.99 ns and holds (clean). κ = 0.215: ua1 rises at 600.991 ns,
falls at 601.885, rises at 601.892, ... (period 894 ps, a 7 ps runt circulating in its feedback loop); by
620 ns 5336 nodes toggle (some every ~5 ps); no out0 by 620 ns (correct run: out0 = 6 at 756 ns).
κ = 0.22-0.3: same shape, longer runts. Mid-window everywhere (no posmap): correct, out0 = 6.
