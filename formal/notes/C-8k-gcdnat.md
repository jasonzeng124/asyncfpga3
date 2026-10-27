# C-8k: gcd_hw C function = Nat.gcd on [0,2^31)^2, and liveness of the bdc gcd graph

Status: IN PROGRESS (notes written first; updated as files check).

Plan: per-op i32 lemmas (shrsi/cmpi/absd/minC/shli on values < 2^31), then
loop3 = 8b's `shared`, strip = 8b's `strip2`, mainLoop = gcd with a log fuel
bound, then the corollary on the imported graph and a liveness theorem from
8b's `prefix_run`.
