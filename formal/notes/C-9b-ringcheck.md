# C-9b: verified ring-depth checker (track 9 companion)

Status: IN PROGRESS (notes kept current as work proceeds).

Plan: per-source capped Bellman-Ford over Nat weights (values in [0,k], k =
"unreached"), fixpoint detection, fuel n*k+1 justified by a strictly
decreasing potential. Spec: every closed walk has stage sum >= k.
