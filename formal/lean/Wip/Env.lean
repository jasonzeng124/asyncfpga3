import Formal.Core.Env

/-!
# Wip/Env — open items of the mechanised environment model (NOT built, NOT claimed)

See `formal/notes/A-env.md`. Everything below is either a conjecture
(`sorry`, clearly marked) or a model definition whose certificate is too
expensive for the kernel as currently encoded.
-/

namespace Formal.Core.Env.Wip

open Formal.Core.LutCells Formal.Core.Env

/-- bd_link with a W = 2 latch pair (LUT6_2 `bd_latch_u_L38`). Signals:
`req 0, c 1, ack 2, en 3, d0 4, d1 5, q0 6, q1 7, rdy 8, rst 9`. -/
def link2Model (A : LinkAsm) : Model where
  n := 10
  gates := [.lut 1 bd_c2n_u .O [9, 1, 2, 0], .wire 3 1,
            .lut 6 bd_latch_u_L38 .O5 [7, 5, 6, 3, 4],
            .lut 7 bd_latch_u_L38 .O6 [7, 5, 6, 3, 4]]
  env := [(4, fun s => !bit s 8 && !bit s 0 && !bit s 1),
          (5, fun s => !bit s 8 && !bit s 0 && !bit s 1),
          (8, fun s => (!bit s 8 && !bit s 0 && !bit s 1) || (bit s 8 && bit s 0)),
          (0, fun s => (!bit s 0 && bit s 8 && !bit s 1) || (bit s 0 && bit s 1)),
          (2, fun s => bit s 2 != bit s 1)]
  prio := (if A.ruleH then [(3, 4), (3, 5), (3, 8)] else []) ++
          (if A.ruleL then [(6, 3), (7, 3)] else []) ++
          (if A.isoEn then [(3, 2)] else []) ++
          (if A.rxBundle then [(6, 2), (7, 2)] else [])
  inits := (List.range 16).map (· * 16)

/-- CONJECTURE. Evidence: the Python prototype (`/tmp/env/proto2.py`, same
semantics) finds 1048 states and no violation; compiled `#eval` of `certify`
returned `true` for the variant with `rxBundle` (752 states, with `linkQ`).
The kernel `decide +kernel` run exceeded 6 GB RSS and was killed. Needs a
cheaper encoding (see notes). -/
theorem link2_sound : Sound (link2Model ⟨true, true, true, false⟩)
    (live (link2Model ⟨true, true, true, false⟩)) := by
  sorry

end Formal.Core.Env.Wip
