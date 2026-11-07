import Formal.Core.EnvFast.Link2

/-!
# Wip/EnvFast — open items of the fast Env checker (NOT built, NOT claimed)

See `formal/notes/A-envfast.md`. Nothing here is used by `Formal/`.

1. `Env.Wip.link2_sound` (`Wip/Env.lean`) is proved as
   `Formal.Core.EnvFast.link2_sound`, for `EnvFast.link2Model`, a verbatim copy of
   `Env.Wip.link2Model` (the Wip file is not built, so it cannot be imported). The
   lead can replace the Wip conjecture by an import of `Formal.Core.EnvFast.Link2`.
2. Not done: bd_mux (`bd_mux_uj0/uj1/uor`, select-steered join) and bd_arb (needs
   a model of the arbiter's nondeterministic resolution). Both fit the same
   recipe: a `Model` in `EnvFast/Models.lean`, tables added to `luts` in
   `formal/tools-A/envfast/Gen.lean`, a `CModel` with `kb` guards, chunk theorems.
3. Cheaper `kpersist`: a bit-parallel form
   `((x0 ^^^ (x0 &&& x1)) minus t, minus env bits if t is env) % 2^n == 0`
   would replace the `n`-step loop; not needed at the current sizes.
-/

namespace Formal.Core.EnvFast.Wip

open Formal.Core.Env Formal.Core.EnvFast

/-- Sanity statement of item 1 (the model is the one of the Wip conjecture). -/
example : (link2Model ⟨true, true, true, false⟩).n = 10 := rfl

end Formal.Core.EnvFast.Wip
