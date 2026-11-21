import Formal.Net.FasmLink.LinkArb
import Formal.Net.FasmLink.S1
import Formal.Net.FasmLink.S2
import Formal.Net.FasmLink.S3
import Formal.Net.FasmLink.S4
import Formal.Net.Import.Proofs

/-!
# Track 11c: four routes of `link_arb`, read from the bits, equal its yosys netlist

`formal/tools/fasm2lean2/route.sh SEED` (toolchain.sh ok, nextpnr sha256
9c732bc6303458df, `--freq 100 --ignore-loops --seed SEED`), seeds 1..4; the
physical nets `S<n>.net` are extracted by `fasm2lean2.py` from the FASM read
back from each `.bit` (xc7frames2bit -> bitread -> bit2fasm) and prjxray-db
alone. `S<n>.rho` is the renaming proposed from nextpnr's placement (a hint:
`check` would fail on a wrong one, see `wrong_rho_caught`).

## Proved here (`decide` on `Design.check`, then `Design.check_sound`)

* `seed1_correct` .. `seed4_correct`: `Design.Correct` for each route: for all
  values of the 9 input ports and the 7 logical state nets (bd_link's `c`,
  `q[0..2]`; bd_arbiter's `ua1.q`, `ua2.q`, `q`), 11a's `Netlist.next` and
  `Netlist.outs` of the yosys-imported `bd_c2n`, `bd_latch_W3` and
  `bd_arbiter` equal the physical LUT netlist's excitation of the renamed
  LUT outputs and its 10 output ports; plus the structural facts (renaming
  injective, ports and LUT counts match).
* `wrong_rho_caught`: swapping two state nets in the renaming (arbiter `q` and
  `ua1.q`) is rejected: the renaming is checked, not trusted.
* `grant_exclusion`, `grant_exclusion_s1..s4`: transfer through 11a's
  `bd_arbiter_outs_spec`: on every one of the four routes, the grant PORTS
  driven by the bits are never both 1 (binary, any state).
-/

namespace Formal.Net.FasmLink.LinkArb
open Formal.Net.FasmLink Formal.Net.Import Formal.Net.Import.Gen

theorem seed1_correct : (design S1.net S1.ports S1.rho).Correct := Design.check_sound _ (by decide)
theorem seed2_correct : (design S2.net S2.ports S2.rho).Correct := Design.check_sound _ (by decide)
theorem seed3_correct : (design S3.net S3.ports S3.rho).Correct := Design.check_sound _ (by decide)
theorem seed4_correct : (design S4.net S4.ports S4.rho).Correct := Design.check_sound _ (by decide)

/-- Negative control on the witness: seed 1's renaming with the arbiter's
`ua1.q` and `q` swapped. -/
def wrongRho : List (List PSrc) :=
  match S1.rho with
  | [a, b, [x, y, z]] => [a, b, [z, y, x]]
  | r => r

theorem wrong_rho_caught : ¬ (design S1.net S1.ports wrongRho).Correct :=
  Design.not_correct _ (by decide)

def arbI : Inst := ⟨"arb", Gen.bd_arbiter, [.port "rst", .port "r1", .port "r2", .port "A0"],
    [(0, "A1"), (1, "A2"), (2, "R0"), (3, "g1"), (4, "g2")]⟩

theorem arb_logical (net ports rho) (h : (design net ports rho).Correct) (val : Sig → Bool) :
    ∃ r, rho[2]? = some r ∧ (design net ports rho).InstOK val 2 arbI r := by
  obtain ⟨hs, hc⟩ := h
  have hlen : rho.length = 3 := by have := hs.1; simpa [design, insts] using this
  have h2 : 2 < rho.length := by omega
  exact ⟨rho[2], List.getElem?_eq_getElem h2, hc val 2 arbI rho[2] rfl (List.getElem?_eq_getElem h2)⟩

theorem arb_lins (val : Sig → Bool) :
    Design.lins val arbI = [val (.port "rst"), val (.port "r1"), val (.port "r2"), val (.port "A0")] := rfl
theorem arb_lst (val : Sig → Bool) :
    Design.lst val 2 arbI = [val (.st 2 0), val (.st 2 1), val (.st 2 2)] := rfl

/-- **Transfer.** On any routed seed whose bits pass `Correct`, the two grant
PORTS the bitstream drives are never both 1 (binary, every valuation of the
inputs and of the arbiter's state nets). -/
theorem grant_exclusion (net ports rho) (h : (design net ports rho).Correct) (val : Sig → Bool) :
    ¬ ((design net ports rho).pport val "g1" = some true ∧
       (design net ports rho).pport val "g2" = some true) := by
  obtain ⟨r, _, hi⟩ := arb_logical net ports rho h val
  have h1 := hi.2 (3, "g1") (by decide)
  have h2 := hi.2 (4, "g2") (by decide)
  rw [arb_lins, arb_lst] at h1 h2
  simp only [arbI] at h1 h2
  rw [Proofs.bd_arbiter_outs_spec] at h1 h2
  rintro ⟨e1, e2⟩
  rw [← h1] at e1; rw [← h2] at e2
  simp at e1 e2
  rw [e1.2] at e2; simp at e2

theorem grant_exclusion_s1 (val : Sig → Bool) :
    ¬ ((design S1.net S1.ports S1.rho).pport val "g1" = some true ∧
       (design S1.net S1.ports S1.rho).pport val "g2" = some true) :=
  grant_exclusion _ _ _ seed1_correct val
theorem grant_exclusion_s2 (val : Sig → Bool) :
    ¬ ((design S2.net S2.ports S2.rho).pport val "g1" = some true ∧
       (design S2.net S2.ports S2.rho).pport val "g2" = some true) :=
  grant_exclusion _ _ _ seed2_correct val
theorem grant_exclusion_s3 (val : Sig → Bool) :
    ¬ ((design S3.net S3.ports S3.rho).pport val "g1" = some true ∧
       (design S3.net S3.ports S3.rho).pport val "g2" = some true) :=
  grant_exclusion _ _ _ seed3_correct val
theorem grant_exclusion_s4 (val : Sig → Bool) :
    ¬ ((design S4.net S4.ports S4.rho).pport val "g1" = some true ∧
       (design S4.net S4.ports S4.rho).pport val "g2" = some true) :=
  grant_exclusion _ _ _ seed4_correct val

end Formal.Net.FasmLink.LinkArb
