import Formal.Net.FasmLink.LinkArb
import Formal.Net.Import.Proofs
open Formal.Net.FasmLink Formal.Net.Import Formal.Net.Import.Gen

namespace Formal.Net.FasmLink.LinkArb

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

end Formal.Net.FasmLink.LinkArb
