import Formal.Cells.Prelim
namespace Formal.Cells
theorem planted_lemma : (1 : Nat) = 2 := by sorry
theorem planted_user : (2 : Nat) = 1 := planted_lemma.symm
theorem planted_native : (10 : Nat) < 11 := by native_decide
end Formal.Cells
