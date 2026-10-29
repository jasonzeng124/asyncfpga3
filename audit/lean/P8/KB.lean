import Formal.Cells.KleeneBox
/-! P8 item 2: H_KLEENE_LUT (lutK = Core mux tree) vs the exact ternary
extension (closure over all Boolean completions), computed independently here,
for the real INITs of the cells KleeneBox uses. -/
namespace Audit.P8.KB
open Formal.Cells
open Formal.Cells (lutK K3)

abbrev K := Formal.Cells.K3

/-- my own completions -/
def comps : List K → List (List Bool)
  | [] => [[]]
  | a :: as =>
    let r := comps as
    (if a = .t then [] else r.map (false :: ·)) ++ (if a = .f then [] else r.map (true :: ·))

def idx : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * idx bs

/-- exact ternary extension of the truth table -/
def ext (init : Nat) (ins : List K) : K :=
  let vs := (comps ins).map (fun bs => init.testBit (idx bs))
  if vs.all (· = true) then .t else if vs.all (· = false) then .f else .x

def allN : Nat → List (List K)
  | 0 => [[]]
  | n + 1 => (allN n).flatMap (fun l => [K3.f, K3.t, K3.x].map (fun k => k :: l))

def all6 : List (List K) := allN 6

def agree (init : Nat) : Bool := all6.all (fun ins => decide (lutK init ins = ext init ins))
def agree5 (init : Nat) : Bool := all6.all (fun ins => decide (lutK (init % 2^32) (ins.take 5) = ext (init % 2^32) (ins.take 5)))

-- steer LUT6_2 (O6 and O5), mux joins uj0/uj1, bd_c2, latch ODD
theorem steer6 : agree 0x8888888822222222 = true := by decide +kernel
theorem steer5 : agree5 0x8888888822222222 = true := by decide +kernel
theorem uj0 : agree 0x0000AE080000AE08 = true := by decide +kernel
theorem uj1 : agree 0x0000EA800000EA80 = true := by decide +kernel
theorem c2 : agree 0x00E800E800E800E8 = true := by decide +kernel
theorem odd : agree 0xB8B8B8B8B8B8B8B8 = true := by decide +kernel
theorem all6_len : all6.length = 729 := by decide +kernel
-- mutation: ext of a 1-bit-flipped table must disagree (so the check is not vacuous)
def agreeM (init : Nat) : Bool := all6.all (fun ins => decide (lutK init ins = ext (init ^^^ 1) ins))
theorem mutant_disagrees : agreeM 0x00E800E800E800E8 = false := by decide +kernel

/-- contrast: plain strong-Kleene gate formula of the C-element is LESS precise
than the LUT closure (shows the hypothesis is the optimistic, hazard-free one). -/
def kand (a b : K) : K := if a = .f ∨ b = .f then .f else if a = .t ∧ b = .t then .t else .x
def kor (a b : K) : K := if a = .t ∨ b = .t then .t else if a = .f ∧ b = .f then .f else .x
theorem c2_formula_less_precise :
    lutK 0x00E800E800E800E8 [.t, .t, .x, .f, .f, .f] = .t ∧
    kor (kor (kand .t .t) (kand .t .x)) (kand .t .x) = .t ∧
    lutK 0x8888888822222222 [.t, .x, .f, .f, .f, .t] = .x := by decide

end Audit.P8.KB
#print axioms Audit.P8.KB.steer6
#print axioms Formal.Cells.KleeneBox.steer_edges_K
#print axioms Formal.Cells.KleeneBox.steer_strict_K
#print axioms Formal.Cells.KleeneBox.join_edges_K
#print axioms Formal.Cells.KleeneBox.join_strict_K
#print axioms Formal.Cells.KleeneBox.muxn_edges_K
#print axioms Formal.Cells.KleeneBox.latch_strict_uniform
#print axioms Formal.Cells.KleeneBox.join_witness_K
#print axioms Formal.Cells.KleeneBox.steer_witness_K
