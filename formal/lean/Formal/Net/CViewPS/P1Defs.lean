import Formal.Net.CViewPS.Idle0

/-!
# Delay facts at g = 1, κ = 0 (shard C)

`correct_n0` at the delay parameters `p1 = (g = 1, κ = 0)`: every arc delay lies in its corner-`c`
window `[lerp(fmin, smin, c), lerp(fmax, smax, c)]`, any corner. Its delay hypotheses are discharged
by the kernel (Nat sums of prjxray numbers over the island's 414 gates), so the only remaining
hypothesis is the reset length `R ≥ R0`.
-/

namespace Formal.Net.CViewPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecSettle Formal.Timing.SpecChain
  Formal.Timing.SpecChainM Formal.Timing.ChunkCM Formal.Timing.Huffman Formal.Timing.SpecLoop
  Formal.Timing.Island

def p1 : DelayPar := ⟨1, 0⟩

theorem sane_p1 : Sane p1 := by refine ⟨?_, ?_, ?_⟩ <;> simp [p1]

theorem dmax_p1 (e : Arc) : dmax p1 e = e.smax := by simp [dmax, p1]
theorem dmin_p1 (e : Arc) : dmin p1 e = e.fmin := by simp [dmin, p1]
theorem start_p1 (g : Gate) : g.start p1 = (g.arcs.map fun e => e.smax).foldr max 0 := by
  simp only [Gate.start, p1, add_zero, mul_one, one_mul]
  congr 1

def startN (g : Gate) : Nat := (g.arcs.map fun e => e.smax).foldr max 0
def sumMaxN (es : List Arc) : Nat := (es.map fun e => e.smax).sum
def sumMinN (es : List Arc) : Nat := (es.map fun e => e.fmin).sum
def chainStartN : List Gate → Nat
  | [] => 0
  | c :: cs => startN c + (arc0 c).smax + chainStartN cs
def cStartN (g : Gate) (pcs : List PinChain) : Nat :=
  startN g + ((List.range g.k).map fun i =>
    chainStartN (pcs.getD i ⟨0, []⟩).chain + (g.arcs.getD i default).smax).sum

theorem sumMax_p1 (es : List Arc) : sumMax p1 es = sumMaxN es := by
  simp only [sumMax, sumMaxN]; congr 1; exact List.map_congr_left (fun e _ => dmax_p1 e)
theorem sumMin_p1 (es : List Arc) : sumMin p1 es = sumMinN es := by
  simp only [sumMin, sumMinN]; congr 1; exact List.map_congr_left (fun e _ => dmin_p1 e)
theorem chainStart_p1 : ∀ cs : List Gate, chainStart p1 cs = chainStartN cs
  | [] => rfl
  | c :: cs => by simp [chainStart, chainStartN, start_p1, dmax_p1, chainStart_p1 cs, startN]
theorem cStart_p1 (g : Gate) (pcs : List PinChain) : cStart p1 g pcs = cStartN g pcs := by
  simp [cStart, cStartN, start_p1, chainStart_p1, dmax_p1, startN]

/-- The island's delay facts at `p1`. -/
def A1 : Nat := 15600
def M1 : Nat := 3881

def p1OK (e : Nat × Bool × List Nat) : Bool :=
  decide (cStartN (gAt cs 2500 e.1) (pcsPS e.1) ≤ A1) &&
  ((List.range (gAt cs 2500 e.1).k).all fun i => decide (sumMaxN (arcsPS e.1 i) ≤ M1)) &&
  ((psI e.1).all fun j => decide (1 ≤ sumMinN (arcsPS e.1 j)))

end Formal.Net.CViewPS
