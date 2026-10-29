import Formal.Cells.ZeroDelayNetPhys

/-!
# ZeroDelayNetWit: non-vacuity of the closed-loop chain refinement

Probe Bzd2 (shard B); note `formal/notes/B-zero-delay-net.md`. Two `bd_link` stages, wired
to each other (stage 1's request pin reads stage 0's node, stage 0's acknowledge pin reads
stage 1's node, stage 1's data pin reads stage 0's latch), every read a nonzero transport delay
(380 to 900 ps; LinkExact's `P0` delay numbers), the source and sink single pulses. The coupled
traces are built by a joint simulator `jr` (strong recursion over time; every read is at least
280 ps in the past). Every hypothesis of `chain_refines` holds (`chain_witness`), so its
conclusion applies to this run. Core Lean only.
-/

namespace Formal.Cells.ZeroDelayNet
open Formal.Cells
open Formal.Cells.CElemFn
open Formal.Cells.LibGapSteer (Rd Rd.const)
open Formal.Cells.LibGapLatch
open Formal.Cells.LinkExact
open Formal.Cells.ZeroDelayRefine

/-! ## 0. A joint simulator -/

/-- Joint state at tick `n` from the states at earlier ticks (index `k` selects a node or latch). -/
def jr (F : Nat → (Nat → Nat → K3) → Nat → K3) (n : Nat) : Nat → K3 :=
  F n (fun m => if h : m < n then jr F m else fun _ => .f)
termination_by n

/-- The simulated trace `k` on Int time (power-up `t < 0`: `.f`). -/
def tr (F : Nat → (Nat → Nat → K3) → Nat → K3) (k : Nat) (t : Int) : K3 :=
  if t < 0 then .f else jr F t.toNat k

/-- Read trace `k` of the history `g` at `n - d` (`.f` before 0). -/
def rdN (g : Nat → Nat → K3) (n d k : Nat) : K3 := if d ≤ n then g (n - d) k else .f

theorem tr_eq (F : Nat → (Nat → Nat → K3) → Nat → K3) (k : Nat) {t : Int} (ht : 0 ≤ t) :
    tr F k t = F t.toNat (fun m => if h : m < t.toNat then jr F m else fun _ => .f) k := by
  simp only [tr, show ¬ t < 0 by omega, if_false]
  rw [jr]

theorem rdN_eq (F : Nat → (Nat → Nat → K3) → Nat → K3) (n d k : Nat) (hd : 1 ≤ d) :
    rdN (fun m => if h : m < n then jr F m else fun _ => .f) n d k = tr F k ((n : Int) - d) := by
  unfold rdN tr
  by_cases h : d ≤ n
  · rw [if_pos h]
    show (if h : n - d < n then jr F (n - d) else fun _ => K3.f) k = _
    rw [dif_pos (by omega), if_neg (by omega)]
    have e : ((n : Int) - d).toNat = n - d := by omega
    rw [e]
  · rw [if_neg h, if_pos (by omega)]

/-! ## 1. The two-stage loop -/

/-- Stage 0 (LinkExact's `P0` delays; acknowledge windows = stage 1's node windows). -/
def Pw0 : Par :=
  { W := 2000, W1 := 2001, Ra := 3000, Ra1 := 3001, Fa := 4500, Fa1 := 4501,
    Rb := 3800, Rb1 := 4041, Fb := 5300, Fb1 := 5541, Td := 2500, Tn := 7000,
    Alo := 400, Ahi := 520, Blo := 380, Bhi := 500, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }
/-- Stage 1 (request windows = stage 0's node windows; data from stage 0's latch). -/
def Pw1 : Par :=
  { W := 2000, W1 := 2001, Ra := 3400, Ra1 := 3521, Fa := 4900, Fa1 := 5021,
    Rb := 4300, Rb1 := 4301, Fb := 6000, Fb1 := 6001, Td := 4221, Tn := 7000,
    Alo := 400, Ahi := 520, Blo := 380, Bhi := 500, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }
def Pw (i : Nat) : Par := if i = 0 then Pw0 else Pw1

theorem pw_wf : ∀ i < 2, Wf (Pw i) := by
  intro i hi
  rcases i with _ | _ | i
  · exact wf_of _ (by decide)
  · exact wf_of _ (by decide)
  · omega

theorem pw_cell : ChainCell 2 Pw := by
  refine ⟨⟨by decide, pw_wf, fun i hi => ?_, fun i hi => ?_, by decide, by decide⟩,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
  · rcases i with _ | i
    · decide
    · omega
  · rcases i with _ | i
    · decide
    · omega
  · rcases i with _ | _ | i
    · exact (conj_iff (Pw 0)).2 (by decide)
    · exact (conj_iff (Pw 1)).2 (by decide)
    · omega
  all_goals (rcases i with _ | i <;> first | decide | omega)

/-- The read maps (every pin read at its slowest box value). -/
def rdw : Rds :=
  ⟨Rd.const 520, Rd.const 500, Rd.const 420, Rd.const 900, Rd.const 480, Rd.const 700,
   Rd.const 400⟩

/-- The coupled simulator: traces 0, 1 = the two nodes, 2, 3 = the two latch bits. -/
def Fw (v : Bool) (n : Nat) (g : Nat → Nat → K3) : Nat → K3
  | 0 => c2nK (win 3001 4500 ((n : Int) - 520)) (rdN g n 500 1) (rdN g n 420 0)
      (win 0 2000 ((n : Int) - 900))
  | 1 => c2nK (rdN g n 520 0) (win 4300 6000 ((n : Int) - 500)) (rdN g n 420 1)
      (win 0 2000 ((n : Int) - 900))
  | 2 => latM (kb v) (rdN g n 700 0) (rdN g n 400 2)
  | 3 => latM (rdN g n 480 2) (rdN g n 700 1) (rdN g n 400 3)
  | _ => .f

def Aw (v : Bool) (i : Nat) : Int → K3 := if i = 0 then win 3001 4500 else tr (Fw v) 0
def Bw (v : Bool) (i : Nat) : Int → K3 := if i = 0 then tr (Fw v) 1 else win 4300 6000
def Dw (v : Bool) (i : Nat) : Int → K3 := if i = 0 then fun _ => kb v else tr (Fw v) 2
def Cw (v : Bool) (i : Nat) : Int → K3 := tr (Fw v) i
def Qw (v : Bool) (i : Nat) : Int → K3 := tr (Fw v) (i + 2)

theorem tn (t : Int) (ht : 0 ≤ t) : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht

theorem pw_beh (v : Bool) :
    ChainBeh 2 Pw v (fun _ => rdw) (win 0 2000) (Aw v) (Bw v) (Dw v) (Cw v) (Qw v) := by
  refine ⟨fun i hi => ?_, fun i hi x h1 h2 => ?_, fun i hi x h1 => ?_, fun i hi => ?_,
    fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun x h => ?_,
    fun x h1 h2 => ?_, fun x h => ?_, fun x h => ?_, fun x h1 h2 => ?_, fun x h => ?_,
    fun x _ _ => rfl⟩
  · rcases i with _ | _ | i
    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
    · omega
  · rcases i with _ | _ | i
    · exact win_t h1 (by simpa [Pw, Pw0] using h2)
    · exact win_t h1 (by simpa [Pw, Pw1] using h2)
    · omega
  · rcases i with _ | _ | i
    · exact win_f2 (by simp [Pw, Pw0] at h1; omega)
    · exact win_f2 (by simp [Pw, Pw1] at h1; omega)
    · omega
  · intro t ht
    rcases i with _ | _ | i
    · show tr (Fw v) 0 t = c2nK (win 3001 4500 (t - 520)) (tr (Fw v) 1 (t - 500))
        (tr (Fw v) 0 (t - 420)) (win 0 2000 (t - 900))
      rw [tr_eq _ _ ht]
      simp only [Fw]
      rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), tn t ht]
      rfl
    · show tr (Fw v) 1 t = c2nK (tr (Fw v) 0 (t - 520)) (win 4300 6000 (t - 500))
        (tr (Fw v) 1 (t - 420)) (win 0 2000 (t - 900))
      rw [tr_eq _ _ ht]
      simp only [Fw]
      rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), tn t ht]
      rfl
    · omega
  · intro t ht
    rcases i with _ | _ | i
    · show tr (Fw v) 2 t = latM (kb v) (tr (Fw v) 0 (t - 700)) (tr (Fw v) 2 (t - 400))
      rw [tr_eq _ _ ht]
      simp only [Fw]
      rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), tn t ht]
      rfl
    · show tr (Fw v) 3 t = latM (tr (Fw v) 2 (t - 480)) (tr (Fw v) 1 (t - 700))
        (tr (Fw v) 3 (t - 400))
      rw [tr_eq _ _ ht]
      simp only [Fw]
      rw [rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide), rdN_eq _ _ _ _ (by decide),
        tn t ht]
      rfl
    · omega
  · rcases i with _ | i
    · rfl
    · omega
  · rcases i with _ | i
    · rfl
    · omega
  · rcases i with _ | i
    · rfl
    · omega
  · exact win_f1 (by simp [Pw, Pw0] at h; omega)
  · exact win_t (by simpa [Pw, Pw0] using h1) (by simpa [Pw, Pw0] using h2)
  · exact win_f2 (by simp [Pw, Pw0] at h; omega)
  · exact win_f1 (by simp [Pw, Pw1] at h; omega)
  · exact win_t (by simp [Pw, Pw1] at h1; omega) (by simpa [Pw, Pw1] using h2)
  · exact win_f2 (by simp [Pw, Pw1] at h; omega)

/-- **Non-vacuity (goal 2).** The two-stage closed loop meets every hypothesis of
`chain_refines` with nonzero delays everywhere, and a coupled behaviour exists; it refines the
zero-delay run (the conclusion of `chain_refines`, here its physical half `NetRef`). -/
theorem chain_witness (v : Bool) :
    ChainCell 2 Pw ∧ ∃ rd r A B D C Q, ChainBeh 2 Pw v rd r A B D C Q ∧ NetRef 2 Pw v rd A B C Q :=
  ⟨pw_cell, _, _, _, _, _, _, _, pw_beh v, chain_ref pw_cell (pw_beh v)⟩

end Formal.Cells.ZeroDelayNet
