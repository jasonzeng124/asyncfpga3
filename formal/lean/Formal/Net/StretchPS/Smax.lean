import Formal.Timing.SpecSettle
import Formal.Target.NetPS.All

/-!
# Every arc of THE target is at most 698 ps at the slow corner (shard C, 2026-11-07)

**Problem, plainly.** How long must the circuit be quiet before a run can be stretched (`Net/Stretch`)? Every
admissible delay is at most its gate's `start`, which is at most `⌈(1+κ)·g·SLOW_MAX⌉` of its slowest arc. This file
bounds SLOW_MAX over the whole decoded netlist.

**Proved.** `smax_all`: every arc of every gate of `DecodedPS.gates` has `smax ≤ 698` (one kernel `decide` per chunk of
2,500 gates). `start_le_of_smax`: then `Gate.start p g ≤ ⌈(1+κ)·698·g⌉` for `0 ≤ (1+κ)·g`.
-/

namespace Formal.Net.StretchPS
open Formal.Target Formal.Target.DecodedPS

theorem s000 : (g000.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s001 : (g001.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s002 : (g002.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s003 : (g003.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s004 : (g004.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s005 : (g005.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s006 : (g006.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s007 : (g007.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s008 : (g008.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s009 : (g009.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s010 : (g010.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s011 : (g011.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s012 : (g012.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s013 : (g013.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s014 : (g014.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s015 : (g015.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s016 : (g016.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s017 : (g017.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s018 : (g018.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s019 : (g019.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s020 : (g020.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s021 : (g021.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s022 : (g022.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s023 : (g023.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s024 : (g024.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s025 : (g025.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s026 : (g026.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s027 : (g027.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s028 : (g028.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s029 : (g029.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s030 : (g030.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s031 : (g031.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s032 : (g032.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s033 : (g033.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s034 : (g034.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s035 : (g035.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s036 : (g036.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s037 : (g037.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s038 : (g038.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s039 : (g039.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s040 : (g040.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s041 : (g041.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s042 : (g042.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s043 : (g043.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s044 : (g044.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s045 : (g045.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s046 : (g046.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s047 : (g047.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s048 : (g048.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s049 : (g049.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s050 : (g050.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s051 : (g051.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s052 : (g052.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s053 : (g053.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s054 : (g054.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s055 : (g055.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s056 : (g056.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s057 : (g057.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s058 : (g058.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s059 : (g059.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s060 : (g060.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s061 : (g061.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s062 : (g062.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s063 : (g063.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s064 : (g064.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s065 : (g065.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s066 : (g066.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s067 : (g067.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s068 : (g068.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s069 : (g069.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s070 : (g070.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s071 : (g071.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s072 : (g072.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s073 : (g073.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel

theorem s074 : (g074.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by decide +kernel


theorem smax_chunks : (gates.all fun g => g.arcs.all fun e => decide (e.smax ≤ 698)) = true := by
  simp only [gates, List.all_append, s000, s001, s002, s003, s004, s005, s006, s007, s008, s009, s010, s011, s012, s013, s014, s015, s016, s017, s018, s019, s020, s021, s022, s023, s024, s025, s026, s027, s028, s029, s030, s031, s032, s033, s034, s035, s036, s037, s038, s039, s040, s041, s042, s043, s044, s045, s046, s047, s048, s049, s050, s051, s052, s053, s054, s055, s056, s057, s058, s059, s060, s061, s062, s063, s064, s065, s066, s067, s068, s069, s070, s071, s072, s073, s074, Bool.and_self]

theorem smax_all : ∀ g ∈ gates, ∀ e ∈ g.arcs, e.smax ≤ 698 := by
  intro g hg e he
  have h1 := List.all_eq_true.mp smax_chunks g hg
  have h2 := List.all_eq_true.mp h1 e he
  simpa using h2

theorem rat_ceil_eq (q : ℚ) : Rat.ceil q = ⌈q⌉ := by
  rw [Rat.ceil_eq_neg_floor_neg]; rfl

theorem foldr_le_of_smax {p : DelayPar} (hp : 0 ≤ (1 + p.κ) * p.g) {M : Nat} :
    ∀ l : List Arc, (∀ e ∈ l, e.smax ≤ M) →
      (l.map fun e => (Rat.ceil ((1 + p.κ) * e.smax * p.g)).toNat).foldr max 0 ≤
        (Rat.ceil ((1 + p.κ) * M * p.g)).toNat
  | [], _ => by simp
  | e :: es, h => by
    simp only [List.map_cons, List.foldr_cons]
    apply max_le
    · have hs : (e.smax : ℚ) ≤ M := by exact_mod_cast h e List.mem_cons_self
      have : (1 + p.κ) * e.smax * p.g ≤ (1 + p.κ) * M * p.g := by
        have e1 : (1 + p.κ) * e.smax * p.g = ((1 + p.κ) * p.g) * e.smax := by ring
        have e2 : (1 + p.κ) * M * p.g = ((1 + p.κ) * p.g) * M := by ring
        rw [e1, e2]; exact mul_le_mul_of_nonneg_left hs hp
      have hc := Int.ceil_mono this
      rw [rat_ceil_eq, rat_ceil_eq]
      omega
    · exact foldr_le_of_smax hp es (fun e he => h e (List.mem_cons_of_mem _ he))

/-- A gate whose arcs all have `smax ≤ M` starts by `⌈(1+κ)·M·g⌉` (when `(1+κ)·g ≥ 0`). -/
theorem start_le_of_smax {p : DelayPar} (hp : 0 ≤ (1 + p.κ) * p.g) {M : Nat} (g : Gate)
    (h : ∀ e ∈ g.arcs, e.smax ≤ M) : g.start p ≤ (Rat.ceil ((1 + p.κ) * M * p.g)).toNat :=
  foldr_le_of_smax hp g.arcs h

end Formal.Net.StretchPS
