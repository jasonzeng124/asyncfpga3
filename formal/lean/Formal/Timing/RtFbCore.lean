import Formal.Timing.WinArrayB

/-!
# Probe C-10f: shared definitions for the RT_FB summaries (`RtFbMuller`, `RtFbGcd`)

`nPass L` counts the entries that pass RT_FB (`rtOne`, 10d's `WinArrayB`), `worstSlack L` is
the minimum over entries and request nodes of 10d's `slackB` (latest feedback arrival vs
earliest response arrival, ps).  `rt_sound_of` / `rt_violated_of` lift 10d's per-entry
`rtOne_sound` / `rtOne_exact` to a list.
-/

namespace Formal.Timing.RtFb
open Formal.Timing Formal.Net

/-- Worst RT_FB slack (ps) over a list of entries: min over entries and request nodes of `slackB`. -/
def omin : Option Int → Option Int → Option Int
  | none, b => b
  | a, none => a
  | some a, some b => some (min a b)

def entSlack (e : RTEntry) : Option Int :=
  e.2.1.foldl (fun acc r => omin acc (slackB e.1 r [e.2.2.1] 0)) none

def worstSlack (L : List RTEntry) : Option Int := L.foldl (fun acc e => omin acc (entSlack e)) none

def nPass (L : List RTEntry) : Nat := (L.filter rtOne).length

/-- Every checked entry of a well-formed list satisfies RT_FB in every run. -/
theorem rt_sound_of (L : List RTEntry) (hw : L.all wfOne = true) :
    ∀ e ∈ L, rtOne e = true → ∀ {sig : Nat → Trace}, Run (ofBuckets e.1) sig →
      ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t :=
  fun e he h _ run => rtOne_sound e (List.all_eq_true.1 hw e he) h run

/-- Every failing entry of a well-formed, separated list has a real violating fixed-delay run. -/
theorem rt_violated_of (L : List RTEntry) (hw : L.all wfOne = true) (hs : L.all sepOne = true) :
    ∀ e ∈ L, rtOne e = false → ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s :=
  fun e he h => rtOne_exact e (List.all_eq_true.1 hw e he) (List.all_eq_true.1 hs e he) h

end Formal.Timing.RtFb
