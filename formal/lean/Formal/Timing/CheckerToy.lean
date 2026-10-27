import Formal.Timing.Checker

/-!
# The checker on a toy one-link netlist, and the correlated-delay question

## 1. A `bd_link`-shaped toy (numbers are ILLUSTRATIVE, not prjxray data)

Launch node 0 = the upstream controller node `C_{i-1}` rising: it raises the
request and opens the upstream data latches. Request path to the capture latch
enable of stage `i`:

    0 →(wire 60..180)→ 1 →(delay element, 3 LUTs)→ 2 →(wire 60..180)→ 3
      →(C-element LUT arc 40..60)→ 4 →(wire 50..150)→ 5 = capture latch G

Data path, a 4-bit bus:

    0 →(G net 50..150)→ 6 →(latch G→Q 100..152, one per bit)→ 7,8,9,10
      →(D wires, four different routes)→ 11,12,13,14 = capture latch D pins

`toyLink` uses a 480..650 ps delay element and passes with setup 30 ps;
`toyShort` uses 330..450 ps and fails. The data bits share node 6 (one G net),
the request and data paths share only the launch node, so the check is exact
here (see section 2 for when it is not).

## 2. Is interval STA exact or only conservative?

`win_exact` (Checker.lean) says per-node windows are exact in both semantics.
The *bundling check* compares two windows at once. `corr` is the smallest
netlist where request and data share an arc with an interval (`0 → 1`, 1..3):

    0 →[1,3]→ 1 →[5,5]→ 2 = req      1 →[4,4]→ 3 = data,   setup 1

`check corr 2 [3] 1 = false` (latest data 7 + 1 > earliest req 6), and:
* `corr_fixed_safe`: in every **fixed-delay** run (one delay per arc) the data
  changes ≥ 1 tick before the request: the check is only CONSERVATIVE there
  (common-path pessimism: the shared arc cannot be both fast and slow);
* `corr_bd_violation`: under **H_BOUNDED_DELAY** (per-event delay, pulses pass)
  there is a run in which the shared node glitches (changes at 1, 2 and 3), the
  request takes the early edge and the data the late one: data changes at 7,
  after the request edge at 6. So the check is EXACT for Prelim's channel.
-/

namespace Formal.Timing
open Formal.Net

/-- The toy link (delay element 480..650 ps). -/
def toyLinkWith (dlo dhi : Nat) : Netlist where
  arcs := [
    ⟨0, 1, 60, 180⟩,  -- C_{i-1} → delay element input (wire)
    ⟨1, 2, dlo, dhi⟩, -- delay element (LUT chain)
    ⟨2, 3, 60, 180⟩,  -- delay element → C_i input (wire)
    ⟨3, 4, 40, 60⟩,   -- C_i LUT arc
    ⟨4, 5, 50, 150⟩,  -- C_i → capture latch G (wire)
    ⟨0, 6, 50, 150⟩,  -- C_{i-1} → upstream latch G pins (net)
    ⟨6, 7, 100, 152⟩, ⟨6, 8, 100, 152⟩, ⟨6, 9, 100, 152⟩, ⟨6, 10, 100, 152⟩, -- latch G→Q
    ⟨7, 11, 80, 220⟩, ⟨8, 12, 90, 260⟩, ⟨9, 13, 70, 200⟩, ⟨10, 14, 100, 300⟩ -- D wires
  ]

def toyLink : Netlist := toyLinkWith 480 650
def toyShort : Netlist := toyLinkWith 330 450

def toyReq : Nat := 5
def toyData : List Nat := [11, 12, 13, 14]
def toySetup : Nat := 30

/-- info: [some (0, 0),
 some (60, 180),
 some (540, 830),
 some (600, 1010),
 some (640, 1070),
 some (690, 1220),
 some (50, 150),
 some (150, 302),
 some (150, 302),
 some (150, 302),
 some (150, 302),
 some (230, 522),
 some (240, 562),
 some (220, 502),
 some (250, 602)] -/
#guard_msgs in
#eval (List.range 15).map (win toyLink)

/-- info: some 58 -/
#guard_msgs in
#eval slack toyLink toyReq toyData toySetup

/-- info: some (-92) -/
#guard_msgs in
#eval slack toyShort toyReq toyData toySetup

theorem toyLink_wf : toyLink.WF := by decide
theorem toyShort_wf : toyShort.WF := by decide

/-- The checker accepts the toy link (kernel evaluation, kernel `decide`, no native code). -/
theorem toyLink_check : check toyLink toyReq toyData toySetup = true := by decide

/-- ...and rejects the one with a short delay element. -/
theorem toyShort_check : check toyShort toyReq toyData toySetup = false := by decide

/-- End-to-end: in every run of the toy link (any delays inside the intervals,
any cell functions), every data bit at the capture latch is stable from 30 ps
before the request edge at its enable onwards. -/
theorem toyLink_bundled {sig : Nat → Trace} (r : Run toyLink sig) :
    ∀ d ∈ toyData, ∀ t, changes (sig toyReq) t → ∀ T, stableOn (sig d) (t + 1 - toySetup) T :=
  check_stable toyLink_wf toyLink_check r

/-- The short link really is broken in the model: a fixed-delay run in which a
data bit changes after the request has reached the enable. Request cone
(nodes 1..5) and data cone (6..14) are disjoint, so `check_exact_disjoint`
applies with `P v := 6 ≤ v`. -/
theorem toyShort_broken : ∃ d ∈ toyData, ∃ sig, Nonempty (FixedRun toyShort sig) ∧
    ∃ s t, changes (sig d) s ∧ changes (sig toyReq) t ∧ t < s + toySetup :=
  check_exact_disjoint toyShort_wf (P := fun v => decide (6 ≤ v)) (by decide) (by decide)
    (by decide) (by decide) toyShort_check

/-! ## 2. Correlated delays -/

def corr : Netlist where
  arcs := [⟨0, 1, 1, 3⟩, ⟨1, 2, 5, 5⟩, ⟨1, 3, 4, 4⟩]

theorem corr_wf : corr.WF := by decide

/-- The interval checker rejects `corr`. -/
theorem corr_check : check corr 2 [3] 1 = false := by decide

/-- info: [some (0, 0), some (1, 3), some (6, 8), some (5, 7)] -/
#guard_msgs in
#eval (List.range 4).map (win corr)

/-- Arcs into `v` in `corr`. -/
theorem corr_arc {k : Nat} {a : Arc} (hk : corr.arcs[k]? = some a) :
    (k = 0 ∧ a = ⟨0, 1, 1, 3⟩) ∨ (k = 1 ∧ a = ⟨1, 2, 5, 5⟩) ∨ (k = 2 ∧ a = ⟨1, 3, 4, 4⟩) := by
  match k, hk with
  | 0, hk => left; simp [corr] at hk; exact ⟨rfl, hk.symm⟩
  | 1, hk => right; left; simp [corr] at hk; exact ⟨rfl, hk.symm⟩
  | 2, hk => right; right; simp [corr] at hk; exact ⟨rfl, hk.symm⟩
  | k + 3, hk => simp [corr] at hk

/-- **Conservative under fixed delays.** In every fixed-delay run of `corr`, every
data change precedes every request change by at least the setup (1), although
the checker rejects it. -/
theorem corr_fixed_safe {sig : Nat → Trace} (r : FixedRun corr sig) :
    ∀ s t, changes (sig 3) s → changes (sig 2) t → s + 1 ≤ t := by
  have h1 : ∀ t, changes (sig 1) t → t = r.d 0 := by
    intro t ht
    obtain ⟨k, a, hk, hd, hle, hc⟩ := r.node_changes (by decide) ht
    rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have := r.launch _ hc; omega
    · cases hd
    · cases hd
  have hd1 : r.d 1 = 5 := by have := r.range 1 _ rfl; simp only at this; omega
  have hd2 : r.d 2 = 4 := by have := r.range 2 _ rfl; simp only at this; omega
  intro s t hs ht
  obtain ⟨k, a, hk, hd, hle, hc⟩ := r.node_changes (by decide) hs
  obtain ⟨k', a', hk', hd', hle', hc'⟩ := r.node_changes (by decide) ht
  rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> try cases hd
  rcases corr_arc hk' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> try cases hd'
  have := h1 _ hc; have := h1 _ hc'; omega

/-- The glitching pin of arc `0 → 1`: rises at 2, falls at 3, rises again at 4. -/
def glitch : Trace := fun t => decide (t = 2 ∨ 4 ≤ t)
def launchSig : Trace := fun t => decide (1 ≤ t)

def corrSig : Nat → Trace
  | 0 => launchSig
  | 1 => glitch
  | 2 => shift 5 glitch
  | 3 => shift 4 glitch
  | _ => fun _ => false

theorem glitch_bd : BoundedDelay 1 3 launchSig glitch where
  cause := by
    intro t ht
    match t with
    | 0 => exact absurd (by decide) ht
    | 1 => exact ⟨1, by decide, by decide, by decide, by decide⟩
    | 2 => exact ⟨3, by decide, by decide, by decide, by decide⟩
    | 3 => exact ⟨1, by decide, by decide, by decide, by decide⟩
    | t + 4 => exact absurd (show glitch (t + 4) = glitch (t + 4 + 1) by
        simp only [glitch, decide_eq_decide]; omega) ht
  settle := by
    intro t ht hs
    by_cases h3 : t = 3
    · subst h3
      have := hs 1 (by decide) (by decide)
      simp [launchSig] at this
    · simp only [glitch, launchSig, decide_eq_decide]; omega

/-- **Exact under H_BOUNDED_DELAY.** A run of `corr` (Prelim's bounded-delay
channel on every arc) in which the data changes at 7, after the request
changed at 6. -/
def corrRun : Run corr corrSig where
  pin := fun k => match k with
    | 0 => glitch
    | 1 => shift 5 glitch
    | 2 => shift 4 glitch
    | _ => fun _ => false
  g := fun v x => match v with
    | 1 => x 0
    | 2 => x 1
    | 3 => x 2
    | _ => false
  launch := by
    intro t ht
    apply Classical.byContradiction; intro h0; apply ht
    simp only [corrSig, launchSig, decide_eq_decide]; omega
  bd := by
    intro k a hk
    rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact glitch_bd
    · exact shift_bd glitch (by decide) (by decide)
    · exact shift_bd glitch (by decide) (by decide)
  quiet := by
    intro k a hk
    rcases corr_arc hk with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  local_ := by
    intro v x y hxy
    match v with
    | 1 => exact hxy 0 _ rfl rfl
    | 2 => exact hxy 1 _ rfl rfl
    | 3 => exact hxy 2 _ rfl rfl
    | 0 => rfl
    | v + 4 => rfl
  node := by
    intro v hv t
    match v with
    | 0 => exact absurd rfl hv
    | 1 => rfl
    | 2 => rfl
    | 3 => rfl
    | v + 4 => rfl

theorem corr_bd_violation :
    ∃ sig, Nonempty (Run corr sig) ∧ changes (sig 3) 7 ∧ changes (sig 2) 6 ∧ ¬ (7 + 1 ≤ 6) :=
  ⟨corrSig, ⟨corrRun⟩, by unfold changes; decide, by unfold changes; decide, by decide⟩

end Formal.Timing
