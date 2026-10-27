import Formal.Cells.ResetGcdWave
import Formal.Cells.CElemStrict2

/-!
# Probe Brst (shard B): the data vector every reset cell of gcd_hw sees at reset release

Notes: `formal/notes/B-reset-gcd-vec.md`.

`CElemStrict2` proved the exact reset-release condition for one rst-carrying
LUT loop: at a HOLD vector of the data pins (the cell's binary function at
rst = 0 is `q ↦ q`) the reset must be held at least the loop delay plus the
release edge (`Dhi + wa ≤ P`); at a FORCED vector (the function is the reset
value for every feedback value) any width is safe. Which vector a cell sees
at release is a property of the network. Here it is decided on Rst2's import
of gcd_hw's control network (`ResetGcd.gNet`, 3322 nodes, real INITs, real
pin lists), for every rst-carrying cell, in the settled reset state
(`ResetGcd.gR`; every data net `x`).

Results (namespace `Formal.Cells.ResetGcdVec`):
* `gcd_vec_census`: of the 423 rst readers, 414 are LUT loops (the cell's own
  output is one of its pins) and 9 (the arbiter O5) are combinational. Of the
  414: 195 sit at a hold vector, 209 at a forced vector, 10 (the frontier
  link controllers of `ResetGcd.gcd_frontier`) at the vector that leaves
  reset. By cell: c2 8 hold / 145 forced; c2n 174 hold / 1 forced / 10 leave;
  c2n_set 1 hold; c3 10 forced; c4 3 hold / 11 forced; bd_mux uj0, uj1 21 + 21
  forced; arbiter ustate O6 9 hold.
* `hold_clean`, `forced_clean'`, `leave_clean` (generic, any LUT loop): the
  release theorems in a model WIDER than CElemStrict2's: data pins arbitrary
  while rst is high, Kleene-below the reset vector from the release on, rst
  arbitrary after its release starts, feedback a bounded window channel
  (delay in `[1, Dhi]`, varying in time), any start value.
* `gcd_reset_vec` (composition): every one of the 414 loop cells leaves reset
  holding its reset value (the frontier ones: holding it until release, then
  going to the other value), assuming `H_RST_LONG` (`T1 + Dhi ≤ s`) ONLY at
  the 195 hold-vector cells (`holdL`), and nothing about width elsewhere.
* `gcd_hold_exact`: at every one of the 195 hold-vector cells the condition
  is exact: CElemStrict2's `reset_width_iff` holds for that cell's real LUT
  at its real vector (`Dhi + wa ≤ P` iff every behaviour is safe), from
  `q = ¬reset` and from the power-up `q = x`.
* `nonvac_hold`, `link_boundary_x`: a witness run meeting every hypothesis at
  a real link controller, and the counter-trace at `P = D` (root `x`).

Core Lean; every certificate is checked with `decide +kernel`.
-/

namespace Formal.Cells.ResetGcdVec
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd

/-! ## The cell seen as a single loop -/

/-- What cell `n`'s pins read: the rst pin (node 0) reads `r`, the cell's own
output reads the feedback `q`, every other pin reads `e`. -/
def cin (e : Nat → K3) (r q : K3) (n i : Nat) : K3 :=
  if i = 0 then r else if i = n then q else e i

/-- The cell's root as a function of rst and feedback, at data valuation `e`. -/
def cellF (init : Nat) (pins : List Src) (n : Nat) (e : Nat → K3) (r q : K3) : K3 :=
  lutK init (pins.map (srcK (cin e r q n)))

/-- The settled reset state as the data vector: control nets at their reset
values, data nets `x` (any value). -/
def rho (i : Nat) : K3 := if gCtl i then K3.ofBool (gR i) else .x
/-- The same with every data net at 1 (for the exactness statement only). -/
def rho1 (i : Nat) : K3 := if gCtl i then K3.ofBool (gR i) else .t
def allXv (_ : Nat) : K3 := .x

def ks : List K3 := [.f, .t, .x]

/-- rst high forces the reset value `b`, whatever the data and the feedback. -/
def followB (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  ks.all fun k => decide (cellF init pins n allXv .t k = K3.ofBool b)
/-- Hold at the reset vector: with feedback at `b`, the root is `b` for every rst value. -/
def holdB (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  ks.all fun r => decide (cellF init pins n rho r (K3.ofBool b) = K3.ofBool b)
/-- Forced at the reset vector: the root is `b` for every rst and feedback value. -/
def forcB (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  ks.all fun r => ks.all fun k => decide (cellF init pins n rho r k = K3.ofBool b)
/-- Leaving: with rst 0 the root is `¬b` for every feedback value. -/
def leaveB (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  ks.all fun k => decide (cellF init pins n rho .f k = K3.ofBool (!b))
/-- CElemStrict2's reset race facts at the vector `rho1`, from `¬b` and from `x`. -/
def exactB (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  CElemStrict2.rstB (cellF init pins n rho1) (K3.ofBool (!b)) b &&
    CElemStrict2.rstB (cellF init pins n rho1) .x b

/-- Class of node `n`: 0 not an rst reader, 1 hold, 2 forced, 3 leave,
4 rst reader without own feedback (combinational), 5 none of these. -/
def vcls (n : Nat) : Nat :=
  match gNode n with
  | .input => 0
  | .gate init pins =>
    if !(pins.contains (p 0)) then 0
    else if !(pins.contains (p n)) then 4
    else if forcB init pins n (gR n) then 2
    else if holdB init pins n (gR n) then 1
    else if leaveB init pins n (gR n) then 3 else 5

/-- The 195 hold-vector cells (generator certificate, checked below). -/
def holdL : List Nat := [65, 99, 103, 107, 287, 425, 533, 606, 630, 825, 849, 1192, 1378, 1402,
  1583, 1638, 1639, 1640, 1658, 1664, 1703, 1713, 1720, 1727, 1734, 1741, 1748, 1755, 1766,
  1777, 1787, 1802, 1809, 1819, 1826, 1836, 1843, 1850, 1857, 1861, 1865, 1866, 1873, 1880,
  1887, 1898, 1909, 1920, 1945, 1955, 1962, 1972, 1979, 1989, 1996, 2006, 2021, 2031, 2046,
  2056, 2063, 2073, 2080, 2090, 2097, 2107, 2114, 2121, 2128, 2135, 2146, 2157, 2167, 2203,
  2210, 2217, 2224, 2234, 2249, 2259, 2274, 2284, 2299, 2309, 2316, 2326, 2333, 2343, 2350,
  2357, 2364, 2371, 2382, 2392, 2407, 2417, 2446, 2456, 2463, 2473, 2480, 2490, 2497, 2507,
  2514, 2521, 2528, 2535, 2546, 2556, 2571, 2581, 2610, 2620, 2627, 2637, 2644, 2654, 2661,
  2671, 2678, 2688, 2695, 2705, 2715, 2722, 2732, 2742, 2749, 2753, 2757, 2758, 2768, 2775,
  2785, 2795, 2802, 2812, 2822, 2829, 2833, 2837, 2838, 2848, 2855, 2865, 2872, 2882, 2889,
  2899, 2906, 2913, 2920, 2927, 2937, 2947, 2954, 2964, 2974, 2981, 2991, 3001, 3008, 3012,
  3016, 3017, 3027, 3034, 3044, 3059, 3069, 3076, 3086, 3093, 3103, 3110, 3120, 3127, 3137,
  3144, 3154, 3161, 3165, 3169, 3170, 3180, 3187, 3197, 3204, 3214, 3221, 3231, 3238, 3248,
  3275]

/-- Everything checked per node. For an rst-reading loop: `n ≠ 0`, rst high
forces the reset value for every data and feedback value, the class is one
of hold / forced / leave, hold ↔ `holdL`, leave ↔ `frontierL`, and every
hold cell has CElemStrict2's race facts. Every other node is outside
`holdL`. -/
def vecOK (n : Nat) : Bool :=
  match gNode n with
  | .input => !holdL.contains n
  | .gate init pins =>
    if pins.contains (p 0) && pins.contains (p n) then
      decide (n ≠ 0) && followB init pins n (gR n) && decide (vcls n ≠ 5) &&
        ((vcls n == 1) == holdL.contains n) && ((vcls n == 3) == frontierL.contains n) &&
        (vcls n != 1 || exactB init pins n (gR n))
    else !holdL.contains n

def chunkV (lo k : Nat) : Bool := (List.range' lo k).all vecOK

theorem chunkV_mem {lo k : Nat} (h : chunkV lo k = true) {n : Nat} (h1 : lo ≤ n)
    (h2 : n < lo + k) : vecOK n = true :=
  List.all_eq_true.1 h n (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem cv0 : chunkV 0 400 = true := by decide +kernel
theorem cv1 : chunkV 400 400 = true := by decide +kernel
theorem cv2 : chunkV 800 400 = true := by decide +kernel
theorem cv3 : chunkV 1200 400 = true := by decide +kernel
theorem cv4 : chunkV 1600 400 = true := by decide +kernel
theorem cv5 : chunkV 2000 400 = true := by decide +kernel
theorem cv6 : chunkV 2400 400 = true := by decide +kernel
theorem cv7 : chunkV 2800 400 = true := by decide +kernel
theorem cv8 : chunkV 3200 122 = true := by decide +kernel

theorem all_vec (n : Nat) (h : n < gM) : vecOK n = true := by
  have hM : gM = 3322 := rfl
  by_cases h0 : n < 400
  · exact chunkV_mem cv0 (by omega) (by omega)
  by_cases h1 : n < 800
  · exact chunkV_mem cv1 (by omega) (by omega)
  by_cases h2 : n < 1200
  · exact chunkV_mem cv2 (by omega) (by omega)
  by_cases h3 : n < 1600
  · exact chunkV_mem cv3 (by omega) (by omega)
  by_cases h4 : n < 2000
  · exact chunkV_mem cv4 (by omega) (by omega)
  by_cases h5 : n < 2400
  · exact chunkV_mem cv5 (by omega) (by omega)
  by_cases h6 : n < 2800
  · exact chunkV_mem cv6 (by omega) (by omega)
  by_cases h7 : n < 3200
  · exact chunkV_mem cv7 (by omega) (by omega)
  exact chunkV_mem cv8 (by omega) (by omega)

theorem gate_lt {n init : Nat} {pins : List Src} (h : gNode n = .gate init pins) : n < gM := by
  unfold gNode at h
  by_cases hn : n < gM
  · exact hn
  · simp only [hn, ite_false] at h; cases h

/-- The per-node facts, unpacked. -/
theorem vec_facts {n init : Nat} {pins : List Src} (hg : gNode n = .gate init pins)
    (h0 : pins.contains (p 0) = true) (hs : pins.contains (p n) = true) :
    n ≠ 0 ∧ followB init pins n (gR n) = true ∧ vcls n ≠ 5 ∧
      (vcls n = 1 ↔ n ∈ holdL) ∧ (vcls n = 3 ↔ n ∈ frontierL) ∧
      (vcls n = 1 → exactB init pins n (gR n) = true) := by
  have h := all_vec n (gate_lt hg)
  simp only [vecOK, hg, h0, hs, Bool.and_self, ite_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨⟨⟨⟨hn0, hf⟩, h5⟩, hh⟩, hl⟩, he⟩ := h
  refine ⟨hn0, hf, h5, ?_, ?_, ?_⟩
  · rw [← List.contains_iff_mem]
    cases hc : holdL.contains n <;> cases hv : decide (vcls n = 1) <;> simp_all
  · rw [← List.contains_iff_mem]
    cases hc : frontierL.contains n <;> cases hv : decide (vcls n = 3) <;> simp_all
  · intro h1; rcases he with he | he
    · exact absurd h1 he
    · exact he

theorem holdL_gate {n init : Nat} {pins : List Src} (hg : gNode n = .gate init pins)
    (hn : n ∈ holdL) : pins.contains (p 0) = true ∧ pins.contains (p n) = true := by
  have h := all_vec n (gate_lt hg)
  have hc : holdL.contains n = true := List.contains_iff_mem.2 hn
  simp only [vecOK, hg] at h
  by_cases hb : (pins.contains (p 0) && pins.contains (p n)) = true
  · simpa [Bool.and_eq_true] using hb
  · simp only [hb, hc, Bool.not_true] at h; cases h

/-! ## Census -/

/-- The 423 rst readers (certificate). -/
def rstL : List Nat := (List.range gM).filter fun n =>
  match gNode n with
  | .gate _ pins => pins.contains (p 0)
  | .input => false

def initOf (n : Nat) : Nat := match gNode n with | .gate init _ => init | .input => 0

/-- Some data pin of `n` (not rst, not its own output) is a first-wave node
of `ResetGcdWave` (it moves after release, during the first wave). -/
def waveIn (n : Nat) : Bool :=
  match gNode n with
  | .input => false
  | .gate _ pins => pins.any fun s => match s with
    | .node i => i != 0 && i != n && ResetGcdWave.wR i != 0
    | .const _ => false

def cntC (L : List Nat) (i c : Nat) : Nat := L.countP fun n => initOf n == i && vcls n == c
def cntW (L : List Nat) (c : Nat) : Nat := L.countP fun n => vcls n == c && waveIn n

/-- **The census.** Rows: c2, c2n, c2n_set, c3, c4, uj0, uj1, arbiter
ustate O6, arbiter O5; columns: hold, forced, leave, combinational. Then the
number of rst-reading loops of each class that have a first-wave data pin. -/
theorem gcd_vec_census :
    rstL.length = 423 ∧
    [I_c2, I_c2n, I_c2n_set, I_c3, I_c4, I_uj0, I_uj1, I_arb, I_arb5].map
        (fun i => [1, 2, 3, 4].map (cntC rstL i)) =
      [[8, 145, 0, 0], [174, 1, 10, 0], [1, 0, 0, 0], [0, 10, 0, 0], [3, 11, 0, 0],
       [0, 21, 0, 0], [0, 21, 0, 0], [9, 0, 0, 0], [0, 0, 0, 9]] ∧
    [1, 2, 3, 4, 5].map (cntW rstL) = [6, 15, 0, 0, 0] ∧
    holdL.length = 195 := by
  decide +kernel

/-! ## Generic release theorems for one LUT loop -/

theorem ks_all {f : K3 → Bool} (h : ks.all f = true) (k : K3) : f k = true :=
  List.all_eq_true.1 h k (by cases k <;> simp [ks])

theorem le_ofBool_eq {a : K3} {b : Bool} (h : le a (K3.ofBool b)) : a = K3.ofBool b :=
  h.elim id (fun h' => absurd h' (CElemStrict.ofBool_ne_x b))

theorem cellF_le {init : Nat} {pins : List Src} {n : Nat} {e e' : Nat → K3} {r q : K3}
    (h : ∀ i, i ≠ 0 → i ≠ n → le (e i) (e' i)) :
    le (cellF init pins n e r q) (cellF init pins n e' r q) := by
  apply lutK_mono
  apply pins_le
  intro i
  by_cases h0 : i = 0
  · simp only [cin, h0, ↓reduceIte]; exact le_refl _
  · by_cases h1 : i = n
    · subst h1; simp only [cin, h0, ↓reduceIte]; exact le_refl _
    · simp only [cin, h0, h1, ↓reduceIte]; exact h i h0 h1

theorem follow_any {init : Nat} {pins : List Src} {n : Nat} {b : Bool}
    (hf : followB init pins n b = true) (e : Nat → K3) (k : K3) :
    cellF init pins n e .t k = K3.ofBool b := by
  have h1 := cellF_le (init := init) (pins := pins) (n := n) (e := e) (e' := allXv) (r := .t) (q := k)
    (fun _ _ _ => Or.inr rfl)
  have h2 : cellF init pins n allXv .t k = K3.ofBool b := of_decide_eq_true (ks_all hf k)
  rw [h2] at h1
  exact le_ofBool_eq h1

theorem hold_at {init : Nat} {pins : List Src} {n : Nat} {b : Bool}
    (hh : holdB init pins n b = true) {e : Nat → K3} (he : ∀ i, i ≠ 0 → i ≠ n → le (e i) (rho i))
    (r : K3) : cellF init pins n e r (K3.ofBool b) = K3.ofBool b := by
  have h1 := cellF_le (init := init) (pins := pins) (r := r) (q := K3.ofBool b) he
  have h2 : cellF init pins n rho r (K3.ofBool b) = K3.ofBool b := of_decide_eq_true (ks_all hh r)
  rw [h2] at h1
  exact le_ofBool_eq h1

theorem forced_at {init : Nat} {pins : List Src} {n : Nat} {b : Bool}
    (hF : forcB init pins n b = true) {e : Nat → K3} (he : ∀ i, i ≠ 0 → i ≠ n → le (e i) (rho i))
    (r k : K3) : cellF init pins n e r k = K3.ofBool b := by
  have h1 := cellF_le (init := init) (pins := pins) (r := r) (q := k) he
  have h2 : cellF init pins n rho r k = K3.ofBool b :=
    of_decide_eq_true (ks_all (ks_all (f := fun r => ks.all fun k =>
      decide (cellF init pins n rho r k = K3.ofBool b)) hF r) k)
  rw [h2] at h1
  exact le_ofBool_eq h1

theorem leave_at {init : Nat} {pins : List Src} {n : Nat} {b : Bool}
    (hl : leaveB init pins n b = true) {e : Nat → K3} (he : ∀ i, i ≠ 0 → i ≠ n → le (e i) (rho i))
    (k : K3) : cellF init pins n e .f k = K3.ofBool (!b) := by
  have h1 := cellF_le (init := init) (pins := pins) (r := .f) (q := k) he
  have h2 : cellF init pins n rho .f k = K3.ofBool (!b) := of_decide_eq_true (ks_all hl k)
  rw [h2] at h1
  exact le_ofBool_eq h1

/-- One rst-carrying LUT loop around its reset pulse. `T1`: rst is settled
high from here (CElemStrict2's `tb + wb`); `s`: the first tick rst is not
settled high (start of the release edge); `Tw`: the first tick a data pin
leaves the reset vector. Nothing is assumed before `T1`, nothing about the
data before `s`, nothing about rst from `s` on. -/
structure CellRun (init : Nat) (pins : List Src) (n : Nat) (T1 s Tw Dhi : Nat)
    (e : Nat → Nat → K3) (r qp G : Nat → K3) : Prop where
  /-- H_TREE: the root is the Kleene LUT of what the pins read. -/
  H_TREE : ∀ t, G t = cellF init pins n (e t) (r t) (qp t)
  /-- H_FB_WIN: from the release on, the feedback reads the root `d` ticks
  ago, `1 ≤ d ≤ Dhi`, `d` may vary with `t`. -/
  H_FB_WIN : ∀ t, s ≤ t → ∃ d, 1 ≤ d ∧ d ≤ Dhi ∧ d ≤ t ∧ qp t = G (t - d)
  /-- H_RST_HIGH: rst reads 1 on `[T1, s)`. -/
  H_RST_HIGH : ∀ t, T1 ≤ t → t < s → r t = .t
  /-- H_DATA_STATIC: on `[s, Tw)` every data pin reads (below) the settled
  reset state (data nets: anything). -/
  H_DATA_STATIC : ∀ t, s ≤ t → t < Tw → ∀ i, i ≠ 0 → i ≠ n → le (e t i) (rho i)

/-- **Hold vector.** With `H_RST_LONG` (`T1 + Dhi ≤ s`, i.e. CElemStrict2's
`Dhi + wa ≤ P`) the root is the reset value on `[T1, Tw)`. -/
theorem hold_clean {init : Nat} {pins : List Src} {n T1 s Tw Dhi : Nat} {b : Bool}
    {e : Nat → Nat → K3} {r qp G : Nat → K3}
    (hf : followB init pins n b = true) (hh : holdB init pins n b = true)
    (C : CellRun init pins n T1 s Tw Dhi e r qp G) (H_RST_LONG : T1 + Dhi ≤ s) :
    ∀ t, T1 ≤ t → t < Tw → G t = K3.ofBool b := by
  have key : ∀ m t, t < m → T1 ≤ t → t < Tw → G t = K3.ofBool b := by
    intro m
    induction m with
    | zero => intro t h; omega
    | succ m ih =>
      intro t ht h1 h2
      rw [C.H_TREE]
      by_cases hs : t < s
      · rw [C.H_RST_HIGH t h1 hs]; exact follow_any hf _ _
      · obtain ⟨d, hd1, hd2, hd3, hq⟩ := C.H_FB_WIN t (by omega)
        rw [hq, ih (t - d) (by omega) (by omega) (by omega)]
        exact hold_at hh (C.H_DATA_STATIC t (by omega) h2) _
  exact fun t => key (t + 1) t (by omega)

/-- **Forced vector.** No width condition: the root is the reset value on
`[T1, Tw)` for every `s` and every feedback. -/
theorem forced_clean' {init : Nat} {pins : List Src} {n T1 s Tw Dhi : Nat} {b : Bool}
    {e : Nat → Nat → K3} {r qp G : Nat → K3}
    (hf : followB init pins n b = true) (hF : forcB init pins n b = true)
    (C : CellRun init pins n T1 s Tw Dhi e r qp G) :
    ∀ t, T1 ≤ t → t < Tw → G t = K3.ofBool b := by
  intro t h1 h2
  rw [C.H_TREE]
  by_cases hs : t < s
  · rw [C.H_RST_HIGH t h1 hs]; exact follow_any hf _ _
  · exact forced_at hF (C.H_DATA_STATIC t (by omega) h2) _ _

/-- **Leaving vector** (the frontier). The root is the reset value while rst
is high, and the other value at every tick of `[s, Tw)` where rst reads 0. -/
theorem leave_clean {init : Nat} {pins : List Src} {n T1 s Tw Dhi : Nat} {b : Bool}
    {e : Nat → Nat → K3} {r qp G : Nat → K3}
    (hf : followB init pins n b = true) (hl : leaveB init pins n b = true)
    (C : CellRun init pins n T1 s Tw Dhi e r qp G) :
    (∀ t, T1 ≤ t → t < s → G t = K3.ofBool b) ∧
      (∀ t, s ≤ t → t < Tw → r t = .f → G t = K3.ofBool (!b)) := by
  refine ⟨fun t h1 h2 => ?_, fun t h1 h2 hr => ?_⟩
  · rw [C.H_TREE, C.H_RST_HIGH t h1 h2]; exact follow_any hf _ _
  · rw [C.H_TREE, hr]; exact leave_at hl (C.H_DATA_STATIC t h1 h2) _

/-! ## The composition over gcd_hw's network -/

/-- **Every reset loop of gcd_hw leaves reset clean**, with the reset-width
condition only at the 195 hold-vector cells. For every rst-reading LUT loop
`n` (414 of them) with a run `CellRun … n` (hypothesis `H_CELL`, each cell
with its own `T1 n`, `s n`, `Tw n`, `Dhi n`, i.e. its own rst pin timing and
loop delay):
* while rst is high the root is the reset value;
* if `n` is not a frontier controller, it stays at the reset value until a
  data pin leaves the reset vector (`Tw n`);
* if it is one of the 10 frontier controllers, it is at the other value at
  every tick after the release starts where rst reads 0.
`H_RST_LONG` is assumed only for `n ∈ holdL`. -/
theorem gcd_reset_vec {T1 s Tw Dhi : Nat → Nat} {e : Nat → Nat → Nat → K3}
    {r qp G : Nat → Nat → K3}
    (H_CELL : ∀ n init pins, gNode n = .gate init pins → pins.contains (p 0) = true →
      pins.contains (p n) = true →
      CellRun init pins n (T1 n) (s n) (Tw n) (Dhi n) (e n) (r n) (qp n) (G n))
    (H_RST_LONG : ∀ n, n ∈ holdL → T1 n + Dhi n ≤ s n) :
    ∀ n init pins, gNode n = .gate init pins → pins.contains (p 0) = true →
      pins.contains (p n) = true →
      (∀ t, T1 n ≤ t → t < s n → G n t = K3.ofBool (gR n)) ∧
      (n ∉ frontierL → ∀ t, T1 n ≤ t → t < Tw n → G n t = K3.ofBool (gR n)) ∧
      (n ∈ frontierL → ∀ t, s n ≤ t → t < Tw n → r n t = .f → G n t = K3.ofBool (!gR n)) := by
  intro n init pins hg h0 hs
  have C := H_CELL n init pins hg h0 hs
  obtain ⟨_, hf, h5, hhold, hlv, _⟩ := vec_facts hg h0 hs
  have hpre : ∀ t, T1 n ≤ t → t < s n → G n t = K3.ofBool (gR n) := fun t h1 h2 => by
    rw [C.H_TREE, C.H_RST_HIGH t h1 h2]; exact follow_any hf _ _
  have hv : vcls n = (if forcB init pins n (gR n) then 2
      else if holdB init pins n (gR n) then 1
      else if leaveB init pins n (gR n) then 3 else 5) := by
    simp only [vcls, hg, h0, hs, Bool.not_true]; rfl
  refine ⟨hpre, fun hnf => ?_, fun hfr => ?_⟩
  · by_cases hF : forcB init pins n (gR n) = true
    · exact forced_clean' hf hF C
    · by_cases hH : holdB init pins n (gR n) = true
      · have h1 : vcls n = 1 := by rw [hv]; simp [hF, hH]
        exact hold_clean hf hH C (H_RST_LONG n (hhold.1 h1))
      · by_cases hL : leaveB init pins n (gR n) = true
        · have h3 : vcls n = 3 := by rw [hv]; simp [hF, hH, hL]
          exact absurd (hlv.1 h3) hnf
        · exact absurd (by rw [hv]; simp [hF, hH, hL]) h5
  · have h3 := hlv.2 hfr
    have hL : leaveB init pins n (gR n) = true := by
      cases hF : forcB init pins n (gR n) <;> cases hH : holdB init pins n (gR n) <;>
        cases hL : leaveB init pins n (gR n) <;> simp_all
    exact (leave_clean hf hL C).2

/-! ## Exactness at every hold-vector cell -/

/-- **The condition is exact at each of the 195 hold-vector cells.** For the
cell's real LUT at its reset vector (data nets at 1), CElemStrict2's reset
race facts hold from `q = ¬reset` and from the power-up `q = x`, so
`reset_width_iff` applies: every behaviour with loop delay in `[Dlo, Dhi]`
and release width `P` is safe iff `Dhi + wa ≤ P`. -/
theorem gcd_hold_exact {n init : Nat} {pins : List Src} (hg : gNode n = .gate init pins)
    (hn : n ∈ holdL) :
    ∀ v ∈ [K3.ofBool (!gR n), K3.x],
      CElemStrict2.FactsK (cellF init pins n rho1) K3.f K3.x K3.t K3.x K3.f v (gR n) ∧
      ∀ {tb wb wa Dlo Dhi P : Nat}, 1 ≤ Dlo → Dlo ≤ Dhi → wa ≤ P →
        (CElemStrict2.SafeBoxK (cellF init pins n rho1) K3.f K3.x K3.t K3.x K3.f v (gR n)
          tb wb wa Dlo Dhi (tb + wb + P - wa) ↔ Dhi + wa ≤ P) := by
  obtain ⟨h0, hs⟩ := holdL_gate hg hn
  obtain ⟨_, _, _, hhold, _, he⟩ := vec_facts hg h0 hs
  have hE := he (hhold.2 hn)
  simp only [exactB, Bool.and_eq_true] at hE
  intro v hv
  have H : CElemStrict2.FactsK (cellF init pins n rho1) K3.f K3.x K3.t K3.x K3.f v (gR n) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact CElemStrict2.factsK_of_B hE.1
    · exact CElemStrict2.factsK_of_B hE.2
  exact ⟨H, fun h1 h2 h3 => CElemStrict2.reset_width_iff H h1 h2 h3⟩

/-! ## CElemStrict2's loop is a `CellRun`; non-vacuity; the boundary trace -/

theorem le_rho1 (i : Nat) : le (rho1 i) (rho i) := by
  unfold rho1 rho
  by_cases h : gCtl i = true
  · simp only [h, ite_true]; exact le_refl _
  · simp only [h, Bool.false_eq_true, ite_false]; exact Or.inr rfl

/-- CElemStrict2's single loop (pure delay `D`, static data `rho1`, rst
phases) is a `CellRun` with `T1 = tb + wb`, `Dhi = D`, any `Tw`. -/
theorem cellRun_of_loopK {init : Nat} {pins : List Src} {n : Nat} {v : K3}
    {tb wb s wa D Tw : Nat} {i : Nat → K3} {qp G : Nat → K3}
    (L : CElemStrict2.LoopK (cellF init pins n rho1) K3.f K3.x K3.t K3.x K3.f v tb wb s wa D i qp G)
    (hD : 1 ≤ D) (hDs : D ≤ s) :
    CellRun init pins n (tb + wb) s Tw D (fun _ => rho1) i qp G where
  H_TREE t := L.H_TREE t
  H_FB_WIN t ht := ⟨D, hD, Nat.le_refl _, by omega, by
    rw [L.H_FB_PURE t]; simp only [show ¬ t < D by omega, ite_false]⟩
  H_RST_HIGH t h1 h2 := by
    rw [L.H_IN_PHASES t]; unfold CElemStrict.phase
    simp only [show ¬ t < tb by omega, show ¬ t < tb + wb by omega, h2, ite_false, ite_true]
  H_DATA_STATIC _ _ _ i _ _ := le_rho1 i

/-- The pins of the link controller `ulink_n106__1.many.stage[0].u.ctl.u`
(node 1703, bd_c2n): `[req, ack, own output, rst]`. -/
def P1703 : List Src := [p 981, p 1719, p 1703, p 0, .const false, .const false]

theorem node1703 : gNode 1703 = .gate I_c2n P1703 := rfl

theorem node1703_hold : 1703 ∈ holdL := by decide

/-- At its reset vector (req = ack = 0) node 1703 is exactly CElemStrict2's
`c2nR false false`. -/
theorem node1703_c2n : cellF I_c2n P1703 1703 rho1 = CElemStrict2.c2nR false false := by
  funext r q
  cases r <;> cases q <;> decide +kernel

/-- **Non-vacuity.** A run of node 1703 meeting every hypothesis of
`hold_clean`, including `H_RST_LONG`: CElemStrict2's simulator with feedback
1 before reset, loop delay 420, rst settled high from tick 1, release edge
starting at 421 (`T1 + Dhi = 421 ≤ s`). Its conclusion: the root is 0 from
tick 1 on. -/
theorem nonvac_hold (Tw : Nat) :
    ∃ (e : Nat → Nat → K3) (r qp G : Nat → K3),
      CellRun I_c2n P1703 1703 1 421 Tw 420 e r qp G ∧ 1 + 420 ≤ 421 ∧
      ∀ t, 1 ≤ t → t < Tw → G t = K3.f := by
  have L := CElemStrict2.sim_loopK (cellF I_c2n P1703 1703 rho1) (CElemStrict2.rstPh 0 1 421 1)
    K3.t 419 (I0 := K3.f) (IX := K3.x) (I1 := K3.t) (RX := K3.x) (R1 := K3.f)
    (tb := 0) (wb := 1) (s := 421) (wa := 1) (fun _ => rfl)
  have C := cellRun_of_loopK (Tw := Tw) L (by omega) (by omega)
  obtain ⟨_, hf, _, hh, _, _⟩ := vec_facts node1703 (by decide +kernel) (by decide +kernel)
  have h1 : vcls 1703 = 1 := hh.2 node1703_hold
  have hH : holdB I_c2n P1703 1703 false = true := by decide +kernel
  have hg : gR 1703 = false := by decide +kernel
  rw [hg] at hf
  exact ⟨_, _, _, _, C, by omega, hold_clean hf hH C (by omega)⟩

/-- **Exactness counter-trace on the real cell.** Same run with release at
`P = D = 420` (release select x at tick 420): node 1703's root is `x` at the
release tick, so the hold fails at equality. -/
theorem link_boundary_x :
    CElemStrict2.simGK (cellF I_c2n P1703 1703 rho1) (CElemStrict2.rstPh 0 1 420 1) K3.t 419 420
      = K3.x := by
  rw [node1703_c2n]; exact CElemStrict2.rst_boundary_x_c2n

end Formal.Cells.ResetGcdVec
