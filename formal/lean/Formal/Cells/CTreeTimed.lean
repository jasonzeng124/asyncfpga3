import Formal.Cells.CElemTiming
import Formal.Cells.CTree

/-!
# Track 5, probe 5f: timing of `bd_c3`, `bd_c4` and `bd_ctree`

Builds on probe 5b (`CElemTiming`: `bd_c2` under window delays) and probe 5c
(`CTree`: the tree equals a flat C-element in a speed-independent model).

## Part 1: `bd_c3` and `bd_c4` with their real INITs and pin maps

    bd_c3: LUT6 #(.INIT(64'h0000_FE80_0000_FE80)) I0=a I1=b I2=c I3=q I4=rst I5=0
    bd_c4: LUT6 #(.INIT(64'h0000_0000_FFFE_8000)) I0=a I1=b I2=c I3=d I4=q I5=rst

5b's `exc_held` is stated for `bd_c2`'s pin map (feedback on `I2`). Here the
loop is stated for an ARBITRARY excitation function `F t q` (the LUT's Boolean
function of its non-feedback pins at time `t`, with value `q` on the feedback
pin), `LoopG`, so the same settle/hold lemma covers every pin map
(`exc_heldG`, `O_heldG`, `qp_heldG`; `loopG_of_loop` shows 5b's `Loop` is an
instance). The cells' INITs are proved equal to `~rst . celem(inputs, q)`
(`c2r_ce`, `c3r_ce`, `c4r_ce`, by `decide` over the INIT), and the C-element
results are proved once for a list of inputs (`ce_follow_hold`, `ce_reset`,
`ce_four_phase`) and instantiated (`c3_follow_hold`, `c4_follow_hold`,
`c3_reset`, `c4_reset`, `c3_four_phase`, `c4_four_phase`). Tightness of the
minimum pulse width `Dmax = dlmax + dwmax` for `bd_c3`/`bd_c4`: `c3_runt`,
`c4_runt` (5b's closed-form oscillating traces satisfy the real `bd_c3`/`bd_c4`
gate relations with the other inputs tied high).

## Part 2: the timed tree

A tree term `S` (constructors `n2`/`n3`/`n4` = `bd_c2`/`bd_c3`/`bd_c4`, the
shapes of the generate block) carries per-node delay windows `ND`: LUT
`[lmin, lmax]`, own feedback wire `[fmin, fmax]`, and the routed wire from the
node's output to its parent's pin `[wmin, wmax]`; a leaf carries the window of
the wire from the port to its parent's pin. `Run rst x s O` is the gate-level
semantics: there exist traces for every internal net such that every cell
satisfies its `LoopG` relation (real INIT, real pin map, own delays) and every
edge its `WinDelay`.

Environment: every leaf `i` switches cleanly once per phase, at time `σ i k`
(`H_LEAF`), targets alternate (`H_ALT`), and every leaf's next switch waits
`E` after the environment saw the root output at `V k` (`H_ACK`).

Timing is max-plus over the leaf times (exact, per phase):
`Late n k = lmax n + max_j (Late j k + wmax j)` (latest settle) and
`Early n k = lmin n + max_j (Early j k + wmin j)` (earliest possible move:
a C-element moves only after ALL inputs have). `tree_phase` /
`tree_four_phase`: every node drives `V k` on `[Late n k, Early n (k+1))`,
given the per-phase lifted fork condition `NodesOK` (every node's feedback
settled, `Late n k + fmax n ≤ Early root k + E`). Static corollaries:
* `Late_le`: `Late s k ≤ c k + Lmax s`, `Lmax` = max over paths of
  `sum (lmax + wmax)` (the depth term of the bundling budget);
  `Lmax_depth`: uniform delays give `Lmax + wmax ≤ depth (lmax + wmax) + imax`.
* `Early_ge`: `c k + MinD s ≤ Early s k`, `MinD` = min over paths of
  `sum (lmin + wmin)`.
* `tree_four_phase_static`: `StaticOK E 0 s` (for every node `n`:
  `Spread n + fmax n ≤ dist_min(n -> root) + E`, `Spread` = accumulated
  `(lmax - lmin) + (wmax - wmin)` below `n`) implies `NodesOK` for all
  phases (`static_ok`, via `Late_le_Early`). For a single cell with zero port
  wires this is exactly 5b's `E ≥ dwmax + (dlmax - dlmin)`.

Instances (`ctree5_timed`, `ctree8_timed`), generate-block shapes N = 5
(`C2(C4(a0..a3), a4)`) and N = 8 (`C2(C4, C4)`) with symbolic uniform delays
(`U`: LUT, feedback, inter-cell wire, port wire): output `= V k` on
`[c k + 2 lmax + wmax + imax, c (k+1) + L)` with `L = lmin + imin` (N = 5,
the a4 path has one cell) and `L = 2 lmin + wmin + imin` (N = 8), under
`fmax + 2 (lmax - lmin) + (wmax - wmin) + (imax - imin) ≤ E`.

Core Lean only (imports 5b and 5c, read-only).
-/

namespace Formal.Cells.CTreeTimed
open Formal.Cells
open Formal.Cells.CElemTiming (Trace WinDelay transport_winDelay runt_lut runt_wire
  runt_oscillates aR bR rstR OR qpR excT exc INIT_c2 c2_eq)

/-! ## 0. The C-element on a list of inputs -/

/-- Flat C-element (5c's definition): all 1 -> 1, all 0 -> 0, else hold `q`. -/
abbrev celem := CTree.celem

theorem celem_all (v q : Bool) (l : List Bool) (hne : l ≠ []) (h : ∀ b ∈ l, b = v) :
    celem l q = v := by
  obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil l hne
  cases v
  · have h1 : l.all id = false := by
      rw [Bool.eq_false_iff]; intro hh
      rw [List.all_eq_true] at hh
      have := hh b hb; rw [h b hb] at this; exact absurd this (by decide)
    have h2 : l.all (! ·) = true := by
      rw [List.all_eq_true]; intro x hx; rw [h x hx]; rfl
    simp [CTree.celem, h1, h2]
  · have h1 : l.all id = true := by
      rw [List.all_eq_true]; intro x hx; rw [h x hx]; rfl
    simp [CTree.celem, h1]

theorem celem_hold (v : Bool) (l : List Bool) (h : ∃ b ∈ l, b = v) : celem l v = v := by
  obtain ⟨b, hb, hbv⟩ := h
  cases v
  · have h1 : l.all id = false := by
      rw [Bool.eq_false_iff]; intro hh
      rw [List.all_eq_true] at hh
      have := hh b hb; rw [hbv] at this; exact absurd this (by decide)
    simp [CTree.celem, h1]
  · have h1 : l.all (! ·) = false := by
      rw [Bool.eq_false_iff]; intro hh
      rw [List.all_eq_true] at hh
      have := hh b hb; rw [hbv] at this; exact absurd this (by decide)
    simp only [CTree.celem, h1]
    split <;> rfl

/-- The real INITs with their real pin maps are `~rst . celem(inputs, q)`. -/
theorem c2r_ce : ∀ r a b q, CTree.c2r r a b q = (!r && celem [a, b] q) := by decide
theorem c3r_ce : ∀ r a b c q, CTree.c3r r a b c q = (!r && celem [a, b, c] q) := by decide
theorem c4r_ce : ∀ r a b c d q, CTree.c4r r a b c d q = (!r && celem [a, b, c, d] q) := by
  decide

/-- 5c's INIT constants are 5b's / `bd_ce.v`'s (same numerals). -/
theorem init_c2_same : CTree.INIT_C2 = INIT_c2 := rfl

/-! ## 1. The loop for an arbitrary pin map -/

/-- **Gate relations of one feedback-LUT cell, any pin map.** `F t q` is the
LUT's Boolean function (real INIT via `lutB`) of its non-feedback pins at time
`t`, with `q` on the feedback pin. -/
structure LoopG (F : Nat → Bool → Bool) (O qp : Trace) (dlmin dlmax dwmin dwmax : Nat) : Prop where
  /-- **H_LUT**: `O` is the excitation delayed by `[dlmin, dlmax]` (window
  channel; prjxray LUT I->O fast-min / slow-max). Test: GLS of a lone LUT at
  the SDF corners. -/
  H_LUT : WinDelay dlmin dlmax (fun t => F t (qp t)) O
  /-- **H_FB**: the routed feedback wire `O -> feedback pin` delays by
  `[dwmin, dwmax]` (prjxray min/max of its pips). Test: SDF INTERCONNECT of
  the cell's `q` net in `cells/gls/`, >= 4 seeds. -/
  H_FB : WinDelay dwmin dwmax O qp
  /-- **H_LOOP_POS**: the loop has positive minimum delay. -/
  H_LOOP_POS : 0 < dlmin + dwmin

/-- 5b's `Loop` (bd_c2 pin map) is an instance. -/
theorem loopG_of_loop {init : Nat} {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}
    (L : CElemTiming.Loop init a b rst O qp dlmin dlmax dwmin dwmax) :
    LoopG (fun t q => exc init (a t) (b t) q (rst t)) O qp dlmin dlmax dwmin dwmax :=
  ⟨L.H_LUT, L.H_FB, L.H_LOOP_POS⟩

section generic
variable {F : Nat → Bool → Bool} {O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

/-- **Forced, then held** (any pin map). Forced to `v` for `Dmax` ticks from
`t0`, fixed point on `[t0, t2)`: the excitation is `v` on
`[t0, max (t0 + Dmax) t2)`. No assumption on the state before `t0`. -/
theorem exc_heldG (L : LoopG F O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : Nat)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, F s q = v)
    (hfix : ∀ s, t0 ≤ s → s < t2 → F s v = v) :
    ∀ s, t0 ≤ s → (s < t0 + (dlmax + dwmax) ∨ s < t2) → F s (qp s) = v := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro hs0 hs2
    by_cases hlt : s < t0 + (dlmax + dwmax)
    · exact hforce s hs0 hlt (qp s)
    · have hs2' : s < t2 := by omega
      obtain ⟨s1, h1a, h1b, e1⟩ := L.H_FB s (by omega)
      obtain ⟨s2, h2a, h2b, e2⟩ := L.H_LUT s1 (by omega)
      have hpos := L.H_LOOP_POS
      have hv : F s2 (qp s2) = v := ih s2 (by omega) (by omega) (by omega)
      have hq : qp s = v := by rw [e1, e2]; exact hv
      rw [hq]; exact hfix s hs0 hs2'

theorem O_heldG (L : LoopG F O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : Nat)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, F s q = v)
    (hfix : ∀ s, t0 ≤ s → s < t2 → F s v = v) :
    ∀ t, t0 + dlmax ≤ t → t < t2 + dlmin → O t = v := by
  intro t h1 h2
  obtain ⟨s, ha, hb, e⟩ := L.H_LUT t (by omega)
  rw [e]; exact exc_heldG L v t0 t2 hforce hfix s (by omega) (by omega)

theorem qp_heldG (L : LoopG F O qp dlmin dlmax dwmin dwmax) (v : Bool) (t0 t2 : Nat)
    (hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, F s q = v)
    (hfix : ∀ s, t0 ≤ s → s < t2 → F s v = v) :
    ∀ t, t0 + (dlmax + dwmax) ≤ t → t < t2 + (dlmin + dwmin) → qp t = v := by
  intro t h1 h2
  obtain ⟨s, ha, hb, e⟩ := L.H_FB t (by omega)
  rw [e]; exact O_heldG L v t0 t2 hforce hfix s (by omega) (by omega)

end generic

/-! ## 2. C-element cells on a list of inputs -/

/-- Excitation of a C-element cell with reset: `~rst . celem(ins, q)`. -/
def ceF (rst : Trace) (ins : Nat → List Bool) : Nat → Bool → Bool :=
  fun t q => !rst t && celem (ins t) q

section ce
variable {rst O qp : Trace} {ins : Nat → List Bool} {dlmin dlmax dwmin dwmax : Nat}

/-- **Follow-and-hold, any fan-in.** `H_PULSE`: all inputs `= v`, `rst = 0`
for `Dmax` ticks from `t0`; `H_NORST`; `H_SOME`: on `[t0, t2]` some input is
`v`. Then `O = v` on `[t0 + dlmax, t2 + dlmin]`, `qp = v` on
`[t0 + Dmax, t2 + Dmin]`. -/
theorem ce_follow_hold (L : LoopG (ceF rst ins) O qp dlmin dlmax dwmin dwmax)
    (hne : ∀ t, ins t ≠ []) (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → (∀ b ∈ ins s, b = v) ∧ rst s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → rst s = false)
    (H_SOME : ∀ s, t0 ≤ s → s ≤ t2 → ∃ b ∈ ins s, b = v) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = v) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = v) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, ceF rst ins s q = v := by
    intro s h1 h2 q
    obtain ⟨ha, hr⟩ := H_PULSE s h1 h2
    simp only [ceF, hr, Bool.not_false, Bool.true_and]
    exact celem_all v q _ (hne s) ha
  have hfix : ∀ s, t0 ≤ s → s < t2 + 1 → ceF rst ins s v = v := by
    intro s h1 h2
    simp only [ceF, H_NORST s h1 (by omega), Bool.not_false, Bool.true_and]
    exact celem_hold v _ (H_SOME s h1 (by omega))
  exact ⟨fun t h1 h2 => O_heldG L v t0 (t2 + 1) hforce hfix t h1 (by omega),
    fun t h1 h2 => qp_heldG L v t0 (t2 + 1) hforce hfix t h1 (by omega)⟩

/-- **Reset, any fan-in.** `rst = 1` for `Dmax` ticks (any power-up state);
afterwards up to `t2` some input is 0 (`rst` free). Then the cell reads 0. -/
theorem ce_reset (L : LoopG (ceF rst ins) O qp dlmin dlmax dwmin dwmax) (t0 t2 : Nat)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → ∃ b ∈ ins s, b = false) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = false) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = false) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → ∀ q, ceF rst ins s q = false := by
    intro s h1 h2 q
    simp [ceF, H_RST_PULSE s h1 h2]
  have hfix : ∀ s, t0 ≤ s → s < t2 + 1 → ceF rst ins s false = false := by
    intro s h1 h2
    simp only [ceF]
    rw [celem_hold false _ (H_RELEASE s h1 (by omega))]
    simp
  exact ⟨fun t h1 h2 => O_heldG L false t0 (t2 + 1) hforce hfix t h1 (by omega),
    fun t h1 h2 => qp_heldG L false t0 (t2 + 1) hforce hfix t h1 (by omega)⟩

theorem winDelay_le' {dmin dmax : Nat} {x y : Trace} (h : WinDelay dmin dmax x y) :
    dmin ≤ dmax := by
  obtain ⟨s, h1, h2, _⟩ := h dmax (Nat.le_refl _); omega

/-- **Four-phase correctness, any fan-in** (5b's `c2_four_phase` with a list of
inputs). Hypotheses as in 5b: `H_ALT`, `H_ORDER`, `H_ALL` (all inputs `= V k`
at `c k`), `H_NEXT` (on `[c k, c (k+1))` some input still `V k`), `H_NORST`,
`H_ACK` (an input leaves `V k` at `s` only `E` after the environment saw
`O = V k` at some `u ≥ c k`), `H_ENV_LATENCY : Dmax ≤ dlmin + E`,
`H_RESET_DONE`. -/
theorem ce_four_phase (L : LoopG (ceF rst ins) O qp dlmin dlmax dwmin dwmax)
    (hne : ∀ t, ins t ≠ [])
    (V : Nat → Bool) (c : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_ORDER : ∀ k, c k < c (k + 1))
    (H_ALL : ∀ k, ∀ b ∈ ins (c k), b = V k)
    (H_NEXT : ∀ k s, c k ≤ s → s < c (k + 1) → ∃ b ∈ ins s, b = V k)
    (H_NORST : ∀ s, c 0 ≤ s → rst s = false)
    (H_ACK : ∀ k s, c k ≤ s → (∃ b ∈ ins s, b ≠ V k) →
        ∃ u, c k ≤ u ∧ u + E ≤ s ∧ O u = V k)
    (H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E)
    (H_RESET_DONE : ∀ u, c 0 ≤ u → u < c 0 + dlmin → O u = !V 0) :
    ∀ k, (∀ t, c k + dlmax ≤ t → t + 1 ≤ c (k + 1) + dlmin → O t = V k) ∧
         (∀ t, c k + (dlmax + dwmax) ≤ t → t + 1 ≤ c (k + 1) + (dlmin + dwmin) → qp t = V k) := by
  have hmono : ∀ k j, k ≤ j → c k ≤ c j := by
    intro k j hkj
    induction j with
    | zero => have : k = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ j ih =>
      rcases Nat.lt_or_ge k (j + 1) with h | h
      · have := ih (by omega); have := H_ORDER j; omega
      · have : k = j + 1 := by omega
        subst this; exact Nat.le_refl _
  have step : ∀ k, (∀ u, c k ≤ u → u < c k + dlmin → O u = !V k) →
      (∀ t, c k + dlmax ≤ t → t + 1 ≤ c (k + 1) + dlmin → O t = V k) ∧
      (∀ t, c k + (dlmax + dwmax) ≤ t → t + 1 ≤ c (k + 1) + (dlmin + dwmin) → qp t = V k) ∧
      c k + (dlmax + dwmax) ≤ c (k + 1) := by
    intro k R
    have arrive : ∀ s, c k ≤ s → s < c k + (dlmax + dwmax) → ∀ b ∈ ins s, b = V k := by
      intro s h1 h2
      rcases Classical.em (∃ b ∈ ins s, b ≠ V k) with hd | hd
      · obtain ⟨u, hu1, hu2, hu3⟩ := H_ACK k s h1 hd
        have := R u hu1 (by omega)
        rw [hu3] at this; cases hv : V k <;> simp [hv] at this
      · intro b hb
        apply Classical.byContradiction; intro hbn; exact hd ⟨b, hb, hbn⟩
    have hgap : c k + (dlmax + dwmax) ≤ c (k + 1) := by
      apply Classical.byContradiction; intro hlt
      obtain ⟨b, hb⟩ := List.exists_mem_of_ne_nil _ (hne (c (k + 1)))
      have h1 := arrive (c (k + 1)) (Nat.le_of_lt (H_ORDER k)) (by omega) b hb
      have h2 := H_ALL (k + 1) b hb
      rw [H_ALT k, h1] at h2; cases hv : V k <;> simp [hv] at h2
    have hnr : ∀ s, c k ≤ s → rst s = false :=
      fun s hs => H_NORST s (by have := hmono 0 k (Nat.zero_le _); omega)
    have res := ce_follow_hold L hne (V k) (c k) (c (k + 1) - 1)
      (fun s h1 h2 => ⟨arrive s h1 h2, hnr s h1⟩)
      (fun s h1 _ => hnr s h1)
      (fun s h1 h2 => H_NEXT k s h1 (by have := H_ORDER k; omega))
    exact ⟨fun t h1 h2 => res.1 t h1 (by omega), fun t h1 h2 => res.2 t h1 (by omega), hgap⟩
  have R : ∀ k, ∀ u, c k ≤ u → u < c k + dlmin → O u = !V k := by
    intro k
    induction k with
    | zero => exact H_RESET_DONE
    | succ k ih =>
      intro u h1 h2
      have ⟨hO, _, hgap⟩ := step k ih
      rw [H_ALT k, Bool.not_not]
      exact hO u (by omega) (by omega)
  intro k
  have ⟨h1, h2, _⟩ := step k (R k)
  exact ⟨h1, h2⟩

end ce

/-! ## 3. `bd_c3` and `bd_c4` with their real INITs and pin maps -/

/-- `bd_c3`'s excitation: `lutB INIT [a, b, c, q, rst, 0]` (feedback on I3). -/
def F3 (a b c rst : Trace) : Nat → Bool → Bool :=
  fun t q => lutB CTree.INIT_C3 [a t, b t, c t, q, rst t, false]
/-- `bd_c4`'s excitation: `lutB INIT [a, b, c, d, q, rst]` (feedback on I4). -/
def F4 (a b c d rst : Trace) : Nat → Bool → Bool :=
  fun t q => lutB CTree.INIT_C4 [a t, b t, c t, d t, q, rst t]

theorem F3_ce (a b c rst : Trace) : F3 a b c rst = ceF rst (fun t => [a t, b t, c t]) := by
  funext t q; exact c3r_ce (rst t) (a t) (b t) (c t) q
theorem F4_ce (a b c d rst : Trace) :
    F4 a b c d rst = ceF rst (fun t => [a t, b t, c t, d t]) := by
  funext t q; exact c4r_ce (rst t) (a t) (b t) (c t) (d t) q

section c34
variable {a b c d rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

/-- **(a) `bd_c3` follows and holds.** -/
theorem c3_follow_hold (L : LoopG (F3 a b c rst) O qp dlmin dlmax dwmin dwmax)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      a s = v ∧ b s = v ∧ c s = v ∧ rst s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → rst s = false)
    (H_NOT_ALL : ∀ s, t0 ≤ s → s ≤ t2 → a s = v ∨ b s = v ∨ c s = v) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = v) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = v) := by
  rw [F3_ce] at L
  refine ce_follow_hold L (fun _ => by simp) v t0 t2 ?_ H_NORST ?_
  · intro s h1 h2
    obtain ⟨ha, hb, hc, hr⟩ := H_PULSE s h1 h2
    refine ⟨?_, hr⟩; intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption
  · intro s h1 h2
    rcases H_NOT_ALL s h1 h2 with h | h | h
    · exact ⟨a s, by simp, h⟩
    · exact ⟨b s, by simp, h⟩
    · exact ⟨c s, by simp, h⟩

/-- **(a) `bd_c4` follows and holds.** -/
theorem c4_follow_hold (L : LoopG (F4 a b c d rst) O qp dlmin dlmax dwmin dwmax)
    (v : Bool) (t0 t2 : Nat)
    (H_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      a s = v ∧ b s = v ∧ c s = v ∧ d s = v ∧ rst s = false)
    (H_NORST : ∀ s, t0 ≤ s → s ≤ t2 → rst s = false)
    (H_NOT_ALL : ∀ s, t0 ≤ s → s ≤ t2 → a s = v ∨ b s = v ∨ c s = v ∨ d s = v) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = v) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = v) := by
  rw [F4_ce] at L
  refine ce_follow_hold L (fun _ => by simp) v t0 t2 ?_ H_NORST ?_
  · intro s h1 h2
    obtain ⟨ha, hb, hc, hd, hr⟩ := H_PULSE s h1 h2
    refine ⟨?_, hr⟩; intro x hx; simp at hx
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · intro s h1 h2
    rcases H_NOT_ALL s h1 h2 with h | h | h | h
    · exact ⟨a s, by simp, h⟩
    · exact ⟨b s, by simp, h⟩
    · exact ⟨c s, by simp, h⟩
    · exact ⟨d s, by simp, h⟩

/-- **Reset of `bd_c3`.** -/
theorem c3_reset (L : LoopG (F3 a b c rst) O qp dlmin dlmax dwmin dwmax) (t0 t2 : Nat)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 → a s = false ∨ b s = false ∨ c s = false) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = false) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = false) := by
  rw [F3_ce] at L
  refine ce_reset L t0 t2 H_RST_PULSE ?_
  intro s h1 h2
  rcases H_RELEASE s h1 h2 with h | h | h
  · exact ⟨a s, by simp, h⟩
  · exact ⟨b s, by simp, h⟩
  · exact ⟨c s, by simp, h⟩

/-- **Reset of `bd_c4`.** -/
theorem c4_reset (L : LoopG (F4 a b c d rst) O qp dlmin dlmax dwmin dwmax) (t0 t2 : Nat)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true)
    (H_RELEASE : ∀ s, t0 ≤ s → s ≤ t2 →
      a s = false ∨ b s = false ∨ c s = false ∨ d s = false) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = false) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = false) := by
  rw [F4_ce] at L
  refine ce_reset L t0 t2 H_RST_PULSE ?_
  intro s h1 h2
  rcases H_RELEASE s h1 h2 with h | h | h | h
  · exact ⟨a s, by simp, h⟩
  · exact ⟨b s, by simp, h⟩
  · exact ⟨c s, by simp, h⟩
  · exact ⟨d s, by simp, h⟩

end c34

/-! ### (b) the `Dmax` bound is exact for `bd_c3` and `bd_c4` too

With the other inputs tied to 1 and `rst = 0`, both cells compute `b || q`,
exactly 5b's `bd_c2` with `a = 1`; so 5b's closed-form traces are gate-level
behaviours of the real `bd_c3`/`bd_c4` LUTs. -/

theorem c3_as_c2 : ∀ b q, lutB CTree.INIT_C3 [true, true, b, q, false, false] =
    exc INIT_c2 true b q false := by decide
theorem c4_as_c2 : ∀ b q, lutB CTree.INIT_C4 [true, true, true, b, q, false] =
    exc INIT_c2 true b q false := by decide

/-- **`bd_c3` runt loop**: `a = b = 1`, `rst = 0`, `c` a pulse of width
`0 < w < D = dl + dw` at `t0`. The traces satisfy every gate relation of the
real `bd_c3` (fixed delays `dl`, `dw`), the inputs are constant after
`t0 + w`, and the feedback pin oscillates forever with period `D`. -/
theorem c3_runt (dl dw w t0 : Nat) (hw0 : 0 < w) (hw : w < dl + dw) :
    LoopG (F3 aR aR (bR w t0) rstR) (OR dl dw w t0) (qpR dl dw w t0) dl dl dw dw ∧
    (∀ t, t0 + w ≤ t → bR w t0 t = false) ∧
    (∀ n, qpR dl dw w t0 (t0 + (dl + dw) * (n + 1)) = true ∧
          qpR dl dw w t0 (t0 + (dl + dw) * (n + 1) + w) = false) := by
  have hF : (fun t => F3 aR aR (bR w t0) rstR t (qpR dl dw w t0 t)) =
      excT INIT_c2 aR (bR w t0) rstR (qpR dl dw w t0) := by
    funext t; exact c3_as_c2 _ _
  have osc := runt_oscillates dl dw w t0 hw0 hw
  refine ⟨⟨?_, transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (runt_wire dl dw w t0),
    by omega⟩, fun t ht => (osc.1 t ht).2.1, osc.2.1⟩
  rw [hF]; exact transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (runt_lut dl dw w t0 hw)

/-- **`bd_c4` runt loop** (`a = b = c = 1`, `d` the runt). -/
theorem c4_runt (dl dw w t0 : Nat) (hw0 : 0 < w) (hw : w < dl + dw) :
    LoopG (F4 aR aR aR (bR w t0) rstR) (OR dl dw w t0) (qpR dl dw w t0) dl dl dw dw ∧
    (∀ t, t0 + w ≤ t → bR w t0 t = false) ∧
    (∀ n, qpR dl dw w t0 (t0 + (dl + dw) * (n + 1)) = true ∧
          qpR dl dw w t0 (t0 + (dl + dw) * (n + 1) + w) = false) := by
  have hF : (fun t => F4 aR aR aR (bR w t0) rstR t (qpR dl dw w t0 t)) =
      excT INIT_c2 aR (bR w t0) rstR (qpR dl dw w t0) := by
    funext t; exact c4_as_c2 _ _
  have osc := runt_oscillates dl dw w t0 hw0 hw
  refine ⟨⟨?_, transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (runt_wire dl dw w t0),
    by omega⟩, fun t ht => (osc.1 t ht).2.1, osc.2.1⟩
  rw [hF]; exact transport_winDelay (Nat.le_refl _) (Nat.le_refl _) (runt_lut dl dw w t0 hw)

/-! ### (c) four-phase for `bd_c3` / `bd_c4` -/

section c34fp
variable {a b c d rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

theorem c3_four_phase (L : LoopG (F3 a b c rst) O qp dlmin dlmax dwmin dwmax)
    (V : Nat → Bool) (cc : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_ORDER : ∀ k, cc k < cc (k + 1))
    (H_ALL : ∀ k, a (cc k) = V k ∧ b (cc k) = V k ∧ c (cc k) = V k)
    (H_NEXT : ∀ k s, cc k ≤ s → s < cc (k + 1) → a s = V k ∨ b s = V k ∨ c s = V k)
    (H_NORST : ∀ s, cc 0 ≤ s → rst s = false)
    (H_ACK : ∀ k s, cc k ≤ s → (a s ≠ V k ∨ b s ≠ V k ∨ c s ≠ V k) →
        ∃ u, cc k ≤ u ∧ u + E ≤ s ∧ O u = V k)
    (H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E)
    (H_RESET_DONE : ∀ u, cc 0 ≤ u → u < cc 0 + dlmin → O u = !V 0) :
    ∀ k, (∀ t, cc k + dlmax ≤ t → t + 1 ≤ cc (k + 1) + dlmin → O t = V k) ∧
         (∀ t, cc k + (dlmax + dwmax) ≤ t → t + 1 ≤ cc (k + 1) + (dlmin + dwmin) →
            qp t = V k) := by
  rw [F3_ce] at L
  refine ce_four_phase L (fun _ => by simp) V cc E H_ALT H_ORDER ?_ ?_ H_NORST ?_
    H_ENV_LATENCY H_RESET_DONE
  · intro k x hx; simp at hx
    obtain ⟨h1, h2, h3⟩ := H_ALL k
    rcases hx with rfl | rfl | rfl <;> assumption
  · intro k s h1 h2
    rcases H_NEXT k s h1 h2 with h | h | h
    · exact ⟨a s, by simp, h⟩
    · exact ⟨b s, by simp, h⟩
    · exact ⟨c s, by simp, h⟩
  · intro k s h1 ⟨x, hx, hxv⟩
    apply H_ACK k s h1
    simp at hx; rcases hx with rfl | rfl | rfl
    · exact Or.inl hxv
    · exact Or.inr (Or.inl hxv)
    · exact Or.inr (Or.inr hxv)

theorem c4_four_phase (L : LoopG (F4 a b c d rst) O qp dlmin dlmax dwmin dwmax)
    (V : Nat → Bool) (cc : Nat → Nat) (E : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_ORDER : ∀ k, cc k < cc (k + 1))
    (H_ALL : ∀ k, a (cc k) = V k ∧ b (cc k) = V k ∧ c (cc k) = V k ∧ d (cc k) = V k)
    (H_NEXT : ∀ k s, cc k ≤ s → s < cc (k + 1) →
      a s = V k ∨ b s = V k ∨ c s = V k ∨ d s = V k)
    (H_NORST : ∀ s, cc 0 ≤ s → rst s = false)
    (H_ACK : ∀ k s, cc k ≤ s → (a s ≠ V k ∨ b s ≠ V k ∨ c s ≠ V k ∨ d s ≠ V k) →
        ∃ u, cc k ≤ u ∧ u + E ≤ s ∧ O u = V k)
    (H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E)
    (H_RESET_DONE : ∀ u, cc 0 ≤ u → u < cc 0 + dlmin → O u = !V 0) :
    ∀ k, (∀ t, cc k + dlmax ≤ t → t + 1 ≤ cc (k + 1) + dlmin → O t = V k) ∧
         (∀ t, cc k + (dlmax + dwmax) ≤ t → t + 1 ≤ cc (k + 1) + (dlmin + dwmin) →
            qp t = V k) := by
  rw [F4_ce] at L
  refine ce_four_phase L (fun _ => by simp) V cc E H_ALT H_ORDER ?_ ?_ H_NORST ?_
    H_ENV_LATENCY H_RESET_DONE
  · intro k x hx; simp at hx
    obtain ⟨h1, h2, h3, h4⟩ := H_ALL k
    rcases hx with rfl | rfl | rfl | rfl <;> assumption
  · intro k s h1 h2
    rcases H_NEXT k s h1 h2 with h | h | h | h
    · exact ⟨a s, by simp, h⟩
    · exact ⟨b s, by simp, h⟩
    · exact ⟨c s, by simp, h⟩
    · exact ⟨d s, by simp, h⟩
  · intro k s h1 ⟨x, hx, hxv⟩
    apply H_ACK k s h1
    simp at hx; rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl hxv
    · exact Or.inr (Or.inl hxv)
    · exact Or.inr (Or.inr (Or.inl hxv))
    · exact Or.inr (Or.inr (Or.inr hxv))

end c34fp

/-! ## 4. The timed tree -/

/-- Maximum of a list of naturals (0 for the empty list). -/
def lmx (l : List Nat) : Nat := l.foldr max 0

theorem le_lmx {x : Nat} {l : List Nat} (h : x ∈ l) : x ≤ lmx l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [lmx, List.foldr] at *
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := ih h; omega

theorem lmx_le {l : List Nat} {B : Nat} (h : ∀ x ∈ l, x ≤ B) : lmx l ≤ B := by
  induction l with
  | nil => simp [lmx]
  | cons a l ih =>
    simp only [lmx, List.foldr] at *
    have h1 := h a (by simp)
    have h2 := ih (fun x hx => h x (by simp [hx]))
    omega

theorem lmx_mem {l : List Nat} (hne : l ≠ []) : lmx l ∈ l := by
  induction l with
  | nil => exact absurd rfl hne
  | cons a l ih =>
    simp only [lmx, List.foldr] at *
    by_cases hl : l = []
    · subst hl; simp
    · have := ih hl
      rcases Nat.le_total a (List.foldr max 0 l) with h | h
      · rw [Nat.max_eq_right h]; exact List.mem_cons_of_mem _ this
      · rw [Nat.max_eq_left h]; exact List.mem_cons_self

/-- A window-delayed copy of a trace that is `v` on `[lo, hi)` is `v` on
`[lo + dmax, hi + dmin)`. -/
theorem win_claim {dmin dmax : Nat} {x y : Trace} (h : WinDelay dmin dmax x y)
    (v : Bool) (lo hi : Nat) (hx : ∀ t, lo ≤ t → t < hi → x t = v) :
    ∀ t, lo + dmax ≤ t → t < hi + dmin → y t = v := by
  intro t h1 h2
  obtain ⟨s, ha, hb, e⟩ := h t (by omega)
  rw [e]; exact hx s (by omega) (by omega)

/-- One input pin of a node and the window `[lo, hi)` on which it is known to
equal the phase value. -/
structure Ch where
  P : Trace
  lo : Nat
  hi : Nat

/-- **One node, one phase.** If every input pin `j` is `v` on `[lo j, hi j)`,
and no pin leaves `v` before the loop has been forced for `Dmax` after the
last pin settled (`hforce : max lo + Dmax ≤ hi j`), then `O = v` on
`[max lo + lmax, max hi + lmin)`. The upper end is the LAST pin's `hi`: the
cell holds while any input still holds. -/
theorem node_step {rst O qp : Trace} {lmin lmax fmin fmax : Nat} (cs : List Ch)
    (hne : cs ≠ []) (v : Bool)
    (L : LoopG (ceF rst (fun t => cs.map (fun ch => ch.P t))) O qp lmin lmax fmin fmax)
    (hcl : ∀ ch ∈ cs, ∀ t, ch.lo ≤ t → t < ch.hi → ch.P t = v)
    (hforce : ∀ ch ∈ cs, lmx (cs.map Ch.lo) + (lmax + fmax) ≤ ch.hi)
    (hrst : ∀ t, lmx (cs.map Ch.lo) ≤ t → rst t = false) :
    ∀ t, lmx (cs.map Ch.lo) + lmax ≤ t → t < lmx (cs.map Ch.hi) + lmin → O t = v := by
  have hA0 : ∀ ch ∈ cs, ch.lo ≤ lmx (cs.map Ch.lo) := fun ch h => le_lmx (List.mem_map_of_mem h)
  obtain ⟨js, hjs, hjsv⟩ := List.mem_map.mp (lmx_mem (l := cs.map Ch.hi) (by simpa using hne))
  have hmne : ∀ t, (cs.map (fun ch => ch.P t)) ≠ [] := by intro t; simpa using hne
  have hf : ∀ s, lmx (cs.map Ch.lo) ≤ s → s < lmx (cs.map Ch.lo) + (lmax + fmax) → ∀ q,
      ceF rst (fun t => cs.map (fun ch => ch.P t)) s q = v := by
    intro s h1 h2 q
    simp only [ceF, hrst s h1, Bool.not_false, Bool.true_and]
    apply celem_all v q _ (hmne s)
    intro b hb
    obtain ⟨ch, hch, rfl⟩ := List.mem_map.mp hb
    have := hA0 ch hch; have := hforce ch hch
    exact hcl ch hch s (by omega) (by omega)
  have hfix : ∀ s, lmx (cs.map Ch.lo) ≤ s → s < lmx (cs.map Ch.hi) →
      ceF rst (fun t => cs.map (fun ch => ch.P t)) s v = v := by
    intro s h1 h2
    simp only [ceF, hrst s h1, Bool.not_false, Bool.true_and]
    apply celem_hold v
    have := hA0 js hjs
    exact ⟨js.P s, List.mem_map_of_mem hjs, hcl js hjs s (by omega) (by omega)⟩
  exact O_heldG L v _ _ hf hfix

/-- Per-node delay windows (ticks): LUT `[lmin, lmax]`, own feedback wire
`[fmin, fmax]`, routed wire from this node's output to its parent's pin
`[wmin, wmax]` (ignored at the root). -/
structure ND where
  lmin : Nat
  lmax : Nat
  fmin : Nat
  fmax : Nat
  wmin : Nat
  wmax : Nat

/-- A C-element tree with per-node delays. `leaf i wmin wmax`: port `a[i]`
and the window of its wire to the parent's pin. -/
inductive S where
  | leaf (i : Nat) (wmin wmax : Nat)
  | n2 (p : ND) (a b : S)
  | n3 (p : ND) (a b c : S)
  | n4 (p : ND) (a b c d : S)

def S.wmin : S → Nat
  | .leaf _ w _ => w
  | .n2 p .. => p.wmin
  | .n3 p .. => p.wmin
  | .n4 p .. => p.wmin

def S.wmax : S → Nat
  | .leaf _ _ w => w
  | .n2 p .. => p.wmax
  | .n3 p .. => p.wmax
  | .n4 p .. => p.wmax

def leaves : S → List Nat
  | .leaf i _ _ => [i]
  | .n2 _ a b => leaves a ++ leaves b
  | .n3 _ a b c => leaves a ++ leaves b ++ leaves c
  | .n4 _ a b c d => leaves a ++ leaves b ++ leaves c ++ leaves d

/-- **Gate-level semantics of the tree.** `O` is the trace the node drives
(a leaf: its port trace `x i`; a cell: its LUT output pin). For a cell there
exist traces for its children's outputs, their pins (after the edge wire,
`WinDelay` with the child's `wmin/wmax`) and its feedback pin such that the
cell satisfies `LoopG` with its REAL INIT and pin map (`CTree.c2r/c3r/c4r`,
i.e. `lutB` on `bd_c2`/`bd_c3`/`bd_c4`'s INIT) and its own delay windows. -/
def Run (rst : Trace) (x : Nat → Trace) : S → Trace → Prop
  | .leaf i _ _, O => O = x i
  | .n2 p a b, O => ∃ Oa Ob Pa Pb qp : Trace,
      Run rst x a Oa ∧ Run rst x b Ob ∧
      WinDelay a.wmin a.wmax Oa Pa ∧ WinDelay b.wmin b.wmax Ob Pb ∧
      LoopG (fun t q => CTree.c2r (rst t) (Pa t) (Pb t) q) O qp p.lmin p.lmax p.fmin p.fmax
  | .n3 p a b c, O => ∃ Oa Ob Oc Pa Pb Pc qp : Trace,
      Run rst x a Oa ∧ Run rst x b Ob ∧ Run rst x c Oc ∧
      WinDelay a.wmin a.wmax Oa Pa ∧ WinDelay b.wmin b.wmax Ob Pb ∧
      WinDelay c.wmin c.wmax Oc Pc ∧
      LoopG (fun t q => CTree.c3r (rst t) (Pa t) (Pb t) (Pc t) q) O qp
        p.lmin p.lmax p.fmin p.fmax
  | .n4 p a b c d, O => ∃ Oa Ob Oc Od Pa Pb Pc Pd qp : Trace,
      Run rst x a Oa ∧ Run rst x b Ob ∧ Run rst x c Oc ∧ Run rst x d Od ∧
      WinDelay a.wmin a.wmax Oa Pa ∧ WinDelay b.wmin b.wmax Ob Pb ∧
      WinDelay c.wmin c.wmax Oc Pc ∧ WinDelay d.wmin d.wmax Od Pd ∧
      LoopG (fun t q => CTree.c4r (rst t) (Pa t) (Pb t) (Pc t) (Pd t) q) O qp
        p.lmin p.lmax p.fmin p.fmax

/-- Phase start of a sub-tree: the time its last leaf reached the phase value. -/
def cT (σ : Nat → Nat → Nat) : S → Nat → Nat
  | .leaf i _ _, k => σ i k
  | .n2 _ a b, k => lmx [cT σ a k, cT σ b k]
  | .n3 _ a b c, k => lmx [cT σ a k, cT σ b k, cT σ c k]
  | .n4 _ a b c d, k => lmx [cT σ a k, cT σ b k, cT σ c k, cT σ d k]

/-- **Upper latency**: max over leaf-to-node paths of the sum of LUT max delay
and wire max delay (the leaf's port wire included, the node's own output wire
not). -/
def Lmax : S → Nat
  | .leaf .. => 0
  | .n2 p a b => p.lmax + lmx [Lmax a + a.wmax, Lmax b + b.wmax]
  | .n3 p a b c => p.lmax + lmx [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax]
  | .n4 p a b c d =>
      p.lmax + lmx [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax, Lmax d + d.wmax]

/-- **Latest settle time** of a node in phase `k` (max-plus, from the leaf
switching times `σ i k`): `Late n = lmax n + max_j (Late j + wmax j)`. -/
def Late (σ : Nat → Nat → Nat) : S → Nat → Nat
  | .leaf i _ _, k => σ i k
  | .n2 p a b, k => p.lmax + lmx [Late σ a k + a.wmax, Late σ b k + b.wmax]
  | .n3 p a b c, k => p.lmax + lmx [Late σ a k + a.wmax, Late σ b k + b.wmax,
      Late σ c k + c.wmax]
  | .n4 p a b c d, k => p.lmax + lmx [Late σ a k + a.wmax, Late σ b k + b.wmax,
      Late σ c k + c.wmax, Late σ d k + d.wmax]

/-- **Earliest leave time** of a node in phase `k`: it cannot change to `V k`
before every input has, `Early n = lmin n + max_j (Early j + wmin j)`. -/
def Early (σ : Nat → Nat → Nat) : S → Nat → Nat
  | .leaf i _ _, k => σ i k
  | .n2 p a b, k => p.lmin + lmx [Early σ a k + a.wmin, Early σ b k + b.wmin]
  | .n3 p a b c, k => p.lmin + lmx [Early σ a k + a.wmin, Early σ b k + b.wmin,
      Early σ c k + c.wmin]
  | .n4 p a b c d, k => p.lmin + lmx [Early σ a k + a.wmin, Early σ b k + b.wmin,
      Early σ c k + c.wmin, Early σ d k + d.wmin]

/-- **Delay spread accumulated in a sub-tree** (static, Nat subtraction):
`Spread n = (lmax - lmin) + max_j (Spread j + (wmax j - wmin j))`. -/
def Spread : S → Nat
  | .leaf .. => 0
  | .n2 p a b => (p.lmax - p.lmin) + lmx [Spread a + (a.wmax - a.wmin),
      Spread b + (b.wmax - b.wmin)]
  | .n3 p a b c => (p.lmax - p.lmin) + lmx [Spread a + (a.wmax - a.wmin),
      Spread b + (b.wmax - b.wmin), Spread c + (c.wmax - c.wmin)]
  | .n4 p a b c d => (p.lmax - p.lmin) + lmx [Spread a + (a.wmax - a.wmin),
      Spread b + (b.wmax - b.wmin), Spread c + (c.wmax - c.wmin), Spread d + (d.wmax - d.wmin)]

/-- **Per-phase fork condition** with deadline `B` (the earliest instant any
leaf may leave `V k`): every node's feedback has settled by `B`:
`Late n k + fmax n ≤ B`. -/
def NodesOK (σ : Nat → Nat → Nat) (k B : Nat) : S → Prop
  | .leaf .. => True
  | .n2 p a b => Late σ (.n2 p a b) k + p.fmax ≤ B ∧ NodesOK σ k B a ∧ NodesOK σ k B b
  | .n3 p a b c => Late σ (.n3 p a b c) k + p.fmax ≤ B ∧ NodesOK σ k B a ∧
      NodesOK σ k B b ∧ NodesOK σ k B c
  | .n4 p a b c d => Late σ (.n4 p a b c d) k + p.fmax ≤ B ∧ NodesOK σ k B a ∧
      NodesOK σ k B b ∧ NodesOK σ k B c ∧ NodesOK σ k B d

/-- **Static (phase-independent) fork condition**, `D` = minimum delay from
this node's output to the root's output: for every node,
`Spread n + fmax n ≤ D n + E`. -/
def StaticOK (E : Nat) : Nat → S → Prop
  | _, .leaf .. => True
  | D, .n2 p a b => Spread (.n2 p a b) + p.fmax ≤ D + E ∧
      StaticOK E (D + p.lmin + a.wmin) a ∧ StaticOK E (D + p.lmin + b.wmin) b
  | D, .n3 p a b c => Spread (.n3 p a b c) + p.fmax ≤ D + E ∧
      StaticOK E (D + p.lmin + a.wmin) a ∧ StaticOK E (D + p.lmin + b.wmin) b ∧
      StaticOK E (D + p.lmin + c.wmin) c
  | D, .n4 p a b c d => Spread (.n4 p a b c d) + p.fmax ≤ D + E ∧
      StaticOK E (D + p.lmin + a.wmin) a ∧ StaticOK E (D + p.lmin + b.wmin) b ∧
      StaticOK E (D + p.lmin + c.wmin) c ∧ StaticOK E (D + p.lmin + d.wmin) d


theorem ge_cT (σ : Nat → Nat → Nat) (B k : Nat) :
    ∀ s : S, (∀ i ∈ leaves s, B ≤ σ i k) → B ≤ cT σ s k
  | .leaf i _ _, h => h i (by simp [leaves])
  | .n2 _ a b, h => by
      have := ge_cT σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := cT σ a k) (l := [cT σ a k, cT σ b k]) (by simp)
      simp only [cT]; omega
  | .n3 _ a b c, h => by
      have := ge_cT σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := cT σ a k) (l := [cT σ a k, cT σ b k, cT σ c k]) (by simp)
      simp only [cT]; omega
  | .n4 _ a b c d, h => by
      have := ge_cT σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := cT σ a k) (l := [cT σ a k, cT σ b k, cT σ c k, cT σ d k]) (by simp)
      simp only [cT]; omega

theorem ge_Late (σ : Nat → Nat → Nat) (B k : Nat) :
    ∀ s : S, (∀ i ∈ leaves s, B ≤ σ i k) → B ≤ Late σ s k
  | .leaf i _ _, h => h i (by simp [leaves])
  | .n2 _ a b, h => by
      have := ge_Late σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := Late σ a k + a.wmax) (l := [Late σ a k + a.wmax, Late σ b k + b.wmax])
        (by simp)
      simp only [Late]; omega
  | .n3 _ a b c, h => by
      have := ge_Late σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := Late σ a k + a.wmax) (l := [Late σ a k + a.wmax, Late σ b k + b.wmax,
        Late σ c k + c.wmax]) (by simp)
      simp only [Late]; omega
  | .n4 _ a b c d, h => by
      have := ge_Late σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := Late σ a k + a.wmax) (l := [Late σ a k + a.wmax, Late σ b k + b.wmax,
        Late σ c k + c.wmax, Late σ d k + d.wmax]) (by simp)
      simp only [Late]; omega

theorem ge_Early (σ : Nat → Nat → Nat) (B k : Nat) :
    ∀ s : S, (∀ i ∈ leaves s, B ≤ σ i k) → B ≤ Early σ s k
  | .leaf i _ _, h => h i (by simp [leaves])
  | .n2 _ a b, h => by
      have := ge_Early σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := Early σ a k + a.wmin)
        (l := [Early σ a k + a.wmin, Early σ b k + b.wmin]) (by simp)
      simp only [Early]; omega
  | .n3 _ a b c, h => by
      have := ge_Early σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := Early σ a k + a.wmin) (l := [Early σ a k + a.wmin,
        Early σ b k + b.wmin, Early σ c k + c.wmin]) (by simp)
      simp only [Early]; omega
  | .n4 _ a b c d, h => by
      have := ge_Early σ B k a (fun i hi => h i (by simp [leaves, hi]))
      have := le_lmx (x := Early σ a k + a.wmin) (l := [Early σ a k + a.wmin,
        Early σ b k + b.wmin, Early σ c k + c.wmin, Early σ d k + d.wmin]) (by simp)
      simp only [Early]; omega

/-- Minimum delay over all leaf-to-node paths (sum of `lmin + wmin`). -/
def MinD : S → Nat
  | .leaf .. => 0
  | .n2 p a b => p.lmin + min (MinD a + a.wmin) (MinD b + b.wmin)
  | .n3 p a b c => p.lmin + min (MinD a + a.wmin) (min (MinD b + b.wmin) (MinD c + c.wmin))
  | .n4 p a b c d => p.lmin + min (MinD a + a.wmin) (min (MinD b + b.wmin)
      (min (MinD c + c.wmin) (MinD d + d.wmin)))

/-- **Hold bound**: a node cannot reach the new phase value before the last
leaf arrival plus the minimum path delay. -/
theorem Early_ge (σ : Nat → Nat → Nat) (k : Nat) : ∀ s : S, cT σ s k + MinD s ≤ Early σ s k
  | .leaf .. => by simp [Early, cT, MinD]
  | .n2 p a b => by
      have ha := Early_ge σ k a; have hb := Early_ge σ k b
      simp only [Early, cT, MinD, lmx, List.foldr]; omega
  | .n3 p a b c => by
      have ha := Early_ge σ k a; have hb := Early_ge σ k b; have hc := Early_ge σ k c
      simp only [Early, cT, MinD, lmx, List.foldr]; omega
  | .n4 p a b c d => by
      have ha := Early_ge σ k a; have hb := Early_ge σ k b; have hc := Early_ge σ k c
      have hd := Early_ge σ k d
      simp only [Early, cT, MinD, lmx, List.foldr]; omega

/-- **Bundling bound**: the latest settle time is at most the last leaf
arrival plus the static upper latency `Lmax` (max over paths of
`sum (lmax + wmax)`). -/
theorem Late_le (σ : Nat → Nat → Nat) (k : Nat) : ∀ s : S, Late σ s k ≤ cT σ s k + Lmax s
  | .leaf .. => by simp [Late, cT, Lmax]
  | .n2 p a b => by
      have ha := Late_le σ k a; have hb := Late_le σ k b
      have h1 := le_lmx (x := cT σ a k) (l := [cT σ a k, cT σ b k]) (by simp)
      have h2 := le_lmx (x := cT σ b k) (l := [cT σ a k, cT σ b k]) (by simp)
      have h3 := le_lmx (x := Lmax a + a.wmax) (l := [Lmax a + a.wmax, Lmax b + b.wmax]) (by simp)
      have h4 := le_lmx (x := Lmax b + b.wmax) (l := [Lmax a + a.wmax, Lmax b + b.wmax]) (by simp)
      have : lmx [Late σ a k + a.wmax, Late σ b k + b.wmax] ≤
          lmx [cT σ a k, cT σ b k] + lmx [Lmax a + a.wmax, Lmax b + b.wmax] := by
        apply lmx_le; intro x hx; simp at hx; omega
      simp only [Late, cT, Lmax]; omega
  | .n3 p a b c => by
      have ha := Late_le σ k a; have hb := Late_le σ k b; have hc := Late_le σ k c
      have : lmx [Late σ a k + a.wmax, Late σ b k + b.wmax, Late σ c k + c.wmax] ≤
          lmx [cT σ a k, cT σ b k, cT σ c k] +
            lmx [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax] := by
        apply lmx_le; intro x hx; simp at hx
        have h1 := le_lmx (x := cT σ a k) (l := [cT σ a k, cT σ b k, cT σ c k]) (by simp)
        have h2 := le_lmx (x := cT σ b k) (l := [cT σ a k, cT σ b k, cT σ c k]) (by simp)
        have h3 := le_lmx (x := cT σ c k) (l := [cT σ a k, cT σ b k, cT σ c k]) (by simp)
        have g1 := le_lmx (x := Lmax a + a.wmax)
          (l := [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax]) (by simp)
        have g2 := le_lmx (x := Lmax b + b.wmax)
          (l := [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax]) (by simp)
        have g3 := le_lmx (x := Lmax c + c.wmax)
          (l := [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax]) (by simp)
        omega
      simp only [Late, cT, Lmax]; omega
  | .n4 p a b c d => by
      have ha := Late_le σ k a; have hb := Late_le σ k b; have hc := Late_le σ k c
      have hd := Late_le σ k d
      have : lmx [Late σ a k + a.wmax, Late σ b k + b.wmax, Late σ c k + c.wmax,
            Late σ d k + d.wmax] ≤
          lmx [cT σ a k, cT σ b k, cT σ c k, cT σ d k] +
            lmx [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax, Lmax d + d.wmax] := by
        apply lmx_le; intro x hx; simp at hx
        have h1 := le_lmx (x := cT σ a k) (l := [cT σ a k, cT σ b k, cT σ c k, cT σ d k]) (by simp)
        have h2 := le_lmx (x := cT σ b k) (l := [cT σ a k, cT σ b k, cT σ c k, cT σ d k]) (by simp)
        have h3 := le_lmx (x := cT σ c k) (l := [cT σ a k, cT σ b k, cT σ c k, cT σ d k]) (by simp)
        have h4 := le_lmx (x := cT σ d k) (l := [cT σ a k, cT σ b k, cT σ c k, cT σ d k]) (by simp)
        have g1 := le_lmx (x := Lmax a + a.wmax)
          (l := [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax, Lmax d + d.wmax]) (by simp)
        have g2 := le_lmx (x := Lmax b + b.wmax)
          (l := [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax, Lmax d + d.wmax]) (by simp)
        have g3 := le_lmx (x := Lmax c + c.wmax)
          (l := [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax, Lmax d + d.wmax]) (by simp)
        have g4 := le_lmx (x := Lmax d + d.wmax)
          (l := [Lmax a + a.wmax, Lmax b + b.wmax, Lmax c + c.wmax, Lmax d + d.wmax]) (by simp)
        omega
      simp only [Late, cT, Lmax]; omega

/-- **Spread bound**: `Late n k ≤ Early n k + Spread n` for every phase. -/
theorem Late_le_Early (σ : Nat → Nat → Nat) (k : Nat) :
    ∀ s : S, Late σ s k ≤ Early σ s k + Spread s
  | .leaf .. => by simp [Late, Early, Spread]
  | .n2 p a b => by
      have ha := Late_le_Early σ k a; have hb := Late_le_Early σ k b
      have : lmx [Late σ a k + a.wmax, Late σ b k + b.wmax] ≤
          lmx [Early σ a k + a.wmin, Early σ b k + b.wmin] +
            lmx [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin)] := by
        apply lmx_le; intro x hx; simp at hx
        have h1 := le_lmx (x := Early σ a k + a.wmin)
          (l := [Early σ a k + a.wmin, Early σ b k + b.wmin]) (by simp)
        have h2 := le_lmx (x := Early σ b k + b.wmin)
          (l := [Early σ a k + a.wmin, Early σ b k + b.wmin]) (by simp)
        have g1 := le_lmx (x := Spread a + (a.wmax - a.wmin))
          (l := [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin)]) (by simp)
        have g2 := le_lmx (x := Spread b + (b.wmax - b.wmin))
          (l := [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin)]) (by simp)
        omega
      simp only [Late, Early, Spread]; omega
  | .n3 p a b c => by
      have ha := Late_le_Early σ k a; have hb := Late_le_Early σ k b
      have hc := Late_le_Early σ k c
      have : lmx [Late σ a k + a.wmax, Late σ b k + b.wmax, Late σ c k + c.wmax] ≤
          lmx [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin] +
            lmx [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin),
              Spread c + (c.wmax - c.wmin)] := by
        apply lmx_le; intro x hx; simp at hx
        have h1 := le_lmx (x := Early σ a k + a.wmin)
          (l := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin]) (by simp)
        have h2 := le_lmx (x := Early σ b k + b.wmin)
          (l := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin]) (by simp)
        have h3 := le_lmx (x := Early σ c k + c.wmin)
          (l := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin]) (by simp)
        have g1 := le_lmx (x := Spread a + (a.wmax - a.wmin))
          (l := [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin),
            Spread c + (c.wmax - c.wmin)]) (by simp)
        have g2 := le_lmx (x := Spread b + (b.wmax - b.wmin))
          (l := [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin),
            Spread c + (c.wmax - c.wmin)]) (by simp)
        have g3 := le_lmx (x := Spread c + (c.wmax - c.wmin))
          (l := [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin),
            Spread c + (c.wmax - c.wmin)]) (by simp)
        omega
      simp only [Late, Early, Spread]; omega
  | .n4 p a b c d => by
      have ha := Late_le_Early σ k a; have hb := Late_le_Early σ k b
      have hc := Late_le_Early σ k c; have hd := Late_le_Early σ k d
      let le := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin,
        Early σ d k + d.wmin]
      let ls := [Spread a + (a.wmax - a.wmin), Spread b + (b.wmax - b.wmin),
        Spread c + (c.wmax - c.wmin), Spread d + (d.wmax - d.wmin)]
      have : lmx [Late σ a k + a.wmax, Late σ b k + b.wmax, Late σ c k + c.wmax,
          Late σ d k + d.wmax] ≤ lmx le + lmx ls := by
        apply lmx_le; intro x hx; simp at hx
        have h1 := le_lmx (x := Early σ a k + a.wmin) (l := le) (by simp [le])
        have h2 := le_lmx (x := Early σ b k + b.wmin) (l := le) (by simp [le])
        have h3 := le_lmx (x := Early σ c k + c.wmin) (l := le) (by simp [le])
        have h4 := le_lmx (x := Early σ d k + d.wmin) (l := le) (by simp [le])
        have g1 := le_lmx (x := Spread a + (a.wmax - a.wmin)) (l := ls) (by simp [ls])
        have g2 := le_lmx (x := Spread b + (b.wmax - b.wmin)) (l := ls) (by simp [ls])
        have g3 := le_lmx (x := Spread c + (c.wmax - c.wmin)) (l := ls) (by simp [ls])
        have g4 := le_lmx (x := Spread d + (d.wmax - d.wmin)) (l := ls) (by simp [ls])
        omega
      simp only [le, ls] at this
      simp only [Late, Early, Spread]; omega

/-- The static condition implies the per-phase one: if `Early n k + D ≤ Y`
(`D` = min delay from `n` to the root, so `Y` can be the root's `Early`), then
every node's feedback settles by `Y + E`. -/
theorem static_ok (σ : Nat → Nat → Nat) (k E : Nat) :
    ∀ (s : S) (D Y : Nat), StaticOK E D s → Early σ s k + D ≤ Y → NodesOK σ k (Y + E) s
  | .leaf .., _, _, _, _ => trivial
  | .n2 p a b, D, Y, h, hy => by
      have hs := Late_le_Early σ k (.n2 p a b)
      have h1 := le_lmx (x := Early σ a k + a.wmin)
        (l := [Early σ a k + a.wmin, Early σ b k + b.wmin]) (by simp)
      have h2 := le_lmx (x := Early σ b k + b.wmin)
        (l := [Early σ a k + a.wmin, Early σ b k + b.wmin]) (by simp)
      simp only [Early] at hy hs
      refine ⟨by have := h.1; omega, static_ok σ k E a _ Y h.2.1 (by omega),
        static_ok σ k E b _ Y h.2.2 (by omega)⟩
  | .n3 p a b c, D, Y, h, hy => by
      have hs := Late_le_Early σ k (.n3 p a b c)
      have h1 := le_lmx (x := Early σ a k + a.wmin)
        (l := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin]) (by simp)
      have h2 := le_lmx (x := Early σ b k + b.wmin)
        (l := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin]) (by simp)
      have h3 := le_lmx (x := Early σ c k + c.wmin)
        (l := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin]) (by simp)
      simp only [Early] at hy hs
      refine ⟨by have := h.1; omega, static_ok σ k E a _ Y h.2.1 (by omega),
        static_ok σ k E b _ Y h.2.2.1 (by omega), static_ok σ k E c _ Y h.2.2.2 (by omega)⟩
  | .n4 p a b c d, D, Y, h, hy => by
      have hs := Late_le_Early σ k (.n4 p a b c d)
      let le := [Early σ a k + a.wmin, Early σ b k + b.wmin, Early σ c k + c.wmin,
        Early σ d k + d.wmin]
      have h1 := le_lmx (x := Early σ a k + a.wmin) (l := le) (by simp [le])
      have h2 := le_lmx (x := Early σ b k + b.wmin) (l := le) (by simp [le])
      have h3 := le_lmx (x := Early σ c k + c.wmin) (l := le) (by simp [le])
      have h4 := le_lmx (x := Early σ d k + d.wmin) (l := le) (by simp [le])
      simp only [le] at h1 h2 h3 h4
      simp only [Early] at hy hs
      refine ⟨by have := h.1; omega, static_ok σ k E a _ Y h.2.1 (by omega),
        static_ok σ k E b _ Y h.2.2.1 (by omega), static_ok σ k E c _ Y h.2.2.2.1 (by omega),
        static_ok σ k E d _ Y h.2.2.2.2 (by omega)⟩

/-- Hypotheses of one phase `k`, for a sub-tree. `B` is the earliest instant
any leaf may leave `V k`. -/
structure PhaseHyp (σ : Nat → Nat → Nat) (V : Nat → Bool) (k : Nat) (x : Nat → Trace)
    (rst : Trace) (B T0 : Nat) (s : S) : Prop where
  leaf : ∀ i ∈ leaves s, ∀ t, σ i k ≤ t → t < σ i (k + 1) → x i t = V k
  next : ∀ i ∈ leaves s, B ≤ σ i (k + 1)
  ok : NodesOK σ k B s
  t0 : ∀ i ∈ leaves s, T0 ≤ σ i k
  norst : ∀ t, T0 ≤ t → rst t = false

theorem PhaseHyp.sub {σ V k x rst B T0 s s'} (h : PhaseHyp σ V k x rst B T0 s)
    (hl : ∀ i, i ∈ leaves s' → i ∈ leaves s) (hok : NodesOK σ k B s') :
    PhaseHyp σ V k x rst B T0 s' :=
  ⟨fun i hi => h.leaf i (hl i hi), fun i hi => h.next i (hl i hi), hok,
    fun i hi => h.t0 i (hl i hi), h.norst⟩

/-- The child pin record: pin `P` of child `s` is `V k` on
`[Late s k + wmax, Early s (k+1) + wmin)`. -/
def chOf (σ : Nat → Nat → Nat) (k : Nat) (s : S) (P : Trace) : Ch :=
  ⟨P, Late σ s k + s.wmax, Early σ s (k + 1) + s.wmin⟩

theorem child_pin {σ : Nat → Nat → Nat} {k : Nat} {V : Bool} {s : S} {O P : Trace}
    (hO : ∀ t, Late σ s k ≤ t → t < Early σ s (k + 1) → O t = V)
    (w : WinDelay s.wmin s.wmax O P) :
    ∀ t, (chOf σ k s P).lo ≤ t → t < (chOf σ k s P).hi → (chOf σ k s P).P t = V := by
  intro t h1 h2
  simp only [chOf] at h1 h2 ⊢
  exact win_claim w V _ _ hO t h1 h2

/-- **The tree in one phase** (exact max-plus windows). Every node of a tree
satisfying `Run` drives `V k` on `[Late s k, Early s (k+1))`, provided the
leaves switch cleanly, no leaf leaves `V k` before `B`, and every node's
feedback has settled by `B` (`NodesOK`). -/
theorem tree_phase (σ : Nat → Nat → Nat) (V : Nat → Bool) (k : Nat) (x : Nat → Trace)
    (rst : Trace) (B T0 : Nat) :
    ∀ (s : S) (O : Trace), Run rst x s O → PhaseHyp σ V k x rst B T0 s →
      ∀ t, Late σ s k ≤ t → t < Early σ s (k + 1) → O t = V k
  | .leaf i _ _, O, hr, H => by
      intro t h1 h2
      simp only [Run] at hr; subst hr
      simp only [Late, Early] at h1 h2
      exact H.leaf i (by simp [leaves]) t h1 h2
  | .n2 p a b, O, hr, H => by
      obtain ⟨Oa, Ob, Pa, Pb, qp, ra, rb, wa, wb, L⟩ := hr
      have ia := tree_phase σ V k x rst B T0 a Oa ra
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.1)
      have ib := tree_phase σ V k x rst B T0 b Ob rb
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.2)
      let cs : List Ch := [chOf σ k a Pa, chOf σ k b Pb]
      have L' : LoopG (ceF rst (fun t => cs.map (fun ch => ch.P t))) O qp
          p.lmin p.lmax p.fmin p.fmax := by
        have hF : (fun t q => CTree.c2r (rst t) (Pa t) (Pb t) q) =
            ceF rst (fun t => cs.map (fun ch => ch.P t)) := by
          funext t q; exact c2r_ce _ _ _ _
        rw [← hF]; exact L
      have e0 : p.lmax + lmx (cs.map Ch.lo) = Late σ (.n2 p a b) k := rfl
      have e1 : p.lmin + lmx (cs.map Ch.hi) = Early σ (.n2 p a b) (k + 1) := rfl
      have hok := H.ok.1
      have g1 : Late σ a k + a.wmax ≤ lmx (cs.map Ch.lo) := le_lmx (by simp [cs, chOf])
      have t1 := ge_Late σ T0 k a (fun i hi => H.t0 i (by simp [leaves, hi]))
      have hE : ∀ s', (∀ i, i ∈ leaves s' → i ∈ leaves (.n2 p a b)) →
          B ≤ Early σ s' (k + 1) :=
        fun s' hs' => ge_Early σ B (k + 1) s' (fun i hi => H.next i (hs' i hi))
      have := node_step cs (by simp [cs]) (V k) L'
        (by
          intro ch hch
          simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hch
          rcases hch with rfl | rfl
          · exact child_pin ia wa
          · exact child_pin ib wb)
        (by
          intro ch hch
          simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hch
          rcases hch with rfl | rfl
          · have := hE a (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega
          · have := hE b (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega)
        (fun t ht => H.norst t (by omega))
      intro t h1 h2
      exact this t (by omega) (by omega)
  | .n3 p a b c, O, hr, H => by
      obtain ⟨Oa, Ob, Oc, Pa, Pb, Pc, qp, ra, rb, rc, wa, wb, wc, L⟩ := hr
      have ia := tree_phase σ V k x rst B T0 a Oa ra
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.1)
      have ib := tree_phase σ V k x rst B T0 b Ob rb
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.2.1)
      have ic := tree_phase σ V k x rst B T0 c Oc rc
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.2.2)
      let cs : List Ch := [chOf σ k a Pa, chOf σ k b Pb, chOf σ k c Pc]
      have L' : LoopG (ceF rst (fun t => cs.map (fun ch => ch.P t))) O qp
          p.lmin p.lmax p.fmin p.fmax := by
        have hF : (fun t q => CTree.c3r (rst t) (Pa t) (Pb t) (Pc t) q) =
            ceF rst (fun t => cs.map (fun ch => ch.P t)) := by
          funext t q; exact c3r_ce _ _ _ _ _
        rw [← hF]; exact L
      have e0 : p.lmax + lmx (cs.map Ch.lo) = Late σ (.n3 p a b c) k := rfl
      have e1 : p.lmin + lmx (cs.map Ch.hi) = Early σ (.n3 p a b c) (k + 1) := rfl
      have hok := H.ok.1
      have g1 : Late σ a k + a.wmax ≤ lmx (cs.map Ch.lo) := le_lmx (by simp [cs, chOf])
      have t1 := ge_Late σ T0 k a (fun i hi => H.t0 i (by simp [leaves, hi]))
      have hE : ∀ s', (∀ i, i ∈ leaves s' → i ∈ leaves (.n3 p a b c)) →
          B ≤ Early σ s' (k + 1) :=
        fun s' hs' => ge_Early σ B (k + 1) s' (fun i hi => H.next i (hs' i hi))
      have := node_step cs (by simp [cs]) (V k) L'
        (by
          intro ch hch
          simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hch
          rcases hch with rfl | rfl | rfl
          · exact child_pin ia wa
          · exact child_pin ib wb
          · exact child_pin ic wc)
        (by
          intro ch hch
          simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hch
          rcases hch with rfl | rfl | rfl
          · have := hE a (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega
          · have := hE b (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega
          · have := hE c (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega)
        (fun t ht => H.norst t (by omega))
      intro t h1 h2
      exact this t (by omega) (by omega)
  | .n4 p a b c d, O, hr, H => by
      obtain ⟨Oa, Ob, Oc, Od, Pa, Pb, Pc, Pd, qp, ra, rb, rc, rd, wa, wb, wc, wd, L⟩ := hr
      have ia := tree_phase σ V k x rst B T0 a Oa ra
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.1)
      have ib := tree_phase σ V k x rst B T0 b Ob rb
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.2.1)
      have ic := tree_phase σ V k x rst B T0 c Oc rc
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.2.2.1)
      have id := tree_phase σ V k x rst B T0 d Od rd
        (H.sub (fun i hi => by simp [leaves, hi]) H.ok.2.2.2.2)
      let cs : List Ch := [chOf σ k a Pa, chOf σ k b Pb, chOf σ k c Pc, chOf σ k d Pd]
      have L' : LoopG (ceF rst (fun t => cs.map (fun ch => ch.P t))) O qp
          p.lmin p.lmax p.fmin p.fmax := by
        have hF : (fun t q => CTree.c4r (rst t) (Pa t) (Pb t) (Pc t) (Pd t) q) =
            ceF rst (fun t => cs.map (fun ch => ch.P t)) := by
          funext t q; exact c4r_ce _ _ _ _ _ _
        rw [← hF]; exact L
      have e0 : p.lmax + lmx (cs.map Ch.lo) = Late σ (.n4 p a b c d) k := rfl
      have e1 : p.lmin + lmx (cs.map Ch.hi) = Early σ (.n4 p a b c d) (k + 1) := rfl
      have hok := H.ok.1
      have g1 : Late σ a k + a.wmax ≤ lmx (cs.map Ch.lo) := le_lmx (by simp [cs, chOf])
      have t1 := ge_Late σ T0 k a (fun i hi => H.t0 i (by simp [leaves, hi]))
      have hE : ∀ s', (∀ i, i ∈ leaves s' → i ∈ leaves (.n4 p a b c d)) →
          B ≤ Early σ s' (k + 1) :=
        fun s' hs' => ge_Early σ B (k + 1) s' (fun i hi => H.next i (hs' i hi))
      have := node_step cs (by simp [cs]) (V k) L'
        (by
          intro ch hch
          simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hch
          rcases hch with rfl | rfl | rfl | rfl
          · exact child_pin ia wa
          · exact child_pin ib wb
          · exact child_pin ic wc
          · exact child_pin id wd)
        (by
          intro ch hch
          simp only [cs, List.mem_cons, List.not_mem_nil, or_false] at hch
          rcases hch with rfl | rfl | rfl | rfl
          · have := hE a (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega
          · have := hE b (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega
          · have := hE c (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega
          · have := hE d (fun i hi => by simp [leaves, hi]); simp only [chOf]; omega)
        (fun t ht => H.norst t (by omega))
      intro t h1 h2
      exact this t (by omega) (by omega)

/-- Helper for the phase turn: the root has settled before the next phase
starts. -/
theorem late_le_next (σ : Nat → Nat → Nat) (k B : Nat) (s : S) (hok : NodesOK σ k B s)
    (hB : ∀ i ∈ leaves s, B ≤ σ i (k + 1)) (hmono : ∀ i ∈ leaves s, σ i k ≤ σ i (k + 1)) :
    Late σ s k ≤ cT σ s (k + 1) := by
  have hc := ge_cT σ B (k + 1) s hB
  cases s with
  | leaf i _ _ => exact hmono i (by simp [leaves])
  | n2 p a b => have := hok.1; omega
  | n3 p a b c => have := hok.1; omega
  | n4 p a b c d => have := hok.1; omega

/-- **The timed tree implements the C-element over all phases.**
Environment hypotheses (all named):
* `H_ALT`: phase targets alternate.
* `H_LEAF` (clean four-phase leaves, at the tree ports): leaf `i` equals
  `V k` on `[σ i k, σ i (k+1))`.
* `H_LEAF_MONO`: `σ i k ≤ σ i (k+1)`.
* `H_ACK` (four-phase ack wait): for every leaf and phase there is a `u ≥ c k`
  with `O u = V k` (the environment saw the root's ack) and
  `u + E ≤ σ i (k+1)`.
* `H_ENV_LATENCY` (per-phase lifted fork condition): every node's feedback
  has settled by `Early s k + E`: `Late n k + fmax n ≤ Early root k + E`.
  `tree_four_phase_static` replaces it by a static condition.
* `H_NORST`, `H_START`: `rst = 0` from `T0`, `T0 ≤ σ i 0`.
* `H_RESET_DONE`: the root reads `!V 0` on `[c 0, Early s 0)` (cleared by
  `ce_reset` at the root). No reset assumption on internal nodes is needed:
  they are forced by their inputs (`exc_heldG` is state-free).
Conclusion: the root drives `V k` on `[Late s k, Early s (k+1))` for every
`k`. -/
theorem tree_four_phase (s : S) (rst : Trace) (x : Nat → Trace) (O : Trace)
    (R : Run rst x s O) (σ : Nat → Nat → Nat) (V : Nat → Bool) (E T0 : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_LEAF : ∀ i ∈ leaves s, ∀ k t, σ i k ≤ t → t < σ i (k + 1) → x i t = V k)
    (H_LEAF_MONO : ∀ i ∈ leaves s, ∀ k, σ i k ≤ σ i (k + 1))
    (H_ACK : ∀ i ∈ leaves s, ∀ k, ∃ u, cT σ s k ≤ u ∧ u + E ≤ σ i (k + 1) ∧ O u = V k)
    (H_ENV_LATENCY : ∀ k, NodesOK σ k (Early σ s k + E) s)
    (H_NORST : ∀ t, T0 ≤ t → rst t = false)
    (H_START : ∀ i ∈ leaves s, T0 ≤ σ i 0)
    (H_RESET_DONE : ∀ u, cT σ s 0 ≤ u → u < Early σ s 0 → O u = !V 0) :
    ∀ k t, Late σ s k ≤ t → t < Early σ s (k + 1) → O t = V k := by
  have ht0 : ∀ i ∈ leaves s, ∀ k, T0 ≤ σ i k := by
    intro i hi k
    induction k with
    | zero => exact H_START i hi
    | succ k ih => have := H_LEAF_MONO i hi k; omega
  have step : ∀ k, (∀ u, cT σ s k ≤ u → u < Early σ s k → O u = !V k) →
      (∀ t, Late σ s k ≤ t → t < Early σ s (k + 1) → O t = V k) ∧
      Late σ s k ≤ cT σ s (k + 1) := by
    intro k Rk
    have hnext : ∀ i ∈ leaves s, Early σ s k + E ≤ σ i (k + 1) := by
      intro i hi
      obtain ⟨u, hu1, hu2, hu3⟩ := H_ACK i hi k
      by_cases hlt : u < Early σ s k
      · have := Rk u hu1 hlt
        rw [hu3] at this; cases hv : V k <;> simp [hv] at this
      · omega
    exact ⟨tree_phase σ V k x rst (Early σ s k + E) T0 s O R
      ⟨fun i hi => H_LEAF i hi k, hnext, H_ENV_LATENCY k, fun i hi => ht0 i hi k, H_NORST⟩,
      late_le_next σ k _ s (H_ENV_LATENCY k) hnext (fun i hi => H_LEAF_MONO i hi k)⟩
  have Rk : ∀ k, ∀ u, cT σ s k ≤ u → u < Early σ s k → O u = !V k := by
    intro k
    induction k with
    | zero => exact H_RESET_DONE
    | succ k ih =>
      intro u h1 h2
      have ⟨hO, hgap⟩ := step k ih
      rw [H_ALT k, Bool.not_not]
      exact hO u (by omega) h2
  intro k
  exact (step k (Rk k)).1

/-- **Static version**: `H_ENV_STATIC : StaticOK E 0 s`, i.e. for every node
`n`, `Spread n + fmax n ≤ dist_min(n -> root) + E` (`Spread` = accumulated
`(lmax - lmin) + (wmax - wmin)` along the worst path below `n`). This is the
per-node fork condition of 5b lifted to the tree. -/
theorem tree_four_phase_static (s : S) (rst : Trace) (x : Nat → Trace) (O : Trace)
    (R : Run rst x s O) (σ : Nat → Nat → Nat) (V : Nat → Bool) (E T0 : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_LEAF : ∀ i ∈ leaves s, ∀ k t, σ i k ≤ t → t < σ i (k + 1) → x i t = V k)
    (H_LEAF_MONO : ∀ i ∈ leaves s, ∀ k, σ i k ≤ σ i (k + 1))
    (H_ACK : ∀ i ∈ leaves s, ∀ k, ∃ u, cT σ s k ≤ u ∧ u + E ≤ σ i (k + 1) ∧ O u = V k)
    (H_ENV_STATIC : StaticOK E 0 s)
    (H_NORST : ∀ t, T0 ≤ t → rst t = false)
    (H_START : ∀ i ∈ leaves s, T0 ≤ σ i 0)
    (H_RESET_DONE : ∀ u, cT σ s 0 ≤ u → u < Early σ s 0 → O u = !V 0) :
    ∀ k t, cT σ s k + Lmax s ≤ t → t < Early σ s (k + 1) → O t = V k := by
  intro k t h1 h2
  have := Late_le σ k s
  exact tree_four_phase s rst x O R σ V E T0 H_ALT H_LEAF H_LEAF_MONO H_ACK
    (fun k => static_ok σ k E s 0 _ H_ENV_STATIC (by omega)) H_NORST H_START H_RESET_DONE
    k t (by omega) h2


/-! ## 5. Depth, and the generate-block instances N = 5 and N = 8 -/

/-- Uniform delay classes: every LUT `[lmin, lmax]`, every feedback wire
`[fmin, fmax]`, every inter-cell wire `[wmin, wmax]`, every port wire
`[imin, imax]`. -/
structure U where
  lmin : Nat
  lmax : Nat
  fmin : Nat
  fmax : Nat
  wmin : Nat
  wmax : Nat
  imin : Nat
  imax : Nat

def U.nd (u : U) : ND := ⟨u.lmin, u.lmax, u.fmin, u.fmax, u.wmin, u.wmax⟩

/-- 5c's tree term (`CTree.T`, the generate block's shape) with uniform
delays. A 5c `wire` node is absorbed: every edge already has a wire window. -/
def ofT (u : U) : CTree.T → S
  | .leaf i => .leaf i u.imin u.imax
  | .wire _ c => ofT u c
  | .n2 _ a b => .n2 u.nd (ofT u a) (ofT u b)
  | .n3 _ a b c => .n3 u.nd (ofT u a) (ofT u b) (ofT u c)
  | .n4 _ a b c d => .n4 u.nd (ofT u a) (ofT u b) (ofT u c) (ofT u d)

/-- Cell depth of a 5c tree (a leaf is 0). -/
def depth : CTree.T → Nat
  | .leaf _ => 0
  | .wire _ c => depth c
  | .n2 _ a b => 1 + max (depth a) (depth b)
  | .n3 _ a b c => 1 + max (depth a) (max (depth b) (depth c))
  | .n4 _ a b c d => 1 + max (depth a) (max (depth b) (max (depth c) (depth d)))

theorem ofT_wmax (u : U) : ∀ t : CTree.T, (ofT u t).wmax = u.imax ∨ (ofT u t).wmax = u.wmax
  | .leaf _ => Or.inl rfl
  | .wire _ c => ofT_wmax u c
  | .n2 .. => Or.inr rfl
  | .n3 .. => Or.inr rfl
  | .n4 .. => Or.inr rfl

/-- **Depth bound.** With uniform delays, every tree (any shape built from
5c's terms, in particular every `CTree.gen n`) has
`Lmax + (its own output wire max) ≤ depth * (lmax + wmax) + imax`; for a
cell-rooted tree that is `Lmax ≤ depth * lmax + (depth - 1) * wmax + imax`. -/
theorem Lmax_depth (u : U) :
    ∀ t : CTree.T, Lmax (ofT u t) + (ofT u t).wmax ≤ depth t * (u.lmax + u.wmax) + u.imax
  | .leaf _ => by simp [ofT, Lmax, S.wmax, depth]
  | .wire _ c => Lmax_depth u c
  | .n2 _ a b => by
      have ha := Lmax_depth u a; have hb := Lmax_depth u b
      have ma := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth a ≤ max (depth a) (depth b) by omega)
      have mb := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth b ≤ max (depth a) (depth b) by omega)
      have e : (1 + max (depth a) (depth b)) * (u.lmax + u.wmax) =
          (u.lmax + u.wmax) + max (depth a) (depth b) * (u.lmax + u.wmax) := by
        rw [Nat.add_mul, Nat.one_mul]
      show u.lmax + lmx [Lmax (ofT u a) + (ofT u a).wmax, Lmax (ofT u b) + (ofT u b).wmax]
        + u.wmax ≤ (1 + max (depth a) (depth b)) * (u.lmax + u.wmax) + u.imax
      simp only [lmx, List.foldr]
      omega
  | .n3 _ a b c => by
      have ha := Lmax_depth u a; have hb := Lmax_depth u b; have hc := Lmax_depth u c
      have ma := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth a ≤ max (depth a) (max (depth b) (depth c)) by omega)
      have mb := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth b ≤ max (depth a) (max (depth b) (depth c)) by omega)
      have mc := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth c ≤ max (depth a) (max (depth b) (depth c)) by omega)
      have e : (1 + max (depth a) (max (depth b) (depth c))) * (u.lmax + u.wmax) =
          (u.lmax + u.wmax) + max (depth a) (max (depth b) (depth c)) * (u.lmax + u.wmax) := by
        rw [Nat.add_mul, Nat.one_mul]
      show u.lmax + lmx [Lmax (ofT u a) + (ofT u a).wmax, Lmax (ofT u b) + (ofT u b).wmax,
          Lmax (ofT u c) + (ofT u c).wmax]
        + u.wmax ≤ (1 + max (depth a) (max (depth b) (depth c))) * (u.lmax + u.wmax) + u.imax
      simp only [lmx, List.foldr]
      omega
  | .n4 _ a b c d => by
      have ha := Lmax_depth u a; have hb := Lmax_depth u b; have hc := Lmax_depth u c
      have hd := Lmax_depth u d
      have ma := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth a ≤ max (depth a) (max (depth b) (max (depth c) (depth d))) by omega)
      have mb := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth b ≤ max (depth a) (max (depth b) (max (depth c) (depth d))) by omega)
      have mc := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth c ≤ max (depth a) (max (depth b) (max (depth c) (depth d))) by omega)
      have md := Nat.mul_le_mul_right (u.lmax + u.wmax)
        (show depth d ≤ max (depth a) (max (depth b) (max (depth c) (depth d))) by omega)
      have e : (1 + max (depth a) (max (depth b) (max (depth c) (depth d)))) * (u.lmax + u.wmax) =
          (u.lmax + u.wmax) +
            max (depth a) (max (depth b) (max (depth c) (depth d))) * (u.lmax + u.wmax) := by
        rw [Nat.add_mul, Nat.one_mul]
      show u.lmax + lmx [Lmax (ofT u a) + (ofT u a).wmax, Lmax (ofT u b) + (ofT u b).wmax,
          Lmax (ofT u c) + (ofT u c).wmax, Lmax (ofT u d) + (ofT u d).wmax]
        + u.wmax ≤ (1 + max (depth a) (max (depth b) (max (depth c) (depth d)))) *
          (u.lmax + u.wmax) + u.imax
      simp only [lmx, List.foldr]
      omega

/-- The generate block's N = 5 tree, `C2(C4(a0..a3), a4)`: depth 2,
`Lmax = 2 lmax + wmax + imax` (critical path a0..a3 -> C4 -> wire -> C2). -/
theorem gen5_lat (u : U) :
    depth (CTree.gen 5) = 2 ∧
    Lmax (ofT u (CTree.gen 5)) = 2 * u.lmax + u.wmax + u.imax ∧
    leaves (ofT u (CTree.gen 5)) = [0, 1, 2, 3, 4] := by
  rw [CTree.gen5]
  simp only [CTree.t5, ofT, depth, Lmax, leaves, lmx, List.foldr, S.wmax, U.nd]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl | omega

/-- N = 5: the root cannot move before `lmin + imin` after the last leaf. -/
theorem gen5_early (u : U) (σ : Nat → Nat → Nat) (k : Nat) :
    cT σ (ofT u (CTree.gen 5)) k + (u.lmin + u.imin) ≤ Early σ (ofT u (CTree.gen 5)) k := by
  have h := Early_ge σ k (ofT u (CTree.gen 5))
  have e : MinD (ofT u (CTree.gen 5)) = u.lmin + u.imin := by
    rw [CTree.gen5]; simp only [CTree.t5, ofT, MinD, S.wmin, U.nd]; omega
  omega

/-- N = 5 static environment condition: it suffices that
`fmax + 2 (lmax - lmin) + (wmax - wmin) + (imax - imin) ≤ E` (the root's
condition; the C4's is implied). -/
theorem gen5_static (u : U) (E : Nat)
    (h : u.fmax + 2 * (u.lmax - u.lmin) + (u.wmax - u.wmin) + (u.imax - u.imin) ≤ E) :
    StaticOK E 0 (ofT u (CTree.gen 5)) := by
  rw [CTree.gen5]
  simp only [CTree.t5, ofT, StaticOK, Spread, lmx, List.foldr, S.wmax, S.wmin, U.nd]
  refine ⟨by omega, ⟨by omega, trivial, trivial, trivial, trivial⟩, trivial⟩

theorem gen8_lat (u : U) :
    depth (CTree.gen 8) = 2 ∧
    Lmax (ofT u (CTree.gen 8)) = 2 * u.lmax + u.wmax + u.imax ∧
    leaves (ofT u (CTree.gen 8)) = [0, 1, 2, 3, 4, 5, 6, 7] := by
  rw [CTree.gen8]
  simp only [CTree.t8, ofT, depth, Lmax, leaves, lmx, List.foldr, S.wmax, U.nd]
  refine ⟨?_, ?_, ?_⟩ <;> first | trivial | rfl | omega

/-- N = 8: every path has two cells, so the root cannot move before
`2 lmin + wmin + imin` after the last leaf. -/
theorem gen8_early (u : U) (σ : Nat → Nat → Nat) (k : Nat) :
    cT σ (ofT u (CTree.gen 8)) k + (2 * u.lmin + u.wmin + u.imin) ≤
      Early σ (ofT u (CTree.gen 8)) k := by
  have h := Early_ge σ k (ofT u (CTree.gen 8))
  have e : MinD (ofT u (CTree.gen 8)) = 2 * u.lmin + u.wmin + u.imin := by
    rw [CTree.gen8]; simp only [CTree.t8, ofT, MinD, S.wmin, U.nd]; omega
  omega

theorem gen8_static (u : U) (E : Nat)
    (h : u.fmax + 2 * (u.lmax - u.lmin) + (u.wmax - u.wmin) + (u.imax - u.imin) ≤ E) :
    StaticOK E 0 (ofT u (CTree.gen 8)) := by
  rw [CTree.gen8]
  simp only [CTree.t8, ofT, StaticOK, Spread, lmx, List.foldr, S.wmax, S.wmin, U.nd]
  refine ⟨by omega, ⟨by omega, trivial, trivial, trivial, trivial⟩,
    ⟨by omega, trivial, trivial, trivial, trivial⟩⟩

/-- **N = 5, timed, symbolic uniform delays.** Under the four-phase
environment and `H_ENV_LATENCY : fmax + 2 (lmax - lmin) + (wmax - wmin) +
(imax - imin) ≤ E`, the output of `bd_ctree #(.N(5))` is `V k` from
`c k + 2 lmax + wmax + imax` until (at least) `c (k+1) + lmin + imin - 1`. -/
theorem ctree5_timed (u : U) (rst : Trace) (x : Nat → Trace) (O : Trace)
    (R : Run rst x (ofT u (CTree.gen 5)) O) (σ : Nat → Nat → Nat) (V : Nat → Bool) (E T0 : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_LEAF : ∀ i, i < 5 → ∀ k t, σ i k ≤ t → t < σ i (k + 1) → x i t = V k)
    (H_LEAF_MONO : ∀ i, i < 5 → ∀ k, σ i k ≤ σ i (k + 1))
    (H_ACK : ∀ i, i < 5 → ∀ k, ∃ u', cT σ (ofT u (CTree.gen 5)) k ≤ u' ∧
        u' + E ≤ σ i (k + 1) ∧ O u' = V k)
    (H_ENV_LATENCY : u.fmax + 2 * (u.lmax - u.lmin) + (u.wmax - u.wmin) + (u.imax - u.imin) ≤ E)
    (H_NORST : ∀ t, T0 ≤ t → rst t = false)
    (H_START : ∀ i, i < 5 → T0 ≤ σ i 0)
    (H_RESET_DONE : ∀ t, cT σ (ofT u (CTree.gen 5)) 0 ≤ t →
        t < Early σ (ofT u (CTree.gen 5)) 0 → O t = !V 0) :
    ∀ k t, cT σ (ofT u (CTree.gen 5)) k + (2 * u.lmax + u.wmax + u.imax) ≤ t →
      t < cT σ (ofT u (CTree.gen 5)) (k + 1) + (u.lmin + u.imin) → O t = V k := by
  obtain ⟨_, hL, hlv⟩ := gen5_lat u
  have hmem : ∀ i, i ∈ leaves (ofT u (CTree.gen 5)) → i < 5 := by
    intro i hi; rw [hlv] at hi; simp at hi; omega
  intro k t h1 h2
  have e1 := gen5_early u σ (k + 1)
  exact tree_four_phase_static _ rst x O R σ V E T0 H_ALT
    (fun i hi => H_LEAF i (hmem i hi)) (fun i hi => H_LEAF_MONO i (hmem i hi))
    (fun i hi => H_ACK i (hmem i hi)) (gen5_static u E H_ENV_LATENCY) H_NORST
    (fun i hi => H_START i (hmem i hi)) H_RESET_DONE k t (by omega) (by omega)

/-- **N = 8, timed, symbolic uniform delays.** Same upper bound as N = 5
(depth 2); the lower bound is `2 lmin + wmin + imin` (every path has two
cells). -/
theorem ctree8_timed (u : U) (rst : Trace) (x : Nat → Trace) (O : Trace)
    (R : Run rst x (ofT u (CTree.gen 8)) O) (σ : Nat → Nat → Nat) (V : Nat → Bool) (E T0 : Nat)
    (H_ALT : ∀ k, V (k + 1) = !V k)
    (H_LEAF : ∀ i, i < 8 → ∀ k t, σ i k ≤ t → t < σ i (k + 1) → x i t = V k)
    (H_LEAF_MONO : ∀ i, i < 8 → ∀ k, σ i k ≤ σ i (k + 1))
    (H_ACK : ∀ i, i < 8 → ∀ k, ∃ u', cT σ (ofT u (CTree.gen 8)) k ≤ u' ∧
        u' + E ≤ σ i (k + 1) ∧ O u' = V k)
    (H_ENV_LATENCY : u.fmax + 2 * (u.lmax - u.lmin) + (u.wmax - u.wmin) + (u.imax - u.imin) ≤ E)
    (H_NORST : ∀ t, T0 ≤ t → rst t = false)
    (H_START : ∀ i, i < 8 → T0 ≤ σ i 0)
    (H_RESET_DONE : ∀ t, cT σ (ofT u (CTree.gen 8)) 0 ≤ t →
        t < Early σ (ofT u (CTree.gen 8)) 0 → O t = !V 0) :
    ∀ k t, cT σ (ofT u (CTree.gen 8)) k + (2 * u.lmax + u.wmax + u.imax) ≤ t →
      t < cT σ (ofT u (CTree.gen 8)) (k + 1) + (2 * u.lmin + u.wmin + u.imin) → O t = V k := by
  obtain ⟨_, hL, hlv⟩ := gen8_lat u
  have hmem : ∀ i, i ∈ leaves (ofT u (CTree.gen 8)) → i < 8 := by
    intro i hi; rw [hlv] at hi; simp at hi; omega
  intro k t h1 h2
  have e1 := gen8_early u σ (k + 1)
  exact tree_four_phase_static _ rst x O R σ V E T0 H_ALT
    (fun i hi => H_LEAF i (hmem i hi)) (fun i hi => H_LEAF_MONO i (hmem i hi))
    (fun i hi => H_ACK i (hmem i hi)) (gen8_static u E H_ENV_LATENCY) H_NORST
    (fun i hi => H_START i (hmem i hi)) H_RESET_DONE k t (by omega) (by omega)

end Formal.Cells.CTreeTimed
