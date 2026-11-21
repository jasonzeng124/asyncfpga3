import Formal.Cells.AssumeGuaranteeFork

/-!
# Probe Bseg (shard B): segment lemmas for the classes at gcd_hw's chain ends

Bnet (`AssumeGuarantee*`) closed the cell/environment circle by a strictly causal
assume-guarantee induction over node SEGMENTS (`net_closed`), with per-segment lemmas
for B's link (`link_segK`), the 2-input `bd_c2` (`celc_segK`) and wires (`wire_segK`). On
gcd_hw it left the 200 chain ends as assumed contracts. This file supplies the segment
lemmas of the end classes that have a B cell model, in the form the network rule consumes.

## Assumed / proved / NOT covered

**Proved (generic):**
* `net_closed_gen`: `net_closed` with each pin's dependency given by an arbitrary bound
  `nb` (segment `k` of the cell reads the pin's segments `k' < nb k`) instead of a fixed
  offset. Needed for cells that consume only SOME of a pin's tokens (steer branches).
  Strict causality is H_WAIT (`gE k' + lo ≤ τ c k` for every read segment) with
  `lo ≥ 1`. No monotonicity hypothesis. `net_closed_of_gen` recovers Bnet's offset form.
* `celG_segK`, `celG_cell`: a C-element LUT with ANY number of pins (Bfb2's `CelG`, any
  `G` with `CelLaw`), one segment: its node's segment `k` from the pins' phase-`k` shapes
  only, plus the (unconditional, in a network) departure bounds. `cmax` (the last arrival
  over `Fin n` pins) meets `H_ARR`/`H_LAST` by construction (`cmax_arr`, `cmax_last`).
* `celG_wait`: H_WAIT of such a cell, from its edge-time definition (unconditional).
* Laws of the REAL cells (`decide +kernel` on the generated netlists): `c2_gen`/`lawC2`
  (`bd_c2`: fork N = 2 acknowledge, join N = 2 request), `c3_gen`/`lawC3` (`bd_ctree`
  N = 3 = `bd_c3`: fork N = 3), `c4_gen`/`lawC4` (`bd_c4`: fork N = 4, `bd_ctree` N = 4).
  `ctree1_wire`: `bd_ctree` N = 1 (join N = 1) has NO cell: it is a wire, not a gate.
* `gated_segK`: segment `k` of a steer branch's gated request `r ∧ (s == b)` from the
  input's segments `≤ sN κ k` (`κ` enumerates the tokens steered to `b`), under
  H_SEL_STABLE. `lutnf_segK`: a feedback-free `Win` LUT with H_NO_REVERT carries one
  excitation segment to its node. `steer_segK`: the two together on the REAL `bd_steer`
  `u` LUT (O5/O6). `steer_wait`: its H_WAIT (unconditional).

**Assumed (named):** the B cell models (`CelG`, the steer LUT's `Win` + H_NO_REVERT),
H_PWR, H_RST_LONG, H_LAT, H_LUT_POS; for steers H_SEL_STABLE, a token enumeration `κ`, and
the excitation spacing H_SPACE (an edge-time inequality, as `net_closed`'s H_SP).

**NOT covered:** the steer acknowledge OR (`uack`): its excitation is clean only if the
two branch acknowledges interleave in token order, an inequality between edge times of
different cells that no segment shape gives; `bd_mux` (its acknowledge C-elements
`uxa`/`uya` read `z_ack`, which carries the OTHER input's tokens too, so their pins are
not four-phase in the cell's own numbering and `CelG`'s environment does not apply; the
`uor` OR has the steer OR's problem); `muxn`, `amerge`, C-trees N ≥ 5. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeEnds
open Formal.Cells
open Formal.Cells.AssumeGuarantee (ag_time)
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK segK_of_phases wire_segK)
open Formal.Cells.AssumeGuaranteeFork (NPin pinE NetA)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before node_win)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc steerF_gate)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo)
open Formal.Net.Ops.Gen (genF cel2 cel3 steerF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The network rule with arbitrary per-pin dependency bounds -/

/-- An input pin: driver, trace, wire band, and the dependency bound `nb` (segment `k` of
the reading cell reads the pin's segments `k' < nb k`). -/
structure GPin (ι : Type) where
  drv : ι
  P : Nat → Bool
  wl : Nat
  wh : Nat
  nb : Nat → Nat

/-- The pin's edges: `ε` of the driver's edges. -/
def gE {ι : Type} (τ : ι → Nat → Nat) (p : GPin ι) : Nat → Nat := ε p.P p.wl p.wh (τ p.drv)

/-- **The environment assumption of segment `k` of cell `c`**: every pin's read segments. -/
def GA {ι : Type} (τ : ι → Nat → Nat) (pins : ι → List (GPin ι)) (c : ι) (k : Nat) : Prop :=
  ∀ p ∈ pins c, ∀ k', k' < p.nb k → SegK p.P (gE τ p) k'

/-- **The assume-guarantee rule on a network, general dependency bounds.** Assumed:
H_CELL (each cell's segment contract), H_WIRE, H_WAIT (strict causality: each read pin
segment ends at least `lo c ≥ 1` before the cell's segment), H_SP (wire spacing). Proved:
every node is a clean step signal. -/
theorem net_closed_gen {ι : Type} (O : ι → Nat → Bool) (τ : ι → Nat → Nat) (lo : ι → Nat)
    (pins : ι → List (GPin ι))
    (H_CELL : ∀ c k, GA τ pins c k → SegK (O c) (τ c) k)
    (H_WIRE : ∀ c, ∀ p ∈ pins c, Wire p.wl p.wh (O p.drv) p.P)
    (H_WAIT : ∀ c, ∀ p ∈ pins c, ∀ k k', k' < p.nb k → gE τ p k' + lo c ≤ τ c k)
    (H_LUT_POS : ∀ c, 1 ≤ lo c)
    (H_SP : ∀ c, ∀ p ∈ pins c, ∀ j,
      p.wh ≤ τ p.drv j ∧ τ p.drv j + p.wh < τ p.drv (j + 1) + p.wl) :
    ∀ c, Phases (O c) (τ c) := by
  have all := ag_time (fun e : ι × Nat => τ e.1 e.2) (fun e => SegK (O e.1) (τ e.1) e.2)
    (fun e => GA τ pins e.1 e.2) (fun e h => H_CELL e.1 e.2 h)
    (fun e ih p hp k' hk' => by
      have hw := H_WIRE e.1 p hp
      have t2 := ε_lo hw (τ p.drv) k'
      have t3 := H_WAIT e.1 p hp e.2 k' hk'
      have := H_LUT_POS e.1
      have := hw.H_POS
      have hG := ih (p.drv, k') (by unfold gE at t3; simp only; omega)
      exact wire_segK hw k' hG (fun j _ => H_SP e.1 p hp j))
  exact fun c => phases_of_segK fun k => all (c, k)

/-- Every pin of such a network is a clean step signal too. -/
theorem net_pins_gen {ι : Type} (O : ι → Nat → Bool) (τ : ι → Nat → Nat)
    (pins : ι → List (GPin ι)) (hO : ∀ c, Phases (O c) (τ c))
    (H_WIRE : ∀ c, ∀ p ∈ pins c, Wire p.wl p.wh (O p.drv) p.P)
    (H_SP : ∀ c, ∀ p ∈ pins c, ∀ j,
      p.wh ≤ τ p.drv j ∧ τ p.drv j + p.wh < τ p.drv (j + 1) + p.wl) :
    ∀ c, ∀ p ∈ pins c, Phases p.P (gE τ p) :=
  fun c p hp => phases_of_segK fun k => wire_segK (H_WIRE c p hp) k
    (segK_of_phases (hO p.drv) k) (fun j _ => H_SP c p hp j)

/-- Bnet's offset pin as a general pin: `nb k = k + 1 - off`. -/
def toG {ι : Type} (p : NPin ι) : GPin ι := ⟨p.drv, p.P, p.wl, p.wh, fun k => k + 1 - p.off⟩

/-- **`net_closed` is the offset instance of `net_closed_gen`** (with its H_MONO). -/
theorem net_closed_of_gen {ι : Type} (O : ι → Nat → Bool) (τ : ι → Nat → Nat) (lo : ι → Nat)
    (pins : ι → List (NPin ι))
    (H_CELL : ∀ c k, NetA τ pins c k → SegK (O c) (τ c) k)
    (H_WIRE : ∀ c, ∀ p ∈ pins c, Wire p.wl p.wh (O p.drv) p.P)
    (H_WAIT : ∀ c, ∀ p ∈ pins c, ∀ j, pinE τ p j + lo c ≤ τ c (j + p.off))
    (H_LUT_POS : ∀ c, 1 ≤ lo c)
    (H_SP : ∀ c, ∀ p ∈ pins c, ∀ j,
      p.wh ≤ τ p.drv j ∧ τ p.drv j + p.wh < τ p.drv (j + 1) + p.wl)
    (H_MONO : ∀ c j, τ c j ≤ τ c (j + 1)) :
    ∀ c, Phases (O c) (τ c) := by
  have mono : ∀ c j j', j ≤ j' → τ c j ≤ τ c j' := by
    intro c j j' h
    induction j' with
    | zero => have : j = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ j' ih =>
      rcases Nat.lt_or_ge j (j' + 1) with h' | h'
      · have := ih (by omega); have := H_MONO c j'; omega
      · have : j = j' + 1 := by omega
        subst this; exact Nat.le_refl _
  refine net_closed_gen O τ lo (fun c => (pins c).map toG) (fun c k hA => H_CELL c k ?_)
    (fun c p hp => ?_) (fun c p hp k k' hk => ?_) H_LUT_POS (fun c p hp j => ?_)
  · intro p hp k' hk'
    exact hA (toG p) (List.mem_map.2 ⟨p, hp, rfl⟩) k' (by show k' < k + 1 - p.off; omega)
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp; exact H_WIRE c q hq
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have hk' : k' < k + 1 - q.off := hk
    have h1 := H_WAIT c q hq k'
    have h2 := mono c (k' + q.off) k (by omega)
    show pinE τ q k' + lo c ≤ τ c k
    omega
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp; exact H_SP c q hq j

/-! ## 2. A C-element with any number of pins, one segment -/

section celg
variable {ι : Type} {G : (ι → Bool) → Bool → Bool → Bool} {p : Nat → ι → Bool}
  {rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ : ι → Nat → Nat} {c : Nat → Nat}

/-- **C-element (any pins), one segment.** B's `CelG` model of a LUT `G` with the C-element
laws (`CelLaw`), feedback wire and real reset pin. `c j` is the last pin arrival of phase
`j` (`H_ARR`, `H_LAST`: definitions, met by `cmax`); the departure bounds `H_SND` (every
pin's next edge `E` after the node's edge) are assumed for all phases (in a network they
follow from the edge-time definitions); the pin SHAPES only for this segment's phase
(`k = 0`: every pin low on `[R, ρ i 0)`; `k = j+1`: pin `i` is `Vph j` on
`[ρ i j, ρ i (j+1))`). Conclusion: segment `k` of the node, edges `nt O lo hi (c j) (Vph j)`. -/
theorem celG_segK (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh) (i0 : ι)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    (H_ARR : ∀ i j, ρ i j ≤ c j) (H_LAST : ∀ j s, s < c j → ∃ i, s < ρ i j)
    (H_RST_EARLY : R ≤ c 0)
    (H_SND : ∀ i j, nt O lo hi (c j) (Vph j) + E ≤ ρ i (j + 1)) (k : Nat)
    (h0 : k = 0 → ∀ i t, R ≤ t → t < ρ i 0 → p t i = false)
    (hph : ∀ j, k = j + 1 → ∀ i t, ρ i j ≤ t → t < ρ i (j + 1) → p t i = Vph j) :
    SegK O (fun j => nt O lo hi (c j) (Vph j)) k := by
  have hlh := win_le C.H_LUT_WIN
  have hlo := C.H_LUT_POS
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := C.H_FB wh (Nat.le_refl _); omega
  have ntl : ∀ j, c j + lo ≤ nt O lo hi (c j) (Vph j) := fun j => nt_lo O _ _ hlh
  have gap : ∀ j, c j + lo + E ≤ c (j + 1) := fun j => by
    have := H_SND i0 j; have := H_ARR i0 (j + 1); have := ntl j; omega
  have cge : ∀ j, R ≤ c j := by
    intro j
    induction j with
    | zero => exact H_RST_EARLY
    | succ j ih => have := gap j; omega
  match k with
  | 0 =>
    have pre : ∀ s, s < c 0 → G (p s) (qp s) (rst s) = false := by
      intro s
      induction s using Nat.strongRecOn with
      | _ s ih =>
        intro h
        by_cases hs : s < R
        · rw [H_RST s]; simp only [hs, decide_true]; exact L.rst _ _
        · have hr : rst s = false := by rw [H_RST]; simp; omega
          obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
          obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
          have hq : qp s = false := by rw [e, q3]; exact ih s' (by omega) (by omega)
          rw [hr, hq]
          obtain ⟨i1, hi1⟩ := H_LAST 0 s h
          exact L.hold _ _ ⟨i1, h0 rfl i1 s (by omega) hi1⟩
    intro t _ ht
    show O t = false
    by_cases hh : t < hi
    · exact H_PWR t hh
    · by_cases h1 : t < c 0 + lo
      · obtain ⟨s, s1, s2, s3⟩ := C.H_LUT_WIN t (by omega)
        rw [s3]; exact pre s (by omega)
      · have := nt_before O lo hi (c 0) (Vph 0) t (by omega) ht
        rw [this, PipeTimed.Vph_even 0]; rfl
  | j + 1 =>
    have hP := hph j rfl
    have hR := cge j
    have hl := ntl j
    have exj : ∀ s, c j ≤ s → s < c (j + 1) → G (p s) (qp s) (rst s) = Vph j := by
      intro s
      induction s using Nat.strongRecOn with
      | _ s ih =>
        intro h1 h2
        have hr : rst s = false := by rw [H_RST]; simp; omega
        rw [hr]
        by_cases hd : ∀ i, s < ρ i (j + 1)
        · exact L.all _ _ _ (fun i => hP i s (Nat.le_trans (H_ARR i j) h1) (hd i))
        · rw [Classical.not_forall] at hd
          obtain ⟨i1, hi1⟩ := hd
          have hsnd := H_SND i1 j
          obtain ⟨u, hu1, hu2, e⟩ := C.H_FB s (by omega)
          obtain ⟨s', q1, q2, q3⟩ := C.H_LUT_WIN u (by omega)
          have hq : qp s = Vph j := by
            rw [e, q3]; exact ih s' (by omega) (by omega) (by omega)
          rw [hq]
          obtain ⟨i2, hi2⟩ := H_LAST (j + 1) s h2
          exact L.hold _ _ ⟨i2, hP i2 s (Nat.le_trans (H_ARR i2 j) h1) hi2⟩
    have hsp : c j + hi < c (j + 1) + lo := by have := gap j; omega
    have nw := node_win (v := Vph j) C.H_LUT_WIN C.H_NO_REVERT (fun s a b => exj s a b)
      (by omega) hsp
    intro t h1 h2
    show O t = Vph j
    by_cases ht : t < c (j + 1) + lo
    · exact nw.2.2.1 t h1 ht
    · have := nt_before O lo hi (c (j + 1)) (Vph (j + 1)) t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-- **The same, with the pins' SEGMENTS as the assumption** (the form the network rule
consumes: segment `k` of the node reads segments `≤ k` of every pin, offset 0). -/
theorem celG_cell (L : CelLaw G) (C : CelG G p rst O qp lo hi wl wh) (i0 : ι)
    (H_RST : ∀ t, rst t = decide (t < R)) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false)
    (H_ARR : ∀ i j, ρ i j ≤ c j) (H_LAST : ∀ j s, s < c j → ∃ i, s < ρ i j)
    (H_RST_EARLY : R ≤ c 0)
    (H_SND : ∀ i j, nt O lo hi (c j) (Vph j) + E ≤ ρ i (j + 1)) (k : Nat)
    (hpin : ∀ i k', k' ≤ k → SegK (fun t => p t i) (ρ i) k') :
    SegK O (fun j => nt O lo hi (c j) (Vph j)) k :=
  celG_segK L C i0 H_RST H_RST_LONG H_LAT H_PWR H_ARR H_LAST H_RST_EARLY H_SND k
    (fun hk i t _ ht => by subst hk; exact hpin i 0 (Nat.le_refl _) t (Nat.zero_le _) ht)
    (fun j hk i t h1 h2 => by subst hk; exact hpin i (j + 1) (Nat.le_refl _) t h1 h2)

/-- **H_WAIT of a C-element, unconditional**: its edge `j` comes at least `lo` after each
pin's edge `j` (from the edge-time definition, H_ARR). -/
theorem celG_wait (C : CelG G p rst O qp lo hi wl wh) (H_ARR : ∀ i j, ρ i j ≤ c j)
    (i : ι) (j : Nat) : ρ i j + lo ≤ nt O lo hi (c j) (Vph j) := by
  have := nt_lo O (c j) (Vph j) (win_le C.H_LUT_WIN) (hi := hi); have := H_ARR i j; omega

end celg

/-! ### The last arrival over `n` pins -/

/-- The last arrival of phase `j` over the pins of a list. -/
def lmax {ι : Type} (ρ : ι → Nat → Nat) (j : Nat) : List ι → Nat
  | [] => 0
  | i :: l => max (ρ i j) (lmax ρ j l)

theorem lmax_ge {ι : Type} (ρ : ι → Nat → Nat) (j : Nat) :
    ∀ (l : List ι) i, i ∈ l → ρ i j ≤ lmax ρ j l
  | [], _, h => absurd h (List.not_mem_nil)
  | i' :: l, i, h => by
    unfold lmax
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_max_left _ _
    · have := lmax_ge ρ j l i h; have := Nat.le_max_right (ρ i' j) (lmax ρ j l); omega

theorem lmax_lt {ι : Type} (ρ : ι → Nat → Nat) (j s : Nat) :
    ∀ l : List ι, s < lmax ρ j l → ∃ i ∈ l, s < ρ i j
  | [], h => absurd h (Nat.not_lt_zero _)
  | i' :: l, h => by
    unfold lmax at h
    by_cases h1 : s < ρ i' j
    · exact ⟨i', List.mem_cons_self .., h1⟩
    · obtain ⟨i, hi, h2⟩ := lmax_lt ρ j s l (by omega)
      exact ⟨i, List.mem_cons_of_mem _ hi, h2⟩

/-- **The last arrival over `Fin n` pins** (the cell's phase start). -/
def cmax {n : Nat} (ρ : Fin n → Nat → Nat) (j : Nat) : Nat := lmax ρ j (List.finRange n)

theorem cmax_arr {n : Nat} (ρ : Fin n → Nat → Nat) (i : Fin n) (j : Nat) : ρ i j ≤ cmax ρ j :=
  lmax_ge ρ j _ i (List.mem_finRange i)

theorem cmax_last {n : Nat} (ρ : Fin n → Nat → Nat) (j s : Nat) (h : s < cmax ρ j) :
    ∃ i, s < ρ i j := by
  obtain ⟨i, _, h⟩ := lmax_lt ρ j s _ h; exact ⟨i, h⟩

/-! ### The real cells: `bd_c2`, `bd_ctree` N = 3 (`bd_c3`), `bd_c4`; `bd_ctree` N = 1 -/

/-- The 4-input C-element. -/
def cel4 (a b c d q : Bool) : Bool := if a = b ∧ b = c ∧ c = d then a else q

/-- **`bd_c2`** (fork N = 2 acknowledge, join N = 2 request, `bd_ctree` N = 2): the
generated LUT is `¬rst ∧ C(a, b; q)`. -/
theorem c2_gen : ∀ a b q r : Bool,
    genF bd_c2 "u" .O ["a", "b", "q", "rst"] [a, b, q, r] = (!r && cel2 a b q) := by
  decide +kernel

/-- **`bd_ctree` N = 3** (fork N = 3 acknowledge): the generated LUT is `¬rst ∧ C(a0,a1,a2; q)`. -/
theorem c3_gen : ∀ a b c q r : Bool,
    genF bd_ctree_N3 "genblk1.genblk1.g3.u.u" .O ["a[0]", "a[1]", "a[2]", "q", "rst"]
      [a, b, c, q, r] = (!r && cel3 a b c q) := by decide +kernel

/-- **`bd_c4`** (fork N = 4 acknowledge, the leaf of `bd_ctree` N = 4). -/
theorem c4_gen : ∀ a b c d q r : Bool,
    genF bd_c4 "u" .O ["a", "b", "c", "d", "q", "rst"] [a, b, c, d, q, r] =
      (!r && cel4 a b c d q) := by decide +kernel

/-- **`bd_ctree` N = 1 (join N = 1) has no cell**: its output is its input net, a wire. -/
theorem ctree1_wire : bd_ctree_N1.cells = [] ∧ bd_ctree_N1.outputs = [("q", .net 2)] ∧
    bd_ctree_N1.inputs.head? = some ("a", 2) := ⟨rfl, rfl, rfl⟩

def GC2 (pv : Fin 2 → Bool) (q r : Bool) : Bool :=
  genF bd_c2 "u" .O ["a", "b", "q", "rst"] [pv 0, pv 1, q, r]
def GC3 (pv : Fin 3 → Bool) (q r : Bool) : Bool :=
  genF bd_ctree_N3 "genblk1.genblk1.g3.u.u" .O ["a[0]", "a[1]", "a[2]", "q", "rst"]
    [pv 0, pv 1, pv 2, q, r]
def GC4 (pv : Fin 4 → Bool) (q r : Bool) : Bool :=
  genF bd_c4 "u" .O ["a", "b", "c", "d", "q", "rst"] [pv 0, pv 1, pv 2, pv 3, q, r]

theorem lawC2 : CelLaw GC2 where
  rst pv q := by unfold GC2; rw [c2_gen]; rfl
  all pv q v h := by unfold GC2; rw [c2_gen, h 0, h 1]; cases v <;> rfl
  hold pv v h := by
    unfold GC2; rw [c2_gen]
    obtain ⟨i, hi⟩ := h
    have : pv 0 = v ∨ pv 1 = v := by
      match i, hi with
      | ⟨0, _⟩, hi => exact Or.inl hi
      | ⟨1, _⟩, hi => exact Or.inr hi
    rcases this with h | h <;> rw [h] <;> cases v <;> cases pv 0 <;> cases pv 1 <;>
      simp_all [cel2]

theorem lawC3 : CelLaw GC3 where
  rst pv q := by unfold GC3; rw [c3_gen]; rfl
  all pv q v h := by unfold GC3; rw [c3_gen, h 0, h 1, h 2]; cases v <;> rfl
  hold pv v h := by
    unfold GC3; rw [c3_gen]
    obtain ⟨i, hi⟩ := h
    have : pv 0 = v ∨ pv 1 = v ∨ pv 2 = v := by
      match i, hi with
      | ⟨0, _⟩, hi => exact Or.inl hi
      | ⟨1, _⟩, hi => exact Or.inr (Or.inl hi)
      | ⟨2, _⟩, hi => exact Or.inr (Or.inr hi)
    rcases this with h | h | h <;> rw [h] <;> cases v <;> cases pv 0 <;> cases pv 1 <;>
      cases pv 2 <;> simp_all [cel3]

theorem lawC4 : CelLaw GC4 where
  rst pv q := by unfold GC4; rw [c4_gen]; rfl
  all pv q v h := by unfold GC4; rw [c4_gen, h 0, h 1, h 2, h 3]; cases v <;> rfl
  hold pv v h := by
    unfold GC4; rw [c4_gen]
    obtain ⟨i, hi⟩ := h
    have : pv 0 = v ∨ pv 1 = v ∨ pv 2 = v ∨ pv 3 = v := by
      match i, hi with
      | ⟨0, _⟩, hi => exact Or.inl hi
      | ⟨1, _⟩, hi => exact Or.inr (Or.inl hi)
      | ⟨2, _⟩, hi => exact Or.inr (Or.inr (Or.inl hi))
      | ⟨3, _⟩, hi => exact Or.inr (Or.inr (Or.inr hi))
    rcases this with h | h | h | h <;> rw [h] <;> cases v <;> cases pv 0 <;> cases pv 1 <;>
      cases pv 2 <;> cases pv 3 <;> simp_all [cel4]

/-! ## 3. Steer branches: a branch fires on a token subset -/

/-- **The input segment a branch segment reads up to**: branch segment `k` (phase-start
`gc κ γ k = γ (sN κ k)`) ends when input segment `sN κ k` ends. -/
def sN (κ : Nat → Nat) (k : Nat) : Nat := 2 * κ (k / 2) + k % 2

theorem gc_sN (κ γ : Nat → Nat) (k : Nat) : gc κ γ k = γ (sN κ k) := rfl
theorem sN_even (κ : Nat → Nat) (m : Nat) : sN κ (2 * m) = 2 * κ m := by
  unfold sN; rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega]; rfl
theorem sN_odd (κ : Nat → Nat) (m : Nat) : sN κ (2 * m + 1) = 2 * κ m + 1 := by
  unfold sN; rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]

/-- **The gated request, one segment** (the segment form of Bfb2's `gated_phases`).
Segment `k` of `r ∧ (s == b)` (phase starts `gc κ γ`) follows from the request's segments
`≤ sN κ k`, H_SEL_STABLE (`s` is `σ n` while `r` is high in token `n`) and an enumeration
`κ` (strictly increasing) of exactly the tokens with `σ n = b`. -/
theorem gated_segK {r s : Nat → Bool} {γ : Nat → Nat} {σ : Nat → Bool} {κ : Nat → Nat}
    {b : Bool} (hγ : ∀ k, γ k < γ (k + 1))
    (H_SEL_STABLE : ∀ n t, γ (2 * n) ≤ t → t < γ (2 * n + 1) → s t = σ n)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκb : ∀ m, σ (κ m) = b)
    (hκall : ∀ n, σ n = b → ∃ m, κ m = n) (k : Nat)
    (hr : ∀ k', k' ≤ sN κ k → SegK r γ k') :
    SegK (fun t => r t && (s t == b)) (gc κ γ) k := by
  have km := LutFbBridge2.mono_of_succ hκ
  have gm := LutFbBridge2.mono_of_succ hγ
  have xoff : ∀ n t, n + 1 ≤ sN κ k → γ n ≤ t → t < γ (n + 1) →
      (∀ m, n = 2 * m → σ m ≠ b) → (r t && (s t == b)) = false := by
    intro n t hn h1 h2 hne
    have hrn : r t = Vph n := hr (n + 1) hn t h1 h2
    by_cases hp : n % 2 = 1
    · rw [hrn, show n = 2 * (n / 2) + 1 by omega, PipeTimed.Vph_odd]; rfl
    · have hn2 : n = 2 * (n / 2) := by omega
      have hs : s t = σ (n / 2) :=
        H_SEL_STABLE (n / 2) t (by rw [← hn2]; exact h1) (by rw [← hn2]; exact h2)
      rw [hs, beq_eq_false_iff_ne.mpr (hne (n / 2) hn2), Bool.and_false]
  match k with
  | 0 =>
    intro t _ ht
    have e0 : sN κ 0 = 2 * κ 0 := by unfold sN; simp
    have ht' : t < γ (2 * κ 0) := by rw [gc_sN, e0] at ht; exact ht
    show (r t && (s t == b)) = false
    rcases LutFbBridge.seg_of_mono γ hγ t with h | ⟨n, n1, n2⟩
    · rw [hr 0 (Nat.zero_le _) t (Nat.zero_le _) h]; rfl
    · have hn : n < 2 * κ 0 := by
        apply Classical.byContradiction; intro hc
        have := gm (2 * κ 0) n (by omega); omega
      refine xoff n t (by rw [e0]; omega) n1 n2
        (fun m hm hm2 => ?_)
      obtain ⟨m', hm'⟩ := hκall m hm2
      have := km 0 m' (Nat.zero_le _); omega
  | j + 1 =>
    obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
    · intro t h1 h2
      have h1' : γ (2 * κ m) ≤ t := by
        have : gc κ γ (2 * m) = γ (2 * κ m) := by rw [gc_sN, sN_even]
        rw [← this]; exact h1
      have h2' : t < γ (2 * κ m + 1) := by
        have : gc κ γ (2 * m + 1) = γ (2 * κ m + 1) := by rw [gc_sN, sN_odd]
        rw [← this]; exact h2
      have hr1 : r t = true := by
        rw [hr (2 * κ m + 1) (by rw [sN_odd]; exact Nat.le_refl _) t h1' h2']; exact PipeTimed.Vph_even _
      have hs : s t = b := by rw [H_SEL_STABLE (κ m) t h1' h2', hκb]
      show (r t && (s t == b)) = Vph (2 * m)
      rw [hr1, hs, PipeTimed.Vph_even]; cases b <;> rfl
    · intro t h1 h2
      have h1' : γ (2 * κ m + 1) ≤ t := by
        have : gc κ γ (2 * m + 1) = γ (2 * κ m + 1) := by rw [gc_sN, sN_odd]
        rw [← this]; exact h1
      have h2' : t < γ (2 * κ (m + 1)) := by
        have : gc κ γ (2 * m + 1 + 1) = γ (2 * κ (m + 1)) := by
          rw [gc_sN, show 2 * m + 1 + 1 = 2 * (m + 1) by omega, sN_even]
        rw [← this]; exact h2
      have hsk : sN κ (2 * m + 1 + 1) = 2 * κ (m + 1) := by
        rw [show 2 * m + 1 + 1 = 2 * (m + 1) by omega, sN_even]
      rcases LutFbBridge.seg_of_mono γ hγ t with h | ⟨n, n1, n2⟩
      · have := gm 0 (2 * κ m + 1) (Nat.zero_le _); omega
      · have hn1 : 2 * κ m + 1 ≤ n := by
          apply Classical.byContradiction; intro hc
          have := gm (n + 1) (2 * κ m + 1) (by omega); omega
        have hn2 : n < 2 * κ (m + 1) := by
          apply Classical.byContradiction; intro hc
          have := gm (2 * κ (m + 1)) n (by omega); omega
        show (r t && (s t == b)) = Vph (2 * m + 1)
        rw [PipeTimed.Vph_odd]
        refine xoff n t (by rw [hsk]; omega) n1 n2 (fun m2 hm2 hm3 => ?_)
        obtain ⟨m', hm'⟩ := hκall m2 hm3
        rcases Nat.lt_or_ge m m' with h | h
        · have := km (m + 1) m' h; omega
        · have := km m' m h; omega

/-- **A feedback-free LUT carries one excitation segment to its node** (`Win` + H_NO_REVERT,
H_PWR, the excitation spacing H_SPACE; no `lo ≥ 1` needed here, only in H_WAIT). -/
theorem lutnf_segK {x O : Nat → Bool} {lo hi : Nat} {g : Nat → Nat}
    (hW : Win lo hi x O) (hN : NoRevertI lo hi x O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_SPACE : hi ≤ g 0 ∧ ∀ j, g j + hi < g (j + 1) + lo) (k : Nat) (hx : SegK x g k) :
    SegK O (fun j => nt O lo hi (g j) (Vph j)) k := by
  have hlh := win_le hW
  have gm : ∀ j, hi ≤ g j := by
    intro j
    induction j with
    | zero => exact H_SPACE.1
    | succ j ih => have := H_SPACE.2 j; omega
  match k with
  | 0 =>
    intro t _ ht
    show O t = false
    by_cases hh : t < hi
    · exact H_PWR t hh
    · by_cases h1 : t < g 0 + lo
      · obtain ⟨s, s1, s2, s3⟩ := hW t (by omega)
        rw [s3]; exact hx s (Nat.zero_le _) (by omega)
      · have := nt_before O lo hi (g 0) (Vph 0) t (by omega) ht
        rw [this, PipeTimed.Vph_even 0]; rfl
  | j + 1 =>
    have nw := node_win (v := Vph j) hW hN (fun s a b => hx s a b) (gm j) (H_SPACE.2 j)
    intro t h1 h2
    show O t = Vph j
    by_cases ht : t < g (j + 1) + lo
    · exact nw.2.2.1 t h1 ht
    · have := nt_before O lo hi (g (j + 1)) (Vph (j + 1)) t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-- **Steer branch `b`, one segment** (the REAL `bd_steer` `u` LUT: O5 for `b = false`, O6
for `b = true`; `Win` + H_NO_REVERT, no feedback, no reset). Segment `k` of the branch's
request node (edges `nt O lo hi (gc κ γ j) (Vph j)`) follows from the input request's
segments `≤ sN κ k` (edges `γ`), H_SEL_STABLE, the enumeration `κ` of the tokens steered
to `b`, and the excitation spacing H_SPACE. -/
theorem steer_segK (b : Bool) {req s O : Nat → Bool} {lo hi : Nat} {γ κ : Nat → Nat}
    {σ : Nat → Bool}
    (H_LUT_WIN : Win lo hi (fun t => steerF b (req t, s t)) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => steerF b (req t, s t)) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (hγ : ∀ k, γ k < γ (k + 1))
    (H_SEL_STABLE : ∀ n t, γ (2 * n) ≤ t → t < γ (2 * n + 1) → s t = σ n)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκb : ∀ m, σ (κ m) = b)
    (hκall : ∀ n, σ n = b → ∃ m, κ m = n)
    (H_SPACE : hi ≤ gc κ γ 0 ∧ ∀ j, gc κ γ j + hi < gc κ γ (j + 1) + lo) (k : Nat)
    (hr : ∀ k', k' ≤ sN κ k → SegK req γ k') :
    SegK O (fun j => nt O lo hi (gc κ γ j) (Vph j)) k := by
  have ex : (fun t => steerF b (req t, s t)) = fun t => req t && (s t == b) :=
    funext fun t => steerF_gate b (req t) (s t)
  rw [ex] at H_LUT_WIN H_NO_REVERT
  exact lutnf_segK H_LUT_WIN H_NO_REVERT H_PWR H_SPACE k
    (gated_segK hγ H_SEL_STABLE hκ hκb hκall k hr)

/-- **H_WAIT of a steer branch, unconditional**: its edge `k` comes at least `lo` after
every input edge it reads (`k' ≤ sN κ k`). -/
theorem steer_wait {O : Nat → Bool} {lo hi : Nat} {γ κ : Nat → Nat} (hlh : lo ≤ hi)
    (hγ : ∀ k, γ k < γ (k + 1)) (k k' : Nat) (hk : k' < sN κ k + 1) :
    γ k' + lo ≤ nt O lo hi (gc κ γ k) (Vph k) := by
  have := nt_lo O (gc κ γ k) (Vph k) hlh (hi := hi)
  have := LutFbBridge2.mono_of_succ hγ k' (sN κ k) (by omega)
  rw [gc_sN] at *; omega

/-! ## 4. Non-vacuity, nonzero delays -/

open Formal.Cells.PipeTimed.Wit (sq sq_pre sq_phase rstW)
open Formal.Cells.LutFbBridge2Env (τ4 phases_sq)

theorem G3_GC3 : LutFbBridge2.G3 = GC3 := by
  funext pv q r; unfold LutFbBridge2.G3 GC3; rw [LutFbBridge2.join3_gen, c3_gen]

/-- **Non-vacuity of `celG_segK`/`celG_cell`** on the REAL `bd_ctree` N = 3 LUT (the
fork N = 3 acknowledge; LUT band `[1, 2]`, feedback 1, reset 4; Bfb2's `join3_witness`
run): every hypothesis holds for every `k` (the run meets Bfb2's whole `EnvG`), the pins
disagree at `t = 4` (the cell holds through its feedback), and every segment follows. -/
theorem celG_witness :
    CelG GC3 (LutFbBridge2.pv3 (sq 4) (sq 5) (sq 4)) rstW (sq 6) (sq 7) 1 2 1 1 ∧
    LutFbBridge2.EnvG (LutFbBridge2.pv3 (sq 4) (sq 5) (sq 4)) rstW (sq 6) 1 2 4
      LutFbBridge2.ρ3 LutFbBridge2.cw 2 ∧ sq 4 4 ≠ sq 5 4 ∧
    (∀ k, SegK (sq 6) (fun j => nt (sq 6) 1 2 (LutFbBridge2.cw j) (Vph j)) k) := by
  have C : CelG GC3 (LutFbBridge2.pv3 (sq 4) (sq 5) (sq 4)) rstW (sq 6) (sq 7) 1 2 1 1 := by
    rw [← G3_GC3]; exact LutFbBridge2.cel3_w
  have Ev := LutFbBridge2.env3_w
  exact ⟨C, Ev, by decide, fun k => celG_segK lawC3 C 0 Ev.H_RST (by decide) (by decide)
    (fun t h => sq_pre 6 t (by omega)) Ev.H_ARR Ev.H_LAST Ev.H_RST_EARLY Ev.H_SND k
    (fun _ => Ev.H_P0) (fun j _ i t h1 h2 => Ev.H_P i j t h1 h2)⟩

/-- Select of the steer witness: token `n` (input phases `2n`, `2n+1`, `[4+8n, 12+8n)`)
is steered to branch `n % 2 == 1`. -/
def sw (t : Nat) : Bool := (t - 4) / 8 % 2 == 1
def σw (n : Nat) : Bool := n % 2 == 1
def κw (m : Nat) : Nat := 2 * m
/-- Branch 0 of the witness: a 1-tick transport copy of its real excitation. -/
def Ow (t : Nat) : Bool := if t = 0 then false else (sq 4 (t - 1) && (sw (t - 1) == false))

/-- **Non-vacuity of `steer_segK` on a token SUBSET**: the input request `sq 4` (phases of
4 ticks), the select alternating per token, so branch 0 (the real `bd_steer` O5, a 1-tick
transport LUT) receives exactly the even tokens (`κ m = 2m`). Every hypothesis holds,
every branch segment follows, and the branch is low during token 1 although the input
request is high (`sq 4 12 = true`, `Ow 13 = false`). -/
theorem steer_seg_witness :
    Win 1 1 (fun t => steerF false (sq 4 t, sw t)) Ow ∧
    NoRevertI 1 1 (fun t => steerF false (sq 4 t, sw t)) Ow ∧
    (∀ t, t < 1 → Ow t = false) ∧ (∀ k, τ4 4 k < τ4 4 (k + 1)) ∧
    (∀ n t, τ4 4 (2 * n) ≤ t → t < τ4 4 (2 * n + 1) → sw t = σw n) ∧
    (∀ m, κw m < κw (m + 1)) ∧ (∀ m, σw (κw m) = false) ∧
    (∀ n, σw n = false → ∃ m, κw m = n) ∧
    (1 ≤ gc κw (τ4 4) 0 ∧ ∀ j, gc κw (τ4 4) j + 1 < gc κw (τ4 4) (j + 1) + 1) ∧
    (∀ k', SegK (sq 4) (τ4 4) k') ∧
    (∀ k, SegK Ow (fun j => nt Ow 1 1 (gc κw (τ4 4) j) (Vph j)) k) ∧
    sq 4 12 = true ∧ Ow 13 = false := by
  have hx : ∀ t, 1 ≤ t → Ow t = steerF false (sq 4 (t - 1), sw (t - 1)) := by
    intro t ht; rw [steerF_gate]; unfold Ow; simp [show t ≠ 0 by omega]
  have hW : Win 1 1 (fun t => steerF false (sq 4 t, sw t)) Ow :=
    fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩
  have hN : NoRevertI 1 1 (fun t => steerF false (sq 4 t, sw t)) Ow :=
    WinFifoCausal.noRevertI_shift (hi := 1) (x := fun t => steerF false (sq 4 t, sw t)) hx
  have hP : ∀ t, t < 1 → Ow t = false := fun t h => by unfold Ow; simp [show t = 0 by omega]
  have hγ : ∀ k, τ4 4 k < τ4 4 (k + 1) := fun k => by unfold τ4; omega
  have hS : ∀ n t, τ4 4 (2 * n) ≤ t → t < τ4 4 (2 * n + 1) → sw t = σw n := by
    intro n t h1 h2
    unfold τ4 at h1 h2
    have : (t - 4) / 8 = n := by omega
    unfold sw σw; rw [this]
  have hκ : ∀ m, κw m < κw (m + 1) := fun m => by unfold κw; omega
  have hκb : ∀ m, σw (κw m) = false := fun m => by
    unfold σw κw; simp
  have hκall : ∀ n, σw n = false → ∃ m, κw m = n := fun n h => by
    unfold σw at h; simp at h; exact ⟨n / 2, by unfold κw; omega⟩
  have hsp : 1 ≤ gc κw (τ4 4) 0 ∧ ∀ j, gc κw (τ4 4) j + 1 < gc κw (τ4 4) (j + 1) + 1 :=
    ⟨by unfold gc τ4; omega, fun j => by unfold gc τ4 κw; omega⟩
  have hr : ∀ k', SegK (sq 4) (τ4 4) k' := fun k' => segK_of_phases (phases_sq 4) k'
  exact ⟨hW, hN, hP, hγ, hS, hκ, hκb, hκall, hsp, hr,
    fun k => steer_segK false hW hN hP hγ hS hκ hκb hκall hsp k (fun k' _ => hr k'),
    by decide, by decide⟩

end Formal.Cells.AssumeGuaranteeEnds
