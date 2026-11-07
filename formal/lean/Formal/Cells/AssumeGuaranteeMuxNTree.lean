import Formal.Cells.AssumeGuaranteeEndsNet

/-!
# Probe Bmn (shard B): the fork acknowledge TREES (`forkH5`, `forkH6`) as cell specs

A `bd_fork` with N outputs joins its N acknowledges in `bd_ctree #(N)` (`bd_ctl.v`). For
N ≤ 4 that is one LUT (Bseg's `CelSpec`); gcd_hw has two forks with N = 5 and one with N = 6,
whose trees are (`bd_ce.v`, chunks of four; `CTreeExact.sh5`, `sh6`):

    N = 5:  C2( C4(a0, a1, a2, a3), a4 )            2 LUTs (the 1-wide chunk is a wire)
    N = 6:  C2( C4(a0, a1, a2, a3), C2(a4, a5) )    3 LUTs

Every node is a C-element whose pins are four-phase IN THE NODE'S OWN NUMBERING (each leaf
acknowledges every token once; an inner node's output is a clean step signal of the same
tokens), so each node is Bseg's `CelSpec` and the network rule (`net_closed_gen`) composes
them with no tree-specific argument. What IS tree-specific is the departure bound `H_SND`
of an inner node: the leaves answer the ROOT's edge (the fork's acknowledge goes upstream),
not the inner node's. This file derives every node's `H_SND` from the leaves' bound
relative to the root (`H_ACK`, as `CTreeExact`'s), composing the node edges along the tree.

## Assumed / proved / NOT covered

**Assumed** (`Tree5`, `Tree6`): per node B's gate model (`CelG` of the real `bd_c4`/`bd_c2`
LUT, `GC4`/`GC2`), H_PWR, H_TIMES, H_RST_EARLY, H_RST_LONG (all of `CelSpec` except
`H_SND`, packaged as `CelNoSnd`); the inner-to-root pins' wires (H_WIRE); **H_ACK**: every
leaf's next edge is `E` after the ROOT's edge (an edge-time inequality, the fork's
protocol); H_LAT per node, with the inner node's latency budget `E + wl + lo_root` (the
root's own delay and the inner→root wire count for the inner node).

**Proved:** `tree5_cel`, `tree6_cel`: every node of the tree is a `CelSpec` (so it sits in
`Proved` and `mixed_closed2` closes it with the rest of the network); `snd_up` / `snd_down`
(the two edge compositions); `fork5_nodes`: the two LUTs of the generated `bd_fork_N5`
netlist are `¬rst ∧ C4(..)` and `¬rst ∧ C2(..)`, the `bd_c4`/`bd_c2` INITs (kernel decide).
Witness `Wit.tree5_witness` / `Wit.tree6_witness`: a gate-level network (`GD`) of each tree
with the REAL LUTs, band `[1, 1]`, feedback 1, wires 1, reset 4, skewed leaves (the inner
C4 holds through its feedback while its pins disagree), meets every hypothesis.

**NOT covered:** N = 6 has no generated netlist in `Formal.Gen.Cells`: its node INITs are
read from `bd_ctree`'s recursion in `bd_ce.v` (two `bd_c2`, one `bd_c4`; named
H_TREE6_MAP); the segment rule's last-arrival form is SUFFICIENT, not `CTreeExact`'s exact
per-node loop condition (no `MaxMin` credit); departure bounds are edge-time inequalities.
Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeMuxNTree
open Formal.Cells
open Formal.Cells.AssumeGuaranteeLinks (SegK)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GC2 GC4 lawC2 lawC4 cmax cmax_arr cmax_last cel4
  c2_gen c4_gen)
open Formal.Cells.AssumeGuaranteeEndsNet
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge2 (CelLaw CelG)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo)
open Formal.Net.Ops.Gen (genF cel2)
open Formal.Gen Formal.Gen.Cells

variable {ι : Type}

/-! ## 1. A C-element node without its departure bound -/

/-- **`CelSpec` without `H_SND` and `H_LAT`** (those depend on where the node sits in the
tree). -/
structure CelNoSnd {n : Nat} (G : (Fin n → Bool) → Bool → Bool → Bool) (D : GD ι) (c : ι)
    (pv : Fin n → GPin ι) : Prop where
  H_NE : 0 < n
  H_PINS : D.pins c = (List.finRange n).map pv
  H_NB : ∀ i, (pv i).nb = fun k => k + 1
  H_LAW : CelLaw G
  H_CEL : CelG G (fun t i => (pv i).P t) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c)
    (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j)
  H_RST_EARLY : D.R ≤ cmax (fun i => gE D.τ (pv i)) 0
  H_RST_LONG : D.hi c + D.fh c ≤ D.R

theorem CelNoSnd.spec {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {D : GD ι} {c : ι}
    {pv : Fin n → GPin ι} (N : CelNoSnd G D c pv) {E : Nat}
    (H_SND : ∀ i j, D.τ c j + E ≤ gE D.τ (pv i) (j + 1))
    (H_LAT : D.hi c + D.fh c ≤ D.lo c + E) : CelSpec G D c pv E :=
  ⟨N.H_NE, N.H_PINS, N.H_NB, N.H_LAW, N.H_CEL, N.H_PWR, N.H_TIMES, N.H_RST_EARLY, H_SND,
    N.H_RST_LONG, H_LAT⟩

/-- **Upward**: a node's edge `j` comes `lo` after each of its pins' edge `j`. -/
theorem snd_up {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {D : GD ι} {c : ι}
    {pv : Fin n → GPin ι} (N : CelNoSnd G D c pv) (i : Fin n) (j : Nat) :
    gE D.τ (pv i) j + D.lo c ≤ D.τ c j := by
  rw [N.H_TIMES j]
  have := nt_lo (D.O c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j) (win_le N.H_CEL.H_LUT_WIN)
    (hi := D.hi c)
  have := cmax_arr (fun i => gE D.τ (pv i)) i j
  omega

/-- **Through a wire**: a pin's edge `j` comes `wl` after its driver's edge `j`. -/
theorem snd_wire {D : GD ι} {p : GPin ι} (W : Wire p.wl p.wh (D.O p.drv) p.P) (j : Nat) :
    D.τ p.drv j + p.wl ≤ gE D.τ p j := ε_lo W (D.τ p.drv) j

/-- **Downward**: if a parent's pin `p` is driven by node `c` through a wire, `c`'s edge `j`
comes `wl + lo_parent` before the parent's. -/
theorem snd_down {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {D : GD ι} {r c : ι}
    {pv : Fin n → GPin ι} (N : CelNoSnd G D r pv) (i : Fin n) (hd : (pv i).drv = c)
    (W : Wire (pv i).wl (pv i).wh (D.O (pv i).drv) (pv i).P) (j : Nat) :
    D.τ c j + (pv i).wl + D.lo r ≤ D.τ r j := by
  have h1 := snd_wire W j
  have h2 := snd_up N i j
  rw [hd] at h1
  omega

/-! ## 2. The N = 5 tree -/

/-- Root pins of `C2(C4(a0..a3), a4)`: the inner node's wire, then leaf 4. -/
def rp5 (pin : GPin ι) (lv : Fin 5 → GPin ι) : Fin 2 → GPin ι :=
  fun i => if i.val = 0 then pin else lv 4
/-- The inner `C4`'s pins: leaves 0..3. -/
def ip4 {m : Nat} (lv : Fin (m + 4) → GPin ι) : Fin 4 → GPin ι :=
  fun i => lv ⟨i.val, by omega⟩

/-- **A `forkH5` acknowledge tree**: root `r` (`bd_c2`), inner node `n` (`bd_c4`), the wire
`pin` from `n` to the root, the five leaf pins `lv` (the fork outputs' acknowledges). -/
structure Tree5 (D : GD ι) (r n : ι) (pin : GPin ι) (lv : Fin 5 → GPin ι) (E : Nat) : Prop where
  root : CelNoSnd GC2 D r (rp5 pin lv)
  inner : CelNoSnd GC4 D n (ip4 (m := 1) lv)
  H_DRV : pin.drv = n
  H_WIRE : Wire pin.wl pin.wh (D.O pin.drv) pin.P
  /-- **H_ACK**: every leaf's next edge comes `E` after the ROOT's edge. -/
  H_ACK : ∀ i j, D.τ r j + E ≤ gE D.τ (lv i) (j + 1)
  H_LAT_R : D.hi r + D.fh r ≤ D.lo r + E
  H_LAT_N : D.hi n + D.fh n ≤ D.lo n + (E + pin.wl + D.lo r)

/-- **The `forkH5` tree's two nodes are `CelSpec`s**: the root with the leaves' `E`, the
inner `C4` with `E + wl + lo_root` (its departure bound DERIVED from the root's by
`snd_down`; the root's on its inner pin from the inner node's by `snd_up` and the wire). -/
theorem tree5_cel {D : GD ι} {r n : ι} {pin : GPin ι} {lv : Fin 5 → GPin ι} {E : Nat}
    (T : Tree5 D r n pin lv E) :
    CelSpec GC2 D r (rp5 pin lv) E ∧ CelSpec GC4 D n (ip4 (m := 1) lv) (E + pin.wl + D.lo r) := by
  have W0 : Wire (rp5 pin lv 0).wl (rp5 pin lv 0).wh (D.O (rp5 pin lv 0).drv) (rp5 pin lv 0).P :=
    T.H_WIRE
  refine ⟨T.root.spec (fun i j => ?_) T.H_LAT_R, T.inner.spec (fun i j => ?_) T.H_LAT_N⟩
  · by_cases h : i.val = 0
    · have e : rp5 pin lv i = pin := by simp only [rp5, h, ite_true]
      rw [e]
      have h1 := snd_wire T.H_WIRE (j + 1)
      rw [T.H_DRV] at h1
      have h2 := snd_up T.inner 0 (j + 1)
      have h3 := T.H_ACK 0 j
      have e2 : ip4 (m := 1) lv 0 = lv 0 := rfl
      rw [e2] at h2
      omega
    · have e : rp5 pin lv i = lv 4 := by simp only [rp5, h, ite_false]
      rw [e]; exact T.H_ACK 4 j
  · have h1 := snd_down T.root 0 T.H_DRV W0 j
    have h3 := T.H_ACK ⟨i.val, by omega⟩ j
    have e : rp5 pin lv 0 = pin := rfl
    rw [e] at h1
    show D.τ n j + (E + pin.wl + D.lo r) ≤ gE D.τ (lv ⟨i.val, by omega⟩) (j + 1)
    omega

/-! ## 3. The N = 6 tree -/

/-- Root pins of `C2(C4(a0..a3), C2(a4, a5))`. -/
def rp6 (pa pb : GPin ι) : Fin 2 → GPin ι := fun i => if i.val = 0 then pa else pb
/-- The inner `C2`'s pins: leaves 4, 5. -/
def ip2 (lv : Fin 6 → GPin ι) : Fin 2 → GPin ι := fun i => lv ⟨i.val + 4, by omega⟩

/-- **A `forkH6` acknowledge tree** (H_TREE6_MAP: `bd_ctree #(6)` = `C2(C4, C2)` with the
frozen `bd_c4`/`bd_c2` INITs): root `r`, inner `na` (`C4` of leaves 0..3) and `nb` (`C2` of
leaves 4, 5), wires `pa`, `pb` to the root. -/
structure Tree6 (D : GD ι) (r na nb : ι) (pa pb : GPin ι) (lv : Fin 6 → GPin ι) (E : Nat) :
    Prop where
  root : CelNoSnd GC2 D r (rp6 pa pb)
  innerA : CelNoSnd GC4 D na (ip4 (m := 2) lv)
  innerB : CelNoSnd GC2 D nb (ip2 lv)
  H_DRVA : pa.drv = na
  H_DRVB : pb.drv = nb
  H_WIREA : Wire pa.wl pa.wh (D.O pa.drv) pa.P
  H_WIREB : Wire pb.wl pb.wh (D.O pb.drv) pb.P
  H_ACK : ∀ i j, D.τ r j + E ≤ gE D.τ (lv i) (j + 1)
  H_LAT_R : D.hi r + D.fh r ≤ D.lo r + E
  H_LAT_A : D.hi na + D.fh na ≤ D.lo na + (E + pa.wl + D.lo r)
  H_LAT_B : D.hi nb + D.fh nb ≤ D.lo nb + (E + pb.wl + D.lo r)

/-- **The `forkH6` tree's three nodes are `CelSpec`s.** -/
theorem tree6_cel {D : GD ι} {r na nb : ι} {pa pb : GPin ι} {lv : Fin 6 → GPin ι} {E : Nat}
    (T : Tree6 D r na nb pa pb lv E) :
    CelSpec GC2 D r (rp6 pa pb) E ∧
    CelSpec GC4 D na (ip4 (m := 2) lv) (E + pa.wl + D.lo r) ∧
    CelSpec GC2 D nb (ip2 lv) (E + pb.wl + D.lo r) := by
  have WA : Wire (rp6 pa pb 0).wl (rp6 pa pb 0).wh (D.O (rp6 pa pb 0).drv) (rp6 pa pb 0).P :=
    T.H_WIREA
  have WB : Wire (rp6 pa pb 1).wl (rp6 pa pb 1).wh (D.O (rp6 pa pb 1).drv) (rp6 pa pb 1).P :=
    T.H_WIREB
  refine ⟨T.root.spec (fun i j => ?_) T.H_LAT_R, T.innerA.spec (fun i j => ?_) T.H_LAT_A,
    T.innerB.spec (fun i j => ?_) T.H_LAT_B⟩
  · by_cases h : i.val = 0
    · have e : rp6 pa pb i = pa := by simp only [rp6, h, ite_true]
      rw [e]
      have h1 := snd_wire T.H_WIREA (j + 1)
      rw [T.H_DRVA] at h1
      have h2 := snd_up T.innerA 0 (j + 1)
      have h3 := T.H_ACK 0 j
      have e2 : ip4 (m := 2) lv 0 = lv 0 := rfl
      rw [e2] at h2
      omega
    · have e : rp6 pa pb i = pb := by simp only [rp6, h, ite_false]
      rw [e]
      have h1 := snd_wire T.H_WIREB (j + 1)
      rw [T.H_DRVB] at h1
      have h2 := snd_up T.innerB 0 (j + 1)
      have h3 := T.H_ACK 4 j
      have e2 : ip2 lv 0 = lv 4 := rfl
      rw [e2] at h2
      omega
  · have h1 := snd_down T.root 0 T.H_DRVA WA j
    have h3 := T.H_ACK ⟨i.val, by omega⟩ j
    have e : rp6 pa pb 0 = pa := rfl
    rw [e] at h1
    show D.τ na j + (E + pa.wl + D.lo r) ≤ gE D.τ (lv ⟨i.val, by omega⟩) (j + 1)
    omega
  · have h1 := snd_down T.root 1 T.H_DRVB WB j
    have h3 := T.H_ACK ⟨i.val + 4, by omega⟩ j
    have e : rp6 pa pb 1 = pb := rfl
    rw [e] at h1
    show D.τ nb j + (E + pb.wl + D.lo r) ≤ gE D.τ (lv ⟨i.val + 4, by omega⟩) (j + 1)
    omega

/-! ## 4. The real LUTs of `bd_fork_N5` -/

/-- **The generated `bd_fork_N5` netlist's two LUTs** are the `bd_c4` and `bd_c2` cells with
their real reset pins (`¬rst ∧ C4`, `¬rst ∧ C2`), i.e. `GC4` and `GC2` of their pins. -/
theorem fork5_nodes :
    (∀ a b c d q r : Bool,
      genF bd_fork_N5 "u.genblk1.genblk1.genblk1.gt.chunk[0].u.genblk1.genblk1.genblk1.g4.u.u" .O
        ["ack_in[0]", "ack_in[1]", "ack_in[2]", "ack_in[3]", "u.genblk1.genblk1.genblk1.gt.part[0]",
         "rst"] [a, b, c, d, q, r] = (!r && cel4 a b c d q)) ∧
    (∀ a b q r : Bool,
      genF bd_fork_N5 "u.genblk1.genblk1.genblk1.gt.utop.genblk1.g2.u.u" .O
        ["u.genblk1.genblk1.genblk1.gt.part[0]", "ack_in[4]", "ack", "rst"] [a, b, q, r] =
        (!r && cel2 a b q)) := by
  constructor <;> decide +kernel

theorem GC4_eq (pv : Fin 4 → Bool) (q r : Bool) :
    GC4 pv q r = (!r && cel4 (pv 0) (pv 1) (pv 2) (pv 3) q) := by unfold GC4; rw [c4_gen]
theorem GC2_eq (pv : Fin 2 → Bool) (q r : Bool) :
    GC2 pv q r = (!r && cel2 (pv 0) (pv 1) q) := by unfold GC2; rw [c2_gen]

/-! ## 5. Non-vacuity: each tree as a gate-level network, REAL LUTs, nonzero delays -/

namespace Wit
open Formal.Cells.PipeTimed.Wit (rstW)
open Formal.Cells.WinFifoCausal (nt_eq noRevertI_shift)

/-- Period-16 waves, high 8 ticks from `o`, and their edges. -/
def q16 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 16 < 8)
def f16 (o j : Nat) : Nat := o + 16 * (j / 2) + 8 * (j % 2)

theorem q16_at (o j : Nat) : q16 (o + 1) (f16 o j + 1) = Vph j := by
  show decide _ = decide (j % 2 = 0)
  unfold f16; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
theorem q16_shift (o t : Nat) (h : 1 ≤ t) : q16 (o + 1) t = q16 o (t - 1) := by
  unfold q16; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
theorem q16_per (o u : Nat) (h : o + 16 ≤ u) : q16 o u = q16 o (u - 16) := by
  unfold q16; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
theorem q16_pre (o t : Nat) (h : t < o) : q16 o t = false := by
  unfold q16; simp only [decide_eq_false_iff_not]; omega

/-- A 1-tick wire from a `q16 o` driver with edges `f16 o`. -/
theorem wire16 (o : Nat) (h : 1 ≤ o) : Wire 1 1 (q16 o) (q16 (o + 1)) :=
  ⟨fun t ht => ⟨t - 1, by omega, by omega, q16_shift o t ht⟩,
   noRevertI_shift (fun t ht => q16_shift o t ht), Nat.le_refl 1,
   fun t ht => q16_pre _ t (by omega)⟩

/-- The pin edges through such a wire. -/
theorem eps16 (o j : Nat) : ε (q16 (o + 1)) 1 1 (f16 o) j = f16 (o + 1) j := by
  unfold ε; rw [nt_eq _ (Nat.le_refl 1) (q16_at o j)]; unfold f16; omega

/-- A node's edge when its excitation's phase start is `f16 o` and it is `q16 (o + 1)`. -/
theorem nt16 (o j : Nat) : nt (q16 (o + 1)) 1 1 (f16 o j) (Vph j) = f16 (o + 1) j := by
  rw [nt_eq _ (Nat.le_refl 1) (q16_at o j)]; unfold f16; omega

/-- `cmax` is the max when one pin attains it. -/
theorem cmax_eq {n : Nat} (ρ : Fin n → Nat → Nat) (j c : Nat) (i0 : Fin n)
    (h1 : ∀ i, ρ i j ≤ c) (h2 : ρ i0 j = c) : cmax ρ j = c := by
  have a := cmax_arr ρ i0 j
  rcases Nat.lt_or_ge c (cmax ρ j) with h | h
  · obtain ⟨i, hi⟩ := cmax_last ρ j c h; have := h1 i; omega
  · omega

theorem c4_small : ∀ t, t < 48 → 1 ≤ t → q16 8 t = (!rstW (t - 1) &&
    cel4 (q16 4 (t - 1)) (q16 5 (t - 1)) (q16 6 (t - 1)) (q16 7 (t - 1)) (q16 8 (t - 1 - 1))) := by
  decide

theorem c4_step : ∀ t, 1 ≤ t → q16 8 t = (!rstW (t - 1) &&
    cel4 (q16 4 (t - 1)) (q16 5 (t - 1)) (q16 6 (t - 1)) (q16 7 (t - 1)) (q16 8 (t - 1 - 1))) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hs : t < 48
    · exact c4_small t hs ht
    · have h := ih (t - 16) (by omega) (by omega)
      have r1 : rstW (t - 1) = rstW (t - 16 - 1) := by unfold rstW; simp; omega
      rw [q16_per 8 t (by omega), q16_per 4 (t - 1) (by omega), q16_per 5 (t - 1) (by omega),
        q16_per 6 (t - 1) (by omega), q16_per 7 (t - 1) (by omega),
        q16_per 8 (t - 1 - 1) (by omega), r1, h,
        show t - 1 - 16 = t - 16 - 1 by omega, show t - 1 - 1 - 16 = t - 16 - 1 - 1 by omega]

/-- A `bd_c2` node `q16 (o+1)` of pins `q16 a`, `q16 b`: its step relation for all `t` from
the first `48` ticks (period 16). -/
theorem c2_ext (a b o : Nat) (ha : a ≤ 12 ∧ b ≤ 12 ∧ o ≤ 12)
    (hs : ∀ t, t < 48 → 1 ≤ t → q16 (o + 1) t = (!rstW (t - 1) &&
      cel2 (q16 a (t - 1)) (q16 b (t - 1)) (q16 (o + 1) (t - 1 - 1)))) :
    ∀ t, 1 ≤ t → q16 (o + 1) t = (!rstW (t - 1) &&
      cel2 (q16 a (t - 1)) (q16 b (t - 1)) (q16 (o + 1) (t - 1 - 1))) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases h48 : t < 48
    · exact hs t h48 ht
    · have h := ih (t - 16) (by omega) (by omega)
      have r1 : rstW (t - 1) = rstW (t - 16 - 1) := by unfold rstW; simp; omega
      rw [q16_per (o + 1) t (by omega), q16_per a (t - 1) (by omega), q16_per b (t - 1) (by omega),
        q16_per (o + 1) (t - 1 - 1) (by omega), r1, h,
        show t - 1 - 16 = t - 16 - 1 by omega, show t - 1 - 1 - 16 = t - 16 - 1 - 1 by omega]

theorem c2_995 : ∀ t, 1 ≤ t → q16 (9 + 1) t = (!rstW (t - 1) &&
    cel2 (q16 9 (t - 1)) (q16 5 (t - 1)) (q16 (9 + 1) (t - 1 - 1))) :=
  c2_ext 9 5 9 (by decide) (by decide)
theorem c2_566 : ∀ t, 1 ≤ t → q16 (6 + 1) t = (!rstW (t - 1) &&
    cel2 (q16 5 (t - 1)) (q16 6 (t - 1)) (q16 (6 + 1) (t - 1 - 1))) :=
  c2_ext 5 6 6 (by decide) (by decide)
theorem c2_989 : ∀ t, 1 ≤ t → q16 (9 + 1) t = (!rstW (t - 1) &&
    cel2 (q16 9 (t - 1)) (q16 8 (t - 1)) (q16 (9 + 1) (t - 1 - 1))) :=
  c2_ext 9 8 9 (by decide) (by decide)

/-! ### N = 5 -/

def off5 (i : Nat) : Nat := if i = 4 then 4 else i + 3
theorem off5_ge (i : Nat) : 3 ≤ off5 i := by unfold off5; split <;> omega

/-- Cells: `0..4` the leaf drivers (environment), `5` the inner `bd_c4`, `6` the root `bd_c2`. -/
def O7 (c : Fin 7) : Nat → Bool :=
  if c.val < 5 then q16 (off5 c.val) else if c.val = 5 then q16 8 else q16 10
def τ7 (c : Fin 7) : Nat → Nat :=
  if c.val < 5 then f16 (off5 c.val) else if c.val = 5 then f16 8 else f16 10
def lv5 (i : Fin 5) : GPin (Fin 7) := ⟨⟨i.val, by omega⟩, q16 (off5 i.val + 1), 1, 1, fun k => k + 1⟩
def pin5 : GPin (Fin 7) := ⟨5, q16 9, 1, 1, fun k => k + 1⟩

def w5 : GD (Fin 7) where
  O := O7
  τ := τ7
  lo := fun _ => 1
  hi := fun _ => 1
  fl := fun _ => 1
  fh := fun _ => 1
  qp := fun c t => O7 c (t - 1)
  rst := rstW
  R := 4
  pins := fun c => if c.val = 5 then (List.finRange 4).map (ip4 (m := 1) lv5)
    else if c.val = 6 then (List.finRange 2).map (rp5 pin5 lv5) else []

theorem gE_lv5 (i : Fin 5) (j : Nat) : gE w5.τ (lv5 i) j = f16 (off5 i.val + 1) j := by
  show ε (q16 (off5 i.val + 1)) 1 1 (τ7 ⟨i.val, by omega⟩) j = _
  have : τ7 ⟨i.val, by omega⟩ = f16 (off5 i.val) := by
    unfold τ7; simp only [i.isLt, ↓reduceIte]
  rw [this, eps16]

theorem gE_pin5 (j : Nat) : gE w5.τ pin5 j = f16 9 j := by
  show ε (q16 (8 + 1)) 1 1 (f16 8) j = _
  rw [eps16]

theorem cm_inner5 (j : Nat) : cmax (fun i => gE w5.τ (ip4 (m := 1) lv5 i)) j = f16 7 j := by
  apply cmax_eq _ j _ 3
  · intro i
    show gE w5.τ (lv5 ⟨i.val, _⟩) j ≤ _
    rw [gE_lv5]; unfold off5 f16; split <;> omega
  · show gE w5.τ (lv5 ⟨3, _⟩) j = _
    rw [gE_lv5]; rfl

theorem cm_root5 (j : Nat) : cmax (fun i => gE w5.τ (rp5 pin5 lv5 i)) j = f16 9 j := by
  apply cmax_eq _ j _ 0
  · intro i
    by_cases h : i.val = 0
    · simp only [rp5, h, ite_true]; rw [gE_pin5]; exact Nat.le_refl _
    · simp only [rp5, h, ite_false]; rw [gE_lv5]
      have e : off5 (4 : Fin 5).val = 4 := rfl
      rw [e]; unfold f16; omega
  · show gE w5.τ pin5 j = _; exact gE_pin5 j

theorem inner5 : CelNoSnd GC4 w5 5 (ip4 (m := 1) lv5) where
  H_NE := by decide
  H_PINS := rfl
  H_NB := fun _ => rfl
  H_LAW := lawC4
  H_CEL := by
    show CelG GC4 (fun t i => (ip4 (m := 1) lv5 i).P t) rstW (q16 8) (fun t => q16 8 (t - 1)) 1 1 1 1
    have hx : ∀ t, 1 ≤ t → q16 8 t = GC4 (fun i => (ip4 (m := 1) lv5 i).P (t - 1))
        (q16 8 (t - 1 - 1)) (rstW (t - 1)) := by
      intro t ht; rw [GC4_eq, c4_step t ht]; rfl
    exact ⟨fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩, noRevertI_shift hx,
      fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, Nat.le_refl 1⟩
  H_PWR := fun t (h : t < 1) => q16_pre 8 t (by omega)
  H_TIMES := fun j => by
    rw [cm_inner5]; exact (nt16 7 j).symm
  H_RST_EARLY := by rw [cm_inner5]; decide
  H_RST_LONG := by decide

theorem root5 : CelNoSnd GC2 w5 6 (rp5 pin5 lv5) where
  H_NE := by decide
  H_PINS := rfl
  H_NB := fun i => by by_cases h : i.val = 0 <;> simp [rp5, h, pin5, lv5]
  H_LAW := lawC2
  H_CEL := by
    show CelG GC2 (fun t i => (rp5 pin5 lv5 i).P t) rstW (q16 10) (fun t => q16 10 (t - 1)) 1 1 1 1
    have hx : ∀ t, 1 ≤ t → q16 10 t = GC2 (fun i => (rp5 pin5 lv5 i).P (t - 1))
        (q16 10 (t - 1 - 1)) (rstW (t - 1)) := by
      intro t ht; rw [GC2_eq]
      exact c2_995 t ht
    exact ⟨fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩, noRevertI_shift hx,
      fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, Nat.le_refl 1⟩
  H_PWR := fun t (h : t < 1) => q16_pre 10 t (by omega)
  H_TIMES := fun j => by
    rw [cm_root5]; exact (nt16 9 j).symm
  H_RST_EARLY := by rw [cm_root5]; decide
  H_RST_LONG := by decide

/-- **Non-vacuity of `tree5_cel`**: the `forkH5` tree as a gate-level network (REAL `bd_c4`
and `bd_c2` LUTs, band `[1, 1]`, feedback 1, wires 1, reset 4; leaves skewed by up to 3
ticks, so the inner `C4`'s pins disagree at `t = 5` while it holds) meets every hypothesis
of `Tree5` with `E = 2`. -/
theorem tree5_witness :
    Tree5 w5 6 5 pin5 lv5 2 ∧ (ip4 (m := 1) lv5 0).P 5 ≠ (ip4 (m := 1) lv5 3).P 5 :=
  ⟨{ root := root5
     inner := inner5
     H_DRV := rfl
     H_WIRE := wire16 8 (by decide)
     H_ACK := fun i j => by
       rw [gE_lv5]
       show f16 10 j + 2 ≤ _
       have := off5_ge i.val; unfold f16; omega
     H_LAT_R := by decide
     H_LAT_N := by decide }, by decide⟩

/-! ### N = 6 -/

def off6 (i : Nat) : Nat := if i < 4 then i + 3 else i
theorem off6_ge (i : Nat) (h : i < 6) : 3 ≤ off6 i ∧ off6 i ≤ 6 := by unfold off6; split <;> omega

/-- Cells: `0..5` the leaf drivers, `6` the inner `bd_c4`, `7` the inner `bd_c2`, `8` the
root `bd_c2`. -/
def O9 (c : Fin 9) : Nat → Bool :=
  if c.val < 6 then q16 (off6 c.val) else if c.val = 6 then q16 8
  else if c.val = 7 then q16 7 else q16 10
def τ9 (c : Fin 9) : Nat → Nat :=
  if c.val < 6 then f16 (off6 c.val) else if c.val = 6 then f16 8
  else if c.val = 7 then f16 7 else f16 10
def lv6 (i : Fin 6) : GPin (Fin 9) := ⟨⟨i.val, by omega⟩, q16 (off6 i.val + 1), 1, 1, fun k => k + 1⟩
def pa6 : GPin (Fin 9) := ⟨6, q16 9, 1, 1, fun k => k + 1⟩
def pb6 : GPin (Fin 9) := ⟨7, q16 8, 1, 1, fun k => k + 1⟩

def w6 : GD (Fin 9) where
  O := O9
  τ := τ9
  lo := fun _ => 1
  hi := fun _ => 1
  fl := fun _ => 1
  fh := fun _ => 1
  qp := fun c t => O9 c (t - 1)
  rst := rstW
  R := 4
  pins := fun c => if c.val = 6 then (List.finRange 4).map (ip4 (m := 2) lv6)
    else if c.val = 7 then (List.finRange 2).map (ip2 lv6)
    else if c.val = 8 then (List.finRange 2).map (rp6 pa6 pb6) else []

theorem gE_lv6 (i : Fin 6) (j : Nat) : gE w6.τ (lv6 i) j = f16 (off6 i.val + 1) j := by
  show ε (q16 (off6 i.val + 1)) 1 1 (τ9 ⟨i.val, by omega⟩) j = _
  have : τ9 ⟨i.val, by omega⟩ = f16 (off6 i.val) := by
    unfold τ9; simp only [i.isLt, ↓reduceIte]
  rw [this, eps16]

theorem gE_pa6 (j : Nat) : gE w6.τ pa6 j = f16 9 j := by
  show ε (q16 (8 + 1)) 1 1 (f16 8) j = _
  rw [eps16]
theorem gE_pb6 (j : Nat) : gE w6.τ pb6 j = f16 8 j := by
  show ε (q16 (7 + 1)) 1 1 (f16 7) j = _
  rw [eps16]

theorem cm_a6 (j : Nat) : cmax (fun i => gE w6.τ (ip4 (m := 2) lv6 i)) j = f16 7 j := by
  apply cmax_eq _ j _ 3
  · intro i
    show gE w6.τ (lv6 ⟨i.val, _⟩) j ≤ _
    rw [gE_lv6]; unfold off6 f16; split <;> omega
  · show gE w6.τ (lv6 ⟨3, _⟩) j = _
    rw [gE_lv6]; rfl

theorem cm_b6 (j : Nat) : cmax (fun i => gE w6.τ (ip2 lv6 i)) j = f16 6 j := by
  apply cmax_eq _ j _ 1
  · intro i
    show gE w6.τ (lv6 ⟨i.val + 4, _⟩) j ≤ _
    rw [gE_lv6]
    show f16 (off6 (i.val + 4) + 1) j ≤ f16 6 j
    have := i.isLt; unfold off6 f16; split <;> omega
  · show gE w6.τ (lv6 ⟨5, _⟩) j = _
    rw [gE_lv6]; rfl

theorem cm_r6 (j : Nat) : cmax (fun i => gE w6.τ (rp6 pa6 pb6 i)) j = f16 9 j := by
  apply cmax_eq _ j _ 0
  · intro i
    by_cases h : i.val = 0
    · simp only [rp6, h, ite_true]; rw [gE_pa6]; exact Nat.le_refl _
    · simp only [rp6, h, ite_false]; rw [gE_pb6]; unfold f16; omega
  · show gE w6.τ pa6 j = _; exact gE_pa6 j

theorem innerA6 : CelNoSnd GC4 w6 6 (ip4 (m := 2) lv6) where
  H_NE := by decide
  H_PINS := rfl
  H_NB := fun _ => rfl
  H_LAW := lawC4
  H_CEL := by
    show CelG GC4 (fun t i => (ip4 (m := 2) lv6 i).P t) rstW (q16 8) (fun t => q16 8 (t - 1)) 1 1 1 1
    have hx : ∀ t, 1 ≤ t → q16 8 t = GC4 (fun i => (ip4 (m := 2) lv6 i).P (t - 1))
        (q16 8 (t - 1 - 1)) (rstW (t - 1)) := by
      intro t ht; rw [GC4_eq, c4_step t ht]; rfl
    exact ⟨fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩, noRevertI_shift hx,
      fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, Nat.le_refl 1⟩
  H_PWR := fun t (h : t < 1) => q16_pre 8 t (by omega)
  H_TIMES := fun j => by
    rw [cm_a6]; exact (nt16 7 j).symm
  H_RST_EARLY := by rw [cm_a6]; decide
  H_RST_LONG := by decide

theorem innerB6 : CelNoSnd GC2 w6 7 (ip2 lv6) where
  H_NE := by decide
  H_PINS := rfl
  H_NB := fun _ => rfl
  H_LAW := lawC2
  H_CEL := by
    show CelG GC2 (fun t i => (ip2 lv6 i).P t) rstW (q16 7) (fun t => q16 7 (t - 1)) 1 1 1 1
    have hx : ∀ t, 1 ≤ t → q16 7 t = GC2 (fun i => (ip2 lv6 i).P (t - 1))
        (q16 7 (t - 1 - 1)) (rstW (t - 1)) := by
      intro t ht; rw [GC2_eq]
      exact c2_566 t ht
    exact ⟨fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩, noRevertI_shift hx,
      fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, Nat.le_refl 1⟩
  H_PWR := fun t (h : t < 1) => q16_pre 7 t (by omega)
  H_TIMES := fun j => by
    rw [cm_b6]; exact (nt16 6 j).symm
  H_RST_EARLY := by rw [cm_b6]; decide
  H_RST_LONG := by decide

theorem root6 : CelNoSnd GC2 w6 8 (rp6 pa6 pb6) where
  H_NE := by decide
  H_PINS := rfl
  H_NB := fun i => by by_cases h : i.val = 0 <;> simp [rp6, h, pa6, pb6]
  H_LAW := lawC2
  H_CEL := by
    show CelG GC2 (fun t i => (rp6 pa6 pb6 i).P t) rstW (q16 10) (fun t => q16 10 (t - 1)) 1 1 1 1
    have hx : ∀ t, 1 ≤ t → q16 10 t = GC2 (fun i => (rp6 pa6 pb6 i).P (t - 1))
        (q16 10 (t - 1 - 1)) (rstW (t - 1)) := by
      intro t ht; rw [GC2_eq]
      exact c2_989 t ht
    exact ⟨fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩, noRevertI_shift hx,
      fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, Nat.le_refl 1⟩
  H_PWR := fun t (h : t < 1) => q16_pre 10 t (by omega)
  H_TIMES := fun j => by
    rw [cm_r6]; exact (nt16 9 j).symm
  H_RST_EARLY := by rw [cm_r6]; decide
  H_RST_LONG := by decide

/-- **Non-vacuity of `tree6_cel`**: the `forkH6` tree as a gate-level network (REAL `bd_c4`,
two `bd_c2`, band `[1, 1]`, feedback 1, wires 1, reset 4; skewed leaves) meets every
hypothesis of `Tree6` with `E = 2`. -/
theorem tree6_witness : Tree6 w6 8 6 7 pa6 pb6 lv6 2 :=
  { root := root6
    innerA := innerA6
    innerB := innerB6
    H_DRVA := rfl
    H_DRVB := rfl
    H_WIREA := wire16 8 (by decide)
    H_WIREB := wire16 7 (by decide)
    H_ACK := fun i j => by
      rw [gE_lv6]
      show f16 10 j + 2 ≤ _
      have := off6_ge i.val i.isLt; unfold f16; omega
    H_LAT_R := by decide
    H_LAT_A := by decide
    H_LAT_B := by decide }

end Wit

end Formal.Cells.AssumeGuaranteeMuxNTree
