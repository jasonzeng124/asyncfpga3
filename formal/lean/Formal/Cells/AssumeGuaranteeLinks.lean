import Formal.Cells.AssumeGuarantee
import Formal.Cells.LutFbBridge2Env

/-!
# Probe Bnet (shard B): closing the assume-guarantee circle for chains of links

Bfb2 (`LutFbBridge2Env`) proved each half of a circle: a link's guarantee from its own
environment `Env1` (`link_guar`), and `Env1` from its neighbours' guarantees
(`link_link_env`). This file closes the circle for a whole chain, by the strictly causal
induction of `AssumeGuarantee.ag_time`, measured by the END TIME of each node segment.

## Assumed / proved / NOT covered

**Assumed** (named fields of `Chain`, `ChainT`):
* every link `1..N`: B's `Stage` (Win LUT + H_NO_REVERT + feedback wire, real `bd_c2n`
  INIT), H_PWR, H_LUT_POS; every wire: `Wire` (H_WIRE); H_RST;
* H_TIMES: each link's edge times are read off its own node trace (`τs` of its pins'
  phase starts, the pins' edges `ε` of the neighbours' edges). These are definitions
  written as equations; the theorems hold for every solution;
* the two END cells (source, sink) are not gates: each has an assume-guarantee CONTRACT
  (`SRC_SEG`, `SNK_SEG`: its node's segment `k` holds if its input pin's segments
  `< k` / `≤ k` hold) and waits at least `lo ≥ 1` for its input (`SRC_WAIT`, `SNK_WAIT`);
* timing: B's `Timing1` per link with the DERIVED slacks `Es`, `Ea`; H_WIRE_R; H_RT.

NO environment hypothesis (`Env1`) on any link.

**Proved:**
* per-segment cell lemmas: `wire_segK` (a wire carries segment `k`), `link_segK` (a link
  controller's segment `k` from its pins' phase-`k` shapes), `celc_segK` (the same for
  `bd_c2`);
* `chain_cell` (H_CELL), `chain_env` (H_ENV with the causality side condition: each
  assumption needs only guarantees at STRICTLY smaller times; the time inequalities are
  unconditional consequences of the edge-time definitions and H_LUT_POS);
* `chain_nodes`, `chain_reqPin`, `chain_ackPin`: every node and pin of the chain is a clean
  step signal; `chain_env1`: every link's `Env1` and `Timing1`, with
  `Es = vl + lo + wl` (upstream round trip) and `Ea = wl + lo + vl` (downstream), exactly
  `link_link_env`'s slacks; `chain_lutFb`: C's `LutFb`/`FbFirst` for every link;
* rings: `ring_dead`, `ring_no_env1`: any CLOSED network of B's (reset-0) links is 0
  forever, so no ring link has `Env1`; the circle closes on no all-link ring;
* non-vacuity: `chain_witness N` (a live chain of ANY length, LUT band `[1, 3]`, wires 1;
  H_LAT and both derived slacks met with equality), `ring_witness`.

**NOT covered:**
* the END contracts are assumptions: on gcd_hw they are the producers/consumers of the
  chains (`AssumeGuaranteeCap.head_classes`, `tail_classes`);
* rings with a token-holding (`_set`) stage: B's `Stage` has no set variant;
* uniqueness/existence of solutions of H_TIMES is not proved (the witness has one);
* infinite runs only (each segment is followed by another), as `Env1`.
Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeLinks
open Formal.Cells
open Formal.Cells.AssumeGuarantee (ag_time)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq nt_before node_win exc_phase_w
  exc_pre_w Stage Env1 Timing1 cph τs cW vW)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)

/-! ## 1. Segments: the per-event guarantee -/

/-- **Segment `k` of a step signal** with edges `e`: `k = 0` is the pre-segment `[0, e 0)`
(value 0); `k = j + 1` is `[e j, e (j+1))` (value `Vph j`). Its END time `e k` is the
event's time in the assume-guarantee induction. -/
def SegK (P : Nat → Bool) (e : Nat → Nat) (k : Nat) : Prop :=
  ∀ t, cW e k ≤ t → t < e k → P t = vW k

theorem phases_of_segK {P : Nat → Bool} {e : Nat → Nat} (h : ∀ k, SegK P e k) : Phases P e :=
  ⟨fun t ht => h 0 t (Nat.zero_le _) ht, fun j t h1 h2 => h (j + 1) t h1 h2⟩

theorem segK_of_phases {P : Nat → Bool} {e : Nat → Nat} (h : Phases P e) : ∀ k, SegK P e k
  | 0 => fun t _ ht => h.pre t ht
  | j + 1 => fun t h1 h2 => h.ph j t h1 h2

/-! ## 2. A wire carries one segment, given the (unconditional) spacing -/

/-- **Wire, one segment.** Segment `k` of the node gives segment `k` of the pin, given
`wh ≤ e j` and the spacing `e j + wh < e (j+1) + wl` (for `k = j + 1`). -/
theorem wire_segK {wl wh : Nat} {O P : Nat → Bool} {e : Nat → Nat} (W : Wire wl wh O P)
    (k : Nat) (hO : SegK O e k)
    (hsp : ∀ j, k = j + 1 → wh ≤ e j ∧ e j + wh < e (j + 1) + wl) :
    SegK P (ε P wl wh e) k := by
  have hlh := win_le W.H_WIN
  match k with
  | 0 =>
    intro t _ ht
    show P t = false
    by_cases h0 : t < wh
    · exact W.H_PWR t h0
    · by_cases h1 : t < e 0 + wl
      · obtain ⟨s, s1, s2, s3⟩ := W.H_WIN t (by omega)
        rw [s3]; exact hO s (Nat.zero_le _) (by omega)
      · have := nt_before P wl wh (e 0) (Vph 0) t (by omega) ht
        rw [this, PipeTimed.Vph_even 0]; rfl
  | j + 1 =>
    obtain ⟨hc, hs⟩ := hsp j rfl
    intro t h1 h2
    show P t = Vph j
    have nw := node_win (v := Vph j) W.H_WIN W.H_NO_REVERT (fun s a b => hO s a b) hc hs
    by_cases ht : t < e (j + 1) + wl
    · exact nw.2.2.1 t h1 ht
    · have := nt_before P wl wh (e (j + 1)) (Vph (j + 1)) t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-! ## 3. A link controller, one segment -/

/-- **Link controller, one segment** (B's `Stage`, the real `bd_c2n` INIT). The departure
bounds `H_SND`/`H_RCV` (measured from the node's own edges) and the reset fields are
assumed for all phases (in the networks below they are UNCONDITIONAL: they follow from the
definitions of the edge times by `nt_lo`); the pin shapes are assumed only for the phase of
this segment (`k = 0`: the request low on `[R, ρ 0)`; `k = j + 1`: request `Vph j` on
`[ρ j, ρ (j+1))` and acknowledge `!Vph j` on `[α j, α (j+1))`). Conclusion: segment `k` of
the node, edges `τs`. -/
theorem link_segK {req ack rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ α : Nat → Nat}
    (S : Stage req ack rst O qp lo hi wl wh) (H_RST : ∀ t, rst t = decide (t < R))
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_LUT_POS : 1 ≤ lo)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_ACK0 : α 0 = R) (H_RST_EARLY : R ≤ ρ 0)
    (H_SND : ∀ j, τs O lo hi ρ α j + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, τs O lo hi ρ α j + E ≤ α (j + 1)) (k : Nat)
    (hreq0 : k = 0 → ∀ t, R ≤ t → t < ρ 0 → req t = false)
    (hph : ∀ j, k = j + 1 →
      (∀ t, ρ j ≤ t → t < ρ (j + 1) → req t = Vph j) ∧
      (∀ t, α j ≤ t → t < α (j + 1) → ack t = !Vph j)) :
    SegK O (τs O lo hi ρ α) k := by
  have hlh := win_le S.H_LUT_WIN
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := S.H_FB wh (Nat.le_refl _); omega
  have ntl : ∀ j, cph ρ α j + lo ≤ τs O lo hi ρ α j := fun j => nt_lo O _ _ hlh
  have cge : ∀ j, R ≤ cph ρ α j := by
    intro j
    induction j with
    | zero => unfold cph; omega
    | succ j ih =>
      have := H_SND j; have := ntl j
      have : ρ (j + 1) ≤ cph ρ α (j + 1) := Nat.le_max_left _ _
      omega
  have gap : ∀ j, cph ρ α j + lo + E ≤ cph ρ α (j + 1) := fun j => by
    have := H_SND j; have := H_RCV j; have := ntl j; unfold cph at *; omega
  have rlo : ∀ t, R ≤ t → rst t = false := fun t h => by rw [H_RST]; simp; omega
  match k with
  | 0 =>
    have hc : cph ρ α 0 = ρ 0 := by unfold cph; rw [H_ACK0]; omega
    have pre := exc_pre_w S.H_LUT_WIN S.H_FB S.H_LOOP_POS R (ρ 0)
      (fun t h => by rw [H_RST]; simp [h]) (hreq0 rfl) H_RST_LONG
    intro t _ ht
    show O t = false
    by_cases h0 : t < hi
    · exact H_PWR t h0
    · by_cases h1 : t < cph ρ α 0 + lo
      · obtain ⟨s, s1, s2, s3⟩ := S.H_LUT_WIN t (by omega)
        rw [s3]; exact pre s (by omega)
      · have := nt_before O lo hi (cph ρ α 0) (Vph 0) t (by omega) ht
        rw [this, PipeTimed.Vph_even 0]; rfl
  | j + 1 =>
    obtain ⟨hr, ha⟩ := hph j rfl
    have hR := cge j
    have exj := exc_phase_w S.H_LUT_WIN S.H_FB S.H_LOOP_POS (Vph j) (ρ j) (ρ (j + 1)) (α j)
      (α (j + 1)) E hr ha (fun t ht => rlo t (by unfold cph at hR; omega))
      (by have := H_SND j; have := ntl j; unfold cph at *; omega)
      (by have := H_RCV j; have := ntl j; unfold cph at *; omega) H_LAT
      (by unfold cph at hR; omega)
    have hsp : cph ρ α j + hi < cph ρ α (j + 1) + lo := by
      have := gap j; have := S.H_LOOP_POS; omega
    have nw := node_win (v := Vph j) S.H_LUT_WIN S.H_NO_REVERT (fun s a b => exj s a b)
      (by unfold cph at hR; omega) hsp
    intro t h1 h2
    show O t = Vph j
    by_cases ht : t < cph ρ α (j + 1) + lo
    · exact nw.2.2.1 t h1 ht
    · have := nt_before O lo hi (cph ρ α (j + 1)) (Vph (j + 1)) t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-! ## 3b. A 2-input C-element (`bd_c2`, the fork/join acknowledge cell), one segment -/

/-- **C-element, one segment** (B's `CelC`, real `bd_c2` INIT): as `link_segK`, with both
inputs read at phase `j` (`k = 0`: both low on `[R, first edge)`). Edges
`nt O lo hi (cph ρ β j) (Vph j)` (Bfb2's `tF`). -/
theorem celc_segK {a b rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ β : Nat → Nat}
    (Cc : LutFbBridge.CelC a b rst O qp lo hi wl wh) (H_RST : ∀ t, rst t = decide (t < R))
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_RST_EARLY : R ≤ ρ 0 ∧ R ≤ β 0)
    (H_SND : ∀ j, nt O lo hi (cph ρ β j) (Vph j) + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, nt O lo hi (cph ρ β j) (Vph j) + E ≤ β (j + 1)) (k : Nat)
    (h0 : k = 0 → (∀ t, R ≤ t → t < ρ 0 → a t = false) ∧ (∀ t, R ≤ t → t < β 0 → b t = false))
    (hph : ∀ j, k = j + 1 →
      (∀ t, ρ j ≤ t → t < ρ (j + 1) → a t = Vph j) ∧
      (∀ t, β j ≤ t → t < β (j + 1) → b t = Vph j)) :
    SegK O (fun j => nt O lo hi (cph ρ β j) (Vph j)) k := by
  have hlh := win_le Cc.H_LUT_WIN
  have hlo := Cc.H_LUT_POS
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := Cc.H_FB wh (Nat.le_refl _); omega
  have hW : Win lo hi (ex a (fun t => !b t) qp rst) O := by
    rw [← LutFbBridge.exC_eq]; exact Cc.H_LUT_WIN
  have hN : NoRevertI lo hi (ex a (fun t => !b t) qp rst) O := by
    rw [← LutFbBridge.exC_eq]; exact Cc.H_NO_REVERT
  have ntl : ∀ j, cph ρ β j + lo ≤ nt O lo hi (cph ρ β j) (Vph j) := fun j => nt_lo O _ _ hlh
  have cge : ∀ j, R ≤ cph ρ β j := by
    intro j
    induction j with
    | zero => unfold cph; omega
    | succ j ih =>
      have := H_SND j; have := ntl j
      have : ρ (j + 1) ≤ cph ρ β (j + 1) := Nat.le_max_left _ _
      omega
  have gap : ∀ j, cph ρ β j + lo + E ≤ cph ρ β (j + 1) := fun j => by
    have := H_SND j; have := H_RCV j; have := ntl j; unfold cph at *; omega
  match k with
  | 0 =>
    obtain ⟨ha0, hb0⟩ := h0 rfl
    have pre : ∀ s, s < cph ρ β 0 → LutFbBridge.exC a b qp rst s = false := by
      intro s
      induction s using Nat.strongRecOn with
      | _ s ih =>
        intro h
        unfold LutFbBridge.exC; rw [CElemTiming.c2_eq]
        by_cases hs : s < R
        · rw [H_RST s]; simp [hs]
        · obtain ⟨u, hu1, hu2, e⟩ := Cc.H_FB s (by omega)
          obtain ⟨s', q1, q2, q3⟩ := Cc.H_LUT_WIN u (by omega)
          have hq : qp s = false := by rw [e, q3]; exact ih _ (by omega) (by omega)
          rw [hq]
          have hab : a s = false ∨ b s = false := by
            unfold cph at h
            rcases Nat.lt_or_ge s (ρ 0) with h' | h'
            · exact Or.inl (ha0 s (by omega) h')
            · exact Or.inr (hb0 s (by omega) (by omega))
          rcases hab with h' | h' <;> rw [h'] <;> cases rst s <;> cases a s <;> cases b s <;> rfl
    intro t _ ht
    show O t = false
    by_cases hh : t < hi
    · exact H_PWR t hh
    · by_cases h1 : t < cph ρ β 0 + lo
      · obtain ⟨s, s1, s2, s3⟩ := Cc.H_LUT_WIN t (by omega)
        rw [s3]; exact pre s (by omega)
      · have := nt_before O lo hi (cph ρ β 0) (Vph 0) t (by omega) ht
        rw [this, PipeTimed.Vph_even 0]; rfl
  | j + 1 =>
    obtain ⟨ha, hb⟩ := hph j rfl
    have hR := cge j
    have exj := exc_phase_w hW Cc.H_FB (by omega) (Vph j) (ρ j) (ρ (j + 1)) (β j)
      (β (j + 1)) E ha (fun t h1 h2 => by show (!b t) = !Vph j; rw [hb t h1 h2])
      (fun t ht => by rw [H_RST t]; unfold cph at hR; simp; omega)
      (by have := H_SND j; have := ntl j; unfold cph at *; omega)
      (by have := H_RCV j; have := ntl j; unfold cph at *; omega) H_LAT
      (by unfold cph at hR; omega)
    have hsp : cph ρ β j + hi < cph ρ β (j + 1) + lo := by have := gap j; omega
    have nw := node_win (v := Vph j) hW hN (fun s a b => exj s a b)
      (by unfold cph at hR; omega) hsp
    intro t h1 h2
    show O t = Vph j
    by_cases ht : t < cph ρ β (j + 1) + lo
    · exact nw.2.2.1 t h1 ht
    · have := nt_before O lo hi (cph ρ β (j + 1)) (Vph (j + 1)) t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-! ## 4. A chain of links between a source and a sink

Cells `0 .. N+1`: cell `0` is the source, cells `1 .. N` are `bd_link` controllers, cell
`N+1` is the sink. Cell `i`'s node `O i` drives the request pin `req (i+1)` of cell `i+1`
through the forward wire `(wl i, wh i)`, and cell `i+1`'s node drives the acknowledge pin
`ack i` of cell `i` through the backward wire `(vl i, vh i)`. Every edge time is READ OFF
THE TRACES: `τ i j` is the node's `j`-th edge (for a link, `τs` of its own pins, H_TIMES);
the pin edges are `ε` of the driving node's edges. -/

/-- The data of a chain (traces, delays, edge times). -/
structure ChainData where
  N : Nat
  R : Nat
  O : Nat → Nat → Bool
  req : Nat → Nat → Bool
  ack : Nat → Nat → Bool
  qp : Nat → Nat → Bool
  rst : Nat → Bool
  lo : Nat → Nat
  hi : Nat → Nat
  fl : Nat → Nat
  fh : Nat → Nat
  wl : Nat → Nat
  wh : Nat → Nat
  vl : Nat → Nat
  vh : Nat → Nat
  τ : Nat → Nat → Nat

namespace ChainData
variable (D : ChainData)

/-- Edges at the request pin of cell `i+1` (driven by cell `i`). -/
def εF (i : Nat) : Nat → Nat := ε (D.req (i + 1)) (D.wl i) (D.wh i) (D.τ i)
/-- Edges at the acknowledge pin of cell `i` (driven by cell `i+1`). -/
def εB (i : Nat) : Nat → Nat := ε (D.ack i) (D.vl i) (D.vh i) (D.τ (i + 1))
/-- Link `m+1`'s phase-start lists (`Env1`'s `ρ`, `α`). -/
def ρL (m : Nat) : Nat → Nat := D.εF m
def αL (m : Nat) : Nat → Nat := ash D.R (D.εB (m + 1))
/-- Link `m+1`'s derived departure slacks (as `link_link_env`). -/
def Es (m : Nat) : Nat := D.vl m + D.lo m + D.wl m
def Ea (m : Nat) : Nat := D.wl (m + 1) + D.lo (m + 2) + D.vl (m + 1)
/-- Minimum round trip through channel `i` (cells `i`, `i+1`). -/
def RT (i : Nat) : Nat := D.wl i + D.lo (i + 1) + D.vl i + D.lo i

end ChainData

/-- **The gate relations of the chain, and the two ends' assume-guarantee contracts.**
No environment hypothesis on any link: only `Stage`, wires, and the edge-time definitions.
The source and the sink are not modelled as gates; each is given by a contract in
assume-guarantee form (its node's segment `k` holds IF its input pin's earlier segments
hold) plus the statement that it waits at least `lo` for its input pin. -/
structure Chain (D : ChainData) : Prop where
  H_RST : ∀ t, D.rst t = decide (t < D.R)
  /-- links `1..N`: B's `Stage` (Win LUT + H_NO_REVERT + feedback wire), real `bd_c2n`. -/
  H_STAGE : ∀ m, m < D.N → Stage (D.req (m + 1)) (D.ack (m + 1)) D.rst (D.O (m + 1))
    (D.qp (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.fl (m + 1)) (D.fh (m + 1))
  H_PWR : ∀ m, m < D.N → ∀ t, t < D.hi (m + 1) → D.O (m + 1) t = false
  /-- **H_LUT_POS** for every cell (for the ends: the minimum wait). -/
  H_LUT_POS : ∀ i, i ≤ D.N + 1 → 1 ≤ D.lo i
  /-- **H_WIRE** forward and backward. -/
  H_WF : ∀ i, i ≤ D.N → Wire (D.wl i) (D.wh i) (D.O i) (D.req (i + 1))
  H_WB : ∀ i, i ≤ D.N → Wire (D.vl i) (D.vh i) (D.O (i + 1)) (D.ack i)
  /-- **H_TIMES**: link edge times are the node's own edges after its pins' phase starts. -/
  H_TIMES : ∀ m, m < D.N → ∀ j, D.τ (m + 1) j =
    τs (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.ρL m) (D.αL m) j
  /-- **Source contract**: waits for its acknowledge pin; first edge late enough; its
  segment `k` holds if its acknowledge pin's segments `< k` hold. -/
  SRC_WAIT : ∀ j, D.εB 0 j + D.lo 0 ≤ D.τ 0 (j + 1)
  SRC_T0 : D.R ≤ D.τ 0 0 + D.wl 0 ∧ D.wh 0 ≤ D.τ 0 0
  SRC_SEG : ∀ k, (∀ k', k' < k → SegK (D.ack 0) (D.εB 0) k') → SegK (D.O 0) (D.τ 0) k
  /-- **Sink contract**: waits for its request pin; its segment `k` holds if its request
  pin's segments `≤ k` hold. -/
  SNK_WAIT : ∀ j, D.εF D.N j + D.lo (D.N + 1) ≤ D.τ (D.N + 1) j
  SNK_SEG : ∀ k, (∀ k', k' ≤ k → SegK (D.req (D.N + 1)) (D.εF D.N) k') →
    SegK (D.O (D.N + 1)) (D.τ (D.N + 1)) k

/-- **Timing of the chain** (B's `Timing1` per link with the derived `Es`, `Ea`; H_WIRE_R;
H_RT as in `link_link_env`). -/
structure ChainT (D : ChainData) : Prop where
  H_RST_LONG : ∀ m, m < D.N → D.hi (m + 1) + D.fh (m + 1) ≤ D.R
  H_LAT : ∀ m, m < D.N → D.hi (m + 1) + D.fh (m + 1) ≤ D.lo (m + 1) + min (D.Es m) (D.Ea m)
  H_WIRE_R : ∀ i, i ≤ D.N → D.wh i ≤ D.R ∧ D.vh i ≤ D.R
  H_RT : ∀ i, i ≤ D.N → D.wh i ≤ D.RT i ∧ D.vh i ≤ D.RT i

section chain
variable {D : ChainData} (C : Chain D)
include C

theorem c_lh (m : Nat) (hm : m < D.N) : D.lo (m + 1) ≤ D.hi (m + 1) :=
  win_le (C.H_STAGE m hm).H_LUT_WIN

/-- Unconditional: a cell waits for its request pin. -/
theorem c_wF (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.εF i j + D.lo (i + 1) ≤ D.τ (i + 1) j := by
  rcases Nat.lt_or_ge i D.N with h | h
  · rw [C.H_TIMES i h j]
    have := nt_lo (D.O (i + 1)) (cph (D.ρL i) (D.αL i) j) (Vph j) (c_lh C i h)
      (hi := D.hi (i + 1))
    have : D.ρL i j ≤ cph (D.ρL i) (D.αL i) j := Nat.le_max_left _ _
    unfold τs; unfold ChainData.ρL at *; omega
  · have : i = D.N := by omega
    subst this; exact C.SNK_WAIT j

/-- Unconditional: a cell waits for its acknowledge pin. -/
theorem c_wB (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.εB i j + D.lo i ≤ D.τ i (j + 1) := by
  cases i with
  | zero => exact C.SRC_WAIT j
  | succ m =>
    rw [C.H_TIMES m (by omega) (j + 1)]
    have := nt_lo (D.O (m + 1)) (cph (D.ρL m) (D.αL m) (j + 1)) (Vph (j + 1))
      (c_lh C m (by omega)) (hi := D.hi (m + 1))
    have : D.αL m (j + 1) ≤ cph (D.ρL m) (D.αL m) (j + 1) := Nat.le_max_right _ _
    have e : D.αL m (j + 1) = D.εB (m + 1) j := rfl
    unfold τs; omega

theorem c_eF (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.τ i j + D.wl i ≤ D.εF i j :=
  ε_lo (C.H_WF i hi) (D.τ i) j

theorem c_eB (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.τ (i + 1) j + D.vl i ≤ D.εB i j :=
  ε_lo (C.H_WB i hi) (D.τ (i + 1)) j

/-- Unconditional spacing, both ends of channel `i`. -/
theorem c_spL (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.τ i j + D.RT i ≤ D.τ i (j + 1) := by
  have := c_wB C i hi j; have := c_eB C i hi j; have := c_wF C i hi j; have := c_eF C i hi j
  unfold ChainData.RT; omega

theorem c_spR (i : Nat) (hi : i ≤ D.N) (j : Nat) :
    D.τ (i + 1) j + D.RT i ≤ D.τ (i + 1) (j + 1) := by
  have := c_wF C i hi (j + 1); have := c_eF C i hi (j + 1); have := c_wB C i hi j
  have := c_eB C i hi j
  unfold ChainData.RT; omega

theorem c_inc (i : Nat) (hi : i ≤ D.N + 1) (j : Nat) : D.τ i j < D.τ i (j + 1) := by
  rcases Nat.lt_or_ge i (D.N + 1) with h | h
  · have := c_spL C i (by omega) j; have := (C.H_WF i (by omega)).H_POS
    unfold ChainData.RT at *; omega
  · have : i = D.N + 1 := by omega
    subst this
    have := c_spR C D.N (Nat.le_refl _) j; have := (C.H_WF D.N (Nat.le_refl _)).H_POS
    unfold ChainData.RT at *; omega

theorem c_mono (i : Nat) (hi : i ≤ D.N + 1) {j j' : Nat} (h : j ≤ j') : D.τ i j ≤ D.τ i j' := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h' | h'
    · have := ih (by omega); have := c_inc C i hi j'; omega
    · have : j = j' + 1 := by omega
      subst this; exact Nat.le_refl _

theorem c_ge0 (i : Nat) (hi : i ≤ D.N) : D.R < D.τ (i + 1) 0 := by
  induction i with
  | zero =>
    have := c_wF C 0 (by omega) 0; have := c_eF C 0 (by omega) 0; have := C.SRC_T0
    have := C.H_LUT_POS (0 + 1) (by omega); omega
  | succ i ih =>
    have := ih (by omega); have := c_wF C (i + 1) hi 0; have := c_eF C (i + 1) hi 0
    omega

theorem c_geR (i : Nat) (hi : i ≤ D.N) (j : Nat) : D.R < D.τ (i + 1) j := by
  have := c_ge0 C i hi; have := c_mono C (i + 1) (by omega) (Nat.zero_le j); omega

/-- The wire hypotheses of `wire_segK`, forward wire from cell `i`. -/
theorem c_hspF (T : ChainT D) (i : Nat) (hi : i ≤ D.N) (j : Nat) :
    D.wh i ≤ D.τ i j ∧ D.τ i j + D.wh i < D.τ i (j + 1) + D.wl i := by
  have hRT := (T.H_RT i hi).1
  have := c_spL C i hi j; have := (C.H_WF i hi).H_POS
  refine ⟨?_, by omega⟩
  cases i with
  | zero => have := C.SRC_T0; have := c_mono C 0 (by omega) (Nat.zero_le j); omega
  | succ m => have := c_geR C m (by omega) j; have := (T.H_WIRE_R (m + 1) hi).1; omega

/-- The wire hypotheses of `wire_segK`, backward wire into `ack i` from cell `i+1`. -/
theorem c_hspB (T : ChainT D) (i : Nat) (hi : i ≤ D.N) (j : Nat) :
    D.vh i ≤ D.τ (i + 1) j ∧ D.τ (i + 1) j + D.vh i < D.τ (i + 1) (j + 1) + D.vl i := by
  have hRT := (T.H_RT i hi).2
  have := c_spR C i hi j; have := (C.H_WB i hi).H_POS
  have := c_geR C i hi j; have := (T.H_WIRE_R i hi).2
  omega

/-- Link `m+1`: its first request edge comes after reset release (unconditional). -/
theorem c_early (m : Nat) (hm : m < D.N) : D.R ≤ D.ρL m 0 := by
  have := c_eF C m (by omega) 0
  unfold ChainData.ρL
  cases m with
  | zero => have := C.SRC_T0; omega
  | succ m => have := c_geR C m (by omega) 0; omega

/-- Link `m+1`'s H_SND with `Es` (unconditional). -/
theorem c_snd (m : Nat) (hm : m < D.N) (j : Nat) :
    τs (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.ρL m) (D.αL m) j + D.Es m ≤
      D.ρL m (j + 1) := by
  rw [← C.H_TIMES m hm j]
  have := c_eF C m (by omega) (j + 1); have := c_wB C m (by omega) j
  have := c_eB C m (by omega) j
  unfold ChainData.Es ChainData.ρL; omega

/-- Link `m+1`'s H_RCV with `Ea` (unconditional). -/
theorem c_rcv (m : Nat) (hm : m < D.N) (j : Nat) :
    τs (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.ρL m) (D.αL m) j + D.Ea m ≤
      D.αL m (j + 1) := by
  rw [← C.H_TIMES m hm j]
  have := c_eB C (m + 1) (by omega) j; have := c_wF C (m + 1) (by omega) j
  have := c_eF C (m + 1) (by omega) j
  have e : D.αL m (j + 1) = D.εB (m + 1) j := rfl
  have e2 : D.lo (m + 2) = D.lo (m + 1 + 1) := rfl
  unfold ChainData.Ea; omega

end chain

/-! ## 5. The circle, closed: events, guarantees, assumptions -/

/-- **Guarantee of event `(i, k)`**: segment `k` of cell `i`'s node (time `τ i k`, its end). -/
def Gev (D : ChainData) (e : Nat × Nat) : Prop :=
  e.1 ≤ D.N + 1 → SegK (D.O e.1) (D.τ e.1) e.2

/-- **Environment assumption of event `(i, k)`**: the input-pin segments that segment `k`
of cell `i` reads (source: acknowledge segments `< k`; link: request segment `k` and
acknowledge segment `k - 1`; sink: request segments `≤ k`). -/
def Aev (D : ChainData) (e : Nat × Nat) : Prop :=
  (e.1 = 0 → ∀ k', k' < e.2 → SegK (D.ack 0) (D.εB 0) k') ∧
  (∀ m, e.1 = m + 1 → m < D.N → SegK (D.req (m + 1)) (D.εF m) e.2 ∧
      ∀ j, e.2 = j + 1 → SegK (D.ack (m + 1)) (D.εB (m + 1)) j) ∧
  (e.1 = D.N + 1 → ∀ k', k' ≤ e.2 → SegK (D.req (D.N + 1)) (D.εF D.N) k')

section closed
variable {D : ChainData} (C : Chain D) (T : ChainT D)
include C T

/-- **H_CELL** for the chain: every cell meets its contract (links: `link_segK`, PROVED
from `Stage`; ends: their contracts). -/
theorem chain_cell (e : Nat × Nat) (hA : Aev D e) : Gev D e := by
  obtain ⟨i, k⟩ := e
  obtain ⟨a0, a1, a2⟩ := hA
  intro hi
  simp only at a0 a1 a2 hi ⊢
  rcases i with _ | m
  · exact C.SRC_SEG k (a0 rfl)
  · rcases Nat.lt_or_ge m D.N with hm | hm
    · obtain ⟨hr, ha⟩ := a1 m rfl hm
      have hτ : D.τ (m + 1) =
          τs (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1)) (D.ρL m) (D.αL m) :=
        funext (C.H_TIMES m hm)
      rw [hτ]
      refine link_segK (E := min (D.Es m) (D.Ea m)) (C.H_STAGE m hm) C.H_RST
        (T.H_RST_LONG m hm) (T.H_LAT m hm) (C.H_LUT_POS (m + 1) (by omega)) (C.H_PWR m hm)
        rfl (c_early C m hm) (fun j => ?_) (fun j => ?_) k (fun hk t _ ht => ?_)
        (fun j hk => ?_)
      · have := c_snd C m hm j; omega
      · have := c_rcv C m hm j; omega
      · subst hk; exact hr t (Nat.zero_le _) ht
      · subst hk
        refine ⟨fun t h1 h2 => hr t h1 h2, fun t h1 h2 => ?_⟩
        have hs := ha j rfl
        cases j with
        | zero => rw [hs t (Nat.zero_le _) h2]; rfl
        | succ j' => rw [hs t h1 h2, PipeTimed.Vph_succ, Bool.not_not]; rfl
    · have hmN : m = D.N := by omega
      rw [hmN]; exact C.SNK_SEG k (a2 (by omega))

/-- **H_ENV** for the chain, with the causality side condition: each assumption follows
from the guarantees of events at STRICTLY smaller times (the wires carry them, `wire_segK`;
the time inequalities are unconditional consequences of the edge-time definitions and
H_LUT_POS). -/
theorem chain_env (e : Nat × Nat) (ih : ∀ e', D.τ e'.1 e'.2 < D.τ e.1 e.2 → Gev D e') :
    Aev D e := by
  obtain ⟨i, k⟩ := e
  simp only at ih
  simp only [Aev]
  refine ⟨fun hi0 k' hk' => ?_, fun m hi hm => ?_, fun hiN k' hk' => ?_⟩
  · subst hi0
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have t1 := c_mono C (0 + 1) (by omega) (show k' ≤ j by omega)
    have := c_eB C 0 (by omega) j; have := c_wB C 0 (by omega) j
    have := C.H_LUT_POS 0 (by omega)
    have hG := ih (0 + 1, k') (by simp only; omega) (by simp only; omega)
    exact wire_segK (C.H_WB 0 (by omega)) k' hG (fun j _ => c_hspB C T 0 (by omega) j)
  · subst hi
    refine ⟨?_, fun j hk => ?_⟩
    · have := c_wF C m (by omega) k; have := c_eF C m (by omega) k
      have := C.H_LUT_POS (m + 1) (by omega)
      have hG := ih (m, k) (by simp only; omega) (by simp only; omega)
      exact wire_segK (C.H_WF m (by omega)) k hG (fun j _ => c_hspF C T m (by omega) j)
    · subst hk
      have := c_wB C (m + 1) (by omega) j; have := c_eB C (m + 1) (by omega) j
      have := C.H_LUT_POS (m + 1) (by omega)
      have hG := ih (m + 1 + 1, j) (by simp only; omega) (by simp only; omega)
      exact wire_segK (C.H_WB (m + 1) (by omega)) j hG
        (fun j _ => c_hspB C T (m + 1) (by omega) j)
  · subst hiN
    have t1 := c_mono C D.N (by omega) hk'
    have := c_wF C D.N (Nat.le_refl _) k; have := c_eF C D.N (Nat.le_refl _) k
    have := C.H_LUT_POS (D.N + 1) (Nat.le_refl _)
    have hG := ih (D.N, k') (by simp only; omega) (by simp only; omega)
    exact wire_segK (C.H_WF D.N (Nat.le_refl _)) k' hG
      (fun j _ => c_hspF C T D.N (Nat.le_refl _) j)

/-- **The circle closed (all nodes).** By `ag_time` with event time `τ i k`: every node of
the chain is a clean step signal with the edges read off its own trace. -/
theorem chain_nodes (i : Nat) (hi : i ≤ D.N + 1) : Phases (D.O i) (D.τ i) :=
  phases_of_segK fun k =>
    ag_time (fun e : Nat × Nat => D.τ e.1 e.2) (Gev D) (Aev D) (chain_cell C T)
      (chain_env C T) (i, k) hi

theorem chain_reqPin (i : Nat) (hi : i ≤ D.N) : Phases (D.req (i + 1)) (D.εF i) :=
  phases_of_segK fun k => wire_segK (C.H_WF i hi) k (segK_of_phases (chain_nodes C T i (by omega)) k)
    (fun j _ => c_hspF C T i hi j)

theorem chain_ackPin (i : Nat) (hi : i ≤ D.N) : Phases (D.ack i) (D.εB i) :=
  phases_of_segK fun k => wire_segK (C.H_WB i hi) k
    (segK_of_phases (chain_nodes C T (i + 1) (by omega)) k) (fun j _ => c_hspB C T i hi j)

/-- **Every link's `Env1` and `Timing1`, derived** (no environment hypothesis on any link):
the request side with `Es = vl m + lo m + wl m`, the acknowledge side with
`Ea = wl (m+1) + lo (m+2) + vl (m+1)`, exactly `link_link_env`'s slacks. -/
theorem chain_env1 (m : Nat) (hm : m < D.N) :
    Env1 (D.req (m + 1)) (D.ack (m + 1)) D.rst (D.O (m + 1)) (D.lo (m + 1)) (D.hi (m + 1))
      D.R (D.ρL m) (D.αL m) (D.Es m) (D.Ea m) ∧
    Timing1 (D.lo (m + 1)) (D.hi (m + 1)) (D.fh (m + 1)) D.R (D.Es m) (D.Ea m) := by
  have pr := chain_reqPin C T m (by omega)
  have pa := chain_ackPin C T (m + 1) (by omega)
  refine ⟨{ H_RST := C.H_RST
            H_REQ_LOW0 := fun t _ h => pr.pre t h
            H_REQ := pr.ph
            H_ACK0 := rfl
            H_ACK := fun j t h1 h2 => ?_
            H_RST_EARLY := c_early C m hm
            H_SND := c_snd C m hm
            H_RCV := c_rcv C m hm },
    ⟨?_, T.H_RST_LONG m hm, T.H_LAT m hm⟩⟩
  · cases j with
    | zero => rw [pa.pre t h2]; rfl
    | succ j' => rw [pa.ph j' t h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  · have := T.H_RST_LONG m hm; have := c_lh C m hm; have := C.H_LUT_POS (m + 1) (by omega)
    omega

/-- **C's `LutFb`/`FbFirst` premise for every link of the chain, with no environment
hypothesis**: Bfb's `link_lutFb` on the derived `Env1`. -/
theorem chain_lutFb (m : Nat) (hm : m < D.N) :
    Formal.Net.Ops.Gen.LutFb Formal.Net.Ops.Gen.linkF
      (fun t => (D.req (m + 1) t, D.ack (m + 1) t)) (D.qp (m + 1)) (D.O (m + 1)) ∧
    Formal.Net.Ops.Gen.FbFirst (D.qp (m + 1)) (D.O (m + 1)) := by
  obtain ⟨E, Tm⟩ := chain_env1 C T m hm
  exact LutFbBridge.link_lutFb (C.H_STAGE m hm) E Tm (C.H_LUT_POS (m + 1) (by omega))
    (C.H_PWR m hm)

end closed

/-! ## 5b. Rings: a closed network of B's links is dead

Every link of B's model resets to 0 (`bd_c2n`, the real INIT, with `rst`). In any CLOSED
network of such links (each request and acknowledge pin wired from some link's node: a
ring, or any other all-link topology) nothing ever fires, so no link has a four-phase
environment: the closure theorems apply to no ring. A live ring needs a token-holding
(`_set`, RESET_VALUE 1) stage, which B's `Stage` does not model. -/

/-- **A closed all-link network is dead** (every node and pin 0 forever). -/
theorem ring_dead {N R lo hi fl fh wl wh vl vh : Nat} {O req ack qp : Nat → Nat → Bool}
    {rst : Nat → Bool} (p s : Nat → Nat) (hp : ∀ i, i < N → p i < N) (hs : ∀ i, i < N → s i < N)
    (H_RST : ∀ t, rst t = decide (t < R))
    (H_STAGE : ∀ i, i < N → Stage (req i) (ack i) rst (O i) (qp i) lo hi fl fh)
    (H_PWR : ∀ i, i < N → ∀ t, t < hi → O i t = false) (H_LUT_POS : 1 ≤ lo) (H_FB_R : fh ≤ R)
    (H_WF : ∀ i, i < N → Wire wl wh (O (p i)) (req i))
    (H_WB : ∀ i, i < N → Wire vl vh (O (s i)) (ack i)) :
    ∀ t i, i < N → O i t = false ∧ req i t = false ∧ ack i t = false := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro i hi'
    refine ⟨?_, ?_, ?_⟩
    · by_cases h0 : t < hi
      · exact H_PWR i hi' t h0
      · obtain ⟨u, u1, u2, u3⟩ := (H_STAGE i hi').H_LUT_WIN t (by omega)
        rw [u3]; unfold ex; rw [CElemTiming.c2n_eq]
        by_cases hR : u < R
        · rw [H_RST u]; simp [hR]
        · obtain ⟨v, v1, v2, v3⟩ := (H_STAGE i hi').H_FB u (by omega)
          rw [(ih u (by omega) i hi').2.1, (ih u (by omega) i hi').2.2, v3,
            (ih v (by omega) i hi').1]
          cases rst u <;> rfl
    · have W := H_WF i hi'
      by_cases h0 : t < wh
      · exact W.H_PWR t h0
      · obtain ⟨u, u1, u2, u3⟩ := W.H_WIN t (by omega)
        have := W.H_POS
        rw [u3]; exact (ih u (by omega) (p i) (hp i hi')).1
    · have W := H_WB i hi'
      by_cases h0 : t < vh
      · exact W.H_PWR t h0
      · obtain ⟨u, u1, u2, u3⟩ := W.H_WIN t (by omega)
        have := W.H_POS
        rw [u3]; exact (ih u (by omega) (s i) (hs i hi')).1

/-- **So no link of a closed all-link network has `Env1`** (for any phase starts and
slacks). -/
theorem ring_no_env1 {N R lo hi fl fh wl wh vl vh : Nat} {O req ack qp : Nat → Nat → Bool}
    {rst : Nat → Bool} (p s : Nat → Nat) (hp : ∀ i, i < N → p i < N) (hs : ∀ i, i < N → s i < N)
    (H_RST : ∀ t, rst t = decide (t < R))
    (H_STAGE : ∀ i, i < N → Stage (req i) (ack i) rst (O i) (qp i) lo hi fl fh)
    (H_PWR : ∀ i, i < N → ∀ t, t < hi → O i t = false) (H_LUT_POS : 1 ≤ lo) (H_FB_R : fh ≤ R)
    (H_WF : ∀ i, i < N → Wire wl wh (O (p i)) (req i))
    (H_WB : ∀ i, i < N → Wire vl vh (O (s i)) (ack i))
    (i : Nat) (hi' : i < N) (ρ α : Nat → Nat) (Es Ea : Nat) :
    ¬ Env1 (req i) (ack i) rst (O i) lo hi R ρ α Es Ea := by
  intro E
  have dead := ring_dead p s hp hs H_RST H_STAGE H_PWR H_LUT_POS H_FB_R H_WF H_WB
  have hlh := win_le (H_STAGE i hi').H_LUT_WIN
  have h1 := E.H_SND 0
  have h2 := nt_lo (O i) (cph ρ α 0) (Vph 0) hlh (hi := hi)
  have h3 : ρ 0 ≤ cph ρ α 0 := Nat.le_max_left _ _
  unfold τs at h1
  have := E.H_REQ 0 (ρ 0) (Nat.le_refl _) (by omega)
  rw [(dead (ρ 0) i hi').2.1] at this
  exact absurd this (by decide)

/-- Non-vacuity of `ring_dead`/`ring_no_env1`: the one-link ring (`p = s = id`) with every
trace 0 satisfies all their hypotheses (LUT band `[1, 1]`, wires 1, reset 4). -/
theorem ring_witness :
    Stage (fun _ => false) (fun _ => false) PipeTimed.Wit.rstW (fun _ => false) (fun _ => false)
      1 1 1 1 ∧ Wire 1 1 (fun _ => false) (fun _ => false) := by
  have hz : ∀ s, ex (fun _ => false) (fun _ => false) (fun _ => false) PipeTimed.Wit.rstW s = false :=
    fun s => by unfold ex; rw [CElemTiming.c2n_eq]; simp
  refine ⟨⟨fun t ht => ⟨t - 1, by omega, by omega, (hz _).symm⟩, ?_,
    fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, by decide⟩,
    ⟨fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, ?_, by decide, fun _ _ => rfl⟩⟩
  · intro a b v t1 t2 _ _ _ _ _ hv; exact hv
  · intro a b v t1 t2 _ _ _ _ _ hv; exact hv

/-! ## 6. Non-vacuity: a live chain of ANY length `N`, nonzero delays

Cell `i`'s node is the square wave `sq (2i+3)` (phases of 4 ticks); every wire is a 1-tick
delay; every link is B's `Wx.stage_sq` (the real `bd_c2n` excitation through a `Win 1 3`
LUT, a band two ticks wide, and a 1-tick feedback wire). The source and the sink are
square waves too (their contracts hold because their conclusions do). -/

open Formal.Cells.PipeTimed.Wit (sq sq_pre sq_phase rstW)
open Formal.Cells.LutFbBridge2Env (τ4 phases_sq wire_sq eps_sq)

def wD (N : Nat) : ChainData where
  N := N
  R := 4
  O i := sq (2 * i + 3)
  req i := sq (2 * i + 2)
  ack i := sq (2 * i + 6)
  qp i := sq (2 * i + 4)
  rst := rstW
  lo _ := 1
  hi _ := 3
  fl _ := 1
  fh _ := 1
  wl _ := 1
  wh _ := 1
  vl _ := 1
  vh _ := 1
  τ i := τ4 (2 * i + 3)

theorem w_εF (N i j : Nat) : (wD N).εF i j = 2 * i + 4 + 4 * j := by
  show ε (sq (2 * (i + 1) + 2)) 1 1 (τ4 (2 * i + 3)) j = _
  rw [eps_sq (2 * i + 3) _ (by omega)]; try omega

theorem w_εB (N i j : Nat) : (wD N).εB i j = 2 * i + 6 + 4 * j := by
  show ε (sq (2 * i + 6)) 1 1 (τ4 (2 * (i + 1) + 3)) j = _
  rw [eps_sq (2 * (i + 1) + 3) _ (by omega)]; try omega

theorem w_cph (N m j : Nat) : cph ((wD N).ρL m) ((wD N).αL m) j = 2 * m + 4 + 4 * j := by
  unfold cph ChainData.ρL
  cases j with
  | zero =>
    rw [w_εF]; show max (2 * m + 4 + 4 * 0) 4 = _; omega
  | succ j =>
    rw [w_εF]; show max _ ((wD N).εB (m + 1) j) = _; rw [w_εB]; omega

theorem w_chain (N : Nat) : Chain (wD N) where
  H_RST _ := rfl
  H_STAGE m _ := by
    have h := WinFifoCausal.Wx.stage_sq (2 * (m + 1) + 2) (by omega)
    rw [show 2 * (m + 1) + 2 + 4 = 2 * (m + 1) + 6 by omega,
      show 2 * (m + 1) + 2 + 1 = 2 * (m + 1) + 3 by omega,
      show 2 * (m + 1) + 2 + 2 = 2 * (m + 1) + 4 by omega] at h
    exact h
  H_PWR m _ t ht := sq_pre _ t (by show t < 2 * (m + 1) + 3; have : t < 3 := ht; omega)
  H_LUT_POS _ _ := Nat.le_refl 1
  H_WF i _ := wire_sq _ _ (by omega)
  H_WB i _ := wire_sq _ _ (by omega)
  H_TIMES m _ j := by
    show τ4 (2 * (m + 1) + 3) j = nt (sq (2 * (m + 1) + 3)) 1 3 _ (Vph j)
    rw [w_cph, nt_eq (sq (2 * (m + 1) + 3)) (by decide)
      (sq_phase (2 * (m + 1) + 3) j _ (by omega) (by omega))]
    unfold τ4; omega
  SRC_WAIT j := by
    rw [w_εB]; show 2 * 0 + 6 + 4 * j + 1 ≤ τ4 (2 * 0 + 3) (j + 1); unfold τ4; omega
  SRC_T0 := by show 4 ≤ τ4 (2 * 0 + 3) 0 + 1 ∧ 1 ≤ τ4 (2 * 0 + 3) 0; unfold τ4; omega
  SRC_SEG k _ := segK_of_phases (phases_sq (2 * 0 + 3)) k
  SNK_WAIT j := by
    rw [w_εF]; show 2 * N + 4 + 4 * j + 1 ≤ τ4 (2 * (N + 1) + 3) j; unfold τ4; omega
  SNK_SEG k _ := segK_of_phases (phases_sq (2 * (N + 1) + 3)) k

theorem w_chainT (N : Nat) : ChainT (wD N) where
  H_RST_LONG _ _ := by show 3 + 1 ≤ 4; decide
  H_LAT _ _ := by show 3 + 1 ≤ 1 + min (1 + 1 + 1) (1 + 1 + 1); decide
  H_WIRE_R _ _ := by show 1 ≤ 4 ∧ 1 ≤ 4; decide
  H_RT _ _ := by show 1 ≤ 1 + 1 + 1 + 1 ∧ 1 ≤ 1 + 1 + 1 + 1; decide

/-- **Non-vacuity of `chain_env1`/`chain_lutFb`, every length `N`**: all hypotheses hold
on a live run with nonzero delays (LUT band `[1, 3]`, wires 1), H_LAT is met with
EQUALITY (`hi + fh = 4 = lo + min Es Ea`), and so are the derived departure slacks
(`τ_{m+1} j + Es = ρ (j+1)`). -/
theorem chain_witness (N : Nat) :
    Chain (wD N) ∧ ChainT (wD N) ∧
    (∀ m, (wD N).hi (m + 1) + (wD N).fh (m + 1) =
      (wD N).lo (m + 1) + min ((wD N).Es m) ((wD N).Ea m)) ∧
    (∀ m j, (wD N).τ (m + 1) j + (wD N).Es m = (wD N).ρL m (j + 1)) ∧
    (∀ m j, (wD N).τ (m + 1) j + (wD N).Ea m = (wD N).αL m (j + 1)) := by
  refine ⟨w_chain N, w_chainT N, fun _ => rfl, fun m j => ?_, fun m j => ?_⟩
  · show τ4 (2 * (m + 1) + 3) j + 3 = (wD N).εF m (j + 1)
    rw [w_εF]; unfold τ4; omega
  · show τ4 (2 * (m + 1) + 3) j + 3 = (wD N).εB (m + 1) j
    rw [w_εB]; unfold τ4; omega

end Formal.Cells.AssumeGuaranteeLinks
