import Formal.Cells.AssumeGuaranteeLinks
import Formal.Net.Ring

/-!
# Probe Bring (shard B), part 1: the `_set` stage and the frozen ring

`AssumeGuaranteeLinks.ring_dead` proved that any closed all-link network of B's reset-0
links is 0 forever, and named what a live ring needs: a stage that comes up HOLDING a
token, `bd_c2n_set` (`cells/rtl/bd_ce.v`, INIT `0xFFB2_FFB2_FFB2_FFB2`, `q = rst + C(a,~b)`).
This file models that stage and proves its per-segment contract, then generalises
`ring_dead` to every ring of mixed reset polarities.

## Assumed / proved / NOT covered

**Assumed** (named fields):
* `SetStage`: B's `Stage` with the real `bd_c2n_set` INIT (`CElemFn.INIT_c2n_set`, read by
  `lutB` exactly as `PipeTimed.ex` reads `bd_c2n`): H_LUT_WIN (shard A's window channel
  `Win`), H_NO_REVERT, H_FB (feedback wire), H_LOOP_POS;
* power-up: the node shows its reset value before the LUT's first sure read (H_PWR, the
  same convention as B's reset-0 `Stage`, where H_PWR is "0 before `hi`");
* `WireB`: B's `Wire` whose pin powers up at its DRIVER's reset value.

**Proved:**
* `exS_dual`: the `_set` INIT is the `bd_c2n` INIT under complement of all three data pins
  and the output (`!c2n_set(a,b,q,r) = c2n(!a,!b,!q,r)`), by `decide` on the verbatim INITs;
  hence `setStage_norm`: a `SetStage` IS a reset-0 `Stage` of the complemented traces;
* `link_segK'`: `link_segK` with a general first acknowledge phase (`α 0 ≥ R`, not `= R`)
  and the exact pre-phase condition of the real INIT (request low OR acknowledge high);
* `set_segK` (the `_set` stage's per-segment contract, the form of `link_segK`): the node
  is `!vW k` on segment `k` (1 first, then 0, 1, ...), given the pins at the complemented
  phase levels; `set_phases`: its whole k-token train; `set_reset_hold`: the node is 1 on
  `[hi, R + lo)` whatever its pins do, i.e. it offers its initial token at reset release;
* `ring_frozen`: ANY ring of reset-0 and `_set` stages (any delays, any power-up of the
  feedback) whose reset pattern `b` has no C-excited stage (`Ring.excited`) is frozen at `b`
  forever; `ring_frozen_D`: this is the case whenever `N ≤ 2` or `¬ (0 < D < N)` (C's
  `dead_of_le_two`, `live_iff`); `ring_dead'` (all stages reset-0) and `ring2_dead` (every
  2-stage ring, any polarities: the (4) counter-run is "dead", for every trace) follow.

**NOT covered:** the `bd_c2_set` cell (only `bd_c2n_set`); X power-up (B's `Stage`
convention: Boolean traces). Core Lean only.
-/

namespace Formal.Cells.RingPhys
open Formal.Cells Formal.Net
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_before node_win exc_phase_w Stage cph τs
  cW vW)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2Env (Wire)
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK segK_of_phases)

/-! ## 1. Complement, and the `_set` INIT -/

/-- `xr c P`: the trace `P`, complemented iff `c`. -/
def xr (c : Bool) (P : Nat → Bool) : Nat → Bool := fun t => cond c (!P t) (P t)

/-- The `bd_c2n_set` excitation (real INIT, `I0=a I1=b I2=q I3=rst`). -/
def exS (req ack qp rst : Nat → Bool) (t : Nat) : Bool :=
  CElemTiming.exc CElemFn.INIT_c2n_set (req t) (ack t) (qp t) (rst t)

theorem c2nset_eq (a b q r : Bool) :
    CElemTiming.exc CElemFn.INIT_c2n_set a b q r = (r || ((a && !b) || (a && q) || (!b && q))) := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- **Duality of the two link INITs**: `!c2n_set(a,b,q,r) = c2n(!a,!b,!q,r)`. -/
theorem exS_dual (a b q r : Bool) :
    (!CElemTiming.exc CElemFn.INIT_c2n_set a b q r) =
      CElemTiming.exc CElemTiming.INIT_c2n (!a) (!b) (!q) r := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- Run mode (`rst = 0`) of both INITs is C's `Ring.ctl`. -/
theorem c2n_ctl (a b q : Bool) : CElemTiming.exc CElemTiming.INIT_c2n a b q false = Ring.ctl a b q := by
  cases a <;> cases b <;> cases q <;> decide
theorem c2nset_ctl (a b q : Bool) :
    CElemTiming.exc CElemFn.INIT_c2n_set a b q false = Ring.ctl a b q := by
  cases a <;> cases b <;> cases q <;> decide

theorem win_neg {lo hi : Nat} {x y : Nat → Bool} (h : Win lo hi x y) :
    Win lo hi (xr true x) (xr true y) := by
  intro t ht
  obtain ⟨s, h1, h2, e⟩ := h t ht
  exact ⟨s, h1, h2, by show (!y t) = !x s; rw [e]⟩

theorem nr_neg {lo hi : Nat} {x y : Nat → Bool} (h : NoRevertI lo hi x y) :
    NoRevertI lo hi (xr true x) (xr true y) := by
  intro a b v t1 t2 hab h0 h1 h12 h2 hv
  have e := h a b (!v) t1 t2 (fun s s1 s2 => by
      have := hab s s1 s2; simp only [xr, Bool.cond_true] at this; rw [← this, Bool.not_not])
    h0 h1 h12 h2 (by simp only [xr, Bool.cond_true] at hv; rw [← hv, Bool.not_not])
  show (!y t2) = v; rw [e, Bool.not_not]

theorem wd_neg {lo hi : Nat} {x y : Nat → Bool} (h : CElemTiming.WinDelay lo hi x y) :
    CElemTiming.WinDelay lo hi (xr true x) (xr true y) := win_neg h

/-! ## 2. The `_set` stage -/

/-- **The gate relations of one `bd_c2n_set` controller** (B's `Stage` with the `_set`
INIT). -/
structure SetStage (req ack rst O qp : Nat → Bool) (lo hi wl wh : Nat) : Prop where
  /-- **H_LUT_WIN**: the LUT is a window channel of the real `bd_c2n_set` excitation. -/
  H_LUT_WIN : Win lo hi (exS req ack qp rst) O
  /-- **H_NO_REVERT** (intrinsic). -/
  H_NO_REVERT : NoRevertI lo hi (exS req ack qp rst) O
  /-- **H_FB**: feedback wire `O → I2`. -/
  H_FB : CElemTiming.WinDelay wl wh O qp
  H_LOOP_POS : 1 ≤ lo + wl

theorem exS_norm (req ack qp rst : Nat → Bool) :
    xr true (exS req ack qp rst) = ex (xr true req) (xr true ack) (xr true qp) rst := by
  funext t; exact exS_dual _ _ _ _

/-- **A `_set` stage is a reset-0 `Stage` of the complemented traces.** -/
theorem setStage_norm {req ack rst O qp : Nat → Bool} {lo hi wl wh : Nat}
    (S : SetStage req ack rst O qp lo hi wl wh) :
    Stage (xr true req) (xr true ack) rst (xr true O) (xr true qp) lo hi wl wh := by
  have hW := win_neg S.H_LUT_WIN
  have hN := nr_neg S.H_NO_REVERT
  rw [exS_norm] at hW hN
  exact ⟨hW, hN, wd_neg S.H_FB, S.H_LOOP_POS⟩

/-- A stage of either reset polarity: `b = true` is `bd_c2n_set`, `false` is `bd_c2n`. -/
def StageB (b : Bool) (req ack rst O qp : Nat → Bool) (lo hi wl wh : Nat) : Prop :=
  cond b (SetStage req ack rst O qp lo hi wl wh) (Stage req ack rst O qp lo hi wl wh)

theorem stageB_norm {b : Bool} {req ack rst O qp : Nat → Bool} {lo hi wl wh : Nat}
    (S : StageB b req ack rst O qp lo hi wl wh) :
    Stage (xr b req) (xr b ack) rst (xr b O) (xr b qp) lo hi wl wh := by
  cases b
  · exact S
  · exact setStage_norm S

/-- **A wire whose pin powers up at its driver's reset value `b0`** (B's `Wire` has
`b0 = false`). -/
structure WireB (b0 : Bool) (wl wh : Nat) (O P : Nat → Bool) : Prop where
  H_WIN : Win wl wh O P
  H_NO_REVERT : NoRevertI wl wh O P
  H_POS : 1 ≤ wl
  H_PWR : ∀ t, t < wh → P t = b0

theorem wireB_norm {b0 : Bool} {wl wh : Nat} {O P : Nat → Bool} (W : WireB b0 wl wh O P) :
    Wire wl wh (xr b0 O) (xr b0 P) := by
  cases b0
  · exact ⟨W.H_WIN, W.H_NO_REVERT, W.H_POS, W.H_PWR⟩
  · exact ⟨win_neg W.H_WIN, nr_neg W.H_NO_REVERT, W.H_POS,
      fun t ht => by show (!P t) = false; rw [W.H_PWR t ht]; rfl⟩

/-! ## 3. The link segment lemma with a general first acknowledge phase -/

/-- **Link controller, one segment, general form.** As `AssumeGuaranteeLinks.link_segK`,
but the first acknowledge phase may start after reset release (`R ≤ α 0`), and before the
first phase start `cph ρ α 0` the pins need only satisfy the real INIT's hold condition:
request low OR acknowledge high (then `c2n(a, b, 0, 0) = a ∧ ¬b = 0`). In a ring this is
the stage whose downstream neighbour is a `_set` stage (its acknowledge is high at reset
release). -/
theorem link_segK' {req ack rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ α : Nat → Nat}
    (S : Stage req ack rst O qp lo hi wl wh) (H_RST : ∀ t, rst t = decide (t < R))
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_LUT_POS : 1 ≤ lo)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_RST_EARLY : R ≤ ρ 0 ∧ R ≤ α 0)
    (H_SND : ∀ j, τs O lo hi ρ α j + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, τs O lo hi ρ α j + E ≤ α (j + 1)) (k : Nat)
    (hpre : k = 0 → ∀ t, R ≤ t → t < cph ρ α 0 → req t = false ∨ ack t = true)
    (hph : ∀ j, k = j + 1 →
      (∀ t, ρ j ≤ t → t < ρ (j + 1) → req t = Vph j) ∧
      (∀ t, α j ≤ t → t < α (j + 1) → ack t = !Vph j)) :
    SegK O (τs O lo hi ρ α) k := by
  have hlh := win_le S.H_LUT_WIN
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := S.H_FB wh (Nat.le_refl _); omega
  have ntl : ∀ j, cph ρ α j + lo ≤ τs O lo hi ρ α j := fun j => nt_lo O _ _ hlh
  obtain ⟨hE1, hE2⟩ := H_RST_EARLY
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
    have pre : ∀ s, s < cph ρ α 0 → ex req ack qp rst s = false := by
      intro s
      induction s using Nat.strongRecOn with
      | _ s ih =>
        intro h
        unfold ex; rw [CElemTiming.c2n_eq]
        by_cases hs : s < R
        · rw [H_RST s]; simp [hs]
        · obtain ⟨u, hu1, hu2, e⟩ := S.H_FB s (by omega)
          obtain ⟨s', q1, q2, q3⟩ := S.H_LUT_WIN u (by omega)
          have hq : qp s = false := by rw [e, q3]; exact ih _ (by omega) (by omega)
          rw [hq, rlo s (by omega)]
          rcases hpre rfl s (by omega) h with h' | h' <;> rw [h'] <;> cases req s <;>
            cases ack s <;> rfl
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

/-! ## 4. The `_set` stage's contract -/

/-- **The `_set` stage, one segment** (real `bd_c2n_set` INIT): the node shows `!vW k` on
segment `k` (segment 0, up to the first edge, is HIGH: the initial token; the first edge is
a FALL). Edges `τs` of the complemented node. Pins at the complemented phase levels:
before the first phase start, request high OR acknowledge low (the INIT holds 1); in phase
`j`, request `!Vph j` and acknowledge `Vph j`. -/
theorem set_segK {req ack rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ α : Nat → Nat}
    (S : SetStage req ack rst O qp lo hi wl wh) (H_RST : ∀ t, rst t = decide (t < R))
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_LUT_POS : 1 ≤ lo)
    (H_PWR : ∀ t, t < hi → O t = true)
    (H_RST_EARLY : R ≤ ρ 0 ∧ R ≤ α 0)
    (H_SND : ∀ j, τs (xr true O) lo hi ρ α j + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, τs (xr true O) lo hi ρ α j + E ≤ α (j + 1)) (k : Nat)
    (hpre : k = 0 → ∀ t, R ≤ t → t < cph ρ α 0 → req t = true ∨ ack t = false)
    (hph : ∀ j, k = j + 1 →
      (∀ t, ρ j ≤ t → t < ρ (j + 1) → req t = !Vph j) ∧
      (∀ t, α j ≤ t → t < α (j + 1) → ack t = Vph j)) :
    SegK (xr true O) (τs (xr true O) lo hi ρ α) k :=
  link_segK' (setStage_norm S) H_RST H_RST_LONG H_LAT H_LUT_POS
    (fun t ht => by show (!O t) = false; rw [H_PWR t ht]; rfl) H_RST_EARLY H_SND H_RCV k
    (fun hk t h1 h2 => by
      rcases hpre hk t h1 h2 with h | h
      · left; show (!req t) = false; rw [h]; rfl
      · right; show (!ack t) = true; rw [h]; rfl)
    (fun j hk => by
      obtain ⟨hr, ha⟩ := hph j hk
      exact ⟨fun t h1 h2 => by show (!req t) = _; rw [hr t h1 h2, Bool.not_not],
        fun t h1 h2 => by show (!ack t) = _; rw [ha t h1 h2]⟩)

/-- **The `_set` stage's whole train** (k tokens): its complemented node is a clean step
signal, i.e. the node is 1 until its first edge, then alternates at the edges `τs`. -/
theorem set_phases {req ack rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ α : Nat → Nat}
    (S : SetStage req ack rst O qp lo hi wl wh) (H_RST : ∀ t, rst t = decide (t < R))
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_LUT_POS : 1 ≤ lo)
    (H_PWR : ∀ t, t < hi → O t = true)
    (H_RST_EARLY : R ≤ ρ 0 ∧ R ≤ α 0)
    (H_SND : ∀ j, τs (xr true O) lo hi ρ α j + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, τs (xr true O) lo hi ρ α j + E ≤ α (j + 1))
    (hpre : ∀ t, R ≤ t → t < cph ρ α 0 → req t = true ∨ ack t = false)
    (hph : ∀ j,
      (∀ t, ρ j ≤ t → t < ρ (j + 1) → req t = !Vph j) ∧
      (∀ t, α j ≤ t → t < α (j + 1) → ack t = Vph j)) :
    Phases (xr true O) (τs (xr true O) lo hi ρ α) :=
  phases_of_segK fun k => set_segK S H_RST H_RST_LONG H_LAT H_LUT_POS H_PWR H_RST_EARLY H_SND
    H_RCV k (fun _ => hpre) (fun j _ => hph j)

/-- **The `_set` stage offers its token at reset release**: whatever its pins and feedback
do, its node is 1 from the LUT's first sure read up to `R + lo` (the LUT reads only reset
values). -/
theorem set_reset_hold {req ack rst O qp : Nat → Bool} {lo hi wl wh R : Nat}
    (S : SetStage req ack rst O qp lo hi wl wh) (H_RST : ∀ t, rst t = decide (t < R)) :
    ∀ t, hi ≤ t → t < R + lo → O t = true := by
  intro t h1 h2
  obtain ⟨s, s1, s2, e⟩ := S.H_LUT_WIN t h1
  rw [e]; unfold exS; rw [c2nset_eq, H_RST s]; simp; omega

/-! ## 5. Frozen rings -/

open Formal.Net.Ring (prv nxt excited)

/-- **A ring with no C-excited stage at reset is frozen** (any delays, any polarities).
Stage `i` (`bd_c2n` if `b i = false`, `bd_c2n_set` if `b i = true`) reads its request from
node `prv i` and its acknowledge from node `nxt i` (tb_ring's wiring, C's `Ring.gate`). If
no stage is excited in the reset pattern `b` (C's `Ring.excited`), every node and pin keeps
its reset value forever. -/
theorem ring_frozen {N R : Nat} {lo hi fl fh wl wh vl vh : Nat → Nat}
    {O req ack qp : Nat → Nat → Bool} {rst : Nat → Bool} (b : Nat → Bool)
    (H_RST : ∀ t, rst t = decide (t < R))
    (H_STAGE : ∀ i, i < N → StageB (b i) (req i) (ack i) rst (O i) (qp i) (lo i) (hi i) (fl i) (fh i))
    (H_PWR : ∀ i, i < N → ∀ t, t < hi i → O i t = b i)
    (H_FB_R : ∀ i, i < N → fh i ≤ R) (H_LUT_POS : ∀ i, i < N → 1 ≤ lo i)
    (H_WF : ∀ i, i < N → WireB (b (prv N i)) (wl i) (wh i) (O (prv N i)) (req i))
    (H_WB : ∀ i, i < N → WireB (b (nxt N i)) (vl i) (vh i) (O (nxt N i)) (ack i))
    (H_NE : ∀ i, i < N → ¬ excited N b i) :
    ∀ t i, i < N → O i t = b i ∧ req i t = b (prv N i) ∧ ack i t = b (nxt N i) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro i hi'
    have hctl : Ring.ctl (b (prv N i)) (b (nxt N i)) (b i) = b i := by
      apply Classical.byContradiction; intro h; exact H_NE i hi' ⟨hi', h⟩
    have hpl := Ring.prv_lt hi'
    have hnl := Ring.nxt_lt hi'
    refine ⟨?_, ?_, ?_⟩
    · by_cases h0 : t < hi i
      · exact H_PWR i hi' t h0
      · have S := H_STAGE i hi'
        cases hb : b i
        · rw [hb] at S
          change Stage _ _ _ _ _ _ _ _ _ at S
          obtain ⟨u, u1, u2, u3⟩ := S.H_LUT_WIN t (by omega)
          have hlp := H_LUT_POS i hi'
          rw [u3]; unfold ex
          by_cases hR : u < R
          · rw [CElemTiming.c2n_eq, H_RST u]; simp [hR]
          · obtain ⟨v, v1, v2, v3⟩ := S.H_FB u (by have := H_FB_R i hi'; omega)
            rw [H_RST u, show decide (u < R) = false by simp; omega, (ih u (by omega) i hi').2.1,
              (ih u (by omega) i hi').2.2, v3, (ih v (by omega) i hi').1, c2n_ctl, hctl, hb]
        · rw [hb] at S
          change SetStage _ _ _ _ _ _ _ _ _ at S
          obtain ⟨u, u1, u2, u3⟩ := S.H_LUT_WIN t (by omega)
          have hlp := H_LUT_POS i hi'
          rw [u3]; unfold exS
          by_cases hR : u < R
          · rw [c2nset_eq, H_RST u]; simp [hR]
          · obtain ⟨v, v1, v2, v3⟩ := S.H_FB u (by have := H_FB_R i hi'; omega)
            rw [H_RST u, show decide (u < R) = false by simp; omega, (ih u (by omega) i hi').2.1,
              (ih u (by omega) i hi').2.2, v3, (ih v (by omega) i hi').1, c2nset_ctl, hctl, hb]
    · have W := H_WF i hi'
      by_cases h0 : t < wh i
      · exact W.H_PWR t h0
      · obtain ⟨u, u1, u2, u3⟩ := W.H_WIN t (by omega)
        have := W.H_POS
        rw [u3]; exact (ih u (by omega) (prv N i) hpl).1
    · have W := H_WB i hi'
      by_cases h0 : t < vh i
      · exact W.H_PWR t h0
      · obtain ⟨u, u1, u2, u3⟩ := W.H_WIN t (by omega)
        have := W.H_POS
        rw [u3]; exact (ih u (by omega) (nxt N i) hnl).1

/-- **When the reset pattern has no excited stage**: exactly when `N ≤ 2`, or the wavefront
count `D` (twice C's loop-token count) is `0` or `N` (C's `dead_of_le_two`, `live_iff`). -/
theorem no_excited_of {N : Nat} (b : Nat → Bool)
    (h : N ≤ 2 ∨ ¬ (0 < Ring.D N b ∧ Ring.D N b < N)) : ∀ i, i < N → ¬ excited N b i := by
  intro i _ he
  rcases h with h | h
  · exact Ring.dead_of_le_two h b i he
  · by_cases h3 : 3 ≤ N
    · exact h (Ring.D_of_live h3 he)
    · exact Ring.dead_of_le_two (by omega) b i he

/-- **A ring outside the token/bubble condition is frozen, physically** (every trace, every
delay): `N ≤ 2`, or `D ∈ {0, N}` (no token, or no bubble). -/
theorem ring_frozen_D {N R : Nat} {lo hi fl fh wl wh vl vh : Nat → Nat}
    {O req ack qp : Nat → Nat → Bool} {rst : Nat → Bool} (b : Nat → Bool)
    (H_RST : ∀ t, rst t = decide (t < R))
    (H_STAGE : ∀ i, i < N → StageB (b i) (req i) (ack i) rst (O i) (qp i) (lo i) (hi i) (fl i) (fh i))
    (H_PWR : ∀ i, i < N → ∀ t, t < hi i → O i t = b i)
    (H_FB_R : ∀ i, i < N → fh i ≤ R) (H_LUT_POS : ∀ i, i < N → 1 ≤ lo i)
    (H_WF : ∀ i, i < N → WireB (b (prv N i)) (wl i) (wh i) (O (prv N i)) (req i))
    (H_WB : ∀ i, i < N → WireB (b (nxt N i)) (vl i) (vh i) (O (nxt N i)) (ack i))
    (h : N ≤ 2 ∨ ¬ (0 < Ring.D N b ∧ Ring.D N b < N)) :
    ∀ t i, i < N → O i t = b i :=
  fun t i hi' => (ring_frozen b H_RST H_STAGE H_PWR H_FB_R H_LUT_POS H_WF H_WB (no_excited_of b h) t i hi').1

/-- **(4) The 2-stage ring is dead, for every trace** (either polarity of either stage, any
delays): both nodes keep their reset values forever. In particular `bd_c2n_set` + `bd_c2n`
(one token) never moves: a dead counter-run, not a hazard. -/
theorem ring2_dead {R : Nat} {lo hi fl fh wl wh vl vh : Nat → Nat}
    {O req ack qp : Nat → Nat → Bool} {rst : Nat → Bool} (b : Nat → Bool)
    (H_RST : ∀ t, rst t = decide (t < R))
    (H_STAGE : ∀ i, i < 2 → StageB (b i) (req i) (ack i) rst (O i) (qp i) (lo i) (hi i) (fl i) (fh i))
    (H_PWR : ∀ i, i < 2 → ∀ t, t < hi i → O i t = b i)
    (H_FB_R : ∀ i, i < 2 → fh i ≤ R) (H_LUT_POS : ∀ i, i < 2 → 1 ≤ lo i)
    (H_WF : ∀ i, i < 2 → WireB (b (prv 2 i)) (wl i) (wh i) (O (prv 2 i)) (req i))
    (H_WB : ∀ i, i < 2 → WireB (b (nxt 2 i)) (vl i) (vh i) (O (nxt 2 i)) (ack i)) :
    ∀ t i, i < 2 → O i t = b i :=
  ring_frozen_D b H_RST H_STAGE H_PWR H_FB_R H_LUT_POS H_WF H_WB (Or.inl (Nat.le_refl 2))

/-- `ring_dead` of `AssumeGuaranteeLinks` (all stages reset-0) as an instance. -/
theorem ring_dead' {N R : Nat} {lo hi fl fh wl wh vl vh : Nat → Nat}
    {O req ack qp : Nat → Nat → Bool} {rst : Nat → Bool}
    (H_RST : ∀ t, rst t = decide (t < R))
    (H_STAGE : ∀ i, i < N → Stage (req i) (ack i) rst (O i) (qp i) (lo i) (hi i) (fl i) (fh i))
    (H_PWR : ∀ i, i < N → ∀ t, t < hi i → O i t = false)
    (H_FB_R : ∀ i, i < N → fh i ≤ R) (H_LUT_POS : ∀ i, i < N → 1 ≤ lo i)
    (H_WF : ∀ i, i < N → WireB false (wl i) (wh i) (O (prv N i)) (req i))
    (H_WB : ∀ i, i < N → WireB false (vl i) (vh i) (O (nxt N i)) (ack i)) :
    ∀ t i, i < N → O i t = false :=
  ring_frozen (fun _ => false) H_RST H_STAGE H_PWR H_FB_R H_LUT_POS H_WF H_WB
    (fun i _ he => by
      rw [Ring.excited_iff] at he; exact he.2.1 rfl)
    |> fun h t i hi' => (h t i hi').1

/-- Non-vacuity of `ring_frozen`/`ring2_dead`: the 2-stage ring `bd_c2n_set` + `bd_c2n`
with constant traces (node 0 high, node 1 low, pins and feedback at the driver's value)
satisfies every hypothesis (LUT band `[1, 1]`, wires and feedback 1, reset 4). -/
theorem ring2_witness :
    SetStage (fun _ => false) (fun _ => false) PipeTimed.Wit.rstW (fun _ => true) (fun _ => true)
      1 1 1 1 ∧
    Stage (fun _ => true) (fun _ => true) PipeTimed.Wit.rstW (fun _ => false) (fun _ => false)
      1 1 1 1 ∧
    WireB true 1 1 (fun _ => true) (fun _ => true) ∧
    WireB false 1 1 (fun _ => false) (fun _ => false) := by
  have hs : ∀ s, exS (fun _ => false) (fun _ => false) (fun _ => true) PipeTimed.Wit.rstW s = true :=
    fun s => by unfold exS; rw [c2nset_eq]; simp
  have hz : ∀ s, ex (fun _ => true) (fun _ => true) (fun _ => false) PipeTimed.Wit.rstW s = false :=
    fun s => by unfold ex; rw [CElemTiming.c2n_eq]; simp
  refine ⟨⟨fun t ht => ⟨t - 1, by omega, by omega, (hs _).symm⟩, ?_,
      fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, by decide⟩,
    ⟨fun t ht => ⟨t - 1, by omega, by omega, (hz _).symm⟩, ?_,
      fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, by decide⟩,
    ⟨fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, ?_, by decide, fun _ _ => rfl⟩,
    ⟨fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, ?_, by decide, fun _ _ => rfl⟩⟩
  · intro a b v t1 t2 _ _ _ _ _ hv; exact hv
  · intro a b v t1 t2 _ _ _ _ _ hv; exact hv
  · intro a b v t1 t2 _ _ _ _ _ hv; exact hv
  · intro a b v t1 t2 _ _ _ _ _ hv; exact hv

end Formal.Cells.RingPhys
