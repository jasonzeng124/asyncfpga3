import Formal.Cells.WinFifo
import Formal.Cells.PipeTimed

/-!
# Probe Bex: the causal induction that discharges H_EX_CLEAN for `bd_link_ctl`

Probe Bw (`WinFifo`) reduced every B FIFO hypothesis, on a CLEAN input with
spacing `H_SPREAD_PULSE`, to shard A's window channel `Win` plus
`H_NO_REVERT`. Its instance `ctl_of_win` (the `bd_link_ctl` LUT) still took
the excitation's cleanliness (`H_EX_CLEAN`) and the loop spacing (`H_LOOP`)
as inputs. This file closes that loop: the node's edge times are DEFINED
from the node trace itself (`nt`: first instant after `c + lo` at which the
node shows the phase value), and

* `exc_phase_w`, `exc_pre_w`: the excitation is clean phase by phase using
  ONLY the window channel (`Win`) for the LUT and the feedback wire (the
  proof of `PipeTimed.exc_phase` never used FIFO);
* `node_win`: through a `Win` LUT with `H_NO_REVERT` (stated intrinsically,
  `NoRevertI`: no reference to edge indices) the node is a clean step
  signal with edges `nt`;
* single stage (`stage_fifo`): with a four-phase environment whose
  departures are measured from the node's own edges, the excitation is
  clean from time 0, `H_LOOP` holds for every edge with `D = min Es Ea`,
  `H_BAND` is IMPLIED by `H_LAT` + `H_LOOP_POS`, and there is a FIFO
  read-time map making the run a `PipeTimed.Ctl` with band `[lo, hi]`
  whose `fst` is exactly the node edge times;
* two-stage pipe (`pipe_fifo`): the same causal induction, interleaved
  across the two stages exactly as `PipeTimed.pipe_ctl`, with Win LUTs.
  Its conclusion is a `PipeTimed.P2` (with the derived FIFO LUT maps) that
  satisfies `Gates2`, `Env2`, `Timing2` of `PipeTimed` with the SAME
  environment times: every PipeTimed theorem then holds for the run.

* non-vacuity (`Wx.witness`, `Wx.witness_fifo`, `Wx.witness1`): live runs
  with LUT band `[1, 3]` (two ticks wide, where `Win ⊄ FIFO`), the single
  stage with junk request/acknowledge before reset release; necessity
  (`Wx.no_revert_needed`): the single-stage witness with ONE in-zone node
  glitch satisfies every other hypothesis and no FIFO read with `hi ≤ 5`
  reproduces it.

Not covered: the request/acknowledge LINES of the pipe stay FIFO read maps
(as in `PipeTimed.Gates2`); general `N`; per-pin LUT arcs (the LUT reads the
lumped excitation, as in `PipeTimed`).

Reset: every hypothesis on the environment's pins starts at reset release
`R > 0`; before `R` the pins (and the feedback) are arbitrary. The
excitation is still clean from time 0 because reset forces it to 0, so
the bridge's "clean from 0" premise costs nothing here.

Core Lean only.
-/

namespace Formal.Cells.WinFifoCausal
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace ex Ctl Vph lfind lfind_le lfind_spec lfind_min)
open Formal.Cells.WinFifo (Win Clean Spread NoRevert win_le)

/-! ## 1. Generic lemmas -/

/-- **H_NO_REVERT, intrinsic form** (no edge indices): if the channel's
input holds `v` on `[a, b)`, and the output shows `v` at some `t1 ≥ a + lo`,
it keeps `v` until `b + lo`. On a clean input with `H_SPREAD_PULSE` this is
implied by any FIFO read of band `[lo, hi]` (`noRevertI_of_ret`), and it
implies Bw's `NoRevert` (`noRevert_of_I`). -/
def NoRevertI (lo hi : Nat) (x y : Trace) : Prop :=
  ∀ (a b : Nat) (v : Bool) (t1 t2 : Nat), (∀ s, a ≤ s → s < b → x s = v) →
    hi ≤ t1 → a + lo ≤ t1 → t1 ≤ t2 → t2 < b + lo → y t1 = v → y t2 = v

/-- **Node edge time**: the first instant `≥ c + lo` at which `O` shows `v`
(searched up to `c + hi`; `c + hi + 1` if none). -/
def nt (O : Trace) (lo hi c : Nat) (v : Bool) : Nat :=
  lfind (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1)

theorem lfind_eq (p : Nat → Bool) (n m : Nat) (hm : m < n) (hp : p m = true)
    (hmin : ∀ t, t < m → p t = false) : lfind p n = m := by
  rcases Nat.lt_trichotomy (lfind p n) m with h | h | h
  · have a := lfind_spec p n (by omega); have b := hmin _ h; rw [a] at b; cases b
  · exact h
  · have := lfind_min p n m h; rw [hp] at this; cases this

theorem nt_lo (O : Trace) {lo hi : Nat} (c : Nat) (v : Bool) (h : lo ≤ hi) :
    c + lo ≤ nt O lo hi c v := by
  unfold nt
  by_cases hl : lfind (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1) < c + hi + 1
  · have := lfind_spec _ _ hl
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; exact this.1
  · have := lfind_le (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1); omega

theorem not_eq_of_ne {a v : Bool} (h : a ≠ v) : a = !v := by
  cases a <;> cases v <;> simp_all

/-- **The node through a `Win` LUT with H_NO_REVERT.** If the excitation is
`v` on `[c, c')` with `c + hi < c' + lo` (the spacing), the node's edge
`nt` lies in `[c + lo, c + hi]`, the node is `v` from there to `c' + lo`,
and `!v` on `[c + lo, nt)`. -/
theorem node_win {x O : Trace} {lo hi c c' : Nat} {v : Bool}
    (hW : Win lo hi x O) (hnr : NoRevertI lo hi x O)
    (hx : ∀ s, c ≤ s → s < c' → x s = v) (hc : hi ≤ c) (hsp : c + hi < c' + lo) :
    c + lo ≤ nt O lo hi c v ∧ nt O lo hi c v ≤ c + hi ∧
    (∀ t, nt O lo hi c v ≤ t → t < c' + lo → O t = v) ∧
    (∀ t, c + lo ≤ t → t < nt O lo hi c v → O t = !v) := by
  have hlh := win_le hW
  have hp : O (c + hi) = v := by
    obtain ⟨s, s1, s2, s3⟩ := hW (c + hi) (by omega)
    rw [s3]; exact hx s (by omega) (by omega)
  have hle : nt O lo hi c v ≤ c + hi := by
    apply Classical.byContradiction; intro hn
    have := lfind_min (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1) (c + hi)
      (by unfold nt at hn; omega)
    simp only [hp, beq_self_eq_true, Bool.and_true, decide_eq_false_iff_not] at this; omega
  have hspec := lfind_spec (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1)
    (by unfold nt at hle; omega)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hspec
  refine ⟨hspec.1, hle, fun t h1 h2 => ?_, fun t h1 h2 => ?_⟩
  · exact hnr c c' v _ t hx (by omega) hspec.1 h1 h2 hspec.2
  · have := lfind_min (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1) t h2
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at this
    rcases this with h | h
    · omega
    · exact not_eq_of_ne h

/-- **The excitation is clean for a whole phase**, with `Win` channels only
(`PipeTimed.exc_phase` with `H_LUT_FIFO` replaced by `Win`). -/
theorem exc_phase_w {req ack rst O qp : Trace} {lo hi wl wh : Nat}
    (hW : Win lo hi (ex req ack qp rst) O) (hFB : CElemTiming.WinDelay wl wh O qp)
    (hpos : 1 ≤ lo + wl) (v : Bool) (ρ ρ' α α' E : Nat)
    (hreq : ∀ t, ρ ≤ t → t < ρ' → req t = v)
    (hack : ∀ t, α ≤ t → t < α' → ack t = !v)
    (hrst : ∀ t, max ρ α ≤ t → rst t = false)
    (hdr : max ρ α + lo + E ≤ ρ') (hda : max ρ α + lo + E ≤ α')
    (hlat : hi + wh ≤ lo + E) (hbig : hi + wh ≤ max ρ α) :
    ∀ s, max ρ α ≤ s → s < max ρ' α' → ex req ack qp rst s = v := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h1 h2
    have hr := hrst s h1
    have hq : (ρ' ≤ s ∨ α' ≤ s) → qp s = v := by
      intro hdep
      have hdep' : max ρ α + lo + E ≤ s := by omega
      obtain ⟨u, hu1, hu2, e⟩ := hFB s (by omega)
      obtain ⟨s', q1, q2, q3⟩ := hW u (by omega)
      rw [e, q3]
      exact ih s' (by omega) (by omega) (by omega)
    unfold ex; rw [CElemTiming.c2n_eq, hr]
    by_cases hr' : s < ρ'
    · by_cases ha' : s < α'
      · rw [hreq s (by omega) hr', hack s (by omega) ha']
        cases v <;> cases qp s <;> rfl
      · rw [hreq s (by omega) hr', hq (Or.inr (by omega))]
        cases v <;> cases ack s <;> rfl
    · have ha' : s < α' := by omega
      rw [hack s (by omega) ha', hq (Or.inl (by omega))]
      cases v <;> cases req s <;> rfl

/-- **Before the first phase**, `Win` channels only. -/
theorem exc_pre_w {req ack rst O qp : Trace} {lo hi wl wh : Nat}
    (hW : Win lo hi (ex req ack qp rst) O) (hFB : CElemTiming.WinDelay wl wh O qp)
    (hpos : 1 ≤ lo + wl) (R ρ : Nat)
    (hrst : ∀ t, t < R → rst t = true) (hreq : ∀ t, R ≤ t → t < ρ → req t = false)
    (hR : hi + wh ≤ R) : ∀ s, s < ρ → ex req ack qp rst s = false := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
    intro h
    unfold ex; rw [CElemTiming.c2n_eq]
    by_cases hs : s < R
    · rw [hrst s hs]; rfl
    · obtain ⟨u, hu1, hu2, e⟩ := hFB s (by omega)
      obtain ⟨s', q1, q2, q3⟩ := hW u (by omega)
      have hq : qp s = false := by
        rw [e, q3]; exact ih _ (by omega) (by omega)
      rw [hreq s (by omega) h, hq]; cases rst s <;> cases ack s <;> rfl

/-- A clean input's FIFO read, from `Win` + intrinsic H_NO_REVERT (Bw's bridge). -/
theorem ret_of_clean {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hW : Win lo hi x y) (hnr : NoRevertI lo hi x y) (hx : Clean x c val)
    (hsp : Spread lo hi c) :
    ∃ r : Ret, r.lo = lo ∧ r.hi = hi ∧ ∀ t, hi ≤ t → y t = x (r.σ t) := by
  refine WinFifo.win_fifo_of_no_revert hW hx hsp ?_
  intro j t1 t2 hj h0 h1 h12 h2 hv
  have := hsp j hj
  exact hnr (c j) (c (j + 1)) (val j) t1 t2 (fun s a b => hx.val j s a b) h0 h1 h12 (by omega) hv

/-- **Converse (exactness of the intrinsic form)**: on a clean input with
`H_SPREAD_PULSE`, EVERY FIFO read of band `[lo, hi]` satisfies `NoRevertI`
for every constant stretch of the input. So `NoRevertI` asks nothing of the
run that B's FIFO hypothesis did not already give. -/
theorem seg_exists {x : Trace} {c : Nat → Nat} {val : Nat → Bool} (hx : Clean x c val) (s : Nat) :
    ∃ k, c k ≤ s ∧ s < c (k + 1) := by
  have hmono : ∀ k, k ≤ c k := by
    intro k; induction k with
    | zero => exact Nat.zero_le _
    | succ k ih => have := hx.mono k (k + 1) (by omega); omega
  have P : ∀ n s, s < c n → ∃ k, c k ≤ s ∧ s < c (k + 1) := by
    intro n
    induction n with
    | zero => intro s h; rw [hx.c0] at h; omega
    | succ n ih =>
      intro s h
      by_cases h' : s < c n
      · exact ih s h'
      · exact ⟨n, by omega, h⟩
  exact P (s + 1) s (by have := hmono (s + 1); omega)

theorem seg_le {c : Nat → Nat} (cm : ∀ i j, i ≤ j → c i ≤ c j) {k k' s s' : Nat}
    (h1 : c k ≤ s) (h2' : s' < c (k' + 1)) (h : s ≤ s') : k ≤ k' := by
  apply Classical.byContradiction; intro hn
  have := cm (k' + 1) k (by omega); omega

theorem noRevertI_of_ret {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hx : Clean x c val) (hsp : Spread lo hi c) (r : Ret) (hl : r.lo = lo) (hh : r.hi = hi)
    (hy : ∀ t, hi ≤ t → y t = x (r.σ t)) : NoRevertI lo hi x y := by
  intro a b v t1 t2 hab h0 h1 h12 h2 hv
  have g1 := r.ge t1; have l2 := r.le t2
  have m := r.mono t1 t2 h12
  rw [hh] at g1; rw [hl] at l2
  rw [hy t1 h0] at hv
  rw [hy t2 (by omega)]
  have cm : ∀ i j, i ≤ j → c i ≤ c j := fun i j h => by
    rcases Nat.lt_or_ge i j with h' | h'
    · exact Nat.le_of_lt (hx.mono _ _ h')
    · have : i = j := by omega
      rw [this]; exact Nat.le_refl _
  obtain ⟨ka, ka1, ka2⟩ := seg_exists hx a
  have va : val ka = v := by rw [← hx.val ka a ka1 ka2]; exact hab a (Nat.le_refl _) (by omega)
  by_cases hA : a ≤ r.σ t2
  · exact hab _ hA (by omega)
  · obtain ⟨k2, k21, k22⟩ := seg_exists hx (r.σ t2)
    obtain ⟨k1, k11, k12⟩ := seg_exists hx (r.σ t1)
    have o12 : k1 ≤ k2 := seg_le cm k11 k22 m
    have o2a : k2 ≤ ka := seg_le cm k21 ka2 (by omega)
    rw [hx.val k2 _ k21 k22]
    rcases Nat.lt_or_ge k2 ka with h | h
    · have k1eq : k1 + 1 = ka := by
        apply Classical.byContradiction; intro hn
        have c1 := cm (k1 + 1) (ka - 1) (by omega)
        have hs := hsp (ka - 1) (by omega)
        rw [show ka - 1 + 1 = ka by omega] at hs
        omega
      have : k2 = k1 := by omega
      subst this
      rw [← hx.val k2 _ k11 k12]; exact hv
    · have : k2 = ka := by omega
      rw [this, va]

/-- On a clean input with spacing, the intrinsic form implies Bw's zone form. -/
theorem noRevert_of_I {lo hi : Nat} {x y : Trace} {c : Nat → Nat} {val : Nat → Bool}
    (hx : Clean x c val) (hsp : Spread lo hi c) (h : NoRevertI lo hi x y) :
    NoRevert lo hi y c val := by
  intro j t1 t2 hj h0 h1 h12 h2 hv
  have := hsp j hj
  exact h (c j) (c (j + 1)) (val j) t1 t2 (fun s a b => hx.val j s a b) h0 h1 h12 (by omega) hv

/-- **Read map's `fst` = node edge time.** For a FIFO read of band
`[lo, hi]` of an input that is `!v` on `[cp, c)` and `v` on `[c, c')`,
with `cp + hi ≤ c + lo`, `c + hi < c' + lo`, `hi ≤ c`, `1 ≤ c`, the first
output instant reading at or after `c` is the first instant after `c + lo`
at which the output shows `v`. -/
theorem fst_eq_nt (r : Ret) {x y : Trace} {lo hi cp c c' : Nat} {v : Bool}
    (hl : r.lo = lo) (hh : r.hi = hi) (hy : ∀ t, hi ≤ t → y t = x (r.σ t))
    (hpre : ∀ s, cp ≤ s → s < c → x s = !v) (hx : ∀ s, c ≤ s → s < c' → x s = v)
    (hcp : cp + hi ≤ c + lo) (hsp : c + hi < c' + lo) (h1 : 1 ≤ c) :
    r.fst c = nt y lo hi c v := by
  have f1 := r.fst_lo h1; have f2 := r.fst_le c; have f3 := r.fst_spec c
  have f4 := r.le (r.fst c)
  rw [hl] at f1 f4; rw [hh] at f2
  unfold nt
  symm
  apply lfind_eq _ _ _ (by omega)
  · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    refine ⟨f1, ?_⟩
    rw [hy _ (by omega)]; exact hx _ f3 (by omega)
  · intro t ht
    simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne]
    by_cases h : c + lo ≤ t
    · right
      have b := r.fst_before ht; have g := r.ge t; rw [hh] at g
      rw [hy t (by omega), hpre _ (by omega) b]; cases v <;> decide
    · left; exact h

/-! ## 2. One `bd_link_ctl` stage with a Win LUT -/

/-- **The gate relations of one controller with a window LUT.** -/
structure Stage (req ack rst O qp : Trace) (lo hi wl wh : Nat) : Prop where
  /-- **H_LUT_WIN**: the controller LUT is shard A's window channel of its
  excitation (`PipeTimed.ex`, the real `bd_c2n` INIT), band `[lo, hi]`. -/
  H_LUT_WIN : Win lo hi (ex req ack qp rst) O
  /-- **H_NO_REVERT** (intrinsic, `NoRevertI`): the only channel-level
  hypothesis beyond `Win`. -/
  H_NO_REVERT : NoRevertI lo hi (ex req ack qp rst) O
  /-- **H_FB**: feedback wire `O → I2`, window channel. -/
  H_FB : CElemTiming.WinDelay wl wh O qp
  /-- **H_LOOP_POS** -/
  H_LOOP_POS : 1 ≤ lo + wl

/-- Phase start of a single stage: both pins at their phase level. -/
def cph (ρ α : Nat → Nat) (j : Nat) : Nat := max (ρ j) (α j)

/-- The node's `j`-th edge, read off the node trace. -/
def τs (O : Trace) (lo hi : Nat) (ρ α : Nat → Nat) (j : Nat) : Nat :=
  nt O lo hi (cph ρ α j) (Vph j)

/-- **The environment of one stage** (sender at I0, receiver's acknowledge
at I1): clean four-phase pins from reset release `R` on (arbitrary before),
and departures measured from the node's own edges. -/
structure Env1 (req ack rst O : Trace) (lo hi R : Nat) (ρ α : Nat → Nat) (Es Ea : Nat) : Prop where
  /-- **H_RST**: reset high on `[0, R)` from power-up, low after. -/
  H_RST : ∀ t, rst t = decide (t < R)
  /-- **H_REQ_SHAPE** (from `R` on). -/
  H_REQ_LOW0 : ∀ t, R ≤ t → t < ρ 0 → req t = false
  H_REQ : ∀ j t, ρ j ≤ t → t < ρ (j + 1) → req t = Vph j
  /-- **H_ACK_SHAPE**: I1 is `!Vph j` on `[α j, α (j+1))`, from `α 0 = R`. -/
  H_ACK0 : α 0 = R
  H_ACK : ∀ j t, α j ≤ t → t < α (j + 1) → ack t = !Vph j
  H_RST_EARLY : R ≤ ρ 0
  /-- **H_SND**: the sender's next edge comes `Es` after the node edge. -/
  H_SND : ∀ j, τs O lo hi ρ α j + Es ≤ ρ (j + 1)
  /-- **H_RCV**: the receiver's next edge comes `Ea` after the node edge. -/
  H_RCV : ∀ j, τs O lo hi ρ α j + Ea ≤ α (j + 1)

/-- **Timing obligations of one stage.** -/
structure Timing1 (lo hi wh R Es Ea : Nat) : Prop where
  H_R_POS : 1 ≤ R
  /-- **H_RST_LONG**: reset outlasts the loop. -/
  H_RST_LONG : hi + wh ≤ R
  /-- **H_LAT** (5b `H_ENV_LATENCY`): both neighbours answer slower than the
  feedback wire plus the LUT spread. -/
  H_LAT : hi + wh ≤ lo + min Es Ea

/-- Clean-from-0 edge list of the excitation: `0`, then the phase starts. -/
def cW (c : Nat → Nat) : Nat → Nat
  | 0 => 0
  | j + 1 => c j

def vW : Nat → Bool
  | 0 => false
  | j + 1 => Vph j

/-- Packaging: an excitation that is 0 before `c 0 ≥ 1` and `Vph j` on each
`[c j, c (j+1))`, with spacing, is a `Clean` input with `Spread`. -/
theorem clean_of_phases {x : Trace} {c : Nat → Nat} {lo hi : Nat}
    (h0 : 1 ≤ c 0) (hpre : ∀ s, s < c 0 → x s = false)
    (hph : ∀ j s, c j ≤ s → s < c (j + 1) → x s = Vph j)
    (hsp : ∀ j, c j + hi < c (j + 1) + lo) (hlh : lo ≤ hi) :
    Clean x (cW c) vW ∧ Spread lo hi (cW c) := by
  have hm : ∀ j, c j < c (j + 1) := fun j => by have := hsp j; omega
  refine ⟨⟨rfl, WinFifo.smono_of_succ _ (fun j => by
    match j with
    | 0 => show 0 < c 0; omega
    | j + 1 => show c j < c (j + 1); exact hm j), fun j s h1 h2 => ?_⟩, fun j hj => ?_⟩
  · match j with
    | 0 => exact hpre s h2
    | j + 1 => exact hph j s h1 h2
  · match j, hj with
    | j + 1, _ => exact hsp j

section stage
variable {req ack rst O qp : Trace} {lo hi wl wh R Es Ea : Nat} {ρ α : Nat → Nat}
variable (S : Stage req ack rst O qp lo hi wl wh) (E : Env1 req ack rst O lo hi R ρ α Es Ea)
  (T : Timing1 lo hi wh R Es Ea)
include S E T
set_option linter.unusedSectionVars false

theorem s_lh : lo ≤ hi := win_le S.H_LUT_WIN
theorem s_wlh : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := S.H_FB wh (Nat.le_refl _); omega

theorem cph_ge (j : Nat) : R ≤ cph ρ α j := by
  induction j with
  | zero => have := E.H_RST_EARLY; unfold cph; omega
  | succ j ih =>
    have h1 := E.H_SND j; have h2 := nt_lo O (cph ρ α j) (Vph j) (s_lh S E T) (hi := hi)
    have h3 : ρ (j + 1) ≤ cph ρ α (j + 1) := Nat.le_max_left _ _
    unfold τs at h1; omega

/-- **H_LOOP, derived for every edge**: the next phase starts at least
`min Es Ea` after the node's edge. -/
theorem s_loop (j : Nat) : τs O lo hi ρ α j + min Es Ea ≤ cph ρ α (j + 1) := by
  have := E.H_SND j; have := E.H_RCV j; unfold cph; omega

theorem s_gap (j : Nat) : cph ρ α j + lo + min Es Ea ≤ cph ρ α (j + 1) := by
  have := s_loop S E T j; have := nt_lo O (cph ρ α j) (Vph j) (s_lh S E T) (hi := hi)
  unfold τs at *; omega

/-- **H_BAND is implied** (by H_LAT and H_LOOP_POS): consecutive phase starts
are more than the LUT spread apart. -/
theorem s_spread (j : Nat) : cph ρ α j + hi < cph ρ α (j + 1) + lo := by
  have := s_gap S E T j; have := T.H_LAT; have := S.H_LOOP_POS; have := s_wlh S E T; omega

theorem s_rst_lo : ∀ t, R ≤ t → rst t = false := by
  intro t h; rw [E.H_RST]; simp; omega

/-- **H_EX_CLEAN, phase `j`**: the excitation is `Vph j` on
`[cph j, cph (j+1))`. -/
theorem s_phase (j : Nat) :
    ∀ s, cph ρ α j ≤ s → s < cph ρ α (j + 1) → ex req ack qp rst s = Vph j := by
  have hR := cph_ge S E T j
  have hl := nt_lo O (cph ρ α j) (Vph j) (s_lh S E T) (hi := hi)
  have d1 := E.H_SND j; have d2 := E.H_RCV j
  have hb := T.H_RST_LONG
  have res := exc_phase_w S.H_LUT_WIN S.H_FB S.H_LOOP_POS (Vph j) (ρ j) (ρ (j + 1)) (α j)
    (α (j + 1)) (min Es Ea) (E.H_REQ j) (E.H_ACK j)
    (fun t ht => s_rst_lo S E T t (by unfold cph at hR; omega))
    (by unfold τs cph at *; omega) (by unfold τs cph at *; omega) T.H_LAT
    (by unfold cph at hR; omega)
  intro s h1 h2; exact res s h1 h2

theorem s_pre : ∀ s, s < cph ρ α 0 → ex req ack qp rst s = false := by
  have hc : cph ρ α 0 = ρ 0 := by unfold cph; rw [E.H_ACK0]; have := E.H_RST_EARLY; omega
  rw [hc]
  exact exc_pre_w S.H_LUT_WIN S.H_FB S.H_LOOP_POS R (ρ 0)
    (fun t h => by rw [E.H_RST]; simp [h]) E.H_REQ_LOW0 T.H_RST_LONG

/-- **The node is a clean step signal** with edges `τs`. -/
theorem s_node :
    (∀ t, hi ≤ t → t < τs O lo hi ρ α 0 → O t = false) ∧
    (∀ j t, τs O lo hi ρ α j ≤ t → t < τs O lo hi ρ α (j + 1) → O t = Vph j) := by
  have hlh := s_lh S E T
  have nw := fun j => node_win S.H_LUT_WIN S.H_NO_REVERT (s_phase S E T j)
    (by have := cph_ge S E T j; have := T.H_RST_LONG; omega) (s_spread S E T j)
  refine ⟨fun t h1 h2 => ?_, fun j t h1 h2 => ?_⟩
  · by_cases ht : t < cph ρ α 0 + lo
    · obtain ⟨s, s1, s2, s3⟩ := S.H_LUT_WIN t h1
      rw [s3]; exact s_pre S E T s (by omega)
    · have := (nw 0).2.2.2 t (by omega) h2; rw [this, PipeTimed.Vph_even 0]; rfl
  · by_cases ht : t < cph ρ α (j + 1) + lo
    · exact (nw j).2.2.1 t h1 ht
    · have := (nw (j + 1)).2.2.2 t (by omega) h2
      rw [this, PipeTimed.Vph_succ, Bool.not_not]

/-- **Probe Bex, single stage.** A `bd_link_ctl` stage whose LUT is a `Win`
channel with H_NO_REVERT, in a four-phase environment (H_SND, H_RCV measured
from the node's edges), under H_RST_LONG and H_LAT, has:
(1) a clean excitation from time 0 (`Clean` with edges `0, cph 0, cph 1, …`)
and `H_SPREAD_PULSE`; (2) `H_LOOP` for every edge with `D = min Es Ea`;
(3) a FIFO read map `L` of band `[lo, hi]` making the run a
`PipeTimed.Ctl` (`H_LUT_FIFO` derived), whose `fst` at each phase start is
the node's edge. -/
theorem stage_fifo :
    Clean (ex req ack qp rst) (cW (cph ρ α)) vW ∧ Spread lo hi (cW (cph ρ α)) ∧
    (∀ j, τs O lo hi ρ α j + min Es Ea ≤ cph ρ α (j + 1)) ∧
    ∃ L : Ret, L.lo = lo ∧ L.hi = hi ∧ Ctl req ack rst O qp L wl wh ∧
      ∀ j, L.fst (cph ρ α j) = τs O lo hi ρ α j := by
  have hlh := s_lh S E T
  have hc := clean_of_phases (by have := cph_ge S E T 0; have := T.H_R_POS; omega)
    (s_pre S E T) (s_phase S E T) (s_spread S E T) hlh
  obtain ⟨L, hl, hh, hr⟩ := ret_of_clean S.H_LUT_WIN S.H_NO_REVERT hc.1 hc.2
  refine ⟨hc.1, hc.2, s_loop S E T, L, hl, hh,
    ⟨fun t ht => hr t (by omega), S.H_FB, by rw [hl]; exact S.H_LOOP_POS⟩, fun j => ?_⟩
  have hR := cph_ge S E T j; have hb := T.H_RST_LONG; have hp := T.H_R_POS
  cases j with
  | zero =>
    exact fst_eq_nt L hl hh hr (cp := 0) (c' := cph ρ α 1)
      (fun s _ h => by rw [s_pre S E T s h, PipeTimed.Vph_even 0]; rfl) (s_phase S E T 0)
      (by omega) (s_spread S E T 0) (by omega)
  | succ j =>
    have hs := s_spread S E T j
    exact fst_eq_nt L hl hh hr (cp := cph ρ α j) (c' := cph ρ α (j + 2))
      (fun s a b => by rw [s_phase S E T j s a b, PipeTimed.Vph_succ, Bool.not_not])
      (s_phase S E T (j + 1)) (by omega) (s_spread S E T (j + 1)) (by omega)

end stage

/-! ## 3. The two-stage pipe with Win LUTs

Same netlist and same environment as `PipeTimed` (§4-§6): the request line
and both acknowledge-line paths stay FIFO read maps (`Rq`, `Ar`, `Af`, as in
`PipeTimed.Gates2`); the two controller LUTs are now `Win` + H_NO_REVERT
(`Stage`). The node edge times are read off the node traces (`nt`) instead
of `L.fst`, so every event time is defined BEFORE anything is known about
the run, exactly as `PipeTimed.P2.cc`. -/

structure P2W where
  R : Nat
  lo0 : Nat
  hi0 : Nat
  lo1 : Nat
  hi1 : Nat
  Rq : Ret
  Ar : Ret
  Af : Ret
  ρ : Nat → Nat
  γ : Nat → Nat
  /-- the two node traces (edge times are read off them) -/
  O0 : Trace
  O1 : Trace

namespace P2W

/-- The `PipeTimed.P2` with the same lines, environment and reset, and LUT
read maps `L0`, `L1`. -/
def sk (W : P2W) (L0 L1 : Ret) : PipeTimed.P2 := ⟨W.R, L0, L1, W.Rq, W.Ar, W.Af, W.ρ, W.γ⟩

/-- The acknowledge line's edge time (independent of the LUT maps). -/
def ackT (W : P2W) (j τ : Nat) : Nat := (W.sk (Ret.shift 0) (Ret.shift 0)).ackT j τ
def alo (W : P2W) : Nat := min W.Ar.lo W.Af.lo
def ahi (W : P2W) : Nat := max W.Ar.hi W.Af.hi

def cc (W : P2W) : Nat → Nat × Nat
  | 0 => (max (W.ρ 0) W.R,
          max (W.Rq.fst (nt W.O0 W.lo0 W.hi0 (max (W.ρ 0) W.R) (Vph 0))) W.R)
  | j + 1 =>
    (max (W.ρ (j + 1)) (W.ackT j (nt W.O1 W.lo1 W.hi1 (cc W j).2 (Vph j))),
     max (W.Rq.fst (nt W.O0 W.lo0 W.hi0
        (max (W.ρ (j + 1)) (W.ackT j (nt W.O1 W.lo1 W.hi1 (cc W j).2 (Vph j)))) (Vph (j + 1))))
       (W.γ j))

def c0 (W : P2W) (j : Nat) : Nat := (W.cc j).1
def c1 (W : P2W) (j : Nat) : Nat := (W.cc j).2
def τ0 (W : P2W) (j : Nat) : Nat := nt W.O0 W.lo0 W.hi0 (W.c0 j) (Vph j)
def τ1 (W : P2W) (j : Nat) : Nat := nt W.O1 W.lo1 W.hi1 (W.c1 j) (Vph j)
def A0 (W : P2W) : Nat → Nat
  | 0 => W.R
  | j + 1 => W.ackT j (W.τ1 j)
def R1 (W : P2W) (j : Nat) : Nat := W.Rq.fst (W.τ0 j)
def A1 (W : P2W) : Nat → Nat
  | 0 => W.R
  | j + 1 => W.γ j
def RT0 (W : P2W) : Nat := W.Rq.lo + W.lo1 + W.alo
def RT1 (W : P2W) : Nat := W.alo + W.lo0 + W.Rq.lo

theorem c0_eq (W : P2W) (j : Nat) : W.c0 j = max (W.ρ j) (W.A0 j) := by cases j <;> rfl
theorem c1_eq (W : P2W) (j : Nat) : W.c1 j = max (W.R1 j) (W.A1 j) := by cases j <;> rfl

theorem ackT_ge (W : P2W) (j τ : Nat) (h : 1 ≤ τ) : τ + W.alo ≤ W.ackT j τ :=
  PipeTimed.P2.ackT_ge (W.sk (Ret.shift 0) (Ret.shift 0)) j τ h
theorem ackT_odd (W : P2W) (j τ : Nat) (hj : j % 2 = 1) (h : 1 ≤ τ) :
    τ + max W.Ar.lo W.Af.lo ≤ W.ackT j τ := PipeTimed.P2.ackT_odd (W.sk (Ret.shift 0) (Ret.shift 0)) j τ hj h

end P2W

/-- **Gate relations, Win LUTs.** -/
structure Gates2W (W : P2W) (rst r0 a0 q0 r1 a1 q1 : Trace) (w0l w0h w1l w1h : Nat) : Prop where
  H_RST : ∀ t, rst t = decide (t < W.R)
  /-- **H_ST0/1**: each controller LUT is `Win` + H_NO_REVERT, feedback `Win`. -/
  H_ST0 : Stage r0 a0 rst W.O0 q0 W.lo0 W.hi0 w0l w0h
  H_ST1 : Stage r1 a1 rst W.O1 q1 W.lo1 W.hi1 w1l w1h
  /-- **H_REQ_LINE**, **H_ACK_LINE**: as `PipeTimed.Gates2`. -/
  H_REQ_LINE : ∀ t, W.Rq.hi ≤ t → r1 t = W.O0 (W.Rq.σ t)
  H_ACK_LINE : ∀ t, max W.Ar.hi W.Af.hi ≤ t → a0 t = (W.O1 (W.Ar.σ t) || W.O1 (W.Af.σ t))

/-- **Environment**, as `PipeTimed.Env2`, departures measured from the node
edges read off the traces. -/
structure Env2W (W : P2W) (r0 a1 : Trace) (Es Er : Nat) : Prop where
  H_REQ_LOW0 : ∀ t, W.R ≤ t → t < W.ρ 0 → r0 t = false
  H_REQ : ∀ j t, W.ρ j ≤ t → t < W.ρ (j + 1) → r0 t = Vph j
  H_ACK_LOW0 : ∀ t, W.R ≤ t → t < W.γ 0 → a1 t = false
  H_ACK : ∀ j t, W.γ j ≤ t → t < W.γ (j + 1) → a1 t = Vph j
  H_SND : ∀ j, W.τ0 j + Es ≤ W.ρ (j + 1)
  H_RCV : ∀ j, W.τ1 j + Er ≤ W.γ j
  H_RST_EARLY : W.R ≤ W.ρ 0

/-- **Timing**, as `PipeTimed.Timing2` with the LUT bands. -/
structure Timing2W (W : P2W) (w0h w1h Es Er : Nat) : Prop where
  H_R_POS : 1 ≤ W.R
  H_RST_LONG : W.hi0 + w0h ≤ W.R ∧ W.hi1 + w1h ≤ W.R
  H_RST_LINES : W.hi0 + W.Rq.hi ≤ W.R ∧ W.hi1 + W.ahi ≤ W.R
  H_LAT0 : W.hi0 + w0h ≤ W.lo0 + min Es W.RT0
  H_LAT1 : W.hi1 + w1h ≤ W.lo1 + min Er W.RT1
  H_ACK_FLUSH : W.ahi ≤ W.lo1 + max Er W.RT1 + W.alo

/-- Minimality of `nt`, unconditionally: before it (after `c + lo`) the
trace does not show `v`. -/
theorem nt_before (O : Trace) (lo hi c : Nat) (v : Bool) :
    ∀ t, c + lo ≤ t → t < nt O lo hi c v → O t = !v := by
  intro t h1 h2
  have := lfind_min (fun t => decide (c + lo ≤ t) && (O t == v)) (c + hi + 1) t h2
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, beq_eq_false_iff_ne] at this
  rcases this with h | h
  · omega
  · exact not_eq_of_ne h

section pipe
variable {W : P2W} {rst r0 a0 q0 r1 a1 q1 : Trace} {w0l w0h w1l w1h Es Er : Nat}
variable (G : Gates2W W rst r0 a0 q0 r1 a1 q1 w0l w0h w1l w1h)
  (E : Env2W W r0 a1 Es Er) (T : Timing2W W w0h w1h Es Er)
include G E T
set_option linter.unusedSectionVars false

theorem lh0 : W.lo0 ≤ W.hi0 := win_le G.H_ST0.H_LUT_WIN
theorem lh1 : W.lo1 ≤ W.hi1 := win_le G.H_ST1.H_LUT_WIN
theorem wlh0 : w0l ≤ w0h := by obtain ⟨s, h1, h2, _⟩ := G.H_ST0.H_FB w0h (Nat.le_refl _); omega
theorem wlh1 : w1l ≤ w1h := by obtain ⟨s, h1, h2, _⟩ := G.H_ST1.H_FB w1h (Nat.le_refl _); omega

theorem tau0_lo (j : Nat) : W.c0 j + W.lo0 ≤ W.τ0 j := nt_lo _ _ _ (lh0 G E T)
theorem tau1_lo (j : Nat) : W.c1 j + W.lo1 ≤ W.τ1 j := nt_lo _ _ _ (lh1 G E T)

theorem ge_R : ∀ j, W.R ≤ W.c0 j ∧ W.R ≤ W.c1 j := by
  have hR := T.H_R_POS
  intro j
  induction j with
  | zero =>
    rw [W.c0_eq, W.c1_eq]; simp only [P2W.A0, P2W.A1]; omega
  | succ j ih =>
    have h1 : W.R ≤ W.c0 (j + 1) := by
      rw [W.c0_eq]; simp only [P2W.A0]
      have := W.ackT_ge j (W.τ1 j) (by have := tau1_lo G E T j; omega)
      have := tau1_lo G E T j; omega
    refine ⟨h1, ?_⟩
    rw [W.c1_eq]
    have := W.Rq.fst_ge (W.τ0 (j + 1)); have := tau0_lo G E T (j + 1)
    unfold P2W.R1; omega

theorem R1_lo (j : Nat) : W.τ0 j + W.Rq.lo ≤ W.R1 j :=
  W.Rq.fst_lo (by have := tau0_lo G E T j; have := (ge_R G E T j).1; have := T.H_R_POS; omega)
theorem A0_lo (j : Nat) : W.τ1 j + W.alo ≤ W.A0 (j + 1) :=
  W.ackT_ge j _ (by have := tau1_lo G E T j; have := (ge_R G E T j).2; have := T.H_R_POS; omega)

theorem dep0r (j : Nat) : W.c0 j + W.lo0 + Es ≤ W.ρ (j + 1) := by
  have := E.H_SND j; have := tau0_lo G E T j; omega

theorem dep0a (j : Nat) : W.c0 j + W.lo0 + W.RT0 ≤ W.A0 (j + 1) := by
  have h1 := A0_lo G E T j; have h2 := tau1_lo G E T j; have h3 := W.c1_eq j
  have h4 := R1_lo G E T j; have h5 := tau0_lo G E T j
  unfold P2W.RT0; omega

theorem dep1r (j : Nat) : W.c1 j + W.lo1 + W.RT1 ≤ W.R1 (j + 1) := by
  have h1 := R1_lo G E T (j + 1); have h2 := tau0_lo G E T (j + 1); have h3 := W.c0_eq (j + 1)
  have h4 := A0_lo G E T j; have h5 := tau1_lo G E T j
  unfold P2W.RT1; omega

theorem dep1a (j : Nat) : W.c1 j + W.lo1 + Er ≤ W.A1 (j + 1) := by
  have := E.H_RCV j; have := tau1_lo G E T j; simp only [P2W.A1]; omega

/-- **H_LOOP, derived, both stages.** -/
theorem loop0 (j : Nat) : W.c0 j + W.lo0 + min Es W.RT0 ≤ W.c0 (j + 1) := by
  have := dep0r G E T j; have := dep0a G E T j; have := W.c0_eq (j + 1); omega
theorem loop1 (j : Nat) : W.c1 j + W.lo1 + min Er W.RT1 ≤ W.c1 (j + 1) := by
  have := dep1r G E T j; have := dep1a G E T j; have := W.c1_eq (j + 1); omega

/-- **H_SPREAD_PULSE (H_BAND) derived from H_LAT + H_LOOP_POS**, both stages. -/
theorem spread0 (j : Nat) : W.c0 j + W.hi0 < W.c0 (j + 1) + W.lo0 := by
  have := loop0 G E T j; have := T.H_LAT0; have := G.H_ST0.H_LOOP_POS; have := wlh0 G E T; omega
theorem spread1 (j : Nat) : W.c1 j + W.hi1 < W.c1 (j + 1) + W.lo1 := by
  have := loop1 G E T j; have := T.H_LAT1; have := G.H_ST1.H_LOOP_POS; have := wlh1 G E T; omega

theorem gap1 (j : Nat) : W.τ1 j + W.lo1 + max Er W.RT1 ≤ W.τ1 (j + 1) := by
  have h1 := tau1_lo G E T (j + 1); have h2 := W.c1_eq (j + 1); have h3 := E.H_RCV j
  have h4 := R1_lo G E T (j + 1); have h5 := tau0_lo G E T (j + 1); have h6 := W.c0_eq (j + 1)
  have h7 := A0_lo G E T j
  simp only [P2W.A1] at h2; unfold P2W.RT1; omega

theorem rst_hi : ∀ t, t < W.R → rst t = true := by
  intro t h; rw [G.H_RST]; simp [h]

theorem rst_lo : ∀ t, W.R ≤ t → rst t = false := by
  intro t h; rw [G.H_RST]; simp; omega

theorem pre0 : ∀ s, s < W.c0 0 → ex r0 a0 q0 rst s = false := by
  have hc : W.c0 0 = W.ρ 0 := by rw [W.c0_eq]; simp only [P2W.A0]; have := E.H_RST_EARLY; omega
  rw [hc]
  exact exc_pre_w G.H_ST0.H_LUT_WIN G.H_ST0.H_FB G.H_ST0.H_LOOP_POS W.R (W.ρ 0) (rst_hi G E T)
    E.H_REQ_LOW0 T.H_RST_LONG.1

theorem node0_pre : ∀ t, W.hi0 ≤ t → t < W.τ0 0 → W.O0 t = false := by
  intro t h1 h2
  by_cases ht : t < W.c0 0 + W.lo0
  · obtain ⟨s, s1, s2, s3⟩ := G.H_ST0.H_LUT_WIN t h1
    rw [s3]; exact pre0 G E T s (by omega)
  · have := nt_before W.O0 W.lo0 W.hi0 (W.c0 0) (Vph 0) t (by omega) h2
    rw [this, PipeTimed.Vph_even 0]; rfl

/-- Stage `i`'s node on `[τ j, τ (j+1))`, from its phase `j` alone. -/
theorem node0_seg (j : Nat)
    (h0 : ∀ s, W.c0 j ≤ s → s < W.c0 (j + 1) → ex r0 a0 q0 rst s = Vph j) :
    ∀ t, W.τ0 j ≤ t → t < W.τ0 (j + 1) → W.O0 t = Vph j := by
  have nw := node_win G.H_ST0.H_LUT_WIN G.H_ST0.H_NO_REVERT h0
    (by have := (ge_R G E T j).1; have := T.H_RST_LONG.1; omega) (spread0 G E T j)
  intro t h1 h2
  by_cases ht : t < W.c0 (j + 1) + W.lo0
  · exact nw.2.2.1 t h1 ht
  · have := nt_before W.O0 W.lo0 W.hi0 (W.c0 (j + 1)) (Vph (j + 1)) t (by omega) h2
    rw [this, PipeTimed.Vph_succ, Bool.not_not]

theorem node1_seg (j : Nat)
    (h1 : ∀ s, W.c1 j ≤ s → s < W.c1 (j + 1) → ex r1 a1 q1 rst s = Vph j) :
    ∀ t, W.τ1 j ≤ t → t < W.τ1 (j + 1) → W.O1 t = Vph j := by
  have nw := node_win G.H_ST1.H_LUT_WIN G.H_ST1.H_NO_REVERT h1
    (by have := (ge_R G E T j).2; have := T.H_RST_LONG.2; omega) (spread1 G E T j)
  intro t a b
  by_cases ht : t < W.c1 (j + 1) + W.lo1
  · exact nw.2.2.1 t a ht
  · have := nt_before W.O1 W.lo1 W.hi1 (W.c1 (j + 1)) (Vph (j + 1)) t (by omega) b
    rw [this, PipeTimed.Vph_succ, Bool.not_not]

theorem pre1 : ∀ s, s < W.c1 0 → ex r1 a1 q1 rst s = false := by
  apply exc_pre_w G.H_ST1.H_LUT_WIN G.H_ST1.H_FB G.H_ST1.H_LOOP_POS W.R (W.c1 0) (rst_hi G E T)
    _ T.H_RST_LONG.2
  intro t h1 h2
  have hc := W.c1_eq 0; simp only [P2W.A1] at hc
  have hr := T.H_RST_LINES.1; have hl := W.Rq.lo_le_hi
  have g := W.Rq.ge t
  rw [G.H_REQ_LINE t (by omega)]
  exact node0_pre G E T _ (by omega) (W.Rq.fst_before (by unfold P2W.R1 at hc; omega))

theorem node1_pre : ∀ t, W.hi1 ≤ t → t < W.τ1 0 → W.O1 t = false := by
  intro t h1 h2
  by_cases ht : t < W.c1 0 + W.lo1
  · obtain ⟨s, s1, s2, s3⟩ := G.H_ST1.H_LUT_WIN t h1
    rw [s3]; exact pre1 G E T s (by omega)
  · have := nt_before W.O1 W.lo1 W.hi1 (W.c1 0) (Vph 0) t (by omega) h2
    rw [this, PipeTimed.Vph_even 0]; rfl

theorem phase0_of (j : Nat) (hack : ∀ t, W.A0 j ≤ t → t < W.A0 (j + 1) → a0 t = !Vph j) :
    ∀ s, W.c0 j ≤ s → s < W.c0 (j + 1) → ex r0 a0 q0 rst s = Vph j := by
  have hR := (ge_R G E T j).1
  have d1 := dep0r G E T j; have d2 := dep0a G E T j
  have hc := W.c0_eq j
  have hb := T.H_RST_LONG.1
  have res := exc_phase_w G.H_ST0.H_LUT_WIN G.H_ST0.H_FB G.H_ST0.H_LOOP_POS (Vph j) (W.ρ j)
    (W.ρ (j + 1)) (W.A0 j) (W.A0 (j + 1)) (min Es W.RT0) (E.H_REQ j) hack
    (fun t ht => rst_lo G E T t (by omega)) (by omega) (by omega) T.H_LAT0 (by omega)
  intro s h1 h2
  rw [W.c0_eq] at h1 h2; exact res s h1 h2

theorem phase1_of (j : Nat)
    (h0 : ∀ s, W.c0 j ≤ s → s < W.c0 (j + 1) → ex r0 a0 q0 rst s = Vph j) :
    ∀ s, W.c1 j ≤ s → s < W.c1 (j + 1) → ex r1 a1 q1 rst s = Vph j := by
  have hR := ge_R G E T j
  have d1 := dep1r G E T j; have d2 := dep1a G E T j
  have hc := W.c1_eq j
  have hb := T.H_RST_LONG
  have hl := T.H_RST_LINES
  have hreq : ∀ t, W.R1 j ≤ t → t < W.R1 (j + 1) → r1 t = Vph j := by
    have hO := node0_seg G E T j h0
    intro t h1 h2
    have := R1_lo G E T j; have := tau0_lo G E T j
    exact PipeTimed.fifo_hold W.Rq G.H_REQ_LINE hO t h1 h2 (by omega)
  have hack : ∀ t, W.A1 j ≤ t → t < W.A1 (j + 1) → a1 t = !Vph j := by
    cases j with
    | zero =>
      intro t h1 h2; simp only [P2W.A1] at h1 h2
      rw [E.H_ACK_LOW0 t h1 h2]; rfl
    | succ j =>
      intro t h1 h2; simp only [P2W.A1] at h1 h2
      rw [E.H_ACK j t h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  have res := exc_phase_w G.H_ST1.H_LUT_WIN G.H_ST1.H_FB G.H_ST1.H_LOOP_POS (Vph j) (W.R1 j)
    (W.R1 (j + 1)) (W.A1 j) (W.A1 (j + 1)) (min Er W.RT1) hreq hack
    (fun t ht => rst_lo G E T t (by omega)) (by omega) (by omega) T.H_LAT1 (by omega)
  intro s h1 h2
  rw [W.c1_eq] at h1 h2; exact res s h1 h2

theorem ack0_zero : ∀ t, W.A0 0 ≤ t → t < W.A0 1 → a0 t = !Vph 0 := by
  intro t h1 h2
  simp only [P2W.A0, P2W.ackT, PipeTimed.P2.ackT, show (0 : Nat) % 2 = 0 from rfl, ite_true,
    P2W.sk] at h1 h2
  have hl := T.H_RST_LINES.2
  have f1 := W.Ar.fst_le W.hi1; have f2 := W.Af.fst_le W.hi1
  have := PipeTimed.or_hold_false W.Ar W.Af G.H_ACK_LINE (a := W.hi1) (b := W.τ1 0)
    (fun s h1 h2 => node1_pre G E T s h1 h2) t (by unfold P2W.ahi at hl; omega) h2
    (by unfold P2W.ahi at hl; omega)
  rw [this]; rfl

theorem ack0_succ (j : Nat)
    (h1 : ∀ s, W.c1 j ≤ s → s < W.c1 (j + 1) → ex r1 a1 q1 rst s = Vph j) :
    ∀ t, W.A0 (j + 1) ≤ t → t < W.A0 (j + 1 + 1) → a0 t = !Vph (j + 1) := by
  have hR := (ge_R G E T j).2
  have hl := T.H_RST_LINES.2
  have hO := node1_seg G E T j h1
  have ha := A0_lo G E T j; have ht := tau1_lo G E T j; have hRp := T.H_R_POS
  rw [PipeTimed.Vph_succ, Bool.not_not]
  intro t t1 t2
  simp only [P2W.A0, P2W.ackT, PipeTimed.P2.ackT, P2W.sk] at t1 t2
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · have hv : Vph j = true := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [hj, ite_true] at t1; simp only [show ¬ ((j + 1) % 2 = 0) by omega, ite_false] at t2
    have g := gap1 G E T j; have fl := T.H_ACK_FLUSH
    have a1 := W.Ar.fst_le (W.τ1 j); have a2 := W.Af.fst_le (W.τ1 j)
    have hpos : 1 ≤ W.τ1 (j + 1) := by omega
    have b1 := W.Ar.fst_lo hpos
    have b2 := W.Af.fst_lo hpos
    have e1 : W.ahi = max W.Ar.hi W.Af.hi := rfl
    have e2 : W.alo = min W.Ar.lo W.Af.lo := rfl
    have ov1 : W.Ar.fst (W.τ1 j) ≤ W.Af.fst (W.τ1 (j + 1)) := by omega
    have ov2 : W.Af.fst (W.τ1 j) ≤ W.Ar.fst (W.τ1 (j + 1)) := by omega
    exact PipeTimed.or_hold_true W.Ar W.Af G.H_ACK_LINE hO ov1 ov2 t t1 t2
      (by have := W.Ar.fst_ge (W.τ1 j); have := W.Af.fst_ge (W.τ1 j); omega)
  · have hv : Vph j = false := by unfold Vph LinkTimed.Vph; simp [hj]
    rw [hv] at hO ⊢
    simp only [show ¬ (j % 2 = 0) by omega, ite_false] at t1
    simp only [show (j + 1) % 2 = 0 by omega, ite_true] at t2
    unfold P2W.ahi at hl
    have := W.Ar.fst_ge (W.τ1 j); have := W.Af.fst_ge (W.τ1 j)
    exact PipeTimed.or_hold_false W.Ar W.Af G.H_ACK_LINE hO t t1 t2 (by omega)

/-- **The causal induction (H_EX_CLEAN for both stages, every phase).**
Stage 0's phase `j+1` uses stage 1's phase `j` (through the ack line and
`node1_seg`, i.e. through H_NO_REVERT of stage 1's LUT); stage 1's phase
`j` uses stage 0's phase `j` (request line, `node0_seg`). -/
theorem pipe_ctl_w : ∀ j,
    (∀ s, W.c0 j ≤ s → s < W.c0 (j + 1) → ex r0 a0 q0 rst s = Vph j) ∧
    (∀ s, W.c1 j ≤ s → s < W.c1 (j + 1) → ex r1 a1 q1 rst s = Vph j) := by
  intro j
  induction j with
  | zero =>
    have h0 := phase0_of G E T 0 (ack0_zero G E T)
    exact ⟨h0, phase1_of G E T 0 h0⟩
  | succ j ih =>
    have h0 := phase0_of G E T (j + 1) (ack0_succ G E T j ih.2)
    exact ⟨h0, phase1_of G E T (j + 1) h0⟩

/-- **Probe Bex, two-stage pipe.** Under `Gates2W` (Win LUTs + H_NO_REVERT,
FIFO lines as in PipeTimed), `Env2W`, `Timing2W`, there are FIFO read
maps `L0`, `L1` of bands `[lo0, hi0]`, `[lo1, hi1]` such that the
`PipeTimed.P2` with these maps (same lines, reset, environment times)
satisfies `PipeTimed.Gates2`, `Env2`, `Timing2`, and its derived node edge
times ARE the ones read off the traces. Hence every theorem of `PipeTimed`
(`pipe_ctl`, `nodes_clean`, `pins_clean`, `token0/1`, `pipe_forward`, `live`)
holds for this run. -/
theorem pipe_fifo :
    ∃ L0 L1 : Ret, L0.lo = W.lo0 ∧ L0.hi = W.hi0 ∧ L1.lo = W.lo1 ∧ L1.hi = W.hi1 ∧
      PipeTimed.Gates2 (W.sk L0 L1) rst r0 a0 W.O0 q0 r1 a1 W.O1 q1 w0l w0h w1l w1h ∧
      PipeTimed.Env2 (W.sk L0 L1) r0 a1 Es Er ∧
      PipeTimed.Timing2 (W.sk L0 L1) w0h w1h Es Er ∧
      ∀ j, (W.sk L0 L1).τ0 j = W.τ0 j ∧ (W.sk L0 L1).τ1 j = W.τ1 j := by
  have hR := ge_R G E T
  have hp := T.H_R_POS; have hb := T.H_RST_LONG
  have c0c := clean_of_phases (by have := (hR 0).1; omega) (pre0 G E T)
    (fun j => (pipe_ctl_w G E T j).1) (spread0 G E T) (lh0 G E T)
  have c1c := clean_of_phases (by have := (hR 0).2; omega) (pre1 G E T)
    (fun j => (pipe_ctl_w G E T j).2) (spread1 G E T) (lh1 G E T)
  obtain ⟨L0, hl0, hh0, hr0⟩ := ret_of_clean G.H_ST0.H_LUT_WIN G.H_ST0.H_NO_REVERT c0c.1 c0c.2
  obtain ⟨L1, hl1, hh1, hr1⟩ := ret_of_clean G.H_ST1.H_LUT_WIN G.H_ST1.H_NO_REVERT c1c.1 c1c.2
  -- the read maps' `fst` at each phase start are the node edges
  have f0 : ∀ j, L0.fst (W.c0 j) = W.τ0 j := by
    intro j
    have h := (hR j).1
    cases j with
    | zero =>
      exact fst_eq_nt L0 hl0 hh0 hr0 (cp := 0) (c' := W.c0 1)
        (fun s _ h => by rw [pre0 G E T s h, PipeTimed.Vph_even 0]; rfl) (pipe_ctl_w G E T 0).1
        (by omega) (spread0 G E T 0) (by omega)
    | succ j =>
      have hs := spread0 G E T j
      exact fst_eq_nt L0 hl0 hh0 hr0 (cp := W.c0 j) (c' := W.c0 (j + 2))
        (fun s a b => by rw [(pipe_ctl_w G E T j).1 s a b, PipeTimed.Vph_succ, Bool.not_not])
        (pipe_ctl_w G E T (j + 1)).1 (by omega) (spread0 G E T (j + 1)) (by omega)
  have f1 : ∀ j, L1.fst (W.c1 j) = W.τ1 j := by
    intro j
    have h := (hR j).2
    cases j with
    | zero =>
      exact fst_eq_nt L1 hl1 hh1 hr1 (cp := 0) (c' := W.c1 1)
        (fun s _ h => by rw [pre1 G E T s h, PipeTimed.Vph_even 0]; rfl) (pipe_ctl_w G E T 0).2
        (by omega) (spread1 G E T 0) (by omega)
    | succ j =>
      have hs := spread1 G E T j
      exact fst_eq_nt L1 hl1 hh1 hr1 (cp := W.c1 j) (c' := W.c1 (j + 2))
        (fun s a b => by rw [(pipe_ctl_w G E T j).2 s a b, PipeTimed.Vph_succ, Bool.not_not])
        (pipe_ctl_w G E T (j + 1)).2 (by omega) (spread1 G E T (j + 1)) (by omega)
  -- the PipeTimed recursion computes the same phase starts
  have hcc : ∀ j, (W.sk L0 L1).cc j = W.cc j := by
    intro j
    induction j with
    | zero =>
      have := f0 0
      show (max (W.ρ 0) W.R, max (W.Rq.fst (L0.fst (max (W.ρ 0) W.R))) W.R) = W.cc 0
      unfold P2W.c0 P2W.τ0 at this
      rw [show (W.cc 0).1 = max (W.ρ 0) W.R from rfl] at this
      rw [this]; rfl
    | succ j ih =>
      have e1 : L1.fst (W.cc j).2 = nt W.O1 W.lo1 W.hi1 (W.cc j).2 (Vph j) := f1 j
      have e0 : L0.fst (max (W.ρ (j + 1)) (W.ackT j (nt W.O1 W.lo1 W.hi1 (W.cc j).2 (Vph j)))) =
          nt W.O0 W.lo0 W.hi0 (max (W.ρ (j + 1)) (W.ackT j (nt W.O1 W.lo1 W.hi1 (W.cc j).2 (Vph j))))
            (Vph (j + 1)) := f0 (j + 1)
      show (max (W.ρ (j + 1)) ((W.sk L0 L1).ackT j (L1.fst ((W.sk L0 L1).cc j).2)),
        max (W.Rq.fst (L0.fst (max (W.ρ (j + 1)) ((W.sk L0 L1).ackT j
          (L1.fst ((W.sk L0 L1).cc j).2))))) (W.γ j)) = W.cc (j + 1)
      rw [ih, e1]
      have e3 : (W.sk L0 L1).ackT j (nt W.O1 W.lo1 W.hi1 (W.cc j).2 (Vph j)) =
          W.ackT j (nt W.O1 W.lo1 W.hi1 (W.cc j).2 (Vph j)) := rfl
      rw [e3, e0]; rfl
  have ht0 : ∀ j, (W.sk L0 L1).τ0 j = W.τ0 j := fun j => by
    show L0.fst ((W.sk L0 L1).cc j).1 = _; rw [hcc]; exact f0 j
  have ht1 : ∀ j, (W.sk L0 L1).τ1 j = W.τ1 j := fun j => by
    show L1.fst ((W.sk L0 L1).cc j).2 = _; rw [hcc]; exact f1 j
  refine ⟨L0, L1, hl0, hh0, hl1, hh1, ?_, ?_, ?_, fun j => ⟨ht0 j, ht1 j⟩⟩
  · exact { H_RST := G.H_RST
            H_CTL0 := ⟨fun t ht => hr0 t (by rw [← hh0]; exact ht), G.H_ST0.H_FB,
              by show 1 ≤ L0.lo + w0l; rw [hl0]; exact G.H_ST0.H_LOOP_POS⟩
            H_CTL1 := ⟨fun t ht => hr1 t (by rw [← hh1]; exact ht), G.H_ST1.H_FB,
              by show 1 ≤ L1.lo + w1l; rw [hl1]; exact G.H_ST1.H_LOOP_POS⟩
            H_REQ_LINE := G.H_REQ_LINE
            H_ACK_LINE := G.H_ACK_LINE }
  · exact { H_REQ_LOW0 := E.H_REQ_LOW0, H_REQ := E.H_REQ, H_ACK_LOW0 := E.H_ACK_LOW0,
            H_ACK := E.H_ACK
            H_SND := fun j => by rw [ht0]; exact E.H_SND j
            H_RCV := fun j => by rw [ht1]; exact E.H_RCV j
            H_RST_EARLY := E.H_RST_EARLY }
  · have t1 := T.H_RST_LONG; have t2 := T.H_RST_LINES; have t3 := T.H_LAT0; have t4 := T.H_LAT1
    have t5 := T.H_ACK_FLUSH
    refine { H_R_POS := T.H_R_POS, H_RST_LONG := ?_, H_RST_LINES := ?_, H_LAT0 := ?_,
             H_LAT1 := ?_, H_ACK_FLUSH := ?_ } <;>
    simp only [P2W.sk, PipeTimed.P2.RT0, PipeTimed.P2.RT1, PipeTimed.P2.alo, PipeTimed.P2.ahi,
      P2W.RT0, P2W.RT1, P2W.alo, P2W.ahi, hl0, hh0, hl1, hh1] at * <;> omega

/-- **Corollary: PipeTimed's `nodes_clean` on Win LUTs**, with the node edges
read off the traces. -/
theorem nodes_clean_w :
    (∀ t, W.hi0 ≤ t → t < W.τ0 0 → W.O0 t = false) ∧
    (∀ j t, W.τ0 j ≤ t → t < W.τ0 (j + 1) → W.O0 t = Vph j) ∧
    (∀ t, W.hi1 ≤ t → t < W.τ1 0 → W.O1 t = false) ∧
    (∀ j t, W.τ1 j ≤ t → t < W.τ1 (j + 1) → W.O1 t = Vph j) := by
  obtain ⟨L0, L1, hl0, hh0, hl1, hh1, G2, E2, T2, hτ⟩ := pipe_fifo G E T
  have n := PipeTimed.nodes_clean G2 E2 T2
  refine ⟨fun t a b => ?_, fun j t a b => ?_, fun t a b => ?_, fun j t a b => ?_⟩
  · exact n.1 t (by show L0.hi ≤ t; rw [hh0]; exact a) (by rw [(hτ 0).1]; exact b)
  · exact n.2.1 j t (by rw [(hτ j).1]; exact a) (by rw [(hτ (j + 1)).1]; exact b)
  · exact n.2.2.1 t (by show L1.hi ≤ t; rw [hh1]; exact a) (by rw [(hτ 0).2]; exact b)
  · exact n.2.2.2 j t (by rw [(hτ j).2]; exact a) (by rw [(hτ (j + 1)).2]; exact b)

end pipe

/-! ## 4. Non-vacuity and the necessity of H_NO_REVERT -/

/-- A transport delay equal to the band's lower end satisfies `NoRevertI`
for every input. -/
theorem noRevertI_shift {lo hi : Nat} {x y : Trace} (h : ∀ t, lo ≤ t → y t = x (t - lo)) :
    NoRevertI lo hi x y := by
  intro a b v t1 t2 hab h0 h1 h12 h2 _
  rw [h t2 (by omega)]; exact hab _ (by omega) (by omega)

/-- `nt` at a point where the trace already shows `v` at `c + lo`. -/
theorem nt_eq (O : Trace) {lo hi c : Nat} {v : Bool} (hlh : lo ≤ hi) (h : O (c + lo) = v) :
    nt O lo hi c v = c + lo := by
  unfold nt
  apply lfind_eq _ _ _ (by omega)
  · simp [h]
  · intro t ht; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not]; left; omega

namespace Wx
open Formal.Cells.PipeTimed.Wit (sq sq_shift sq_pre sq_phase rstW key)

/-- The witness: PipeTimed's fixed-delay run (all delays 1 tick, phases 4
ticks), but each controller LUT is only assumed to be a `Win 1 3` channel,
a band two ticks wide, where `Win` is NOT contained in FIFO
(`WinFifo.win_glitch_not_fifo`). -/
def Ww : P2W where
  R := 4
  lo0 := 1
  hi0 := 3
  lo1 := 1
  hi1 := 3
  Rq := Ret.shift 1
  Ar := Ret.shift 1
  Af := Ret.shift 1
  ρ j := 4 + 4 * j
  γ j := 10 + 4 * j
  O0 := sq 5
  O1 := sq 7

theorem fst1 (c : Nat) (h : 1 ≤ c) : (Ret.shift 1).fst c = c + 1 := Ret.fst_shift 1 c h

theorem cc_w : ∀ j, Ww.cc j = (4 + 4 * j, 6 + 4 * j) := by
  intro j
  induction j with
  | zero =>
    show (max 4 4, max ((Ret.shift 1).fst (nt (sq 5) 1 3 (max 4 4) (Vph 0))) 4) = _
    rw [show max 4 4 = 4 from rfl, nt_eq (sq 5) (by decide) (sq_phase 5 0 _ (by omega) (by omega)),
      fst1 _ (by omega)]; rfl
  | succ j ih =>
    show (max (4 + 4 * (j + 1)) (Ww.ackT j (nt (sq 7) 1 3 (Ww.cc j).2 (Vph j))),
      max ((Ret.shift 1).fst (nt (sq 5) 1 3
        (max (4 + 4 * (j + 1)) (Ww.ackT j (nt (sq 7) 1 3 (Ww.cc j).2 (Vph j)))) (Vph (j + 1))))
        (10 + 4 * j)) = _
    have hn : nt (sq 7) 1 3 (Ww.cc j).2 (Vph j) = 7 + 4 * j := by
      rw [ih]; simp only
      rw [nt_eq (sq 7) (by decide) (sq_phase 7 j _ (by omega) (by omega))]; omega
    have ha : Ww.ackT j (7 + 4 * j) = 8 + 4 * j := by
      show (if j % 2 = 0 then min ((Ret.shift 1).fst _) ((Ret.shift 1).fst _)
        else max ((Ret.shift 1).fst _) ((Ret.shift 1).fst _)) = _
      rw [fst1 _ (by omega)]
      split <;> omega
    rw [hn, ha, show max (4 + 4 * (j + 1)) (8 + 4 * j) = 8 + 4 * j by omega,
      nt_eq (sq 5) (by decide) (sq_phase 5 (j + 1) _ (by omega) (by omega)),
      fst1 _ (by omega)]
    simp only [Prod.mk.injEq]; omega

theorem τ0_w (j : Nat) : Ww.τ0 j = 5 + 4 * j := by
  show nt (sq 5) 1 3 (Ww.cc j).1 (Vph j) = _
  rw [cc_w]; simp only
  rw [nt_eq (sq 5) (by decide) (sq_phase 5 j _ (by omega) (by omega))]; omega

theorem τ1_w (j : Nat) : Ww.τ1 j = 7 + 4 * j := by
  show nt (sq 7) 1 3 (Ww.cc j).2 (Vph j) = _
  rw [cc_w]; simp only
  rw [nt_eq (sq 7) (by decide) (sq_phase 7 j _ (by omega) (by omega))]; omega

/-- A `Win 1 3` controller LUT that is in fact a 1-tick transport delay of
the real `bd_c2n` excitation of square waves (`o`, `o+4`, feedback `o+2`). -/
theorem stage_sq (o : Nat) (ho : 4 ≤ o) :
    Stage (sq o) (sq (o + 4)) rstW (sq (o + 1)) (sq (o + 2)) 1 3 1 1 := by
  have hx : ∀ t, 1 ≤ t → sq (o + 1) t = ex (sq o) (sq (o + 4)) (sq (o + 2)) rstW (t - 1) := by
    intro t ht
    rw [key o (t - 1) ho]
    have := sq_shift o 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this
  exact { H_LUT_WIN := fun t ht => ⟨t - 1, by omega, by omega, hx t (by omega)⟩
          H_NO_REVERT := noRevertI_shift hx
          H_FB := CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
            (fun t => by have := sq_shift (o + 1) 1 t; rw [show o + 1 + 1 = o + 2 by omega] at this
                         exact this)
          H_LOOP_POS := by decide }

theorem gates_w : Gates2W Ww rstW (sq 4) (sq 8) (sq 6) (sq 6) (sq 10) (sq 8) 1 1 1 1 where
  H_RST _ := rfl
  H_ST0 := stage_sq 4 (by omega)
  H_ST1 := stage_sq 6 (by omega)
  H_REQ_LINE := PipeTimed.Wit.gates_w.H_REQ_LINE
  H_ACK_LINE := PipeTimed.Wit.gates_w.H_ACK_LINE

theorem env_w : Env2W Ww (sq 4) (sq 10) 3 3 where
  H_REQ_LOW0 t h1 h2 := by simp only [Ww] at h1 h2; omega
  H_REQ j t h1 h2 := sq_phase 4 j t h1 (by simp only [Ww] at h2; omega)
  H_ACK_LOW0 t h1 h2 := sq_pre 10 t h2
  H_ACK j t h1 h2 := sq_phase 10 j t h1 (by simp only [Ww] at h2; omega)
  H_SND j := by rw [τ0_w]; show 5 + 4 * j + 3 ≤ 4 + 4 * (j + 1); omega
  H_RCV j := by rw [τ1_w]; show 7 + 4 * j + 3 ≤ 10 + 4 * j; omega
  H_RST_EARLY := by decide

theorem timing_w : Timing2W Ww 1 1 3 3 where
  H_R_POS := by decide
  H_RST_LONG := by decide
  H_RST_LINES := by decide
  H_LAT0 := by decide
  H_LAT1 := by decide
  H_ACK_FLUSH := by decide

/-- **Non-vacuity of `pipe_fifo`.** A concrete live run satisfies every
hypothesis; its LUT bands are two ticks wide (`lo + 2 ≤ hi`), so the
window channel there admits glitching behaviours that no FIFO read
reproduces; the nodes alternate every 4 ticks. -/
theorem witness :
    Gates2W Ww rstW (sq 4) (sq 8) (sq 6) (sq 6) (sq 10) (sq 8) 1 1 1 1 ∧
    Env2W Ww (sq 4) (sq 10) 3 3 ∧ Timing2W Ww 1 1 3 3 ∧
    Ww.lo0 + 2 ≤ Ww.hi0 ∧ Ww.lo1 + 2 ≤ Ww.hi1 ∧
    (∀ j, Ww.τ0 j = 5 + 4 * j ∧ Ww.τ1 j = 7 + 4 * j) :=
  ⟨gates_w, env_w, timing_w, by decide, by decide, fun j => ⟨τ0_w j, τ1_w j⟩⟩

theorem witness_fifo :
    ∃ L0 L1 : Ret, L0.lo = 1 ∧ L0.hi = 3 ∧ L1.lo = 1 ∧ L1.hi = 3 ∧
      PipeTimed.Gates2 (Ww.sk L0 L1) rstW (sq 4) (sq 8) (sq 5) (sq 6) (sq 6) (sq 10) (sq 7) (sq 8)
        1 1 1 1 ∧
      PipeTimed.Env2 (Ww.sk L0 L1) (sq 4) (sq 10) 3 3 ∧ PipeTimed.Timing2 (Ww.sk L0 L1) 1 1 3 3 :=
  by
  obtain ⟨L0, L1, a, b, c, d, e, f, g, _⟩ := pipe_fifo gates_w env_w timing_w
  exact ⟨L0, L1, a, b, c, d, e, f, g⟩

/-! ### Single stage, with junk pins before reset release -/

/-- Request and acknowledge are HIGH (junk) before reset release at 4. -/
def reqJ (t : Nat) : Bool := if t < 4 then true else sq 4 t
def ackJ (t : Nat) : Bool := if t < 4 then true else sq 8 t

theorem exJ (q : Trace) (s : Nat) : ex reqJ ackJ q rstW s = ex (sq 4) (sq 8) q rstW s := by
  by_cases h : s < 4
  · unfold ex; rw [CElemTiming.c2n_eq, CElemTiming.c2n_eq]
    have : rstW s = true := by unfold rstW; simp [h]
    rw [this]; rfl
  · unfold ex reqJ ackJ; simp only [h, ite_false]

theorem stage1_w : Stage reqJ ackJ rstW (sq 5) (sq 6) 1 3 1 1 := by
  have S := stage_sq 4 (by omega)
  have e : ex reqJ ackJ (sq 6) rstW = ex (sq 4) (sq 8) (sq 6) rstW := funext (exJ (sq 6))
  exact ⟨e ▸ S.H_LUT_WIN, e ▸ S.H_NO_REVERT, S.H_FB, S.H_LOOP_POS⟩

def ρ1 (j : Nat) : Nat := 4 + 4 * j

theorem τs_w (j : Nat) : τs (sq 5) 1 3 ρ1 ρ1 j = 5 + 4 * j := by
  unfold τs cph ρ1; rw [Nat.max_self, nt_eq (sq 5) (by decide) (sq_phase 5 j _ (by omega) (by omega))]
  omega

theorem env1_w : Env1 reqJ ackJ rstW (sq 5) 1 3 4 ρ1 ρ1 3 3 where
  H_RST _ := rfl
  H_REQ_LOW0 t h1 h2 := by simp only [ρ1] at h2; omega
  H_REQ j t h1 h2 := by
    simp only [ρ1] at h1 h2
    unfold reqJ; simp only [show ¬ (t < 4) by omega, ite_false]; exact sq_phase 4 j t h1 (by omega)
  H_ACK0 := rfl
  H_ACK j t h1 h2 := by
    simp only [ρ1] at h1 h2
    unfold ackJ; simp only [show ¬ (t < 4) by omega, ite_false]
    cases j with
    | zero => rw [sq_pre 8 t (by omega)]; rfl
    | succ k =>
      rw [sq_phase 8 k t (by omega) (by omega), PipeTimed.Vph_succ, Bool.not_not]
  H_RST_EARLY := by decide
  H_SND j := by rw [τs_w]; simp only [ρ1]; omega
  H_RCV j := by rw [τs_w]; simp only [ρ1]; omega

theorem timing1_w : Timing1 1 3 1 4 3 3 := ⟨by decide, by decide, by decide⟩

/-- **Non-vacuity of `stage_fifo`**, with request and acknowledge junk
(high) before reset release `R = 4`: the conclusion (clean excitation from
time 0, a FIFO `Ctl` of band `[1, 3]`) holds. -/
theorem witness1 :
    Stage reqJ ackJ rstW (sq 5) (sq 6) 1 3 1 1 ∧ Env1 reqJ ackJ rstW (sq 5) 1 3 4 ρ1 ρ1 3 3 ∧
    Timing1 1 3 1 4 3 3 ∧ reqJ 0 = true ∧ sq 4 0 = false ∧
    ∃ L : Ret, L.lo = 1 ∧ L.hi = 3 ∧ Ctl reqJ ackJ rstW (sq 5) (sq 6) L 1 1 := by
  obtain ⟨_, _, _, L, a, b, c, _⟩ := stage_fifo stage1_w env1_w timing1_w
  exact ⟨stage1_w, env1_w, timing1_w, rfl, rfl, L, a, b, c⟩

/-! ### Counter-run: H_NO_REVERT cannot be dropped

The single-stage witness with ONE glitch: the node drops for one tick at
`t = 6`, inside its first uncertainty zone `[5, 7)` (the LUT window `[3, 5]`
still contains the excitation's old value 0 at 3). The feedback carries the
glitch to I2 at 7, where the excitation is forced by req = 1, ack = 0, so it
is unchanged. Every hypothesis of `stage_fifo` except H_NO_REVERT holds; the
conclusion fails for every FIFO band with `hi ≤ 5`. -/
def Og (t : Nat) : Bool := if t = 6 then false else sq 5 t
def qg (t : Nat) : Bool := if t = 7 then false else sq 6 t

theorem exg (s : Nat) : ex (sq 4) (sq 8) qg rstW s = sq 4 s := by
  by_cases h : s = 7
  · subst h; decide
  · have : ex (sq 4) (sq 8) qg rstW s = ex (sq 4) (sq 8) (sq 6) rstW s := by
      unfold ex qg; simp only [h, ite_false]
    rw [this, key 4 s (by omega)]

theorem Og_eq (t : Nat) (h : t ≠ 6) : Og t = sq 5 t := by unfold Og; simp [h]

theorem τs_g (j : Nat) : τs Og 1 3 ρ1 ρ1 j = 5 + 4 * j := by
  unfold τs cph ρ1; rw [Nat.max_self]
  rw [nt_eq Og (by decide) (by rw [Og_eq _ (by omega)]; exact sq_phase 5 j _ (by omega) (by omega))]
  omega

theorem no_revert_needed :
    Win 1 3 (ex (sq 4) (sq 8) qg rstW) Og ∧ CElemTiming.WinDelay 1 1 Og qg ∧ 1 ≤ 1 + 1 ∧
    Env1 (sq 4) (sq 8) rstW Og 1 3 4 ρ1 ρ1 3 3 ∧ Timing1 1 3 1 4 3 3 ∧
    ¬ NoRevertI 1 3 (ex (sq 4) (sq 8) qg rstW) Og ∧
    ∀ L : Ret, L.hi ≤ 5 → ¬ Ctl (sq 4) (sq 8) rstW Og qg L 1 1 := by
  refine ⟨?_, ?_, by decide, ?_, timing1_w, ?_, ?_⟩
  · intro t ht
    by_cases h : t = 6
    · subst h; exact ⟨3, by omega, by omega, by rw [exg]; decide⟩
    · refine ⟨t - 1, by omega, by omega, ?_⟩
      rw [exg, Og_eq t h]
      have := sq_shift 4 1 (t - 1); rw [Nat.sub_add_cancel (by omega)] at this; exact this
  · apply CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
    intro t
    unfold qg Og
    by_cases h : t = 6
    · subst h; rfl
    · simp only [show t + 1 ≠ 7 by omega, h, ite_false]; exact sq_shift 5 1 t
  · exact { H_RST := fun _ => rfl
            H_REQ_LOW0 := fun t h1 h2 => by simp only [ρ1] at h2; omega
            H_REQ := fun j t h1 h2 => by simp only [ρ1] at h1 h2; exact sq_phase 4 j t h1 (by omega)
            H_ACK0 := rfl
            H_ACK := fun j t h1 h2 => by
              simp only [ρ1] at h1 h2
              cases j with
              | zero => rw [sq_pre 8 t (by omega)]; rfl
              | succ k => rw [sq_phase 8 k t (by omega) (by omega), PipeTimed.Vph_succ, Bool.not_not]
            H_RST_EARLY := by decide
            H_SND := fun j => by rw [τs_g]; simp only [ρ1]; omega
            H_RCV := fun j => by rw [τs_g]; simp only [ρ1]; omega }
  · intro h
    have := h 4 8 true 5 6 (fun s a b => by rw [exg]; exact sq_phase 4 0 s (by omega) (by omega))
      (by omega) (by omega) (by omega) (by omega) (by decide)
    exact absurd this (by decide)
  · intro L hL C
    have h5 := C.H_LUT_FIFO 5 hL
    have h6 := C.H_LUT_FIFO 6 (by omega)
    have m := L.mono 5 6 (by omega)
    have l6 := L.le 6
    rw [exg] at h5 h6
    have o5 : Og 5 = true := by decide
    have o6 : Og 6 = false := by decide
    rw [o5] at h5; rw [o6] at h6
    unfold sq at h5 h6
    simp only [eq_comm (a := true), eq_comm (a := false), decide_eq_true_eq,
      decide_eq_false_iff_not] at h5 h6
    omega

end Wx

end Formal.Cells.WinFifoCausal
