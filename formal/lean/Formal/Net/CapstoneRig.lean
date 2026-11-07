import Formal.Net.CapstoneWalk
import Formal.Net.CapstoneRigTime

/-!
# Probe C-8s2: from one start offer to gcd_rig's re-offering environment

`gcd_hw_circuit_safe3` (8s) assumes H_START_ONCE: `start.req` rises at most once in the whole
run. gcd_rig (`cells/hw/gcd_rig.v`) re-offers `start` after every result, forever, so that
hypothesis is false for the rig's run. This module removes it for the FIRST result, and
settles the rig's reset level.

* `gcd_hw_offer_safe`: the offer-level form of 8s's theorem (the value on `out0` right after
  each request rise is `gcd a b`), under the same hypotheses.
* `gcd_hw_window`: under H_CELLS and H_BUNDLE only (and the range), every `out0` token OFFERED
  while `start` has risen at most once is `gcd a b`. Proof: freeze the whole run (every wire
  and every ghost trace) right after that offer (`CapstoneRigTime.cell_rt`, `frz`); the frozen
  run meets H_CELLS, H_BUNDLE and H_START_ONCE.
* `gcd_hw_first`: with H_START_AFTER_RESULT (`start`'s second offer comes after `out0`'s first
  offer) instead of H_START_ONCE, the first value latched on `out0` is `gcd a b`.
* The reset caveat: gcd_rig's `uenv1` is a `bd_c2n_set`, so `start_req = a_req = b_req = 1`
  through reset and at reset release; `Src.iz` (request low at tick 0) is false for the rig.
  `gcd_rig_first` takes `CellR` (= H_CELLS with `Src.iz` dropped) and prepends one idle tick
  (`CapstoneRigTime.cell_pc`): the reset level becomes the first offer. Its environment
  hypothesis `H_ENV` is uenv1's own gate model: `env_c` (= `start_req`) rises only while
  `env_c0` (= `out0_ack`) is high.
* Several invocations: `gcd_hw_window_from` proves every result in a window that starts at a
  re-arm point `T` (the cell models hold again from `T`, reset fields included: `H_REARM`).
  `rearm_fails_at_reoffer`: under `H_ENV`, `H_REARM` is FALSE at every re-offer of `start`,
  because `out0`'s acknowledge is still high there (the rig's `env_c0` falls only after
  `env_c` has risen again). So induction over invocations by re-arming does not apply to the
  rig; see `formal/notes/C-8s2-rig.md`.
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw
open Formal.Net.CapSafe

/-! ## Counting lemmas -/

theorem cnt_frz (s : Trace) (T : Nat) :
    ∀ t, cnt (riseB (fun u => s (frz T u))) t = cnt (riseB s) (min t T)
  | 0 => by simp [Handshake.cnt]
  | t + 1 => by
    have ih := cnt_frz s T t
    show cnt (riseB (fun u => s (frz T u))) t +
        (if riseB (fun u => s (frz T u)) t = true then 1 else 0) = _
    rw [ih]
    by_cases h : t + 1 ≤ T
    · have e1 : min (t + 1) T = t + 1 := by omega
      have e2 : min t T = t := by omega
      have e3 : frz T t = t := e2
      have e4 : frz T (t + 1) = t + 1 := e1
      rw [e1, e2]
      simp only [riseB, e3, e4]; rfl
    · have e1 : min (t + 1) T = T := by omega
      have e2 : min t T = T := by omega
      have e3 : frz T t = T := e2
      have e4 : frz T (t + 1) = T := e1
      rw [e1, e2]
      simp [riseB, e3, e4]

theorem cnt_shf (s : Trace) (T : Nat) :
    ∀ t, cnt (riseB (fun u => s (shf T u))) t + cnt (riseB s) T = cnt (riseB s) (t + T)
  | 0 => by simp [Handshake.cnt]
  | t + 1 => by
    have ih := cnt_shf s T t
    rw [show t + 1 + T = (t + T) + 1 by omega]
    show cnt (riseB (fun u => s (shf T u))) t +
        (if riseB (fun u => s (shf T u)) t = true then 1 else 0) + cnt (riseB s) T =
        cnt (riseB s) (t + T) + (if riseB s (t + T) = true then 1 else 0)
    have : riseB (fun u => s (shf T u)) t = riseB s (t + T) := by
      simp only [riseB, shf, Nat.add_right_comm t 1 T]
    rw [this]; omega

theorem cnt_pc_rise (c : Chan) :
    ∀ t, cnt (riseB (pc c).req) (t + 1) = (if c.req 0 = true then 1 else 0) + cnt (riseB c.req) t
  | 0 => by simp [Handshake.cnt, riseB]
  | t + 1 => by
    have ih := cnt_pc_rise c t
    show cnt (riseB (pc c).req) (t + 1) + (if riseB (pc c).req (t + 1) = true then 1 else 0) =
      _ + (cnt (riseB c.req) t + if riseB c.req t = true then 1 else 0)
    have : riseB (pc c).req (t + 1) = riseB c.req t := rfl
    rw [ih, this]; omega

theorem cnt_pd_fall (x : Trace) : ∀ t, cnt (fallB (pd x)) (t + 1) = cnt (fallB x) t
  | 0 => by simp [Handshake.cnt, fallB]
  | t + 1 => by
    have ih := cnt_pd_fall x t
    show cnt (fallB (pd x)) (t + 1) + (if fallB (pd x) (t + 1) = true then 1 else 0) =
      cnt (fallB x) t + if fallB x t = true then 1 else 0
    have : fallB (pd x) (t + 1) = fallB x t := rfl
    rw [ih, this]

/-- If at least `k+1` events happened before `t`, the `k`-th one happened at some `e < t`. -/
theorem cnt_ge (f : Nat → Bool) : ∀ t k, k + 1 ≤ cnt f t → ∃ e, e < t ∧ f e = true ∧ cnt f e = k
  | 0, k, h => by simp [Handshake.cnt] at h
  | t + 1, k, h => by
    have hs : cnt f (t + 1) = cnt f t + if f t = true then 1 else 0 := rfl
    by_cases hk : k + 1 ≤ cnt f t
    · obtain ⟨e, he, hf, hc⟩ := cnt_ge f t k hk
      exact ⟨e, by omega, hf, hc⟩
    · cases hft : f t
      · rw [hs, hft] at h; simp at h; omega
      · rw [hs, hft] at h; simp at h
        exact ⟨t, by omega, hft, by omega⟩

/-! ## The offer-level circuit theorem -/

/-- **8s's circuit theorem at offers**: under H_CELLS, H_BUNDLE, H_START_ONCE and the range,
the bus of `out0` right after each request rise is `gcd a b`. -/
theorem gcd_hw_offer_safe (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    ∀ k r, OffAt (ch out0) k r → (ch out0).dat (r + 1) = Nat.gcd a b := by
  obtain ⟨y, hy, hw⟩ := gcd_hw_walk a b ha hb
  have hF := gcd_hw_forced a b ch y hy H_CELLS H_BUNDLE H_START_ONCE hw
  have hop := fun o => cell_op ch (omOf a b y) (srcV a b) (opAt o) (H_CELLS o) (hF o)
    (dist_of _ (ops_ok o))
  intro k r ho
  rw [← Ops.net_refines net ch (fun o => Eqn ch (omOf a b y) (srcV a b) (opAt o))
    (fun o => (hop o).1) H_BUNDLE (fun o => (hop o).2) (fun c i => refT tab (Hh a b y) c.val i)
    (fun o => eqn_sound hy rank_ok nf_pos ch (opAt o) (ops_ok o)) out0 k r ho]
  show refT tab (Hh a b y) out0.val k = Nat.gcd a b
  rw [ref_hist tab _ out0_desc nf_pos, out0_hist hy]
  simp [perL, Nat.mod_one]

/-! ## Freezing: the window theorem -/

/-- **Window theorem (freezing)**: under H_CELLS, H_BUNDLE and the range only, every `out0`
token offered at a step `r` such that `start.req` rose at most once in steps `≤ r` carries
`gcd a b`. -/
theorem gcd_hw_window (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ k r, OffAt (ch out0) k r → cnt (riseB (ch start).req) (r + 1) ≤ 1 →
      (ch out0).dat (r + 1) = Nat.gcd a b := by
  intro k r ho hst
  generalize hTd : r + 1 = T
  rw [hTd] at hst
  let ch' : Fin NC → Chan := fun c => rtC (frz T) (ch c)
  have hC : ∀ o, Cell ch' (srcV a b) (opAt o) := fun o =>
    cell_rt (frz_mono T) (frz_zero T) (opAt o) (H_CELLS o)
  have hH : ∀ c, Held (ch' c) := fun c => held_rt (frz_mono T) (H_BUNDLE c)
  have hS : ∀ t, cnt (riseB (ch' start).req) t ≤ 1 := by
    intro t
    have e := cnt_frz (ch start).req T t
    have m := cnt_mono (riseB (ch start).req) (Nat.min_le_right t T)
    show cnt (riseB (fun u => (ch start).req (frz T u))) t ≤ 1
    omega
  have ho' : OffAt (ch' out0) k r := by
    have e3 : frz T r = r := by simp only [frz]; omega
    have e4 : frz T (r + 1) = r + 1 := by simp only [frz]; omega
    refine ⟨?_, ?_⟩
    · show riseB (fun u => (ch out0).req (frz T u)) r = true
      simp only [riseB, e3, e4]; exact ho.1
    · show cnt (riseB (fun u => (ch out0).req (frz T u))) r = k
      rw [cnt_frz, show min r T = r by omega]; exact ho.2
  have := gcd_hw_offer_safe a b ha hb ch' hC hH hS k r ho'
  have e4 : frz T (r + 1) = r + 1 := by simp only [frz]; omega
  have e5 : (ch' out0).dat (r + 1) = (ch out0).dat T := by
    show (ch out0).dat (frz T (r + 1)) = _
    rw [e4, hTd]
  rw [← e5]; exact this

/-- The window theorem at the close: the value latched by the close of an `out0` token that was
offered while `start` had risen at most once is `gcd a b`. -/
theorem gcd_hw_window_close (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ k e r, TokAt (ch out0) k e → OffAt (ch out0) k r → cnt (riseB (ch start).req) (r + 1) ≤ 1 →
      (ch out0).dat e = Nat.gcd a b := by
  intro k e r ht ho hst
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE out0
  rw [close_val hp (H_BUNDLE out0) ht ho]
  exact gcd_hw_window a b ha hb ch H_CELLS H_BUNDLE k r ho hst

/-! ## The first result under "start is re-offered only after a result" -/

/-- **First result, without H_START_ONCE**: if `start`'s second offer (if any) comes after
`out0`'s first offer (H_START_AFTER_RESULT), the first value latched on `out0` is `gcd a b`. -/
theorem gcd_hw_first (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_AFTER_RESULT : ∀ r2, OffAt (ch start) 1 r2 → ∃ r, r < r2 ∧ OffAt (ch out0) 0 r) :
    (∀ r, OffAt (ch out0) 0 r → (ch out0).dat (r + 1) = Nat.gcd a b) ∧
    (∀ e, TokAt (ch out0) 0 e → (ch out0).dat e = Nat.gcd a b) := by
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE out0
  have key : ∀ r, OffAt (ch out0) 0 r → cnt (riseB (ch start).req) (r + 1) ≤ 1 := by
    intro r ho
    apply Classical.byContradiction
    intro hc
    obtain ⟨r2, hr2, hf, hn⟩ := cnt_ge (riseB (ch start).req) (r + 1) 1 (by omega)
    obtain ⟨r', hr', ho'⟩ := H_START_AFTER_RESULT r2 ⟨hf, hn⟩
    have := off_unique ho ho'
    omega
  refine ⟨fun r ho => gcd_hw_window a b ha hb ch H_CELLS H_BUNDLE 0 r ho (key r ho), ?_⟩
  intro e ht
  obtain ⟨r, _, ho⟩ := tok_off hp ht
  exact gcd_hw_window_close a b ha hb ch H_CELLS H_BUNDLE 0 e r ht ho (key r ho)

/-! ## The rig's reset level: a prepended idle tick -/

def isSrcK {n : Nat} : K n → Bool
  | .src _ _ _ => true
  | _ => false

theorem cell_of_cellR {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} (k : K n)
    (hk : isSrcK k = false) (h : CellR ch sv k) : Cell ch sv k := by
  cases k with
  | src z which d => simp [isSrcK] at hk
  | _ => exact h

theorem src_ins_nil {n : Nat} (k : K n) (c : Fin n) (h : c ∈ k.insC) : isSrcK k = false := by
  cases k <;> first | rfl | simp [K.insC] at h

theorem out0_prod_nsrc : isSrcK (opAt (prodOf out0)) = false := by decide

/-- The run with one idle tick prepended (every request low, everything else as at tick 0). -/
def preRun (ch : Fin NC → Chan) : Fin NC → Chan := fun c => pc (ch c)

/-- **H_CELLS for the prepended run, from H_CELLS without `Src.iz`.** -/
theorem preRun_cells (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_R : ∀ o : Fin NO, CellR ch (srcV a b) (opAt o)) :
    ∀ o, Cell (preRun ch) (srcV a b) (opAt o) := by
  intro o
  refine cell_pc (opAt o) (H_CELLS_R o) ?_
  intro z which d _
  -- the source's acknowledge is driven by its (non-source) consumer, low at reset
  have hz : z ∈ (opAt (consOf z)).insC := (net.cons_iff z (consOf z)).2 rfl
  have hns := src_ins_nil _ z hz
  have hc := cell_of_cellR _ hns (H_CELLS_R (consOf z))
  exact (cell_proto ch (srcV a b) _ hc (dist_of _ (ops_ok _))).initIn z hz

theorem out0_req0 (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_R : ∀ o : Fin NO, CellR ch (srcV a b) (opAt o)) : (ch out0).req 0 = false := by
  have hz : out0 ∈ (opAt (prodOf out0)).outsC := (net.prod_iff out0 (prodOf out0)).2 rfl
  have hc := cell_of_cellR _ out0_prod_nsrc (H_CELLS_R (prodOf out0))
  exact (cell_proto ch (srcV a b) _ hc (dist_of _ (ops_ok _))).initOut out0 hz

theorem off_pre {c : Chan} (h0 : c.req 0 = false) {k r : Nat} (h : OffAt c k r) :
    OffAt (pc c) k (r + 1) := by
  refine ⟨h.1, ?_⟩
  rw [cnt_pc_rise, h0]; simpa using h.2

theorem off_pre_inv {c : Chan} (h0 : c.req 0 = false) {k r : Nat} (h : OffAt (pc c) k (r + 1)) :
    OffAt c k r := by
  refine ⟨h.1, ?_⟩
  have := h.2; rw [cnt_pc_rise, h0] at this; simpa using this

theorem tok_pre {c : Chan} {k e : Nat} (h : TokAt c k e) : TokAt (pc c) k (e + 1) := by
  refine ⟨h.1, ?_⟩
  show cnt (fallB (pd c.ack)) (e + 1) = k
  rw [cnt_pd_fall]; exact h.2

/-- **The rig's environment, as a gate model.** gcd_rig: `uenv1 = bd_c2n_set(a = env_c0,
b = in_ack)` drives `start_req` (through `bd_fork`, a wire), and `env_c0` is `out0_ack`. A
C-element `C(a, ¬b)` rises only when `a` is high, so (H_CEL_SI, one tick of inertial delay)
`start.req` rises only while `out0.ack` is high. -/
def H_ENV (ch : Fin NC → Chan) : Prop :=
  ∀ t, riseB (ch start).req t = true → (ch out0).ack t = true

/-- **The first result of gcd_rig.** `ch` starts at reset release (`start_req` may already be
high: `Src.iz` is not assumed). Under H_CELLS without `Src.iz`, H_BUNDLE, the rig's
environment gate `H_ENV`, and the range: the first value `out0` offers and the first value it
latches are `gcd a b`. -/
theorem gcd_rig_first (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS_R : ∀ o : Fin NO, CellR ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_ENV : H_ENV ch) :
    (∀ r, OffAt (ch out0) 0 r → (ch out0).dat (r + 1) = Nat.gcd a b) ∧
    (∀ e, TokAt (ch out0) 0 e → (ch out0).dat e = Nat.gcd a b) := by
  have hC := preRun_cells a b ch H_CELLS_R
  have hH : ∀ c, Held (preRun ch c) := fun c => held_pc (H_BUNDLE c)
  have h0 := out0_req0 a b ch H_CELLS_R
  have hp := gcd_hw_protocol a b (preRun ch) hC hH out0
  have hSAR : ∀ r2, OffAt (preRun ch start) 1 r2 →
      ∃ r, r < r2 ∧ OffAt (preRun ch out0) 0 r := by
    intro r2 ho
    cases r2 with
    | zero => have := ho.2; simp [Handshake.cnt] at this
    | succ s =>
      have hack : (ch out0).ack s = true := H_ENV s ho.1
      -- out0's acknowledge is high at prepended tick s+1, so it has been offered before
      have hi := rise_inv hp (s + 1)
      have hin : inTx (preRun ch out0) (s + 1) = true := by
        simp [inTx, preRun, hack]
      rw [hin] at hi
      obtain ⟨r, hr, hf, hc⟩ :=
        cnt_ge (riseB (preRun ch out0).req) (s + 1) 0 (by simp at hi; omega)
      exact ⟨r, hr, hf, hc⟩
  obtain ⟨h1, h2⟩ := gcd_hw_first a b ha hb (preRun ch) hC hH hSAR
  refine ⟨fun r ho => ?_, fun e ht => ?_⟩
  · exact h1 (r + 1) (off_pre h0 ho)
  · exact h2 (e + 1) (tok_pre ht)

/-- The rig's window theorem: every `out0` token offered while `start` has been offered at
most once, COUNTING THE RESET LEVEL as an offer, carries `gcd a b`. -/
theorem gcd_rig_window (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS_R : ∀ o : Fin NO, CellR ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ k r, OffAt (ch out0) k r →
      (if (ch start).req 0 = true then 1 else 0) + cnt (riseB (ch start).req) (r + 1) ≤ 1 →
      (ch out0).dat (r + 1) = Nat.gcd a b := by
  intro k r ho hst
  have hC := preRun_cells a b ch H_CELLS_R
  have hH : ∀ c, Held (preRun ch c) := fun c => held_pc (H_BUNDLE c)
  have h0 := out0_req0 a b ch H_CELLS_R
  have := gcd_hw_window a b ha hb (preRun ch) hC hH k (r + 1) (off_pre h0 ho)
    (by show cnt (riseB (pc (ch start)).req) (r + 1 + 1) ≤ 1; rw [cnt_pc_rise]; exact hst)
  exact this

/-! ## Several invocations: re-arming, and why it fails for the rig -/

/-- The run seen from tick `T` on. -/
def shiftRun (T : Nat) (ch : Fin NC → Chan) : Fin NC → Chan := fun c => rtC (shf T) (ch c)

/-- H_REARM at `T`: the gate models hold again from `T` on, as if `T` were reset (their reset
fields at `T`: every channel's request/acknowledge as the cell's reset field says, every
C-element ghost trace low). -/
def H_REARM (a b T : Nat) (ch : Fin NC → Chan) : Prop :=
  ∀ o, Cell (shiftRun T ch) (srcV a b) (opAt o)

/-- **One invocation after a re-arm point**: if the network re-arms at `T`, every `out0` token
offered at `r ≥ T` while `start` rose at most once in steps `T ≤ s ≤ r` carries `gcd a b`. -/
theorem gcd_hw_window_from (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (T : Nat) (hR : H_REARM a b T ch) (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ k r, OffAt (ch out0) k r → T ≤ r →
      cnt (riseB (ch start).req) (r + 1) ≤ cnt (riseB (ch start).req) T + 1 →
      (ch out0).dat (r + 1) = Nat.gcd a b := by
  intro k r ho hT hst
  have hH : ∀ c, Held (shiftRun T ch c) := fun c => held_rt (shf_mono T) (H_BUNDLE c)
  have e1 : r - T + T = r := by omega
  have ho' : OffAt (shiftRun T ch out0) (k - cnt (riseB (ch out0).req) T) (r - T) := by
    refine ⟨?_, ?_⟩
    · show riseB (fun u => (ch out0).req (shf T u)) (r - T) = true
      simp only [riseB, shf, e1, show r - T + 1 + T = r + 1 by omega]; exact ho.1
    · show cnt (riseB (fun u => (ch out0).req (shf T u))) (r - T) = _
      have := cnt_shf (ch out0).req T (r - T)
      rw [e1, ho.2] at this; omega
  have hs : cnt (riseB (shiftRun T ch start).req) (r - T + 1) ≤ 1 := by
    have := cnt_shf (ch start).req T (r - T + 1)
    rw [show r - T + 1 + T = r + 1 by omega] at this
    show cnt (riseB (fun u => (ch start).req (shf T u))) (r - T + 1) ≤ 1
    omega
  have := gcd_hw_window a b ha hb (shiftRun T ch) hR hH _ (r - T) ho' hs
  simpa [shiftRun, rtC, shf, show r - T + 1 + T = r + 1 by omega] using this

theorem out0_cons_sink : opAt (consOf out0) = K.sink out0 := rfl

/-- **Re-arming fails at the rig's re-offers.** Under `H_ENV`, at every step `T` where `start`
is re-offered, `out0`'s acknowledge is still high, while the re-armed `out0` sink requires it
low: `H_REARM` is false at `T`. (gcd_rig: `env_c0 = out0_ack` falls only after `env_c` has
risen again, so `out0`'s first handshake is still open at the second `start` offer.) -/
theorem rearm_fails_at_reoffer (a b : Nat) (ch : Fin NC → Chan) (H_ENV : H_ENV ch) (T : Nat)
    (hT : riseB (ch start).req T = true) : ¬ H_REARM a b T ch := by
  intro hR
  have hs := hR (consOf out0)
  rw [out0_cons_sink] at hs
  have h := hs.init
  have hack := H_ENV T hT
  simp [shiftRun, rtC, shf] at h
  rw [hack] at h
  exact absurd h (by decide)

end Formal.Net.CapNet.Gcd
