import Formal.Net.CapstoneRigAllPer
import Formal.Net.CapstoneRig

/-!
# Probe C-8s3: every result of gcd_rig is `gcd a b`

`gcd_rig` (`cells/hw/gcd_rig.v`) closes the kernel into a ring through two C-elements with one
inverted input each (`bd_c2n` = C(a, ¬b), INIT `0x..B2`):

* `uenv1 = bd_c2n_set(a = env_c0, b = in_ack)` drives `start_req` (`bd_fork`'s `req_out` is the
  wire `{N{req}}`);
* `uenv0 = bd_c2n(a = res_req, b = env_c)`, and `out0_ack = res_ack = env_c0`.

Their gate models (H_CEL_SI style: a C-element moves only to the value its inputs agreed on
one tick earlier) give four facts about the kernel's `start.req` (= `env_c`) and `out0.ack`
(= `env_c0`), `RigEnv`:

* `start.req` rises only while `out0.ack` is high, falls only while it is low (uenv1);
* `out0.ack` rises only while `start.req` is low, falls only while it is high (uenv0).

So the environment is a strict four-phase cycle `(1,0) → (0,0) → (0,1) → (1,1) → (1,0)` of
`(start.req, out0.ack)`, and (`env_inv`) `#rises(out0.ack) = #rises(start.req) + [¬start ∧ ack]`:
at the `j`-th re-offer of `start`, `out0` has been acknowledged `j` times.

The kernel side (`out0_le_zEnd`, from the gate models alone): `out0` is the 3-way mux whose select
`g250` comes through two links from `forkG 464 [417, 413]`, so `out0` is never offered more
often than `z251` (464). Together these give H_START_GATE, and `gcd_hw_circuit_safe_all` gives:

**`gcd_rig_all`**: under H_CELLS without `Src.iz` (the rig's reset level), H_BUNDLE and
`RigEnv`, every value `out0` offers and every value it latches, in every invocation, is
`gcd a b` (for `a, b < 2^31`).
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.GcdHw
open Formal.Net.CapSafe Formal.Net.Capstone.O1 Formal.Net.Capstone.Cut

/-! ## Counting -/

theorem cum_of_strict {x y : Trace}
    (h : ∀ t, riseB x t = true → cnt (riseB x) (t + 1) ≤ cnt (riseB y) t) :
    ∀ t, cnt (riseB x) t ≤ cnt (riseB y) t
  | 0 => by simp [Handshake.cnt]
  | t + 1 => by
    have ih := cum_of_strict h t
    have hm : cnt (riseB y) t ≤ cnt (riseB y) (t + 1) := cnt_mono _ (Nat.le_succ t)
    by_cases hr : riseB x t = true
    · exact Nat.le_trans (h t hr) hm
    · have : cnt (riseB x) (t + 1) = cnt (riseB x) t := by
        rw [cnt_succ']; simp [bn, hr]
      omega

/-- Four-phase: requests are offered exactly as often as they are acknowledged, plus the one
pending. -/
theorem req_ack_cnt {c : Chan} (hp : Protocol c) :
    ∀ t, cnt (riseB c.req) t = cnt (riseB c.ack) t + bn (c.req t && !c.ack t)
  | 0 => by simp [Handshake.cnt, bn, hp.1.1]
  | t + 1 => by
    have ih := req_ack_cnt hp t
    rw [cnt_succ', cnt_succ']
    obtain ⟨hs, hr⟩ := hp.2 t
    unfold SendStep at hs
    unfold RecvStep at hr
    cases h1 : c.req t <;> cases h2 : c.req (t + 1) <;> cases h3 : c.ack t <;>
      cases h4 : c.ack (t + 1) <;> simp_all [riseB, bn] <;> omega

theorem ack_le_req {c : Chan} (hp : Protocol c) (t : Nat) :
    cnt (riseB c.ack) t ≤ cnt (riseB c.req) t := by
  have := req_ack_cnt hp t; omega

/-! ## The rig's environment -/

/-- **The rig's environment gates** (uenv1 and uenv0 of `gcd_rig.v`, as C(a, ¬b) gate models):
`s` is `start_req` (= `env_c`), `k` is `out0_ack` (= `env_c0`). -/
structure RigEnv (s k : Trace) : Prop where
  s_rise : ∀ t, riseB s t = true → k t = true
  s_fall : ∀ t, fallB s t = true → k t = false
  k_rise : ∀ t, riseB k t = true → s t = false
  k_fall : ∀ t, fallB k t = true → s t = true

/-- The environment's counter invariant: `out0` has been acknowledged once per offer of
`start` after reset, plus one while the environment holds a result and has not yet re-offered. -/
theorem env_inv {s k : Trace} (E : RigEnv s k) (h0 : k 0 = false) :
    ∀ t, cnt (riseB k) t = cnt (riseB s) t + bn (!s t && k t)
  | 0 => by simp [Handshake.cnt, bn, h0]
  | t + 1 => by
    have ih := env_inv E h0 t
    rw [cnt_succ', cnt_succ']
    have g1 := E.s_rise t
    have g2 := E.s_fall t
    have g3 := E.k_rise t
    have g4 := E.k_fall t
    cases h1 : s t <;> cases h2 : s (t + 1) <;> cases h3 : k t <;>
      cases h4 : k (t + 1) <;> simp_all [riseB, fallB, bn] <;> omega

/-- At every re-offer of `start`, `out0` has been acknowledged once more than `start` was
re-offered before. -/
theorem env_at_rise {s k : Trace} (E : RigEnv s k) (h0 : k 0 = false) {t : Nat}
    (hr : riseB s t = true) : cnt (riseB k) t = cnt (riseB s) t + 1 := by
  have := env_inv E h0 t
  have hk := E.s_rise t hr
  have hs : s t = false := by simp [riseB] at hr; exact hr.1
  rw [hs, hk] at this; simpa [bn] using this

/-! ## The kernel side: `out0` is never ahead of `z251` -/

section kern
variable {a b : Nat} {ch : Fin NC → Chan}
variable (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
variable (H_BUNDLE : ∀ c, Held (ch c))

def g413 : Fin NC := 413
def g414 : Fin NC := 414
def g415 : Fin NC := 415

theorem prod_out0 : opAt (prodOf out0) = .muxn g415 14 32 412 out0
    ⟨153, 249, 11, 25, 248, 250, 0, 0, 0, 0, 464, 463, 408, 16, 34, 8, 7⟩ := rfl
theorem prod_415 : opAt (prodOf g415) = .link g414 g415 := rfl
theorem prod_414 : opAt (prodOf g414) = .link g413 g414 := rfl
theorem prod_413 : opAt (prodOf g413) = .forkG zEnd [eEnd, g413] := rfl

include H_CELLS H_BUNDLE in
theorem out0_le_415 (t : Nat) : cnt (riseB (ch out0).req) t ≤ cnt (riseB (ch g415).req) t := by
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE
  have hc := H_CELLS (prodOf out0)
  rw [prod_out0] at hc
  obtain ⟨j, M⟩ := hc
  have := (MuxN.muxn_inv M (fun k _ => (hp _).1.1) (hp g415).1.1 (hp out0).1.2 (H_BUNDLE g415) t
    (fun s _ => ⟨fun k _ => (hp _).2 s |>.1, (hp g415).2 s |>.1, (hp out0).2 s |>.2⟩)).2.1
  omega

include H_CELLS H_BUNDLE in
theorem link_le {i o : Fin NC} (hk : opAt (prodOf o) = .link i o) (t : Nat) :
    cnt (riseB (ch o).req) t ≤ cnt (riseB (ch i).req) t := by
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE
  have hc := H_CELLS (prodOf o)
  rw [hk] at hc
  obtain ⟨cc, L⟩ := hc
  exact cum_of_strict (fun t hr => link_strict L (hp i) (hp o) hr) t

include H_CELLS H_BUNDLE in
theorem g413_le_zEnd (t : Nat) : cnt (riseB (ch g413).req) t ≤ cnt (riseB (ch zEnd).req) t := by
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE
  have hc := H_CELLS (prodOf g413)
  rw [prod_413] at hc
  exact cum_of_strict (fun t hr => fork_strict hc (hp zEnd)
    (fun o ho => by obtain ⟨c', _, e⟩ := List.mem_map.mp ho; rw [← e]; exact hp c')
    (by simp) hr) t

include H_CELLS H_BUNDLE in
/-- **`out0` is never offered more often than `z251`** (gate models only). -/
theorem out0_le_zEnd (t : Nat) : cnt (riseB (ch out0).req) t ≤ cnt (riseB (ch zEnd).req) t := by
  have h1 := out0_le_415 H_CELLS H_BUNDLE t
  have h2 := link_le H_CELLS H_BUNDLE prod_415 t
  have h3 := link_le H_CELLS H_BUNDLE prod_414 t
  have h4 := g413_le_zEnd H_CELLS H_BUNDLE t
  omega

end kern

/-! ## The rig -/

theorem cnt_pd_rise (x : Trace) : ∀ t, cnt (riseB (pd x)) (t + 1) = cnt (riseB x) t
  | 0 => by simp [Handshake.cnt, riseB]
  | t + 1 => by
    have ih := cnt_pd_rise x t
    show cnt (riseB (pd x)) (t + 1) + (if riseB (pd x) (t + 1) = true then 1 else 0) =
      cnt (riseB x) t + if riseB x t = true then 1 else 0
    have : riseB (pd x) (t + 1) = riseB x t := rfl
    rw [ih, this]

/-- **H_START_GATE for the rig**, on the run with one idle tick prepended (the reset level of
`start_req` is its first offer). -/
theorem rig_gate (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_R : ∀ o : Fin NO, CellR ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_ENV : RigEnv (ch start).req (ch out0).ack) :
    H_START_GATE (preRun ch) := by
  have hC := preRun_cells a b ch H_CELLS_R
  have hH : ∀ c, Held (preRun ch c) := fun c => held_pc (H_BUNDLE c)
  have hp := gcd_hw_protocol a b (preRun ch) hC hH
  have hk0 : (ch out0).ack 0 = false := (hp out0).1.2
  intro t hr
  cases t with
  | zero => simp [Handshake.cnt]
  | succ s =>
    have hr' : riseB (ch start).req s = true := hr
    have e1 := env_at_rise H_ENV hk0 hr'
    have e2 : cnt (riseB (preRun ch out0).ack) (s + 1) = cnt (riseB (ch out0).ack) s :=
      cnt_pd_rise _ s
    have e3 := ack_le_req (hp out0) (s + 1)
    have e4 := out0_le_zEnd hC hH (s + 1)
    have e5 : cnt (riseB (preRun ch start).req) (s + 1) =
        (if (ch start).req 0 = true then 1 else 0) + cnt (riseB (ch start).req) s :=
      cnt_pc_rise _ s
    have e6 : (if (ch start).req 0 = true then 1 else 0) ≤ 1 := by split <;> omega
    omega

/-- **Every result of gcd_rig is `gcd a b`.** `ch` starts at reset release (`start_req` may be
high: `Src.iz` is not assumed). Under H_CELLS without `Src.iz`, H_BUNDLE, the rig's environment
gates `RigEnv` (uenv1/uenv0) and the range: every value `out0` offers (the bus right after each
request rise) and every value it latches (at each acknowledge fall), in every invocation, is
`gcd a b`. -/
theorem gcd_rig_all (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (H_CELLS_R : ∀ o : Fin NO, CellR ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_ENV : RigEnv (ch start).req (ch out0).ack) :
    (∀ k r, OffAt (ch out0) k r → (ch out0).dat (r + 1) = Nat.gcd a b) ∧
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) := by
  have hC := preRun_cells a b ch H_CELLS_R
  have hH : ∀ c, Held (preRun ch c) := fun c => held_pc (H_BUNDLE c)
  have hG := rig_gate a b ch H_CELLS_R H_BUNDLE H_ENV
  have h0 := out0_req0 a b ch H_CELLS_R
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  have hF := gcd_hw_forcedR a b (preRun ch) y hy hC hH hG (walk_okR hy hex)
  have hop := fun o => cell_op (preRun ch) (omOf a b y) (srcV a b) (opAt o) (hC o) (hF o)
    (dist_of _ (ops_ok o))
  have hoff : ∀ k r, OffAt (preRun ch out0) k r → (preRun ch out0).dat (r + 1) = Nat.gcd a b := by
    intro k r ho
    rw [← Ops.net_refines net (preRun ch) (fun o => Eqn (preRun ch) (omOf a b y) (srcV a b) (opAt o))
      (fun o => (hop o).1) hH (fun o => (hop o).2) (fun c i => refT tab (Hh a b y) c.val i)
      (fun o => eqn_sound hy rank_ok nf_pos (preRun ch) (opAt o) (ops_ok o)) out0 k r ho]
    show refT tab (Hh a b y) out0.val k = Nat.gcd a b
    rw [ref_hist tab _ out0_desc nf_pos, out0_hist hy]
    simp [perL, Nat.mod_one]
  have hsafe := (gcd_hw_circuit_safeR a b (preRun ch) hC hH hG ⟨y, hy, walk_okR hy hex⟩).1
  refine ⟨fun k r ho => ?_, fun k e ht => ?_⟩
  · exact hoff k (r + 1) (off_pre h0 ho)
  · exact hsafe k (e + 1) (tok_pre ht)

end Formal.Net.CapNet.Gcd
