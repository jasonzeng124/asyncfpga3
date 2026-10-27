import Formal.Net.CapstoneRig
import Formal.Cells.RigToken
import Formal.Cells.CElemFn

/-!
# Probe Bsrc (shard B): the rig environment as C's `Capstone.Src`, and the time origin

Notes: `formal/notes/B-rig-src.md`. Builds on `RigToken` (probe Bu) and on shard C's
`CapstoneRigTime` / `CapstoneRig` (used, never edited).

The rig (`cells/hw/gcd_rig.v`): `uenv1 = bd_c2n_set(a = env_c0, b = in_ack)` drives
`env_c`; `bd_fork #(3) ufork` makes `a_req = b_req = start_req = env_c` (wires) and
`in_ack = bd_c3(a_ack, b_ack, start_ack)` (`bd_ctree #(3)` = one `bd_c3`, with rst);
`uenv0 = bd_c2n(a = res_req, b = env_c)` drives `env_c0 = out0_ack`. `a_data`, `b_data`
come from `vector(idx)`, combinational, and idx moves only under rst (rig contract).

C's network has three sources `K.src 0 0 0`, `K.src 1 1 0`, `K.src 2 2 0` (channels `a`,
`b`, `start`, values `srcV a b`), modelled by `Capstone.Src` (H_LUT_SI: `req` moves only
to `¬ack` of the previous tick; constant bus; `req 0 = false`).

## Results

* §1 time origin (bridge 3). `shiftC_req`/`shiftC_ack`: RigToken's `shiftC` (origin just
  before release, virtual `req = 0` tick) IS C's `pc ∘ rtC (shf T0)`, i.e. C's
  `preRun (shiftRun T0 ch)` (`rigC`), applied to every channel the same way.
  `start_per_result_C`: RigToken's count theorem on `rigC` channels verbatim.
* §2 prefix form. `RigPrefix` (the proposition) and `rig_prefix` (proved from C's
  `gcd_rig_window` and B's `start_per_result`): every `out0` offer made before `out0.ack`
  has risen carries `gcd a b`.
* §3 the env as `Src`, in rig time (bridge 4, B's timed model). `c3_move`: the fork's real
  `bd_c3` INIT in step form. `env_lut_si`: uenv1's `b` half + the c3 + the kernel's ack
  rule give exactly `Src.H_LUT_SI` on each of `a`, `b`, `start`, with every wire and pin a
  monotone causal read map (no SI assumption on the env). `env_lut_si_upto`: the causal
  version (kernel ack rule only before the step). `env_H_ENV`: C's `H_ENV` from
  RigToken's ring hypotheses.
* §4 composed with C (bridge 4, discharged in C's network). `rig_cellR`: C's `CellR` for
  every operator of gcd_hw, sources included, from the KERNEL's cell models only plus the
  env model: the kernel ack rule is not assumed but obtained from C's `gcd_hw_protocol`
  by freezing (no circularity). `gcd_rig_first_env`: C's `gcd_rig_first` with `H_ENV` and
  the sources' `SrcR` discharged.
* §5 witnesses and counter-runs.

`Src.iz` itself is FALSE for the rig at release (`env_c = 1`); that is the field which
cannot hold, and it is exactly what C's prepended tick (`preRun`) supplies.
-/

namespace Formal.Cells.RigSrc
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

/-! ## 1. The time origin (bridge 3) -/

/-- The rig run in C's convention: origin moved to release `T0` (`shiftRun`), then C's idle
tick prepended (`preRun`): the SAME re-timing on every channel. -/
def rigC (T0 : Nat) (ch : Fin NC → Chan) : Fin NC → Chan := preRun (shiftRun T0 ch)

theorem shiftC_req (c : Chan) (T0 : Nat) :
    ∀ u, RigToken.shiftC c.req T0 u = (pc (rtC (shf T0) c)).req u
  | 0 => rfl
  | u + 1 => by
    show (if u + 1 = 0 then false else c.req (T0 + (u + 1 - 1))) = c.req (u + T0)
    rw [if_neg (by omega), show T0 + (u + 1 - 1) = u + T0 by omega]

theorem shiftC_ack (c : Chan) (T0 : Nat) (h : c.ack T0 = false) :
    ∀ u, RigToken.shiftC c.ack T0 u = (pc (rtC (shf T0) c)).ack u
  | 0 => by
    show false = c.ack (0 + T0)
    rw [Nat.zero_add, h]
  | u + 1 => by
    show (if u + 1 = 0 then false else c.ack (T0 + (u + 1 - 1))) = c.ack (u + T0)
    rw [if_neg (by omega), show T0 + (u + 1 - 1) = u + T0 by omega]

theorem rigC_eq (T0 : Nat) (ch : Fin NC → Chan) (c : Fin NC) :
    rigC T0 ch c = pc (rtC (shf T0) (ch c)) := rfl

/-- **RigToken's count theorem, on C's channels.** `ch` is the rig run in rig time;
`(ch start).req` = `env_c` = `e`, `(ch out0).ack` = `env_c0` = `q`; the hypotheses are
`RigToken.ring_alternation`'s. At every tick `u` of C's run `rigC T0 ch`:
`#rises(start.req) ≤ #rises(out0.ack) + 1` and `#rises(out0.ack) ≤ #rises(start.req)`. -/
theorem start_per_result_C (ch : Fin NC → Chan) (T0 Tq : Nat) (φ1 φ0 : Nat → Nat)
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → (ch start).req s = true)
    (H_INIT_Q : ∀ s, Tq ≤ s → s ≤ T0 → (ch out0).ack s = false)
    (hφ1m : ∀ t t', T0 ≤ t → t ≤ t' → φ1 t ≤ φ1 t') (hφ1c : ∀ t, T0 ≤ t → φ1 t ≤ t)
    (hφ1q : ∀ t, T0 ≤ t → Tq ≤ φ1 t)
    (hφ0m : ∀ t t', T0 ≤ t → t ≤ t' → φ0 t ≤ φ0 t') (hφ0c : ∀ t, T0 ≤ t → φ0 t ≤ t)
    (hφ0q : ∀ t, T0 ≤ t → Tq ≤ φ0 t)
    (M1 : ∀ t, T0 ≤ t → (ch start).req (t + 1) ≠ (ch start).req t →
      (ch out0).ack (φ1 t) = (ch start).req (t + 1))
    (M0 : ∀ t, T0 ≤ t → (ch out0).ack (t + 1) ≠ (ch out0).ack t →
      (ch start).req (φ0 t) = !(ch out0).ack (t + 1)) :
    ∀ u, cnt (riseB (rigC T0 ch start).req) u ≤ cnt (riseB (rigC T0 ch out0).ack) u + 1 ∧
      cnt (riseB (rigC T0 ch out0).ack) u ≤ cnt (riseB (rigC T0 ch start).req) u := by
  have hTq : Tq ≤ T0 := by
    have := hφ1q T0 (Nat.le_refl _); have := hφ1c T0 (Nat.le_refl _); omega
  have hq0 : (ch out0).ack T0 = false := H_INIT_Q T0 hTq (Nat.le_refl _)
  have h := RigToken.start_per_result (ch start).req (ch out0).ack T0 Tq φ1 φ0 H_INIT_E H_INIT_Q
    hφ1m hφ1c hφ1q hφ0m hφ0c hφ0q M1 M0
  have e1 : RigToken.shiftC (ch start).req T0 = (rigC T0 ch start).req :=
    funext (shiftC_req (ch start) T0)
  have e2 : RigToken.shiftC (ch out0).ack T0 = (rigC T0 ch out0).ack :=
    funext (shiftC_ack (ch out0) T0 hq0)
  rw [e1, e2] at h
  exact h

/-! ## 2. The prefix form of C's theorem that `start_once_prefix` discharges -/

theorem cnt_pd_rise (x : Trace) : ∀ t, cnt (riseB (pd x)) (t + 1) = cnt (riseB x) t
  | 0 => by simp [Handshake.cnt, riseB]
  | t + 1 => by
    have ih := cnt_pd_rise x t
    show cnt (riseB (pd x)) (t + 1) + (if riseB (pd x) (t + 1) = true then 1 else 0) =
      cnt (riseB x) t + if riseB x t = true then 1 else 0
    have : riseB (pd x) (t + 1) = riseB x t := rfl
    rw [ih, this]

/-- **The prefix proposition** (C's main theorem restricted to the prefix before the first
returned result): every `out0` token offered at `r`, while `out0.ack` has not yet risen in
steps `< r + 1`, carries `gcd a b`. `ch` is a run in C's rig convention (tick 0 = release,
`start.req` may be high at tick 0). -/
def RigPrefix (a b : Nat) (ch : Fin NC → Chan) : Prop :=
  ∀ k r, OffAt (ch out0) k r → cnt (riseB (ch out0).ack) (r + 1) = 0 →
    (ch out0).dat (r + 1) = Nat.gcd a b

/-- **`RigPrefix`, proved**: C's `gcd_rig_window` (kernel cells without `Src.iz`, H_BUNDLE)
with its start-count premise discharged by B's `start_per_result` (RigToken's ring
hypotheses in rig time, `ch` the rig run, `shiftRun T0 ch` C's run). -/
theorem rig_prefix (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (T0 Tq : Nat) (φ1 φ0 : Nat → Nat)
    (H_CELLS_R : ∀ o : Fin NO, CellR (shiftRun T0 ch) (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (shiftRun T0 ch c))
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → (ch start).req s = true)
    (H_INIT_Q : ∀ s, Tq ≤ s → s ≤ T0 → (ch out0).ack s = false)
    (hφ1m : ∀ t t', T0 ≤ t → t ≤ t' → φ1 t ≤ φ1 t') (hφ1c : ∀ t, T0 ≤ t → φ1 t ≤ t)
    (hφ1q : ∀ t, T0 ≤ t → Tq ≤ φ1 t)
    (hφ0m : ∀ t t', T0 ≤ t → t ≤ t' → φ0 t ≤ φ0 t') (hφ0c : ∀ t, T0 ≤ t → φ0 t ≤ t)
    (hφ0q : ∀ t, T0 ≤ t → Tq ≤ φ0 t)
    (M1 : ∀ t, T0 ≤ t → (ch start).req (t + 1) ≠ (ch start).req t →
      (ch out0).ack (φ1 t) = (ch start).req (t + 1))
    (M0 : ∀ t, T0 ≤ t → (ch out0).ack (t + 1) ≠ (ch out0).ack t →
      (ch start).req (φ0 t) = !(ch out0).ack (t + 1)) :
    RigPrefix a b (shiftRun T0 ch) := by
  intro k r ho hack
  apply gcd_rig_window a b ha hb (shiftRun T0 ch) H_CELLS_R H_BUNDLE k r ho
  have hc := (start_per_result_C ch T0 Tq φ1 φ0 H_INIT_E H_INIT_Q hφ1m hφ1c hφ1q hφ0m hφ0c hφ0q
    M1 M0 (r + 1 + 1)).1
  rw [rigC_eq, rigC_eq] at hc
  have e1 := cnt_pc_rise (rtC (shf T0) (ch start)) (r + 1)
  have e2 : cnt (riseB (pc (rtC (shf T0) (ch out0))).ack) (r + 1 + 1) =
      cnt (riseB (rtC (shf T0) (ch out0)).ack) (r + 1) := cnt_pd_rise _ (r + 1)
  have e3 : cnt (riseB (rtC (shf T0) (ch out0)).ack) (r + 1) = 0 := hack
  show (if (rtC (shf T0) (ch start)).req 0 = true then 1 else 0) +
    cnt (riseB (rtC (shf T0) (ch start)).req) (r + 1) ≤ 1
  omega

/-! ## 3. The env as `Src`, in rig time (B's timed model) -/

open Formal.Cells.CElemFn (c3B)

theorem c3B_rst : ∀ a b c q : Bool, c3B a b c q true = false := by decide

/-- **The fork's `bd_c3` (INIT `0000FE80_0000FE80`) in step form**, same hypotheses as
`RigToken.set_move`: H_LUT_FIFO (output = the LUT of its pins read at one monotone instant
`σ t`), H_RST_ONE_FALL, H_FB_FIRST (RT_FB at the read). Then every move goes to the value
all three inputs show at the read. -/
theorem c3_move {a b c rst O qp : Nat → Bool} {σ : Nat → Nat} {T0 Tr : Nat}
    (H_LUT_FIFO : ∀ t, T0 ≤ t → O t = c3B (a (σ t)) (b (σ t)) (c (σ t)) (qp (σ t)) (rst (σ t)))
    (hσm : ∀ t t', t ≤ t' → σ t ≤ σ t')
    (hσr : ∀ t, T0 ≤ t → Tr ≤ σ t)
    (H_RST_ONE_FALL : ∀ s s', Tr ≤ s → s ≤ s' → rst s' = true → rst s = true)
    (H_FB_FIRST : ∀ t, T0 ≤ t → O (t + 1) ≠ O t → qp (σ (t + 1)) = O t) :
    ∀ t, T0 ≤ t → O (t + 1) ≠ O t →
      a (σ (t + 1)) = O (t + 1) ∧ b (σ (t + 1)) = O (t + 1) ∧ c (σ (t + 1)) = O (t + 1) := by
  intro t ht hne
  have h1 := H_LUT_FIFO (t + 1) (by omega)
  have h0 := H_LUT_FIFO t ht
  cases hr : rst (σ (t + 1))
  · rw [hr, H_FB_FIRST t ht hne] at h1
    revert hne h1
    generalize a (σ (t + 1)) = A
    generalize b (σ (t + 1)) = B
    generalize c (σ (t + 1)) = Cc
    generalize O t = P
    generalize O (t + 1) = P'
    cases A <;> cases B <;> cases Cc <;> cases P <;> cases P' <;> decide
  · have hr0 := H_RST_ONE_FALL (σ t) (σ (t + 1)) (hσr t ht) (hσm t (t + 1) (Nat.le_succ t)) hr
    rw [hr, c3B_rst] at h1
    rw [hr0, c3B_rst] at h0
    exact absurd (by rw [h1, h0]) hne

open RigToken (N N_succ N_mono N_pre par cell_count chg)

theorem N_step {x : Nat → Bool} {T0 t : Nat} (ht : T0 ≤ t) (h : x (t + 1) ≠ x t) :
    N x T0 (t + 1) = N x T0 t + 1 := by
  rw [N_succ]
  have : chg x t = true := by
    simp only [chg, bne_iff_ne, ne_eq]; exact fun e => h e.symm
  simp [ht, this]

/-- **Src.H_LUT_SI for one kernel input channel, in rig time.** `e` = `env_c` (= that
channel's `req`, a fork wire), `k` = `in_ack` (the c3), `x` = that channel's `ack` (the
kernel). Quiet window `[Tq, T0]` at the reset values (`e = 1`, `k = 0`, `x = 0`). Every
move reads its input through a monotone causal map that does not reach before `Tq`:
* H_UENV1_B (uenv1's `b` half, `set_move` + the wire `in_ack → uenv1.I1`): `e` moves only
  to `¬ k` as read at `β t`;
* H_C3 (`c3_move` + the wire from this ack to the c3's pin): `k` moves only to `x` as
  read at `γ t`;
* H_KER_ACK (the kernel's input-ack rule, C's `RecvStep` when `δ = id`): `x` moves only to
  `e` as read at `δ t`.
Then at every move of `e`, `x` at the previous tick is `¬ e` after the move: exactly
`Src.H_LUT_SI`. -/
theorem env_lut_si (e k x : Nat → Bool) (T0 Tq : Nat) (β γ δ : Nat → Nat)
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → e s = true)
    (H_INIT_K : ∀ s, Tq ≤ s → s ≤ T0 → k s = false)
    (H_INIT_X : ∀ s, Tq ≤ s → s ≤ T0 → x s = false)
    (hTq : Tq ≤ T0)
    (hβm : ∀ t t', T0 ≤ t → t ≤ t' → β t ≤ β t') (hβc : ∀ t, T0 ≤ t → β t ≤ t)
    (hβq : ∀ t, T0 ≤ t → Tq ≤ β t)
    (hγm : ∀ t t', T0 ≤ t → t ≤ t' → γ t ≤ γ t') (hγc : ∀ t, T0 ≤ t → γ t ≤ t)
    (hγq : ∀ t, T0 ≤ t → Tq ≤ γ t)
    (hδm : ∀ t t', T0 ≤ t → t ≤ t' → δ t ≤ δ t') (hδc : ∀ t, T0 ≤ t → δ t ≤ t)
    (hδq : ∀ t, T0 ≤ t → Tq ≤ δ t)
    (H_UENV1_B : ∀ t, T0 ≤ t → e (t + 1) ≠ e t → k (β t) = !e (t + 1))
    (H_C3 : ∀ t, T0 ≤ t → k (t + 1) ≠ k t → x (γ t) = k (t + 1))
    (H_KER_ACK : ∀ t, T0 ≤ t → x (t + 1) ≠ x t → e (δ t) = x (t + 1)) :
    ∀ t, T0 ≤ t → e (t + 1) ≠ e t → x t = !e (t + 1) := by
  have eT : e T0 = true := H_INIT_E T0 hTq (Nat.le_refl _)
  have kT : k T0 = false := H_INIT_K T0 hTq (Nat.le_refl _)
  have xT : x T0 = false := H_INIT_X T0 hTq (Nat.le_refl _)
  have Ce := cell_count e k T0 Tq β true 0 hβm hβc hβq
    (fun s h1 h2 => by rw [H_INIT_K s h1 h2, kT])
    (fun t ht hne => by rw [H_UENV1_B t ht hne]; cases e (t + 1) <;> rfl)
    (by rw [kT, eT]; rfl)
  have Ck := cell_count k x T0 Tq γ false 0 hγm hγc hγq
    (fun s h1 h2 => by rw [H_INIT_X s h1 h2, xT])
    (fun t ht hne => by rw [Bool.xor_false]; exact H_C3 t ht hne)
    (by rw [xT, kT]; rfl)
  have Cx := cell_count x e T0 Tq δ false 1 hδm hδc hδq
    (fun s h1 h2 => by rw [H_INIT_E s h1 h2, eT])
    (fun t ht hne => by rw [Bool.xor_false]; exact H_KER_ACK t ht hne)
    (by rw [eT, xT]; rfl)
  intro t ht hne
  have hNe := N_step ht hne
  have a1 := Ce t ht
  -- N k (β t) ≤ N x t
  have a2 : N k T0 (β t) ≤ N x T0 t := by
    by_cases hb : β t ≤ T0
    · rw [N_pre k T0 _ hb]; omega
    · obtain ⟨s, hs⟩ : ∃ s, β t = s + 1 := ⟨β t - 1, by omega⟩
      have hsT : T0 ≤ s := by omega
      have := Ck s hsT
      have hγ := hγc s hsT
      have := N_mono x T0 (show γ s ≤ t by have := hβc t ht; omega)
      rw [hs]; omega
  -- N x t ≤ N e t + 1
  have a3 : N x T0 t ≤ N e T0 t + 1 := by
    by_cases h0 : t = T0
    · rw [h0, N_pre x T0 T0 (Nat.le_refl _)]; omega
    · obtain ⟨s, hs⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hsT : T0 ≤ s := by omega
      have := Cx s hsT
      have := N_mono e T0 (show δ s ≤ t by have := hδc s hsT; omega)
      rw [hs] at this ⊢; omega
  have hN : N x T0 t = N e T0 t + 1 := by omega
  have px := par x T0 Tq (fun s h1 h2 => by rw [H_INIT_X s h1 h2, xT]) t (by omega)
  have pe := par e T0 Tq (fun s h1 h2 => by rw [H_INIT_E s h1 h2, eT]) t (by omega)
  have he1 : e (t + 1) = !e t := by
    revert hne; cases e (t + 1) <;> cases e t <;> simp
  rw [he1, Bool.not_not, px, pe, hN, xT, eT]
  by_cases hp : N e T0 t % 2 = 1
  · have : ¬ (N e T0 t + 1) % 2 = 1 := by omega
    simp [hp, this]
  · have : (N e T0 t + 1) % 2 = 1 := by omega
    simp [hp, this]

/-- Freeze a trace at `T`. -/
def fz (T : Nat) (x : Nat → Bool) : Nat → Bool := fun s => x (min s T)

/-- **`env_lut_si`, causal form**: the step at `T` needs the kernel's ack rule only at steps
`< T` (and the env's own rules only at steps `≤ T`). Proof: freeze `x` at `T` and `e`, `k`
at `T + 1`, then apply `env_lut_si`. -/
theorem env_lut_si_upto (e k x : Nat → Bool) (T0 Tq : Nat) (β γ δ : Nat → Nat)
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → e s = true)
    (H_INIT_K : ∀ s, Tq ≤ s → s ≤ T0 → k s = false)
    (H_INIT_X : ∀ s, Tq ≤ s → s ≤ T0 → x s = false)
    (hTq : Tq ≤ T0)
    (hβm : ∀ t t', T0 ≤ t → t ≤ t' → β t ≤ β t') (hβc : ∀ t, T0 ≤ t → β t ≤ t)
    (hβq : ∀ t, T0 ≤ t → Tq ≤ β t)
    (hγm : ∀ t t', T0 ≤ t → t ≤ t' → γ t ≤ γ t') (hγc : ∀ t, T0 ≤ t → γ t ≤ t)
    (hγq : ∀ t, T0 ≤ t → Tq ≤ γ t)
    (hδm : ∀ t t', T0 ≤ t → t ≤ t' → δ t ≤ δ t') (hδc : ∀ t, T0 ≤ t → δ t ≤ t)
    (hδq : ∀ t, T0 ≤ t → Tq ≤ δ t)
    (T : Nat) (hT : T0 ≤ T)
    (H_UENV1_B : ∀ t, T0 ≤ t → t ≤ T → e (t + 1) ≠ e t → k (β t) = !e (t + 1))
    (H_C3 : ∀ t, T0 ≤ t → t ≤ T → k (t + 1) ≠ k t → x (γ t) = k (t + 1))
    (H_KER_ACK : ∀ t, T0 ≤ t → t < T → x (t + 1) ≠ x t → e (δ t) = x (t + 1)) :
    e (T + 1) ≠ e T → x T = !e (T + 1) := by
  have h := env_lut_si (fz (T + 1) e) (fz (T + 1) k) (fz T x) T0 Tq β γ δ
    (fun s h1 h2 => by simp only [fz]; rw [Nat.min_eq_left (by omega)]; exact H_INIT_E s h1 h2)
    (fun s h1 h2 => by simp only [fz]; rw [Nat.min_eq_left (by omega)]; exact H_INIT_K s h1 h2)
    (fun s h1 h2 => by simp only [fz]; rw [Nat.min_eq_left (by omega)]; exact H_INIT_X s h1 h2)
    hTq hβm hβc hβq hγm hγc hγq hδm hδc hδq
    (by
      intro t ht hne
      by_cases hle : t ≤ T
      · have m1 : min (t + 1) (T + 1) = t + 1 := by omega
        have m2 : min t (T + 1) = t := by omega
        have m3 : min (β t) (T + 1) = β t := by have := hβc t ht; omega
        simp only [fz, m1, m2, m3] at hne ⊢
        exact H_UENV1_B t ht hle hne
      · have m1 : min (t + 1) (T + 1) = T + 1 := by omega
        have m2 : min t (T + 1) = T + 1 := by omega
        exact absurd (by simp only [fz, m1, m2]) hne)
    (by
      intro t ht hne
      by_cases hle : t ≤ T
      · have m1 : min (t + 1) (T + 1) = t + 1 := by omega
        have m2 : min t (T + 1) = t := by omega
        have m3 : min (γ t) T = γ t := by have := hγc t ht; omega
        simp only [fz, m1, m2, m3] at hne ⊢
        exact H_C3 t ht hle hne
      · have m1 : min (t + 1) (T + 1) = T + 1 := by omega
        have m2 : min t (T + 1) = T + 1 := by omega
        exact absurd (by simp only [fz, m1, m2]) hne)
    (by
      intro t ht hne
      by_cases hlt : t < T
      · have m1 : min (t + 1) T = t + 1 := by omega
        have m2 : min t T = t := by omega
        have m3 : min (δ t) (T + 1) = δ t := by have := hδc t ht; omega
        simp only [fz, m1, m2, m3] at hne ⊢
        exact H_KER_ACK t ht hlt hne
      · have m1 : min (t + 1) T = T := by omega
        have m2 : min t T = T := by omega
        exact absurd (by simp only [fz, m1, m2]) hne)
    T hT
  intro hne
  simp only [fz, Nat.min_self, Nat.min_eq_left (Nat.le_succ T)] at h
  exact h hne

/-- **C's `H_ENV` from RigToken's ring hypotheses** (rig time, read maps): `env_c` rises only
while `env_c0` (= `out0.ack`) is high. uenv1 reads `env_c0` high at `φ1 t` (M1), and the
ring's counts (`ring_alternation`) forbid uenv0 from having fallen since. -/
theorem env_H_ENV (e q : Nat → Bool) (T0 Tq : Nat) (φ1 φ0 : Nat → Nat)
    (H_INIT_E : ∀ s, Tq ≤ s → s ≤ T0 → e s = true)
    (H_INIT_Q : ∀ s, Tq ≤ s → s ≤ T0 → q s = false)
    (hφ1m : ∀ t t', T0 ≤ t → t ≤ t' → φ1 t ≤ φ1 t') (hφ1c : ∀ t, T0 ≤ t → φ1 t ≤ t)
    (hφ1q : ∀ t, T0 ≤ t → Tq ≤ φ1 t)
    (hφ0m : ∀ t t', T0 ≤ t → t ≤ t' → φ0 t ≤ φ0 t') (hφ0c : ∀ t, T0 ≤ t → φ0 t ≤ t)
    (hφ0q : ∀ t, T0 ≤ t → Tq ≤ φ0 t)
    (M1 : ∀ t, T0 ≤ t → e (t + 1) ≠ e t → q (φ1 t) = e (t + 1))
    (M0 : ∀ t, T0 ≤ t → q (t + 1) ≠ q t → e (φ0 t) = !q (t + 1)) :
    ∀ t, T0 ≤ t → riseB e t = true → q t = true := by
  have hTq : Tq ≤ T0 := by
    have := hφ1q T0 (Nat.le_refl _); have := hφ1c T0 (Nat.le_refl _); omega
  have eT : e T0 = true := H_INIT_E T0 hTq (Nat.le_refl _)
  have qT : q T0 = false := H_INIT_Q T0 hTq (Nat.le_refl _)
  have A := RigToken.ring_alternation e q T0 Tq φ1 φ0 H_INIT_E H_INIT_Q hφ1m hφ1c hφ1q hφ0m
    hφ0c hφ0q M1 M0
  have C1 := cell_count e q T0 Tq φ1 false 1 hφ1m hφ1c hφ1q
    (fun s h1 h2 => by rw [H_INIT_Q s h1 h2, qT])
    (fun t ht hne => by rw [Bool.xor_false]; exact M1 t ht hne)
    (by rw [qT, eT]; rfl)
  intro t ht hr
  simp only [riseB, Bool.and_eq_true, Bool.not_eq_true'] at hr
  obtain ⟨h0, h1⟩ := hr
  have hne : e (t + 1) ≠ e t := by rw [h0, h1]; decide
  have hNe := N_step ht hne
  have m := M1 t ht hne
  rw [h1] at m
  have c1 := C1 t ht
  have mono := N_mono q T0 (hφ1c t ht)
  have a := A t
  have hN : N q T0 (φ1 t) = N q T0 t := by omega
  have pq1 := par q T0 Tq (fun s h1 h2 => by rw [H_INIT_Q s h1 h2, qT]) (φ1 t) (hφ1q t ht)
  have pq := par q T0 Tq (fun s h1 h2 => by rw [H_INIT_Q s h1 h2, qT]) t (by omega)
  rw [pq, ← hN, ← pq1, m]

/-! ## 4. Composed with C's network: `CellR` for the sources, without circularity -/

theorem src_ack0 (a b : Nat) (ch : Fin NC → Chan)
    (H_KER : ∀ o : Fin NO, isSrcK (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (z : Fin NC) : (ch z).ack 0 = false := by
  have hz : z ∈ (opAt (consOf z)).insC := (net.cons_iff z (consOf z)).2 rfl
  have hns := src_ins_nil _ z hz
  exact (cell_proto ch (srcV a b) _ (H_KER _ hns) (dist_of _ (ops_ok _))).initIn z hz

theorem cell_nsrc {n : Nat} {ch : Fin n → Chan} {sv : Nat → Nat} (k : K n) (hk : isSrcK k = false)
    (h : CellR ch sv k) : Cell ch sv k := cell_of_cellR k hk h

/-- **The rig environment refines C's sources (bridge 4), in C's network.** `ch` is a run
of C's gcd_hw network in C's rig convention (tick 0 = release; `start.req` high there).
Assumed:
* H_KER: every NON-source operator meets its C cell model (the kernel; C's H_CELLS minus
  the three sources);
* H_BUNDLE (C's);
* the env, with every read through a monotone causal map (`β`, `γ z`):
  H_FORK_WIRE (`bd_fork`: every source channel's `req` is `env_c`), H_DAT (its bus is the
  source's value: `vector(idx)` held, idx moves only under rst; `start` carries 0),
  H_REL (release state: `env_c = 1`, `in_ack = 0`), H_UENV1_B (uenv1's `b` half), H_C3 (the
  fork's c3, per source channel).
NOT assumed: any rule about the kernel's acknowledges. They come from C's own
`gcd_hw_protocol`, on the run frozen at each step (`frz`, C's `cell_rt`), so the argument is
a strong induction on time with no circular use of `Src`.
Proved: C's `CellR` for EVERY operator (sources: `SrcR`, i.e. `Src` without `iz`). -/
theorem rig_cellR (a b : Nat) (ch : Fin NC → Chan) (e k : Trace) (β : Nat → Nat)
    (γ : Fin NC → Nat → Nat)
    (H_KER : ∀ o : Fin NO, isSrcK (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_FORK_WIRE : ∀ o z w d, opAt o = .src z w d → ∀ t, (ch z).req t = e t)
    (H_DAT : ∀ o z w d, opAt o = .src z w d → ∀ t, (ch z).dat t = srcV a b w)
    (H_REL : e 0 = true ∧ k 0 = false)
    (hβm : ∀ t t', t ≤ t' → β t ≤ β t') (hβc : ∀ t, β t ≤ t)
    (hγm : ∀ z t t', t ≤ t' → γ z t ≤ γ z t') (hγc : ∀ z t, γ z t ≤ t)
    (H_UENV1_B : ∀ t, e (t + 1) ≠ e t → k (β t) = !e (t + 1))
    (H_C3 : ∀ o z w d, opAt o = .src z w d → ∀ t, k (t + 1) ≠ k t → (ch z).ack (γ z t) = k (t + 1)) :
    ∀ o : Fin NO, CellR ch (srcV a b) (opAt o) := by
  have key : ∀ t, ∀ z w, (∃ o d, opAt o = .src z w d) → ∀ s, s < t →
      ((ch z).req (s + 1) ≠ (ch z).req s → (ch z).req (s + 1) = !(ch z).ack s) := by
    intro t
    induction t with
    | zero => intro z w _ s hs; omega
    | succ T ih =>
      intro z w hz s hs
      -- it suffices to prove the step at T (steps < T are ih)
      rcases Nat.lt_or_ge s T with hlt | hge
      · exact ih z w hz s hlt
      have hsT : s = T := by omega
      rw [hsT]
      obtain ⟨oz, dz, hoz⟩ := hz
      -- the run frozen at T meets every cell model, sources included
      let chF : Fin NC → Chan := fun c => rtC (frz T) (ch c)
      have hCR : ∀ o, CellR chF (srcV a b) (opAt o) := by
        intro o
        cases hk : opAt o with
        | src z' w' d' =>
          show SrcR (rtC (frz T) (ch z')) (srcV a b w')
          refine ⟨?_, ?_⟩
          · intro u hne
            by_cases hu : u + 1 ≤ T
            · have m1 : min (u + 1) T = u + 1 := by omega
              have m2 : min u T = u := by omega
              simp only [rtC, frz, m1, m2] at hne ⊢
              exact ih z' w' ⟨o, d', hk⟩ u (by omega) hne
            · have m1 : min (u + 1) T = T := by omega
              have m2 : min u T = T := by omega
              exact absurd (by simp only [rtC, frz, m1, m2]) hne
          · intro u; exact H_DAT o z' w' d' hk _
        | _ =>
          have hns : isSrcK (opAt o) = false := by rw [hk]; rfl
          have hc := cell_rt (frz_mono T) (frz_zero T) (opAt o) (H_KER o hns)
          rw [hk] at hc
          exact cellR_of _ hc
      have hC := preRun_cells a b chF hCR
      have hH : ∀ c, Held (preRun chF c) := fun c => held_pc (held_rt (frz_mono T) (H_BUNDLE c))
      have hp := gcd_hw_protocol a b (preRun chF) hC hH
      -- the kernel's ack rule on `z` before T, read off the frozen run
      have hrecv : ∀ u, u < T → (ch z).ack (u + 1) ≠ (ch z).ack u → (ch z).req u = (ch z).ack (u + 1) := by
        intro u hu hne
        have r := ((hp z).2 (u + 1)).2
        have e1 : frz T (u + 1) = u + 1 := by simp only [frz]; omega
        have e2 : frz T u = u := by simp only [frz]; omega
        have r' : (ch z).ack (frz T (u + 1)) ≠ (ch z).ack (frz T u) →
            (ch z).ack (frz T u) ≠ (ch z).req (frz T u) := r
        rw [e1, e2] at r'
        have := r' hne
        revert hne this
        cases (ch z).ack (u + 1) <;> cases (ch z).ack u <;> cases (ch z).req u <;> simp
      have hx0 : (ch z).ack 0 = false := src_ack0 a b ch H_KER z
      have hw := H_FORK_WIRE oz z w dz hoz
      intro hne
      simp only [hw] at hne ⊢
      have hx := env_lut_si_upto e k (ch z).ack 0 0 β (γ z) id
        (fun s' _ h2 => by rw [show s' = 0 by omega]; exact H_REL.1)
        (fun s' _ h2 => by rw [show s' = 0 by omega]; exact H_REL.2)
        (fun s' _ h2 => by rw [show s' = 0 by omega]; exact hx0)
        (Nat.le_refl _) (fun t t' _ h => hβm t t' h) (fun t _ => hβc t) (fun t _ => Nat.zero_le _)
        (fun t t' _ h => hγm z t t' h) (fun t _ => hγc z t) (fun t _ => Nat.zero_le _)
        (fun t t' _ h => h) (fun t _ => Nat.le_refl _) (fun t _ => Nat.zero_le _)
        T (Nat.zero_le _)
        (fun t _ _ hne' => H_UENV1_B t hne')
        (fun t _ _ hne' => H_C3 oz z w dz hoz t hne')
        (fun t _ hlt hne' => by simp only [id]; rw [← hw]; exact hrecv t hlt hne')
        hne
      rw [hx, Bool.not_not]
  intro o
  cases hk : opAt o with
  | src z w d =>
    show SrcR (ch z) (srcV a b w)
    exact ⟨fun t hne => key (t + 1) z w ⟨o, d, hk⟩ t (Nat.lt_succ_self t) hne, H_DAT o z w d hk⟩
  | _ =>
    have hns : isSrcK (opAt o) = false := by rw [hk]; rfl
    have hc := H_KER o hns
    rw [hk] at hc
    exact cellR_of _ hc

/-- **C's `gcd_rig_first` with the environment discharged.** Under the kernel's cell models
(H_KER), H_BUNDLE, and the env model of `rig_cellR` plus uenv0/uenv1's `a` halves in
RigToken's form (M1, M0; `out0.ack = env_c0`, H_REL0: `env_c0 = 0` at release), with all
reads through monotone causal maps: the first value `out0` offers, and the first value it
latches, are `gcd a b`. -/
theorem gcd_rig_first_env (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin NC → Chan)
    (e k q : Trace) (β φ1 φ0 : Nat → Nat) (γ : Fin NC → Nat → Nat)
    (H_KER : ∀ o : Fin NO, isSrcK (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_FORK_WIRE : ∀ o z w d, opAt o = .src z w d → ∀ t, (ch z).req t = e t)
    (H_DAT : ∀ o z w d, opAt o = .src z w d → ∀ t, (ch z).dat t = srcV a b w)
    (H_REL : e 0 = true ∧ k 0 = false) (H_REL0 : q 0 = false)
    (H_OUT0_ACK : ∀ t, (ch out0).ack t = q t)
    (hβm : ∀ t t', t ≤ t' → β t ≤ β t') (hβc : ∀ t, β t ≤ t)
    (hγm : ∀ z t t', t ≤ t' → γ z t ≤ γ z t') (hγc : ∀ z t, γ z t ≤ t)
    (hφ1m : ∀ t t', t ≤ t' → φ1 t ≤ φ1 t') (hφ1c : ∀ t, φ1 t ≤ t)
    (hφ0m : ∀ t t', t ≤ t' → φ0 t ≤ φ0 t') (hφ0c : ∀ t, φ0 t ≤ t)
    (H_UENV1_B : ∀ t, e (t + 1) ≠ e t → k (β t) = !e (t + 1))
    (H_C3 : ∀ o z w d, opAt o = .src z w d → ∀ t, k (t + 1) ≠ k t → (ch z).ack (γ z t) = k (t + 1))
    (M1 : ∀ t, e (t + 1) ≠ e t → q (φ1 t) = e (t + 1))
    (M0 : ∀ t, q (t + 1) ≠ q t → e (φ0 t) = !q (t + 1)) :
    (∀ r, OffAt (ch out0) 0 r → (ch out0).dat (r + 1) = Nat.gcd a b) ∧
    (∀ e', TokAt (ch out0) 0 e' → (ch out0).dat e' = Nat.gcd a b) := by
  have hCR := rig_cellR a b ch e k β γ H_KER H_BUNDLE H_FORK_WIRE H_DAT H_REL hβm hβc hγm hγc
    H_UENV1_B H_C3
  have hEnv : Gcd.H_ENV ch := by
    intro t hr
    have hws := H_FORK_WIRE (prodOf start) start 2 0 prod_start
    have hr' : riseB e t = true := by
      have : (ch start).req = e := funext hws
      rw [this] at hr; exact hr
    rw [H_OUT0_ACK]
    exact env_H_ENV e q 0 0 φ1 φ0
      (fun s _ h2 => by rw [show s = 0 by omega]; exact H_REL.1)
      (fun s _ h2 => by rw [show s = 0 by omega]; exact H_REL0)
      (fun t t' _ h => hφ1m t t' h) (fun t _ => hφ1c t) (fun t _ => Nat.zero_le _)
      (fun t t' _ h => hφ0m t t' h) (fun t _ => hφ0c t) (fun t _ => Nat.zero_le _)
      (fun t _ hne => M1 t hne) (fun t _ hne => M0 t hne) t (Nat.zero_le _) hr'
  exact gcd_rig_first a b ha hb ch hCR H_BUNDLE hEnv

/-! ## 5. Witnesses and counter-runs -/

/-! A tick-level env lap meeting every hypothesis of `env_lut_si` and `env_H_ENV` (all read
maps `id`, `T0 = Tq = 0`): `e` = env_c, `x` = one kernel ack, `k` = in_ack, `q` = env_c0.
Lap: x↑ k↑ e↓ (x↓,q↑) k↓ e↑ (x↑,q↓) ... -/
namespace W

def eL : List Bool := [true, true, true, false, false, false, true]
def xL : List Bool := [false, true, true, true, false, false, false]
def kL : List Bool := [false, false, true, true, true, false, false]
def qL : List Bool := [false, false, false, false, true, true, true]

def p (t : Nat) : Nat := if t = 0 then 0 else 1 + (t - 1) % 6
def nxt (i : Nat) : Nat := if i < 6 then i + 1 else 1

theorem p_lt (t : Nat) : p t < 7 := by
  unfold p; split <;> omega

theorem p_succ (t : Nat) : p (t + 1) = nxt (p t) := by
  unfold p nxt
  cases t with
  | zero => rfl
  | succ s =>
    simp only [show s + 1 + 1 ≠ 0 by omega, show s + 1 ≠ 0 by omega, ite_false]
    split <;> omega

def e (t : Nat) : Bool := eL.getD (p t) false
def x (t : Nat) : Bool := xL.getD (p t) false
def k (t : Nat) : Bool := kL.getD (p t) false
def q (t : Nat) : Bool := qL.getD (p t) false

theorem tbl : ∀ i, i < 7 →
    (eL.getD (nxt i) false ≠ eL.getD i false → kL.getD i false = !eL.getD (nxt i) false) ∧
    (kL.getD (nxt i) false ≠ kL.getD i false → xL.getD i false = kL.getD (nxt i) false) ∧
    (xL.getD (nxt i) false ≠ xL.getD i false → eL.getD i false = xL.getD (nxt i) false) ∧
    (eL.getD (nxt i) false ≠ eL.getD i false → qL.getD i false = eL.getD (nxt i) false) ∧
    (qL.getD (nxt i) false ≠ qL.getD i false → eL.getD i false = !qL.getD (nxt i) false) := by
  decide

theorem row (t : Nat) :
    (e (t + 1) ≠ e t → k t = !e (t + 1)) ∧ (k (t + 1) ≠ k t → x t = k (t + 1)) ∧
    (x (t + 1) ≠ x t → e t = x (t + 1)) ∧ (e (t + 1) ≠ e t → q t = e (t + 1)) ∧
    (q (t + 1) ≠ q t → e t = !q (t + 1)) := by
  unfold e x k q; rw [p_succ]; exact tbl _ (p_lt t)

/-- **Non-vacuity of §3**: the lap meets every hypothesis of `env_lut_si` and `env_H_ENV`;
the environment offers `start` 3 times by tick 20. -/
theorem env_nonvacuous :
    (∀ t, e (t + 1) ≠ e t → x t = !e (t + 1)) ∧ (∀ t, riseB e t = true → q t = true) ∧
    cnt (riseB e) 20 = 3 := by
  have i0 : ∀ s, 0 ≤ s → s ≤ 0 → s = 0 := fun s _ h => by omega
  refine ⟨fun t hne => env_lut_si e k x 0 0 id id id
      (fun s h1 h2 => by rw [i0 s h1 h2]; rfl) (fun s h1 h2 => by rw [i0 s h1 h2]; rfl)
      (fun s h1 h2 => by rw [i0 s h1 h2]; rfl) (Nat.le_refl _)
      (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.zero_le _)
      (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.zero_le _)
      (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.zero_le _)
      (fun t _ h => (row t).1 h) (fun t _ h => (row t).2.1 h) (fun t _ h => (row t).2.2.1 h)
      t (Nat.zero_le _) hne,
    fun t hr => env_H_ENV e q 0 0 id id
      (fun s h1 h2 => by rw [i0 s h1 h2]; rfl) (fun s h1 h2 => by rw [i0 s h1 h2]; rfl)
      (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.zero_le _)
      (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _) (fun _ _ => Nat.zero_le _)
      (fun t _ h => (row t).2.2.2.1 h) (fun t _ h => (row t).2.2.2.2 h) t (Nat.zero_le _) hr,
    by decide⟩

end W

/-! **H_KER_ACK cannot be dropped** (counter-run). Every other hypothesis of `env_lut_si`
holds (maps `id`, `T0 = Tq = 0`), but the kernel raises this channel's ack while `req` is low
(tick 5 → 6, after the c3 has already fallen): `env_c` then rises at 6 → 7 with that ack
high, and `Src.H_LUT_SI` fails. -/
namespace CX

def eL : List Bool := [true, true, true, false, false, false, false, true]
def xL : List Bool := [false, true, true, true, false, false, true, true]
def kL : List Bool := [false, false, true, true, true, false, false, false]

def e (t : Nat) : Bool := eL.getD (min t 7) false
def x (t : Nat) : Bool := xL.getD (min t 7) false
def k (t : Nat) : Bool := kL.getD (min t 7) false

theorem rows : ∀ t, t < 7 →
    (e (t + 1) ≠ e t → k t = !e (t + 1)) ∧ (k (t + 1) ≠ k t → x t = k (t + 1)) := by decide

theorem tail (t : Nat) (h : 7 ≤ t) : e (t + 1) = e t ∧ k (t + 1) = k t := by
  unfold e k
  rw [Nat.min_eq_right (show 7 ≤ t + 1 by omega), Nat.min_eq_right h]
  exact ⟨rfl, rfl⟩

theorem ker_ack_needed :
    (e 0 = true ∧ k 0 = false ∧ x 0 = false) ∧
    (∀ t, e (t + 1) ≠ e t → k t = !e (t + 1)) ∧
    (∀ t, k (t + 1) ≠ k t → x t = k (t + 1)) ∧
    ¬ (∀ t, x (t + 1) ≠ x t → e t = x (t + 1)) ∧
    ¬ (∀ t, e (t + 1) ≠ e t → x t = !e (t + 1)) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · intro t hne
    by_cases h : t < 7
    · exact (rows t h).1 hne
    · exact absurd (tail t (by omega)).1 hne
  · intro t hne
    by_cases h : t < 7
    · exact (rows t h).2 hne
    · exact absurd (tail t (by omega)).2 hne
  · intro hc; exact absurd (hc 5 (by decide)) (by decide)
  · intro hc; exact absurd (hc 6 (by decide)) (by decide)

end CX

/-- **`Src.iz` is the one field that cannot hold at the rig's release**: under H_FORK_WIRE
and H_REL every source channel's `req` is high at tick 0. (C's `preRun` supplies it.) -/
theorem iz_fails (ch : Fin NC → Chan) (e : Trace)
    (H_FORK_WIRE : ∀ o z w d, opAt o = .src z w d → ∀ t, (ch z).req t = e t)
    (H_REL : e 0 = true) : ¬ Capstone.Src (ch start) 0 := by
  intro S
  have := S.iz
  rw [H_FORK_WIRE (prodOf start) start 2 0 prod_start, H_REL] at this
  exact absurd this (by decide)

end Formal.Cells.RigSrc
