import Formal.Core.XAudit.Events2
import Formal.Cells.ArbBinary

/-!
# Formal.Core.XAudit.Events8Arb — H_ARB (`HARB7`) against the real `bd_arbiter` in A's per-pin model

Probe E8Arb. See `formal/notes/A-e8arb.md`.

`design_verdict8` assumes H_ARB (`Events7.HARB7`): every arbiter core is a *virtual* core
(events4/model.py `vctl:` / `arb:g` / `arb:R0`): a node `ctl = ¬A0` read through a warp in
`[lo, 10^12]`, two grant C-elements `g_b = C(r_b, ctl·[σ = b])` with the grant LUT band, and
`R0 = g1 + g2`. This file states, at CELL level, the real `bd_arbiter` core in A's per-pin
semantics (every LUT output reads every pin through its own monotone warp, `PinRel`), with the
REAL INITs (`ArbBinary.ARB_ST`, `ArbBinary.GRANT`, decoded here by `cases`), the virtual grant
node in the shape of `Events7.ND7`, and the "uncontested" predicate; and proves:

* `vgrant_hold`: a virtual grant that has been high for `hiF + 1` steps stays high while its
  request stays high (it never falls with a steady request): the bounded-response content of
  HARB7 for a grant.
* the contested runt trace `ct` (§3): a behaviour of the real cell (`ct_pin`, real INITs,
  constant per-pin delays: every read 1 step, the state LUT's own q pin 10 steps), with
  exclusive grants (`ct_excl`) and C's instantaneous "no free contention" predicate
  (`ct_noFree`: both requests high ⇒ some grant high, at EVERY time), in which `g2` falls for
  ever while `r2` is steadily high (`ct_g2_osc`). So no virtual grant with
  `hiF ≤ 7`, `hiF + hiR ≤ 12` matches it (`ct_not_virtual`), and C's instantaneous predicate
  on A's wires does not imply HARB7 (`noFree_not_harb`).
* `Unc W`: the requests are never both pending (request high, own grant low) within `W` steps.
  `unc0_iff_noFree`: `Unc 0` is exactly C's instantaneous predicate; `ct` satisfies `Unc 0` and
  violates `Unc 1` (`ct_unc0`, `ct_not_unc1`): a positive window is necessary.

What this file does NOT prove: the sufficiency direction (an `Unc W` real cell, with B's cell
conditions, IS a virtual-core behaviour). Its statement and the missing pieces are in the
notes (§4) and `formal/lean/Wip/E8Arb/`.
-/

namespace Formal.Core.XAudit.Events8Arb

open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.LutList (o5B o6B)
open Formal.Cells.ArbBinary (ARB_ST GRANT)

/-! ## 1. The real cell, from its INITs -/

/-- `ustate` O6 (`q`), pins `I0 = r1, I1 = r2, I2 = q, I3 = rst, I4 = A0, I5 = 1`:
`q = rst + (A0 ? q : C(r1, ¬r2))`. -/
theorem st_eq (r1 r2 q rs a : Bool) : o6B ARB_ST [r1, r2, q, rs, a, true] =
    (rs || if a then q else ((r1 && !r2) || (q && !(!r1 && r2)))) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rs <;> cases a <;> rfl

/-- `ustate` O5 (`R0`): `r1·q + r2·¬q` (independent of `rst`, `A0`). -/
theorem r0_eq (r1 r2 q rs a : Bool) : o5B ARB_ST [r1, r2, q, rs, a, true] = ((r1 && q) || (r2 && !q)) := by
  cases r1 <;> cases r2 <;> cases q <;> cases rs <;> cases a <;> rfl

/-- `ugrant` O5 (`g1`), pins `I0 = r1, I1 = r2, I2 = q, I3 = I4 = 0, I5 = 1`: `r1·q`. -/
theorem g1_eq (r1 r2 q : Bool) : o5B GRANT [r1, r2, q, false, false, true] = (r1 && q) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

/-- `ugrant` O6 (`g2`): `r2·¬q`. -/
theorem g2_eq (r1 r2 q : Bool) : o6B GRANT [r1, r2, q, false, false, true] = (r2 && !q) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

/-- Per-pin bands of the four LUT outputs of `bd_arbiter`'s core: `st` = `ustate` O6 (`q`),
`r0` = `ustate` O5 (`R0`), `g1` / `g2` = `ugrant` O5 / O6. Index `i` = LUT input `Ii` (for
`ugrant` only `I0..I2` are not tied). Each band is the whole read (route, site pin, LUT arc)
from the source signal. -/
structure ArbBands where
  st : Fin 5 → Nat × Nat
  r0 : Fin 5 → Nat × Nat
  g1 : Fin 3 → Nat × Nat
  g2 : Fin 3 → Nat × Nat

/-- Every read `f i` is a monotone warp in its band. -/
def Rd (k : Nat) (bd : Fin k → Nat × Nat) (f : Fin k → Nat → Nat) : Prop :=
  ∀ i, Warp (bd i).1 (bd i).2 (f i)

/-- **The real `bd_arbiter` core in A's per-pin semantics** (`Events2Pin.PinRel` for its four
LUT outputs; the A1 / A2 C-elements are ordinary real nodes and are not part of the core).
`r1`, `r2`, `rs`, `a` are the source signals of the request, reset and `A0` pins. -/
structure ArbPin (B : ArbBands) (r1 r2 rs a q R0 g1 g2 : Sig) : Prop where
  st : ∃ f, Rd 5 B.st f ∧ ∀ t, q t = o6B ARB_ST [r1 (f 0 t), r2 (f 1 t), q (f 2 t), rs (f 3 t), a (f 4 t), true]
  r0 : ∃ f, Rd 5 B.r0 f ∧ ∀ t, R0 t = o5B ARB_ST [r1 (f 0 t), r2 (f 1 t), q (f 2 t), rs (f 3 t), a (f 4 t), true]
  g1 : ∃ f, Rd 3 B.g1 f ∧ ∀ t, g1 t = o5B GRANT [r1 (f 0 t), r2 (f 1 t), q (f 2 t), false, false, true]
  g2 : ∃ f, Rd 3 B.g2 f ∧ ∀ t, g2 t = o6B GRANT [r1 (f 0 t), r2 (f 1 t), q (f 2 t), false, false, true]

/-! ## 2. The virtual grant (the `ND7` of an `arb:g` node) and its bounded response -/

/-- **The virtual grant node** `arb:g` of events4/model.py, in the shape of `Events7.ND7`
(non-merge node, reset value 0, two pins with one copy each): pin 0 = the request source `s`
read through `GR` (band `[loR, hiR]`, the real request arc), pin 1 = the filtered `ctl` pin
`ctl·[σ = br]` (band `(1,1)`), the node's own value through `Q` (band `(1,1)`), all read at the
stage time `F t` (band `[loF, hiF]`, the grant LUT band); `r` is the node's reset signal
(true on an initial segment). `σ = sv` is free here (SelOK constrains it in `Beh7`). -/
def VGrant (loF hiF loR hiR : Nat) (br : Bool) (s ctl g : Sig) : Prop :=
  ∃ (F GR GC Q : Nat → Nat) (r sv : Sig), Warp loF hiF F ∧ Warp loR hiR GR ∧ Warp 1 1 GC ∧
    Warp 1 1 Q ∧ r 0 = true ∧ (∀ x y, x ≤ y → r y = true → r x = true) ∧
    ∀ t, g t = if r (F t) then false else
      cel (fun p : Fin 2 => if p.val = 0 then s (GR (F t)) else (ctl (GC (F t)) && (sv (F t) == br)))
        (g (Q (F t)))

theorem cel2_hold (x : Fin 2 → Bool) (h0 : x 0 = true) : cel x true = true := by
  unfold cel
  split
  · rfl
  · split
    · rename_i h; exact absurd (h 0) (by rw [h0]; decide)
    · rfl

/-- **A virtual grant never falls while its request is high.** If the virtual grant `g` is
high on `[t0, t0 + hiF]` and its request source `s` is high on `[t0 - (hiF + hiR), t1]`, then
`g` is high on all of `[t0, t1]`, whatever `ctl` and `σ` do. -/
theorem vgrant_hold {loF hiF loR hiR : Nat} {br : Bool} {s ctl g : Sig}
    (hv : VGrant loF hiF loR hiR br s ctl g) {t0 t1 : Nat}
    (hg : ∀ u, t0 ≤ u → u ≤ t0 + hiF → g u = true)
    (hs : ∀ u, t0 - (hiF + hiR) ≤ u → u ≤ t1 → s u = true) :
    ∀ u, t0 ≤ u → u ≤ t1 → g u = true := by
  obtain ⟨F, GR, GC, Q, r, sv, wF, wR, _wC, wQ, _r0, ranti, hc⟩ := hv
  have hr0 : r (F t0) = false := by
    have h := hc t0
    rw [hg t0 (Nat.le_refl _) (by omega)] at h
    cases hr : r (F t0)
    · rfl
    · rw [hr] at h; simp at h
  suffices H : ∀ n u, u ≤ n → t0 ≤ u → u ≤ t1 → g u = true from fun u => H u u (Nat.le_refl _)
  intro n
  induction n with
  | zero => intro u hn hu1 _; exact hg u hu1 (by omega)
  | succ n ih =>
    intro u hn hu1 hu2
    by_cases hb : u ≤ t0 + hiF
    · exact hg u hu1 hb
    · have hFu := wF.le_late u
      have hFu' := wF.early_le u
      have hrF : r (F u) = false := by
        cases hr : r (F u)
        · rfl
        · rw [ranti (F t0) (F u) (wF.mono _ _ hu1) hr] at hr0; exact absurd hr0 (by decide)
      have hR1 := wR.le_late (F u)
      have hR2 := wR.early_le (F u)
      have hQ1 := wQ.le_late (F u)
      have hQ2 := wQ.early_le (F u)
      have hsR : s (GR (F u)) = true := hs _ (by omega) (by omega)
      have hq : g (Q (F u)) = true := ih _ (by omega) (by omega) (by omega)
      rw [hc u, hrF, hq]
      exact cel2_hold _ (by simpa using hsR)

/-! ## 3. A contested runt: a real-cell behaviour that is not a virtual-core behaviour -/

/-- request 1: rises at 10 + 8 = 18 (a runt of the reset excitation, 8 < the loop of 10). -/
def r1c : Sig := fun t => decide (18 ≤ t)
/-- request 2: rises at 10. -/
def r2c : Sig := fun t => decide (10 ≤ t)
/-- `A0`, reset: low (the server has not answered yet; reset released before time 0). -/
def lowc : Sig := fun _ => false
/-- `q`: 1 up to 10, then a low pulse of width 8 circulating in the loop of period 10 for ever. -/
def qc : Sig := fun t => decide (t ≤ 10 ∨ 8 ≤ (t - 11) % 10)
def g1c : Sig := fun t => r1c (t - 1) && qc (t - 1)
def g2c : Sig := fun t => r2c (t - 1) && !qc (t - 1)
def R0c : Sig := fun t => (r1c (t - 1) && qc (t - 1)) || (r2c (t - 1) && !qc (t - 1))

/-- The per-pin bands of `ct`: every read 1 step, except `ustate`'s own `q` pin (the state
loop): 10 steps. -/
def Bct : ArbBands where
  st := fun i => if i.val = 2 then (10, 10) else (1, 1)
  r0 := fun _ => (1, 1)
  g1 := fun _ => (1, 1)
  g2 := fun _ => (1, 1)

theorem shift_w (k : Nat) : Warp k k (fun t => t - k) :=
  ⟨fun a b hab => by omega, fun t => by omega, fun t => by omega⟩

/-- **`ct` is a behaviour of the real cell** (real INITs, per-pin semantics, `rst = A0 = 0`). -/
theorem ct_pin : ArbPin Bct r1c r2c lowc lowc qc R0c g1c g2c := by
  refine ⟨⟨fun i => if i.val = 2 then (fun t => t - 10) else (fun t => t - 1), ?_, ?_⟩,
    ⟨fun _ t => t - 1, fun _ => shift_w 1, ?_⟩, ⟨fun _ t => t - 1, fun _ => shift_w 1, ?_⟩,
    ⟨fun _ t => t - 1, fun _ => shift_w 1, ?_⟩⟩
  · intro i
    by_cases h : i.val = 2
    · simp only [Bct, h, if_true]; exact shift_w 10
    · simp only [Bct, h, if_false]; exact shift_w 1
  · intro t
    show qc t = o6B ARB_ST [r1c (t - 1), r2c (t - 1), qc (t - 10), lowc (t - 1), lowc (t - 1), true]
    rw [st_eq]
    simp only [lowc, qc, r1c, r2c, Bool.false_or, Bool.false_eq_true, ite_false]
    rw [Bool.eq_iff_iff]; simp; omega
  · intro t; show _ = o5B ARB_ST [_, _, _, _, _, true]; rw [r0_eq]; rfl
  · intro t; show _ = o5B GRANT [_, _, _, false, false, true]; rw [g1_eq]; rfl
  · intro t; show _ = o6B GRANT [_, _, _, false, false, true]; rw [g2_eq]; rfl

/-- The grants of `ct` are exclusive at every time. -/
theorem ct_excl (t : Nat) : (g1c t && g2c t) = false := by
  simp only [g1c, g2c]; cases r1c (t - 1) <;> cases r2c (t - 1) <;> cases qc (t - 1) <;> rfl

/-- **C's instantaneous "no free contention"** (`CapstoneCut.gcd_hw_arbiters_uncontended'`'s
conclusion, read on the cell's wires) holds on `ct` at every time. -/
theorem ct_noFree (t : Nat) (h1 : r1c t = true) (h2 : r2c t = true) : g1c t = true ∨ g2c t = true := by
  simp only [r1c, decide_eq_true_eq] at h1
  by_cases h : t = 18
  · subst h; right; decide
  · have e1 : r1c (t - 1) = true := by simp [r1c]; omega
    have e2 : r2c (t - 1) = true := by simp [r2c]; omega
    simp only [g1c, g2c, e1, e2, Bool.true_and]
    cases qc (t - 1) <;> simp

/-- `g2` of `ct` is high on `[22 + 10k, 29 + 10k]` and low at `30 + 10k`, while `r2` is high
from 10 on: the grant pulses for ever under a steady request. -/
theorem ct_g2_osc (k : Nat) :
    (∀ u, 22 + 10 * k ≤ u → u ≤ 29 + 10 * k → g2c u = true) ∧ g2c (30 + 10 * k) = false := by
  constructor
  · intro u h1 h2
    simp [g2c, r2c, qc]; omega
  · simp [g2c, r2c, qc]; omega

/-- **No virtual grant matches `ct`'s `g2`** (for any `ctl`, any `σ`, any branch label, any
grant band with `hiF ≤ 7` and request band with `hiF + hiR ≤ 12`, i.e. any band shorter than the
pulse it would have to hold through). -/
theorem ct_not_virtual {loF hiF loR hiR : Nat} (br : Bool) (ctl : Sig) (h7 : hiF ≤ 7)
    (h12 : hiF + hiR ≤ 12) : ¬ VGrant loF hiF loR hiR br r2c ctl g2c := by
  intro hv
  have h := vgrant_hold hv (t0 := 22) (t1 := 30)
    (fun u hu1 hu2 => (ct_g2_osc 0).1 u (by omega) (by omega))
    (fun u hu1 _ => by simp [r2c]; omega) 30 (by omega) (Nat.le_refl _)
  rw [(ct_g2_osc 0).2] at h
  exact absurd h (by decide)

/-! ## 4. "Uncontested" -/

/-- Request `r` is pending at `t`: high, its grant low. -/
def Pend (r g : Sig) (t : Nat) : Prop := r t = true ∧ g t = false

/-- **Uncontested within `W`**: the two requests of the arbiter are never both pending at times
less than or equal to `W` apart. `W` is the race window (notes §2: at least B's loop `L` of
`ArbBinary.H_REQ_SEP` plus the pin skews of the per-pin model). -/
def Unc (W : Nat) (r1 r2 g1 g2 : Sig) : Prop :=
  ∀ u v, Pend r1 g1 u → Pend r2 g2 v → u + W < v ∨ v + W < u

/-- `Unc 0` is exactly C's instantaneous predicate (both requests high ⇒ a grant high). -/
theorem unc0_iff_noFree (r1 r2 g1 g2 : Sig) :
    Unc 0 r1 r2 g1 g2 ↔ ∀ t, r1 t = true → r2 t = true → g1 t = true ∨ g2 t = true := by
  constructor
  · intro h t h1 h2
    cases e1 : g1 t
    · cases e2 : g2 t
      · have := h t t ⟨h1, e1⟩ ⟨h2, e2⟩; omega
      · exact Or.inr rfl
    · exact Or.inl rfl
  · intro h u v ⟨h1, e1⟩ ⟨h2, e2⟩
    by_cases huv : u = v
    · subst huv; rcases h u h1 h2 with h' | h' <;> simp_all
    · omega

/-- `Unc` is antitone in the window. -/
theorem unc_mono {W W' : Nat} (hW : W ≤ W') {r1 r2 g1 g2 : Sig} (h : Unc W' r1 r2 g1 g2) :
    Unc W r1 r2 g1 g2 := fun u v h1 h2 => by have := h u v h1 h2; omega

theorem ct_unc0 : Unc 0 r1c r2c g1c g2c := (unc0_iff_noFree _ _ _ _).2 ct_noFree

/-- `ct` is contested within window 1: `r1` pending at 19, `r2` pending at 20. -/
theorem ct_not_unc1 : ¬ Unc 1 r1c r2c g1c g2c := by
  intro h
  have := h 19 20 ⟨by decide, by decide⟩ ⟨by decide, by decide⟩
  omega

/-- **C's instantaneous no-free-contention predicate does not imply H_ARB on A's wires.** There
is a behaviour of the real `bd_arbiter` core (real INITs, A's per-pin semantics) with exclusive
grants and no instant of free contention whose grant `g2` is not a virtual-grant behaviour for
any band with `hiF ≤ 7`, `hiF + hiR ≤ 12` (the scale of `ct`). -/
theorem noFree_not_harb : ∃ (B : ArbBands) (r1 r2 rs a q R0 g1 g2 : Sig),
    ArbPin B r1 r2 rs a q R0 g1 g2 ∧ (∀ t, (g1 t && g2 t) = false) ∧ Unc 0 r1 r2 g1 g2 ∧
    ¬ Unc 1 r1 r2 g1 g2 ∧
    ∀ loF hiF loR hiR br ctl, hiF ≤ 7 → hiF + hiR ≤ 12 → ¬ VGrant loF hiF loR hiR br r2 ctl g2 :=
  ⟨Bct, r1c, r2c, lowc, lowc, qc, R0c, g1c, g2c, ct_pin, ct_excl, ct_unc0, ct_not_unc1,
    fun _ _ _ _ br ctl h7 h12 => ct_not_virtual br ctl h7 h12⟩

/-! ## 5. An UNCONTESTED handover that is not a virtual-core behaviour (HARB7's encoding) -/

/-- **The virtual ctl node** `vctl:` (events4/model.py; `ND7` of a non-merge node with ONE
inverted plain pin from `A0`'s source `a`, band `[lo, hi]`, stage band `(1,1)`, own-value band
`(1,1)`, reset value 0). -/
def VCtl (lo hi : Nat) (a ctl : Sig) : Prop :=
  ∃ (F G Q : Nat → Nat) (r : Sig), Warp 1 1 F ∧ Warp lo hi G ∧ Warp 1 1 Q ∧ r 0 = true ∧
    (∀ x y, x ≤ y → r y = true → r x = true) ∧
    ∀ t, ctl t = if r (F t) then false else cel (fun _ : Fin 1 => !(a (G (F t)))) (ctl (Q (F t)))

/-- **The virtual R0 node** `arb:R0` (`ND7` of a merge node, two plain one-copy pins from the
two virtual grants, tap bands `[lo1, hi1]`, `[lo2, hi2]`, stage band `[loF, hiF]`). -/
def VMerge (loF hiF lo1 hi1 lo2 hi2 : Nat) (g1 g2 R0 : Sig) : Prop :=
  ∃ (F G1 G2 : Nat → Nat), Warp loF hiF F ∧ Warp lo1 hi1 G1 ∧ Warp lo2 hi2 G2 ∧
    ∀ t, R0 t = (g1 (G1 (F t)) || g2 (G2 (F t)))

theorem cel1 (v q : Bool) : cel (fun _ : Fin 1 => v) q = v := by
  unfold cel; cases v <;> simp

theorem cel2_all (x : Fin 2 → Bool) (q : Bool) (h : cel x q = true) (hq : q = false) :
    x 0 = true ∧ x 1 = true := by
  unfold cel at h
  split at h
  · rename_i h'; exact ⟨h' 0, h' 1⟩
  · split at h
    · simp at h
    · rw [hq] at h; simp at h

/-- **A virtual R0 edge needs an earlier grant**: virtual `R0` high at `t` means some grant was
high at a time at most `t - (loF + min lo1 lo2)`. -/
theorem vmerge_needs_grant {loF hiF lo1 hi1 lo2 hi2 : Nat} {g1 g2 R0 : Sig}
    (hv : VMerge loF hiF lo1 hi1 lo2 hi2 g1 g2 R0) {t : Nat} (h : R0 t = true) :
    (∃ u, u ≤ t - (loF + lo1) ∧ g1 u = true) ∨ (∃ u, u ≤ t - (loF + lo2) ∧ g2 u = true) := by
  obtain ⟨F, G1, G2, wF, w1, w2, hc⟩ := hv
  rw [hc t] at h
  have := wF.le_late t; have := w1.le_late (F t); have := w2.le_late (F t)
  cases e : g1 (G1 (F t))
  · rw [e] at h; simp at h
    exact Or.inr ⟨G2 (F t), by omega, h⟩
  · exact Or.inl ⟨G1 (F t), by omega, e⟩

/-- **A virtual grant's first rise needs `A0` low `loF + lo + 2` steps earlier**: if the virtual
grant `g` (stage band `[loF, hiF]`) reading a virtual `ctl` (pin band `[lo, hi]`) is high at
`t > 0` and low before, then `A0`'s source `a` was low at some time `≤ t - (loF + lo + 2)`:
the two `(1,1)` bands (ctl's stage, the filtered pin) add 2 steps to every grant rise. -/
theorem vgrant_rise_ctl {loF hiF loR hiR lo hi : Nat} {br : Bool} {s a ctl g : Sig}
    (hc : VCtl lo hi a ctl) (hg : VGrant loF hiF loR hiR br s ctl g) {t : Nat} (ht : 0 < t)
    (h1 : g t = true) (h0 : ∀ u, u < t → g u = false) : ∃ u, u ≤ t - (loF + lo + 2) ∧ a u = false := by
  obtain ⟨Fc, Gc, Qc, rc, wFc, wGc, _wQc, _rc0, _rcanti, hcc⟩ := hc
  obtain ⟨F, GR, GC, Q, r, sv, wF, _wR, wC, wQ, _r0, _ranti, hgc⟩ := hg
  have hFt := wF.le_late t
  have hQ := wQ.le_late (F t)
  have hC1 := wC.le_late (F t)
  rw [hgc t] at h1
  have hr : r (F t) = false := by
    cases e : r (F t)
    · rfl
    · rw [e] at h1; simp at h1
  rw [hr] at h1
  simp only [Bool.false_eq_true, ite_false] at h1
  have hq0 : g (Q (F t)) = false := h0 _ (by omega)
  obtain ⟨_, hp1⟩ := cel2_all _ _ h1 hq0
  simp only [Fin.isValue, show ((1 : Fin 2).val = 0) = False from by decide, ite_false,
    Bool.and_eq_true] at hp1
  have hct := hp1.1
  rw [hcc] at hct
  have hrc : rc (Fc (GC (F t))) = false := by
    cases e : rc (Fc (GC (F t)))
    · rfl
    · rw [e] at hct; simp at hct
  rw [hrc] at hct
  simp only [Bool.false_eq_true, ite_false, cel1, Bool.not_eq_eq_eq_not, Bool.not_true] at hct
  have := wFc.le_late (GC (F t)); have := wGc.le_late (Fc (GC (F t)))
  exact ⟨_, by omega, hct⟩

/-- The handover trace `ho`: request 2 is waiting (high from 0), request 1 never asks; `A0` is
high until 10 (the server is still acknowledging the previous client) and then falls. Every
read takes 1 step except `ugrant`'s `q` pin for `g2` (3 steps). Then `q` falls at 11 (A0 read
low, r2 alone), `R0 = r2·¬q` rises at 12, `g2 = r2·¬q` rises at 14. -/
def oneS : Sig := fun _ => true
def a0h : Sig := fun t => decide (t < 10)
def qh : Sig := fun t => decide (t ≤ 10)
def R0h : Sig := fun t => decide (12 ≤ t)
def g2h : Sig := fun t => decide (14 ≤ t)

def Bho : ArbBands where
  st := fun _ => (1, 1)
  r0 := fun _ => (1, 1)
  g1 := fun _ => (1, 1)
  g2 := fun i => if i.val = 2 then (3, 3) else (1, 1)

theorem ho_pin : ArbPin Bho lowc oneS lowc a0h qh R0h lowc g2h := by
  refine ⟨⟨fun _ t => t - 1, fun _ => shift_w 1, ?_⟩, ⟨fun _ t => t - 1, fun _ => shift_w 1, ?_⟩,
    ⟨fun _ t => t - 1, fun _ => shift_w 1, ?_⟩,
    ⟨fun i => if i.val = 2 then (fun t => t - 3) else (fun t => t - 1), ?_, ?_⟩⟩
  · intro t
    show qh t = o6B ARB_ST [lowc (t - 1), oneS (t - 1), qh (t - 1), lowc (t - 1), a0h (t - 1), true]
    rw [st_eq]
    simp only [lowc, oneS, qh, a0h, Bool.false_or]
    by_cases h : t - 1 < 10
    · simp only [h, decide_true, ite_true]; rw [Bool.eq_iff_iff]; simp; omega
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show R0h t = o5B ARB_ST [lowc (t - 1), oneS (t - 1), qh (t - 1), lowc (t - 1), a0h (t - 1), true]
    rw [r0_eq]; simp only [lowc, oneS, qh, R0h]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show lowc t = o5B GRANT [lowc (t - 1), oneS (t - 1), qh (t - 1), false, false, true]
    rw [g1_eq]; rfl
  · intro i
    by_cases h : i.val = 2
    · simp only [Bho, h, if_true]; exact shift_w 3
    · simp only [Bho, h, if_false]; exact shift_w 1
  · intro t
    show g2h t = o6B GRANT [lowc (t - 1), oneS (t - 1), qh (t - 3), false, false, true]
    rw [g2_eq]; simp only [oneS, qh, g2h]; rw [Bool.eq_iff_iff]; simp; omega

/-- `ho` is uncontested for every window (request 1 is never pending). -/
theorem ho_unc (W : Nat) : Unc W lowc oneS lowc g2h := fun u _ h _ => by
  simp [Pend, lowc] at h

/-- **The real R0 rises before the grant** in `ho`, so no virtual R0 (any bands whose stage
lower end plus tap lower end is at least 1, as every cert8 band is) matches it. -/
theorem ho_not_vmerge {loF hiF lo1 hi1 lo2 hi2 : Nat} (h1 : 1 ≤ loF + lo1) (h2 : 1 ≤ loF + lo2) :
    ¬ VMerge loF hiF lo1 hi1 lo2 hi2 lowc g2h R0h := by
  intro hv
  rcases vmerge_needs_grant hv (t := 12) (by decide) with ⟨u, _, hu⟩ | ⟨u, hu1, hu⟩
  · simp [lowc] at hu
  · simp [g2h] at hu; omega

/-- **The virtual ctl band is 2 steps too late** in `ho`: with cert8's choice of bands, the
virtual stage band plus the ctl pin band lower ends sum to the real lower path
`A0 -> ustate -> q -> ugrant` (here `1 + 3 = 4`, all lower ends), and no virtual ctl / grant pair
matches the real `g2` rise at 14 = 10 + 4. -/
theorem ho_not_vctl {loF hiF loR hiR lo hi : Nat} (br : Bool) (s ctl : Sig) (hsum : loF + lo = 4)
    (hc : VCtl lo hi a0h ctl) : ¬ VGrant loF hiF loR hiR br s ctl g2h := by
  intro hg
  obtain ⟨u, hu, ha⟩ := vgrant_rise_ctl hc hg (t := 14) (by decide) (by decide)
    (fun u hu => by simp [g2h]; omega)
  simp [a0h] at ha; omega

/-- **HARB7's virtual core is refuted by an UNCONTESTED handover of the real cell.** There is a
behaviour of the real `bd_arbiter` core (real INITs, per-pin semantics), uncontested for every
window `W`, with exclusive grants, whose `R0` is no virtual R0 (bands with lower ends summing to
`≥ 1`) and whose `g2` is no virtual grant over any virtual ctl with cert8's lower-band split. -/
theorem unc_not_harb : ∃ (B : ArbBands) (r1 r2 rs a q R0 g1 g2 : Sig),
    ArbPin B r1 r2 rs a q R0 g1 g2 ∧ (∀ t, (g1 t && g2 t) = false) ∧ (∀ W, Unc W r1 r2 g1 g2) ∧
    (∀ loF hiF lo1 hi1 lo2 hi2, 1 ≤ loF + lo1 → 1 ≤ loF + lo2 → ¬ VMerge loF hiF lo1 hi1 lo2 hi2 g1 g2 R0) ∧
    (∀ loF hiF loR hiR lo hi br ctl, loF + lo = 4 → VCtl lo hi a ctl → ¬ VGrant loF hiF loR hiR br r2 ctl g2) :=
  ⟨Bho, lowc, oneS, lowc, a0h, qh, R0h, lowc, g2h, ho_pin, fun t => by simp [lowc], ho_unc,
    fun _ _ _ _ _ _ h1 h2 => ho_not_vmerge h1 h2,
    fun _ _ _ _ _ _ br ctl hs hc => ho_not_vctl br oneS ctl hs hc⟩

end Formal.Core.XAudit.Events8Arb
