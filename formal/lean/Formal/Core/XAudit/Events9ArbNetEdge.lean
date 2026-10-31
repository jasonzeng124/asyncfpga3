import Formal.Core.XAudit.Events9ArbNet

/-!
# Formal.Core.XAudit.Events9ArbNetEdge — B1 / B2 / C from edge-window conditions

Probe E9ArbNet, part 2 (shard A). See `formal/notes/A-e9arbnet.md` §4.

`Events9Arb.RdOK` (B1 / B2 / C of one reader `y t = s (wr t) && e (wq t)`) quantifies over every
reader time. This file reduces it to conditions on the EDGES of the request `s` and of the state
literal `e`, each with a window whose ends are band numbers:

* **B1** (`b1_of`): from (i) "a flip of `e` away from the branch at `τ` leaves ustate O6 reading
  the request low" (`FlipAway`; proved from ustate O6's INIT function and `QClean` in
  `flipAway1` / `flipAway2`), (ii) the ROW `lo DrQ + lo Dq ≥ hi Dr + 2`, and (iii) `NoReReq`: the
  request stays low from that read until `τ + hi Dq + 2 − lo Dr` (no re-request of the branch while
  the arbiter switches away from it: the uncontested schedule, in the form B1 needs);
* **B2** (`b2_of`): `HB2r` (after each request rise `σ`, every ustate time in
  `[σ + lo Dr − hi Dq, σ + hi Dr + 2 − lo Dq)` at which the literal holds is settled) and `HB2f`
  (after each flip of the literal toward the branch at `τ`, every ustate time in
  `[τ, τ + hi Dq + 2 − lo Dq)` is settled);
* **C** (`c_of`): `HC` (around each request fall `σ`, ustate reads A0 HIGH at every time in
  `[σ + lo Dr − hi Dq, σ + hi Dr + 2 − lo Dq)`).

`rdOK_of` packages the three. `QClean` is the digital no-metastability hypothesis: whenever `q`
changes at `τ`, ustate O6's own read of `q` at `τ` still sees the old value (no runt shorter than
the loop). These window conditions are where the uncontested schedule and the environment enter;
their discharge from the certificate's walks is the (untrusted) rows of `Events9ArbNetRows`.
-/

namespace Formal.Core.XAudit.Events9ArbNet

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events8Arb
open Formal.Core.XAudit.Events9Arb
open Formal.Core.LutList (o5B o6B)
open Formal.Cells.ArbBinary (ARB_ST GRANT)

/-- Discrete intermediate value: a Boolean signal true at `u` and false at `v ≥ u` has a falling
step in `(u, v]`. -/
theorem first_fall (e : Sig) {u v : Nat} (hu : e u = true) (hv : e v = false) (huv : u ≤ v) :
    ∃ τ, u < τ ∧ τ ≤ v ∧ e (τ - 1) = true ∧ e τ = false := by
  suffices H : ∀ k w, w = u + k → e w = false → ∃ τ, u < τ ∧ τ ≤ w ∧ e (τ - 1) = true ∧ e τ = false from
    H (v - u) v (by omega) hv
  intro k
  induction k with
  | zero => intro w hw h; subst hw; rw [hu] at h; exact absurd h (by decide)
  | succ k ih =>
    intro w hw h
    cases hp : e (w - 1)
    · obtain ⟨τ, h1, h2, h3, h4⟩ := ih (w - 1) (by omega) hp
      exact ⟨τ, h1, by omega, h3, h4⟩
    · exact ⟨w, by omega, Nat.le_refl _, hp, h⟩

/-! ## The state flip needs the request read low (ustate O6) -/

section
variable {r1 r2 q rs a : Sig} {f0 f1 f2 f3 f4 : Nat → Nat}

/-- **QClean** (named hypothesis; the digital no-metastability condition): at every change of `q`,
ustate O6's own read of `q` still sees the previous value. -/
def QClean (q : Sig) (f2 : Nat → Nat) : Prop := ∀ τ, 1 ≤ τ → q (τ - 1) ≠ q τ → q (f2 τ) = q (τ - 1)

/-- A flip of `q` from 1 to 0 needs ustate O6 to read `r1` low (and A0 low). -/
theorem flipAway1 (hq : ∀ t, q t = o6B ARB_ST [r1 (f0 t), r2 (f1 t), q (f2 t), rs (f3 t), a (f4 t), true])
    (hc : QClean q f2) {τ : Nat} (h1 : 1 ≤ τ) (hp : q (τ - 1) = true) (hn : q τ = false) :
    r1 (f0 τ) = false := by
  have hq2 : q (f2 τ) = true := by rw [hc τ h1 (by rw [hp, hn]; decide)]; exact hp
  have e := hq τ
  rw [st_eq, hn, hq2] at e
  revert e
  cases r1 (f0 τ) <;> cases r2 (f1 τ) <;> cases rs (f3 τ) <;> cases a (f4 τ) <;> simp

/-- A flip of `q` from 0 to 1 after the reset is released needs ustate O6 to read `r2` low. -/
theorem flipAway2 (hq : ∀ t, q t = o6B ARB_ST [r1 (f0 t), r2 (f1 t), q (f2 t), rs (f3 t), a (f4 t), true])
    (hc : QClean q f2) {τ : Nat} (h1 : 1 ≤ τ) (hr : rs (f3 τ) = false) (hp : q (τ - 1) = false)
    (hn : q τ = true) : r2 (f1 τ) = false := by
  have hq2 : q (f2 τ) = false := by rw [hc τ h1 (by rw [hp, hn]; decide)]; exact hp
  have e := hq τ
  rw [st_eq, hn, hq2, hr] at e
  revert e
  cases r1 (f0 τ) <;> cases r2 (f1 τ) <;> cases a (f4 τ) <;> simp

end

/-! ## One reader -/

theorem sh2W {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) (h : 2 ≤ lo) :
    Warp (lo - 2) (hi - 2) (fun t => f (t + 2)) :=
  ⟨fun x z hxz => w.mono _ _ (by omega), fun t => by have := w.le_late (t + 2); omega,
    fun t => by have := w.early_le (t + 2); omega⟩

theorem warp_le {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : lo ≤ hi := by
  have a := w.le_late (hi + lo); have b := w.early_le (hi + lo); omega

section
variable {s e y : Sig} {wr wq fQ : Nat → Nat} {loDr hiDr loDq hiDq loQ hiQ T0 : Nat}

/-- **B1** from the flip property, the row, and no re-request during the switch. -/
theorem b1_of (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hfQ : Warp loQ hiQ fQ)
    (hT : hiDr + hiDq + 2 ≤ T0)
    (hrow : hiDr + 2 ≤ loQ + loDq)
    (hflip : ∀ τ, T0 < τ + hiDq + 2 → 1 ≤ τ → e (τ - 1) = true → e τ = false → s (fQ τ) = false)
    (hnore : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false) :
    ∀ t, T0 < t → s (wr t) = true → e (wq t) = false → y (t - 2) = false := by
  intro t ht hs he
  rw [hy]
  have l1 := warp_le hwr; have l2 := warp_le hwq
  cases hs2 : s (wr (t - 2))
  · rfl
  · cases he2 : e (wq (t - 2))
    · rfl
    · exfalso
      obtain ⟨τ, h1, h2, h3, h4⟩ := first_fall e he2 he (hwq.mono _ _ (by omega))
      have a1 := hfQ.le_late τ
      have a2 := hwq.le_late t
      have a3 := hwq.early_le (t - 2)
      have a4 := hwr.early_le (t - 2)
      have a5 := hwr.le_late (t - 2)
      have hfl := hflip τ (by omega) (by omega) h3 h4
      have := hnore τ (by omega) h3 h4 (wr (t - 2)) (by omega) (by omega)
      rw [hs2] at this; exact absurd this (by decide)

/-- **B2** from the two settledness windows. -/
theorem b2_of {St : Nat → Prop} (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hT : hiDr + hiDq + 2 ≤ T0)
    (hr : ∀ σ, 1 ≤ σ → s (σ - 1) = false → s σ = true →
      ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → e u = true → St u)
    (hf : ∀ τ, 1 ≤ τ → e (τ - 1) = false → e τ = true →
      ∀ u, τ ≤ u → u + loDq < τ + hiDq + 2 → St u) :
    ∀ t, T0 < t → s (wr t) = true → e (wq t) = true → ¬ St (wq t) → y (t - 2) = true := by
  intro t ht hs he hns
  rw [hy]
  have l1 := warp_le hwr; have l2 := warp_le hwq
  have a2 := hwq.le_late t
  have a2' := hwq.early_le t
  have a3 := hwq.early_le (t - 2)
  have a4 := hwr.early_le (t - 2)
  have a5 := hwr.le_late t
  cases hs2 : s (wr (t - 2))
  · exfalso
    obtain ⟨σ, h1, h2, h3, h4⟩ := first_fall (fun v => !s v) (u := wr (t - 2)) (v := wr t)
      (by simp [hs2]) (by simp [hs]) (hwr.mono _ _ (by omega))
    simp only [Bool.not_eq_true', Bool.not_eq_false'] at h3 h4
    exact hns (hr σ (by omega) h3 h4 (wq t) (by omega) (by omega) he)
  · cases he2 : e (wq (t - 2))
    · exfalso
      obtain ⟨τ, h1, h2, h3, h4⟩ := first_fall (fun v => !e v) (u := wq (t - 2)) (v := wq t)
        (by simp [he2]) (by simp [he]) (hwq.mono _ _ (by omega))
      simp only [Bool.not_eq_true', Bool.not_eq_false'] at h3 h4
      exact hns (hf τ (by omega) h3 h4 (wq t) h2 (by omega))
    · rfl

/-- **C** from "ustate reads A0 high around each request fall". -/
theorem c_of {a q : Sig} {f4 : Nat → Nat} (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hT : hiDr + hiDq + 2 ≤ T0)
    (hc : ∀ σ, 1 ≤ σ → s (σ - 1) = true → s σ = false →
      ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → a (f4 u) = true) :
    ∀ t, T0 < t → s (wr t) = false → Settled a q f4 (wq t) → e (wq t) = true → y (t - 2) = false := by
  intro t ht hs hst _
  rw [hy]
  have l1 := warp_le hwr; have l2 := warp_le hwq
  have a2 := hwq.le_late t
  have a2' := hwq.early_le t
  have a4 := hwr.early_le (t - 2)
  have a5 := hwr.le_late t
  cases hs2 : s (wr (t - 2))
  · rfl
  · exfalso
    obtain ⟨σ, h1, h2, h3, h4⟩ := first_fall s hs2 hs (hwr.mono _ _ (by omega))
    have := hc σ (by omega) h3 h4 (wq t) (by omega) (by omega)
    rw [hst.1] at this; exact absurd this (by decide)

/-- **`rdOK_of`**: B1, B2 and C of one reader from the edge-window conditions. -/
theorem rdOK_of {a q : Sig} {f4 : Nat → Nat} (hy : ∀ t, y t = (s (wr t) && e (wq t)))
    (hwr : Warp loDr hiDr wr) (hwq : Warp loDq hiDq wq) (hfQ : Warp loQ hiQ fQ)
    (hT : hiDr + hiDq + 2 ≤ T0) (hrow : hiDr + 2 ≤ loQ + loDq)
    (hflip : ∀ τ, T0 < τ + hiDq + 2 → 1 ≤ τ → e (τ - 1) = true → e τ = false → s (fQ τ) = false)
    (hnore : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
      ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false)
    (hr : ∀ σ, 1 ≤ σ → s (σ - 1) = false → s σ = true →
      ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → e u = true → Settled a q f4 u)
    (hf : ∀ τ, 1 ≤ τ → e (τ - 1) = false → e τ = true →
      ∀ u, τ ≤ u → u + loDq < τ + hiDq + 2 → Settled a q f4 u)
    (hc : ∀ σ, 1 ≤ σ → s (σ - 1) = true → s σ = false →
      ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → a (f4 u) = true) :
    RdOK (Settled a q f4) s e y wr wq T0 := fun t ht =>
  ⟨b1_of hy hwr hwq hfQ hT hrow hflip hnore t ht, b2_of hy hwr hwq hT hr hf t ht,
    fun hs hst he => c_of (q := q) hy hwr hwq hT hc t ht hs hst he⟩

end


/-! ## The arbiter of `d`: `ArbCond` from the edge-window conditions -/

/-- The edge-window conditions of one reader (B1's no-re-request window, B2's two settledness
windows, C's A0-high window), against ustate O6's A0 read `f4`. -/
structure RdEdge (a q : Sig) (f4 : Nat → Nat) (s e : Sig) (fQ : Nat → Nat) (loDr hiDr loDq hiDq : Nat) : Prop where
  nore : ∀ τ, 1 ≤ τ → e (τ - 1) = true → e τ = false →
    ∀ v, fQ τ ≤ v → v + loDr < τ + hiDq + 2 → s v = false
  rise : ∀ σ, 1 ≤ σ → s (σ - 1) = false → s σ = true →
    ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → e u = true → Settled a q f4 u
  flip : ∀ τ, 1 ≤ τ → e (τ - 1) = false → e τ = true →
    ∀ u, τ ≤ u → u + loDq < τ + hiDq + 2 → Settled a q f4 u
  fall : ∀ σ, 1 ≤ σ → s (σ - 1) = true → s σ = false →
    ∀ u, σ + loDr ≤ u + hiDq → u + loDq < σ + hiDr + 2 → a (f4 u) = true

section
variable {N : Nat} (d : Design) (a : ArbD N)

/-- ustate O6's own `q` read and its reset read. -/
def PqQ : Path := (a.gQ, a.iqQ) :: a.pqQ
def PrQ : Path := (a.gQ, a.irQ) :: a.prQ
def P1Q : Path := (a.gQ, a.i1Q) :: a.p1Q
def P2Q : Path := (a.gQ, a.i2Q) :: a.p2Q

/-- **The B1 rows and the start bounds** (decidable): per reader `hi Dr + 2 ≤ lo DrQ + lo Dq` (B1)
and `hi Dr + hi Dq + 2 ≤ T0`; and the reset of ustate O6 is released by `T0` (`T + hi PrQ ≤ T0`). -/
def ArbRowsOK (T T0 : Nat) : Prop :=
  let B := bandsOf d a
  (B.g1 0).2 + 2 ≤ plo d (P1Q a) + (B.g1 2).1 ∧ (B.g2 1).2 + 2 ≤ plo d (P2Q a) + (B.g2 2).1 ∧
  (B.r0 0).2 - 2 + 2 ≤ plo d (P1Q a) + ((B.r0 2).1 - 2) ∧ (B.r0 1).2 - 2 + 2 ≤ plo d (P2Q a) + ((B.r0 2).1 - 2) ∧
  (B.g1 0).2 + (B.g1 2).2 + 2 ≤ T0 ∧ (B.g2 1).2 + (B.g2 2).2 + 2 ≤ T0 ∧
  (B.r0 0).2 + (B.r0 2).2 + 2 ≤ T0 ∧ (B.r0 1).2 + (B.r0 2).2 + 2 ≤ T0 ∧
  T + phi d (PrQ a) + (B.g2 2).2 + 2 ≤ T0 ∧ T + phi d (PrQ a) + (B.r0 2).2 ≤ T0 ∧
  2 ≤ (B.r0 0).1 ∧ 2 ≤ (B.r0 1).1 ∧ 2 ≤ (B.r0 2).1

instance (T T0 : Nat) : Decidable (ArbRowsOK d a T T0) := by unfold ArbRowsOK; exact inferInstance

end

section
variable {N : Nat} {d : Design} {x : Fin d.n → Sig} (hsat : SatPinW d plG x) (rn : Fin N → RNode)
  (a : ArbD N)

/-- **The edge-window conditions of one arbiter** (hypotheses on the traces of `d`): `QClean` for
`q`, the quiet start, the settle bound, and `RdEdge` for the four readers (each with its own
request / q bands and ustate O6's read of its request). -/
structure ArbEdge (T0 H : Nat) : Prop where
  clean : QClean (qS (x := x) a) (tau hsat (PqQ a))
  low : ∀ t, t ≤ T0 + 2 → g1S (x := x) a t = false ∧ g2S (x := x) a t = false ∧ R0S (x := x) a t = false
  stall : ∀ v, ∃ v', v' ≤ v ∧ v ≤ v' + H ∧
    (v' = 0 ∨ Ok (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a) (v' + 1 - kOf (bandsOf d a)))
  hi : H + kOf (bandsOf d a) + ((bandsOf d a).st 4).2 ≤ 10 ^ 12
  e1 : RdEdge (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a) (r1S (x := x) a) (qS (x := x) a)
    (tau hsat (P1Q a)) ((bandsOf d a).g1 0).1 ((bandsOf d a).g1 0).2 ((bandsOf d a).g1 2).1 ((bandsOf d a).g1 2).2
  e2 : RdEdge (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a) (r2S (x := x) a) (fun u => !qS (x := x) a u)
    (tau hsat (P2Q a)) ((bandsOf d a).g2 1).1 ((bandsOf d a).g2 1).2 ((bandsOf d a).g2 2).1 ((bandsOf d a).g2 2).2
  e3 : RdEdge (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a) (r1S (x := x) a) (qS (x := x) a)
    (tau hsat (P1Q a)) (((bandsOf d a).r0 0).1 - 2) (((bandsOf d a).r0 0).2 - 2)
    (((bandsOf d a).r0 2).1 - 2) (((bandsOf d a).r0 2).2 - 2)
  e4 : RdEdge (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a) (r2S (x := x) a) (fun u => !qS (x := x) a u)
    (tau hsat (P2Q a)) (((bandsOf d a).r0 1).1 - 2) (((bandsOf d a).r0 1).2 - 2)
    (((bandsOf d a).r0 2).1 - 2) (((bandsOf d a).r0 2).2 - 2)

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {fuel rw : Nat}
  {x : Fin d.n → Sig} (hsat : SatPinW d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include h0 h1

/-- **`arbCond_of_edge`**: at an `ArbOK` arbiter with its rows (`ArbRowsOK`), the edge-window
conditions `ArbEdge` and the design reset (`rw` high until `T`) give the trace conditions
`ArbCond` of `design_verdict9arbnet`. The state flips are taken from ustate O6's INIT function
(`flipAway1` / `flipAway2`, under `QClean`). -/
theorem arbCond_of_edge {a : ArbD N} (hA : ArbOK d net b rn fuel rw a) {T T0 H : Nat}
    (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (hrows : ArbRowsOK d a T T0)
    (he : ArbEdge hsat rn a T0 H) : ArbCond hsat rn a T0 H := by
  obtain ⟨r11, r1q, s1, r22, r2q, s2, rR1, rR2, rRq, _sR, _hgQ, rQ1, rQ2, rQq, rQr, rQA, sQ, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hA
  obtain ⟨w1, w2, w3, w4, t1, t2, t3, t4, tr, tr', l0, l1, l2⟩ := hrows
  have wP : ∀ {gi i w : Nat} {p : Path}, RdP d fuel gi i p w → Warp (plo d ((gi, i) :: p)) (phi d ((gi, i) :: p))
      (tau hsat ((gi, i) :: p)) := fun h => tau_warp hsat _ h.2.2.1
  -- ustate O6's equation
  have hq : ∀ t, qS (x := x) a t = o6B ARB_ST [r1S (x := x) a (tau hsat (P1Q a) t), r2S (x := x) a (tau hsat (P2Q a) t),
      qS (x := x) a (tau hsat (PqQ a) t), x (d.wire rw) (tau hsat (PrQ a) t),
      aS (x := x) rn a (tau hsat (PA a) t), true] := by
    intro t
    rw [st_eq]
    show x (d.wire (gt d a.gQ).out) t = _
    rw [gate_spec hsat h0 h1 rQ1.1 sQ t]
    simp only
    rw [rdP_val hsat h0 h1 rQ1 t, rdP_val hsat h0 h1 rQ2 t, rdP_val hsat h0 h1 rQq t,
      rdP_val hsat h0 h1 rQr t, rdP_val hsat h0 h1 rQA t]
    rfl
  have hrs : ∀ τ, T + phi d (PrQ a) ≤ τ → x (d.wire rw) (tau hsat (PrQ a) τ) = false := by
    intro τ hτ
    rw [hrst]
    have := (wP rQr).early_le τ
    simp only [decide_eq_false_iff_not, Nat.not_lt]
    show T ≤ tau hsat ((a.gQ, a.irQ) :: a.prQ) τ
    simp only [PrQ] at hτ
    omega
  -- the reader equations
  have hg1 : ∀ t, g1S (x := x) a t = (r1S (x := x) a (f1Of hsat a 0 t) && qS (x := x) a (f1Of hsat a 2 t)) := by
    intro t
    unfold g1S
    rw [gate_spec hsat h0 h1 r11.1 s1 t]
    simp only
    rw [rdP_val hsat h0 h1 r11 t, rdP_val hsat h0 h1 r1q t]
    rfl
  have hg2 : ∀ t, g2S (x := x) a t = (r2S (x := x) a (f2Of hsat a 1 t) && !qS (x := x) a (f2Of hsat a 2 t)) := by
    intro t
    unfold g2S
    rw [gate_spec hsat h0 h1 r22.1 s2 t]
    simp only
    rw [rdP_val hsat h0 h1 r22 t, rdP_val hsat h0 h1 r2q t]
    rfl
  -- the flips
  have fl1 : ∀ τ, 1 ≤ τ → qS (x := x) a (τ - 1) = true → qS (x := x) a τ = false →
      r1S (x := x) a (tau hsat (P1Q a) τ) = false := fun τ h1' hp hn =>
    flipAway1 hq he.clean h1' hp hn
  have fl2 : ∀ τ, T + phi d (PrQ a) ≤ τ → 1 ≤ τ → (fun u => !qS (x := x) a u) (τ - 1) = true →
      (fun u => !qS (x := x) a u) τ = false → r2S (x := x) a (tau hsat (P2Q a) τ) = false := fun τ hτ h1' hp hn => by
    simp only [Bool.not_eq_true', Bool.not_eq_false'] at hp hn
    exact flipAway2 hq he.clean h1' (hrs τ hτ) hp hn
  -- the warps
  have wg10 : Warp ((bandsOf d a).g1 0).1 ((bandsOf d a).g1 0).2 (f1Of hsat a 0) := wP r11
  have wg12 : Warp ((bandsOf d a).g1 2).1 ((bandsOf d a).g1 2).2 (f1Of hsat a 2) := wP r1q
  have wg21 : Warp ((bandsOf d a).g2 1).1 ((bandsOf d a).g2 1).2 (f2Of hsat a 1) := wP r22
  have wg22 : Warp ((bandsOf d a).g2 2).1 ((bandsOf d a).g2 2).2 (f2Of hsat a 2) := wP r2q
  have wr0 : Warp ((bandsOf d a).r0 0).1 ((bandsOf d a).r0 0).2 (frOf hsat a 0) := wP rR1
  have wr1 : Warp ((bandsOf d a).r0 1).1 ((bandsOf d a).r0 1).2 (frOf hsat a 1) := wP rR2
  have wr2 : Warp ((bandsOf d a).r0 2).1 ((bandsOf d a).r0 2).2 (frOf hsat a 2) := wP rRq
  have wq1 : Warp (plo d (P1Q a)) (phi d (P1Q a)) (tau hsat (P1Q a)) := wP rQ1
  have wq2 : Warp (plo d (P2Q a)) (phi d (P2Q a)) (tau hsat (P2Q a)) := wP rQ2
  have lg12 := warp_le wg12
  have lg22 := warp_le wg22
  have lr2 := warp_le wr2
  refine ⟨he.low, by omega, by omega, by omega, he.stall, he.hi, ?_, ?_, ?_, ?_⟩
  · exact rdOK_of hg1 wg10 wg12 wq1 t1 w1 (fun τ _ h1' hp hn => fl1 τ h1' hp hn)
      he.e1.nore he.e1.rise he.e1.flip he.e1.fall
  · exact rdOK_of hg2 wg21 wg22 wq2 t2 w2 (fun τ hτ h1' hp hn => fl2 τ (by omega) h1' hp hn)
      he.e2.nore he.e2.rise he.e2.flip he.e2.fall
  · exact rdOK_of (fun t => rfl) (sh2W wr0 l0) (sh2W wr2 l2) wq1 (by omega) w3
      (fun τ _ h1' hp hn => fl1 τ h1' hp hn) he.e3.nore he.e3.rise he.e3.flip he.e3.fall
  · exact rdOK_of (fun t => rfl) (sh2W wr1 l1) (sh2W wr2 l2) wq2 (by omega) w4
      (fun τ hτ h1' hp hn => fl2 τ (by omega) h1' hp hn) he.e4.nore he.e4.rise he.e4.flip he.e4.fall

end

end Formal.Core.XAudit.Events9ArbNet
