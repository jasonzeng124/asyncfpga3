import Formal.Core.XAudit.Events2

/-!
# Formal.Core.XAudit.Events2Strict — the strict own-feedback race (contradiction X2)

Shard A, contradiction X2 of `formal/out/gcd_hw_hypotheses.md`. Notes:
`formal/notes/A-contradictions.md` §X2.

`Events.Race` and `Events2.Back` state the C-element's own-feedback race with
`≤`; C's `FbBound` is strict, and C-8g (`Net.MullerTimedCx.boundary_function_hazard`)
shows that at equality the feedback (I2) and the neighbour's answer (I1)
reach the LUT in the same step, a transition that crosses a function hazard
of the real `bd_c2n` INIT.

## Which assumption makes `≤` sound in Events

`Events.Beh.hc` / `Events2.Beh.hc`: the LUT output at `t` is the settled
function of ALL its pins read at ONE instant `F j t`. Named here:

* **H_ATOMIC_LUT** (`AtomicLUT`): every pin of a LUT (inputs, own feedback,
  reset) is read through the same warp. A behaviour of `Events2.Beh` is
  exactly a per-pin behaviour (`BehP`) with `AtomicLUT` (`Beh.toP`,
  `Beh.toP_atomic`). With one sample instant a feedback edge and a neighbour
  edge that arrive in the same step are seen together, so equality is safe.

A 7-series LUT is a mux tree (`Core.LutTree`): each pin enters at its own
level and reaches `O` through its own path. The per-pin model `BehP` reads
pin `p` through its own warp `Fp j p` (band `[loP, hiP]`, the pin-to-O arc),
the feedback pin through `Fq j` and the reset through `Fr j`. That is the
pure per-pin delay form of the mux tree, B's H_PIN_FIFO; it exhibits the
function hazards (the output shows the function of a vector mixing old and
new pin values).

## Results

* `RaceStrict` / `BackStrict` (decidable) and `RaceStrict.race`,
  `BackStrict.back`: the strict forms imply the old ones.
* `BackMargin m` (`m` steps of margin); `backStrict_iff`: `BackStrict` is
  `BackMargin 1`.
* `BackPin` (decidable): the race measured to the LUT OUTPUT with per-pin
  arcs, `hiQ j + hiPq j ≤ loP j p + loG j p + Σ_walk (loP + loG)`.
* **`BehP.safe`**: under `BackPin`, every node of every per-pin behaviour is
  `ph v (M t j)` at every time. No H_ATOMIC_LUT.
* **`PinSkew m`**: the LUT's own-feedback pin is at most `m` steps slower
  than any of its input pins (`hiPq j ≤ loP j p + m`), and the atomic band's
  `loF` is no faster than any input pin. `back_pin_of_margin`:
  `BackMargin m ∧ PinSkew m ⇒ BackPin`. **`safe_strict`**: `BackStrict` and
  `PinSkew 1` make every per-pin behaviour safe.
* **`cx_unsafe`** (the equality case fails without H_ATOMIC_LUT): a one-stage
  network with `Back` holding WITH EQUALITY (`cx_back`, and `cx_not_strict`)
  and a per-pin behaviour whose feedback pin is one step slower than an
  input pin (`PinSkew 1` holds, `cx_skew`) in which the C-element fires on
  ONE input: its output differs from the counter model at step 4.

So the strict form is sound without H_ATOMIC_LUT exactly when the intra-LUT
skew between the feedback pin and the input pins is at most the margin; with
whole-step bands, `<` is a margin of one step. A larger measured pin skew
needs `BackMargin m` with that `m` (the general statement).
-/

namespace Formal.Core.XAudit.Events2Strict

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph ph_zero ph_off offB)
open Formal.Core.XAudit.Events2

/-! ## 1. The strict forms -/

/-- **RaceStrict** (Events, decidable): own feedback strictly faster than the
fastest round trip through a neighbour. -/
def RaceStrict {N : Nat} (net : Events.MNet N) (b : Events.Bands N) : Prop :=
  ∀ j p p', net.src (net.src j p) p' = j →
    b.hiQ j < b.loG j p + b.loF (net.src j p) + b.loG (net.src j p) p'

instance {N : Nat} (net : Events.MNet N) (b : Events.Bands N) : Decidable (RaceStrict net b) := by
  unfold RaceStrict; exact inferInstance

theorem RaceStrict.race {N : Nat} {net : Events.MNet N} {b : Events.Bands N}
    (h : RaceStrict net b) : Events.Race net b :=
  fun j p p' hs => Nat.le_of_lt (h j p p' hs)

/-- **BackStrict** (Events2, decidable): `Back` with `<` in the timing clause. -/
def BackStrict {N : Nat} {net : CNet N} (b : Bands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Prop :=
  ∀ j p, walkOK net (net.src j p) j (back j p) = true ∧
    wTok net (back j p) + net.off j p ≤ 1 ∧ b.hiQ j < b.loG j p + wLo b (back j p)

instance {N : Nat} {net : CNet N} (b : Bands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Decidable (BackStrict b back) := by
  unfold BackStrict; exact inferInstance

theorem BackStrict.back {N : Nat} {net : CNet N} {b : Bands net}
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (h : BackStrict b back) :
    Back b back :=
  fun j p => ⟨(h j p).1, (h j p).2.1, Nat.le_of_lt (h j p).2.2⟩

/-- `Back` with `m` steps of margin. -/
def BackMargin {N : Nat} {net : CNet N} (m : Nat) (b : Bands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Prop :=
  ∀ j p, walkOK net (net.src j p) j (back j p) = true ∧
    wTok net (back j p) + net.off j p ≤ 1 ∧ b.hiQ j + m ≤ b.loG j p + wLo b (back j p)

theorem backStrict_iff {N : Nat} {net : CNet N} (b : Bands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) :
    BackStrict b back ↔ BackMargin 1 b back := by
  constructor
  · intro h j p; exact ⟨(h j p).1, (h j p).2.1, (h j p).2.2⟩
  · intro h j p; exact ⟨(h j p).1, (h j p).2.1, (h j p).2.2⟩

theorem BackMargin.back {N : Nat} {net : CNet N} {m : Nat} {b : Bands net}
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (h : BackMargin m b back) :
    Back b back :=
  fun j p => ⟨(h j p).1, (h j p).2.1, by have := (h j p).2.2; omega⟩

/-! ## 2. The per-pin LUT model -/

/-- Per-pin LUT arcs (pin-to-O delay bands, in steps): input pin `p`, own
feedback pin, reset pin. -/
structure PinBands {N : Nat} (net : CNet N) where
  loP : (j : Fin N) → Fin (net.ar j) → Nat
  hiP : (j : Fin N) → Fin (net.ar j) → Nat
  loPq : Fin N → Nat
  hiPq : Fin N → Nat
  loPr : Fin N → Nat
  hiPr : Fin N → Nat

/-- A behaviour with per-pin LUT sampling: the LUT output at `t` is the
settled function of input pin `p` read at `Fp j p t`, the feedback pin read
at `Fq j t` and the reset pin read at `Fr j t`, each a monotone warp in its
own band. Routes (`G`) and the feedback route (`Q`) as in `Events2.Beh`
(their bands from `b`; `b.loF`/`b.hiF` are not used). -/
structure BehP {N : Nat} (net : CNet N) (b : Bands net) (pb : PinBands net) where
  c : Fin N → Sig
  pin : (j : Fin N) → Fin (net.ar j) → Sig
  q : Fin N → Sig
  r : Fin N → Sig
  Fp : (j : Fin N) → Fin (net.ar j) → Nat → Nat
  Fq : Fin N → Nat → Nat
  Fr : Fin N → Nat → Nat
  G : (j : Fin N) → Fin (net.ar j) → Nat → Nat
  Q : Fin N → Nat → Nat
  wFp : ∀ j p, Warp (pb.loP j p) (pb.hiP j p) (Fp j p)
  wFq : ∀ j, Warp (pb.loPq j) (pb.hiPq j) (Fq j)
  wFr : ∀ j, Warp (pb.loPr j) (pb.hiPr j) (Fr j)
  wG : ∀ j p, Warp (b.loG j p) (b.hiG j p) (G j p)
  wQ : ∀ j, Warp (b.loQ j) (b.hiQ j) (Q j)
  loP1 : ∀ j p, 1 ≤ pb.loP j p
  loPq1 : ∀ j, 1 ≤ pb.loPq j
  loG1 : ∀ j p, 1 ≤ b.loG j p
  loQ1 : ∀ j, 1 ≤ b.loQ j
  hc : ∀ j t, c j t = net.lutF j (fun p => pin j p (Fp j p t)) (q j (Fq j t)) (r j (Fr j t))
  hpin : ∀ j p t, pin j p t = (net.inv j p ^^ c (net.src j p) (G j p t))
  hq : ∀ j t, q j t = c j (Q j t)
  r0 : ∀ j, r j 0 = true
  ranti : ∀ j a b, a ≤ b → r j b = true → r j a = true

/-- **H_ATOMIC_LUT**: all pins of every LUT are read at one instant. -/
def AtomicLUT {N : Nat} {net : CNet N} {b : Bands net} {pb : PinBands net}
    (x : BehP net b pb) : Prop :=
  ∀ j, (∀ p, x.Fp j p = x.Fq j) ∧ x.Fr j = x.Fq j

/-- The atomic bands as per-pin bands (every pin gets the LUT's band). -/
def atomicBands {N : Nat} {net : CNet N} (b : Bands net) : PinBands net :=
  ⟨fun j _ => b.loF j, fun j _ => b.hiF j, b.loF, b.hiF, b.loF, b.hiF⟩

/-- An `Events2.Beh` is a per-pin behaviour (with the LUT band on every pin)… -/
def toP {N : Nat} {net : CNet N} {b : Bands net} (x : Beh net b) : BehP net b (atomicBands b) where
  c := x.c
  pin := x.pin
  q := x.q
  r := x.r
  Fp j _ := x.F j
  Fq := x.F
  Fr := x.F
  G := x.G
  Q := x.Q
  wFp j _ := x.wF j
  wFq := x.wF
  wFr := x.wF
  wG := x.wG
  wQ := x.wQ
  loP1 j _ := x.loF1 j
  loPq1 := x.loF1
  loG1 := x.loG1
  loQ1 := x.loQ1
  hc := x.hc
  hpin := x.hpin
  hq := x.hq
  r0 := x.r0
  ranti := x.ranti

/-- … that satisfies H_ATOMIC_LUT. -/
theorem toP_atomic {N : Nat} {net : CNet N} {b : Bands net} (x : Beh net b) :
    AtomicLUT (toP x) := fun _ => ⟨fun _ => rfl, rfl⟩

/-- Fastest traversal of a walk with per-pin LUT arcs. -/
def wLoP {N : Nat} {net : CNet N} (b : Bands net) (pb : PinBands net) : List (Arc net) → Nat
  | [] => 0
  | ⟨k, p⟩ :: w => pb.loP k p + b.loG k p + wLoP b pb w

/-- **BackPin** (decidable): the own-feedback race measured to the LUT
output, with per-pin arcs: the slowest feedback (route + feedback pin) is no
slower than the fastest return through the input pin `p` (pin arc + route +
the walk, each arc through its own pin). -/
def BackPin {N : Nat} {net : CNet N} (b : Bands net) (pb : PinBands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Prop :=
  ∀ j p, walkOK net (net.src j p) j (back j p) = true ∧
    wTok net (back j p) + net.off j p ≤ 1 ∧
    b.hiQ j + pb.hiPq j ≤ pb.loP j p + b.loG j p + wLoP b pb (back j p)

instance {N : Nat} {net : CNet N} (b : Bands net) (pb : PinBands net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net)) : Decidable (BackPin b pb back) := by
  unfold BackPin; exact inferInstance

namespace BehP
variable {N : Nat} {net : CNet N} {b : Bands net} {pb : PinBands net} (x : BehP net b pb)

theorem Fr_zero (j : Fin N) : x.Fr j 0 = 0 := by have := (x.wFr j).le_late 0; omega

theorem pos_of_nr (j : Fin N) (t : Nat) (h : ¬ x.r j (x.Fr j t) = true) : 1 ≤ t := by
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0; rw [x.Fr_zero, x.r0] at h; exact absurd rfl h
  · exact h0

theorem GFp_lt (j : Fin N) (p : Fin (net.ar j)) (t : Nat) (ht : 1 ≤ t) :
    x.G j p (x.Fp j p t) < t := by
  have := (x.wG j p).le_late (x.Fp j p t); have := (x.wFp j p).le_late t
  have := x.loG1 j p; have := x.loP1 j p; omega

theorem QFq_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.Q j (x.Fq j t) < t := by
  have := (x.wQ j).le_late (x.Fq j t); have := (x.wFq j).le_late t
  have := x.loQ1 j; have := x.loPq1 j; omega

/-- **The counts** with per-pin sampling. -/
def M (t : Nat) (j : Fin N) : Nat :=
  if x.r j (x.Fr j t) then 0 else
    fmin (net.ar j) (fun p =>
      if h : x.G j p (x.Fp j p t) < t then M (x.G j p (x.Fp j p t)) (net.src j p) + net.off j p
      else 0)
termination_by t

/-- Phase count of pin `p` of stage `j` read at pin time `u`. -/
def P (j : Fin N) (p : Fin (net.ar j)) (u : Nat) : Nat := x.M (x.G j p u) (net.src j p) + net.off j p

theorem M_reset (t : Nat) (j : Fin N) (h : x.r j (x.Fr j t) = true) : x.M t j = 0 := by
  rw [M]; simp [h]

theorem M_run (t : Nat) (j : Fin N) (h : ¬ x.r j (x.Fr j t) = true) :
    x.M t j = fmin (net.ar j) (fun p => x.P j p (x.Fp j p t)) := by
  rw [M]
  simp only [h, ite_false, Bool.false_eq_true]
  congr 1; funext p
  rw [dif_pos (x.GFp_lt j p t (x.pos_of_nr j t h))]; rfl

theorem M_mono : ∀ (n : Nat) (j : Fin N) (a : Nat), a ≤ n → x.M a j ≤ x.M n j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j a han
    by_cases hrn : x.r j (x.Fr j n) = true
    · have := x.ranti j _ _ ((x.wFr j).mono a n han) hrn
      rw [x.M_reset a j this]; exact Nat.zero_le _
    · by_cases hra : x.r j (x.Fr j a) = true
      · rw [x.M_reset a j hra]; exact Nat.zero_le _
      · rw [x.M_run a j hra, x.M_run n j hrn]
        apply fmin_mono _ _ _ (net.ar_pos j)
        intro p
        unfold P
        have hG := (x.wG j p).mono _ _ ((x.wFp j p).mono a n han)
        have hGn := x.GFp_lt j p n (x.pos_of_nr j n hrn)
        have := ih (x.G j p (x.Fp j p n)) hGn (net.src j p) _ hG
        omega

theorem M_le_pin (k : Fin N) (p : Fin (net.ar k)) (u : Nat) :
    x.M u k ≤ x.M (x.G k p (x.Fp k p u)) (net.src k p) + net.off k p := by
  by_cases hr : x.r k (x.Fr k u) = true
  · rw [x.M_reset u k hr]; exact Nat.zero_le _
  · rw [x.M_run u k hr]; exact fmin_le _ _ p

theorem walk_le : ∀ (w : List (Arc net)) (a bb : Fin N), walkOK net a bb w = true →
    ∀ u, x.M u a ≤ x.M (u - wLoP b pb w) bb + wTok net w
  | [], a, bb, h, u => by
      simp only [walkOK, beq_iff_eq] at h; subst h; simp [wLoP, wTok]
  | ⟨k, p⟩ :: w, a, bb, h, u => by
      simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hk, hw⟩ := h
      subst hk
      have h1 := x.M_le_pin k p u
      have h2 := walk_le w (net.src k p) bb hw (x.G k p (x.Fp k p u))
      have a1 := (x.wFp k p).le_late u
      have a2 := (x.wG k p).le_late (x.Fp k p u)
      have h3 := x.M_mono (u - wLoP b pb (⟨k, p⟩ :: w)) bb (x.G k p (x.Fp k p u) - wLoP b pb w)
        (by simp only [wLoP]; omega)
      simp only [wTok]
      omega

/-- **Neighbour bound** from `BackPin`: the phase of every input pin as the
LUT reads it at `t` is at most one ahead of the feedback count it reads. -/
theorem pin_le_q {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : BackPin b pb back)
    (j : Fin N) (p : Fin (net.ar j)) (t : Nat) :
    x.P j p (x.Fp j p t) ≤ x.M (x.Q j (x.Fq j t)) j + 1 := by
  obtain ⟨hw, htok, hrace⟩ := hB j p
  unfold P
  have h1 := x.walk_le (back j p) _ _ hw (x.G j p (x.Fp j p t))
  have a1 := (x.wG j p).le_late (x.Fp j p t)
  have a2 := (x.wFp j p).le_late t
  have a3 := (x.wFq j).early_le t
  have a4 := (x.wQ j).early_le (x.Fq j t)
  have := x.M_mono (x.Q j (x.Fq j t)) j (x.G j p (x.Fp j p t) - wLoP b pb (back j p)) (by omega)
  omega

/-- **Soundness of the counter domain without H_ATOMIC_LUT.** Under
`BackPin`, every node of every per-pin behaviour equals its reset value
flipped `M t j` times, at every time. -/
theorem safe {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : BackPin b pb back) :
    ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    rw [x.hc j t]
    unfold CNet.lutF
    by_cases hr : x.r j (x.Fr j t) = true
    · rw [x.M_reset t j hr]; simp [hr, ph_zero]
    · rw [x.M_run t j hr]
      simp only [hr, ite_false, Bool.false_eq_true]
      have ht1 := x.pos_of_nr j t hr
      have hpin : ∀ p, (x.pin j p (x.Fp j p t) ^^ net.neg j p) =
          ph (net.v j) (x.P j p (x.Fp j p t)) := by
        intro p
        rw [x.hpin j p _, ih _ (x.GFp_lt j p t ht1), ph_xor]
        unfold P CNet.off
        exact ph_off _ _ _
      have hq : x.q j (x.Fq j t) = ph (net.v j) (x.M (x.Q j (x.Fq j t)) j) := by
        rw [x.hq j _]; exact ih _ (x.QFq_lt j t ht1) _
      simp only [hpin, hq]
      have e1 : x.M (x.Q j (x.Fq j t)) j ≤ x.M t j := by
        apply x.M_mono
        have := (x.wQ j).le_late (x.Fq j t); have := (x.wFq j).le_late t; omega
      rw [x.M_run t j hr] at e1
      apply cel_ph _ _ (net.ar_pos j)
      · intro p; exact Nat.le_trans e1 (fmin_le _ _ p)
      · intro p; exact x.pin_le_q hB j p t

end BehP

/-! ## 3. From the strict (margin) form to the per-pin form -/

/-- **PinSkew m**: each LUT's own-feedback pin arc is at most `m` steps
slower than each of its input pin arcs, and the atomic band's lower bound is
no faster than any input pin arc. -/
structure PinSkew {N : Nat} {net : CNet N} (m : Nat) (b : Bands net) (pb : PinBands net) : Prop where
  skew : ∀ j p, pb.hiPq j ≤ pb.loP j p + m
  lo : ∀ j p, b.loF j ≤ pb.loP j p

theorem wLo_le_wLoP {N : Nat} {net : CNet N} {m : Nat} {b : Bands net} {pb : PinBands net}
    (hs : PinSkew m b pb) : ∀ w : List (Arc net), wLo b w ≤ wLoP b pb w
  | [] => Nat.le_refl _
  | ⟨k, p⟩ :: w => by
      have := wLo_le_wLoP hs w; have := hs.lo k p
      simp only [wLo, wLoP]; omega

theorem back_pin_of_margin {N : Nat} {net : CNet N} {m : Nat} {b : Bands net} {pb : PinBands net}
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)}
    (hB : BackMargin m b back) (hs : PinSkew m b pb) : BackPin b pb back := by
  intro j p
  obtain ⟨h1, h2, h3⟩ := hB j p
  refine ⟨h1, h2, ?_⟩
  have := wLo_le_wLoP hs (back j p); have := hs.skew j p
  omega

/-- **The strict form is sound without H_ATOMIC_LUT** when the feedback pin
is at most one step slower than the input pins. -/
theorem safe_strict {N : Nat} {net : CNet N} {b : Bands net} {pb : PinBands net}
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)}
    (hB : BackStrict b back) (hs : PinSkew 1 b pb) (x : BehP net b pb) :
    ∀ t j, x.c j t = ph (net.v j) (x.M t j) :=
  x.safe (back_pin_of_margin ((backStrict_iff b back).1 hB) hs)

/-- The general margin form. -/
theorem safe_margin {N : Nat} {net : CNet N} {m : Nat} {b : Bands net} {pb : PinBands net}
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)}
    (hB : BackMargin m b back) (hs : PinSkew m b pb) (x : BehP net b pb) :
    ∀ t j, x.c j t = ph (net.v j) (x.M t j) :=
  x.safe (back_pin_of_margin hB hs)

/-! ## 4. The equality case fails without H_ATOMIC_LUT

One stage (`v = false`), two input pins, each an inverting channel from the
stage itself (an eager environment closing the stage on both inputs, as
`Events2`'s E2 environment), route delays 1 and 2, feedback route 1. `Back`
holds with equality on pin 0 (`hiQ = 1 = loG 0 + 0`). Per-pin LUT arcs:
both input pins 1 step, the feedback pin 2 steps, reset pin 1 step. -/

def cxNet : CNet 1 where
  v _ := false
  ar _ := 2
  ar_pos _ := by decide
  src _ _ := 0
  inv _ _ := true
  neg _ _ := false

def cxG (p : Fin 2) : Nat := if p.val = 0 then 1 else 2

def cxBands : Bands cxNet where
  loF _ := 1
  hiF _ := 2
  loG _ p := cxG p
  hiG _ p := cxG p
  loQ _ := 1
  hiQ _ := 1

def cxBack : (j : Fin 1) → Fin (cxNet.ar j) → List (Arc cxNet) := fun _ _ => []

theorem cx_back : Back cxBands cxBack := by
  unfold Back; decide

theorem cx_not_strict : ¬ BackStrict cxBands cxBack := by
  unfold BackStrict; decide

def cxPB : PinBands cxNet := ⟨fun _ _ => 1, fun _ _ => 1, fun _ => 2, fun _ => 2, fun _ => 1, fun _ => 1⟩

theorem cx_skew : PinSkew 1 cxBands cxPB :=
  ⟨fun _ _ => by show (2 : Nat) ≤ 1 + 1; omega, fun _ _ => by show (1 : Nat) ≤ 1; omega⟩

theorem cx_not_pin : ¬ BackPin cxBands cxPB cxBack := by
  unfold BackPin; decide

theorem shift_warp (d : Nat) : Warp d d (fun t => t - d) :=
  ⟨fun a b h => by omega, fun t => by omega, fun t => by omega⟩

/-- The node: low for 2 steps, then flipping every 2 steps (period 4). -/
def cxc (t : Nat) : Bool := (t / 2) % 2 == 1

theorem cel2 (a bq : Bool) :
    cel (fun p : Fin 2 => (if p.val = 0 then !a else !bq) ^^ false) bq = !a := by
  cases a <;> cases bq <;> decide

theorem cxc_step (t : Nat) (ht : 2 ≤ t) : cxc t = !cxc (t - 2) := by
  unfold cxc
  have : t / 2 = (t - 2) / 2 + 1 := by omega
  rw [this]
  rcases Nat.mod_two_eq_zero_or_one ((t - 2) / 2) with h | h
  · have : ((t - 2) / 2 + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : ((t - 2) / 2 + 1) % 2 = 0 := by omega
    simp [h, this]

def cxBeh : BehP cxNet cxBands cxPB where
  c _ := cxc
  pin _ p u := true ^^ cxc (u - cxG p)
  q _ u := cxc (u - 1)
  r _ u := decide (u < 1)
  Fp _ _ t := t - 1
  Fq _ t := t - 2
  Fr _ t := t - 1
  G _ p u := u - cxG p
  Q _ u := u - 1
  wFp _ _ := shift_warp 1
  wFq _ := shift_warp 2
  wFr _ := shift_warp 1
  wG _ p := shift_warp (cxG p)
  wQ _ := shift_warp 1
  loP1 _ _ := by show (1 : Nat) ≤ 1; omega
  loPq1 _ := by show (1 : Nat) ≤ 2; omega
  loG1 _ p := by show 1 ≤ cxG p; unfold cxG; split <;> omega
  loQ1 _ := by show (1 : Nat) ≤ 1; omega
  hc j t := by
    show cxc t = (if decide (t - 1 < 1) then false else
      cel (fun p : Fin 2 => (true ^^ cxc (t - 1 - cxG p)) ^^ false) (cxc (t - 2 - 1)))
    by_cases ht : t - 1 < 1
    · have : t / 2 = 0 := by omega
      simp [ht, cxc, this]
    · simp only [ht, decide_false, Bool.false_eq_true, ite_false]
      have e : (fun p : Fin 2 => (true ^^ cxc (t - 1 - cxG p)) ^^ false) =
          (fun p : Fin 2 => (if p.val = 0 then !cxc (t - 2) else !cxc (t - 2 - 1)) ^^ false) := by
        funext p; unfold cxG
        by_cases hp : p.val = 0
        · simp [hp, show t - 1 - 1 = t - 2 by omega]
        · simp [hp, show t - 1 - 2 = t - 2 - 1 by omega]
      rw [e, cel2, cxc_step t (by omega)]
  hpin _ _ _ := rfl
  hq _ _ := rfl
  r0 _ := rfl
  ranti _ a b h hb := by simp at hb ⊢; omega

/-- **The equality case of `Back` is unsound for a LUT whose feedback pin
lags an input pin by one step.** `Back` holds (with equality), `PinSkew 1`
holds, and the node of this per-pin behaviour is not the counter model at
step 4: the C-element fired as soon as pin 0 saw the stage's previous edge,
without waiting for pin 1 (a C-element firing on one input), because its
stale feedback pin made "hold" equal to "fire". -/
theorem cx_unsafe : ¬ ∀ t j, cxBeh.c j t = ph (cxNet.v j) (cxBeh.M t j) := by
  intro h
  have m1 : cxBeh.M 1 0 = 0 := cxBeh.M_reset 1 0 (by decide)
  have m4 := cxBeh.M_run 4 0 (by decide)
  have hP0 : cxBeh.P 0 ⟨0, by decide⟩ (cxBeh.Fp 0 ⟨0, by decide⟩ 4) = cxBeh.M 2 0 + 1 := rfl
  have hP1 : cxBeh.P 0 ⟨1, by decide⟩ (cxBeh.Fp 0 ⟨1, by decide⟩ 4) = cxBeh.M 1 0 + 1 := rfl
  have hf : fmin (cxNet.ar 0) (fun p => cxBeh.P 0 p (cxBeh.Fp 0 p 4)) =
      min (cxBeh.P 0 ⟨0, by decide⟩ (cxBeh.Fp 0 ⟨0, by decide⟩ 4))
        (cxBeh.P 0 ⟨1, by decide⟩ (cxBeh.Fp 0 ⟨1, by decide⟩ 4)) := rfl
  rw [hf, hP0, hP1, m1] at m4
  have hM : cxBeh.M 4 0 = 1 := by rw [m4]; omega
  have := h 4 0
  rw [hM] at this
  revert this; decide

end Formal.Core.XAudit.Events2Strict
