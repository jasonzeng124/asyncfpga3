import Formal.Net.PerLink
import Formal.Net.PerLinkPin

/-!
# Probe C-8h: end to end with per-link margins, rise/fall pins, per-event delays

`end_to_end2`: if the verified checker accepts the routed netlist
(`checkPipe2 R n W = true`), every run of the `n`-stage `bd_pipe` whose pins
are related to their sources by the pin relations below, with bounds realized
inside the routed intervals, obeys the protocol on every link and is a FIFO.

Differences with 8e's `end_to_end`:

1. **Per-link margins** (`muller_pipeline2`): no global `(m, h)`. The margins
   of link `j` are taken from the run itself (`mOf`, `hOf`: the smallest
   request / acknowledge delays of that link), so `checkPipe2` has NO free
   parameter and each bundling race compares the two real paths of one link:
   the data wire into stage `j` against the request path into stage `j`.
2. **Rise/fall asymmetric pins.** Every control path has two interval lists,
   one per edge direction (`Route2.reqR/reqF`, `ackR/ackF`, `enR/enF`). The
   races use the edge that matters: request FALL for Sep and setup at internal
   links, request RISE at the source, acknowledge FALL for hold, RISE for the
   open width, enable FALL for the latch hold, RISE for the open width. A
   `bd_delay FASTRISE` (DACK ≥ 2) or `FASTFALL` line is now a legal path.
3. **Per-event delays.** Control pins are `EPin` (ordered per-event transport,
   the k-th pin change within `[lo k, hi k]` of the k-th source change); data
   pins are `DPin` (arbitrary glitches allowed while the source moves). An
   exact shift is both (`shift_epin`, `shift_dpin`), so 8e's fixed-delay runs
   are a special case (`EndToEnd2Fixed` below). `PerLinkEvent` shows when a
   per-event channel IS an `EPin` (a pulse-width condition) and that Prelim's
   `BoundedDelay` alone is not (echoes).

Assumed path convention (H_NONINV_PATH): every arc of a control path is
non-inverting (wires, pips, `bd_delay` LUT1/LUT2 buffers, a LUT input-pin
arc), so the edge direction at every arc is the source node's. The inversion
of `ack_out` in `C(req, ~ack)` is in the node function, after the pin.
-/

namespace Formal.Net.PerLink
open Formal.Net Formal.Net.Handshake Formal.Net.EndToEnd Formal.Timing

/-- Per-run delay bounds of one control path, by edge: rise in `[rl, rh]`,
fall in `[fl, fh]`. -/
structure EB where
  rl : Nat
  rh : Nat
  fl : Nat
  fh : Nat

def EB.lo (b : EB) : Nat → Nat := ed b.rl b.fl
def EB.hi (b : EB) : Nat → Nat := ed b.rh b.fh

/-- One run of an `n`-stage `bd_pipe`, with every pin an explicit trace.
`x 0` = source request, `x (j+1)` = node of stage `j`, `x (n+1)` = sink ack.
`pR k` = req pin of `x k` (copy of `x (k-1)`), `pA k` = ack pin of `x k`
(copy of `x (k+1)`), `pG j b` / `pD j b` = EN / D pins of stage `j`'s latch
LUT for bit `b`. -/
structure Pipe2 where
  x : Nat → Trace
  Q : Nat → Nat → Trace
  pR : Nat → Trace
  pA : Nat → Trace
  pG : Nat → Nat → Trace
  pD : Nat → Nat → Trace
  bR : Nat → EB
  bA : Nat → EB
  bG : Nat → Nat → EB
  /-- data pin band `(lo, hi)`: one shared band for both edges (the latch only
  needs stability, and a data bit moves in either direction). -/
  bD : Nat → Nat → Nat × Nat

structure PipeRun2 (n W : Nat) (P : Pipe2) : Prop where
  H_RESET : ∀ k, k ≤ n + 1 → P.x k 0 = false
  /-- pin-level SI C-element, real `bd_c2n` INIT on its pins. -/
  H_CEL : ∀ k, 1 ≤ k → k ≤ n → ∀ t, P.x k (t + 1) = P.x k t ∨
    P.x k (t + 1) = celN (P.pR k t) (P.pA k t) (P.x k t)
  H_SRC : ∀ t, P.x 0 (t + 1) ≠ P.x 0 t → P.x 0 t = P.pA 0 t
  H_SNK : ∀ t, P.x (n + 1) (t + 1) ≠ P.x (n + 1) t → P.x (n + 1) t ≠ P.pR (n + 1) t
  H_SRC_DATA : ∀ b, b < W → ∀ t, P.Q 0 b (t + 1) ≠ P.Q 0 b t → P.x 0 t = false ∧ P.x 0 (t + 1) = true
  /-- latch LUT (`bd_latch` INIT) on its pins, one tick. -/
  H_LATCH_CELL : ∀ j, j < n → ∀ b, b < W → ∀ t, P.Q (j + 1) b (t + 1) =
    latchF (P.pD j b t) (P.pG j b t) (P.Q (j + 1) b t)
  /-- H_PIN for every control pin (ordered, per-edge, per-event). -/
  H_PIN_R : ∀ k, 1 ≤ k → k ≤ n + 1 → EPin (P.bR k).lo (P.bR k).hi (P.x (k - 1)) (P.pR k)
  H_PIN_A : ∀ k, k ≤ n → EPin (P.bA k).lo (P.bA k).hi (P.x (k + 1)) (P.pA k)
  H_PIN_G : ∀ j, j < n → ∀ b, b < W → EPin (P.bG j b).lo (P.bG j b).hi (P.x (j + 1)) (P.pG j b)
  /-- H_DPIN for every data pin (glitches allowed). -/
  H_PIN_D : ∀ j, j < n → ∀ b, b < W → DPin (P.bD j b).1 (P.bD j b).2 (P.Q j b) (P.pD j b)
  H_DBAND : ∀ j, j < n → ∀ b, b < W → (P.bD j b).1 ≤ (P.bD j b).2

/-- Routed netlist, two interval lists per control path (rise, fall). -/
structure Route2 where
  reqR : Nat → Path
  reqF : Nat → Path
  ackR : Nat → Path
  ackF : Nat → Path
  enR : Nat → Nat → Path
  enF : Nat → Nat → Path
  dat : Nat → Nat → Path

/-- H_ROUTE: each bound the theorem uses is a sum of per-arc values inside
the routed intervals (for a fixed-delay run lo = hi = the run's delay; for a
per-event run the per-arc bounds compose by `epin_comp`). -/
def Realizes2 (R : Route2) (n W : Nat) (P : Pipe2) : Prop :=
  (∀ k, 1 ≤ k → k ≤ n + 1 →
    (∃ ds, inPath ds (R.reqR k) ∧ ds.sum = (P.bR k).rl) ∧ (∃ ds, inPath ds (R.reqF k) ∧ ds.sum = (P.bR k).fl)) ∧
  (∀ k, k ≤ n →
    (∃ ds, inPath ds (R.ackR k) ∧ ds.sum = (P.bA k).rl) ∧ (∃ ds, inPath ds (R.ackF k) ∧ ds.sum = (P.bA k).fl)) ∧
  (∀ j, j < n → ∀ b, b < W →
    (∃ ds, inPath ds (R.enR j b) ∧ ds.sum = (P.bG j b).rh) ∧ (∃ ds, inPath ds (R.enF j b) ∧ ds.sum = (P.bG j b).fh)) ∧
  (∀ j, j < n → ∀ b, b < W →
    (∃ ds, inPath ds (R.dat j b) ∧ ds.sum = (P.bD j b).1) ∧ (∃ ds, inPath ds (R.dat j b) ∧ ds.sum = (P.bD j b).2))

/-- **The per-link check.** Three races per stage and bit, no free margin:
* setup: data wire of link `j` vs request path into stage `j` (rise + 1 at
  the source, fall for internal links): `race2 (reqR 1 ++ [(1,1)]) (dat 0 b) 0`,
  `race2 (reqF (j+1)) (dat j b) 0`;
* hold: enable FALL of stage `j` bit `b` vs data wire + acknowledge FALL of
  link `j` + 1: `race2 (dat j b ++ ackF j ++ [(1,1)]) (enF j b) 0`;
* open width: enable RISE vs the next stage's round trip (request rise +
  acknowledge rise + 1): `race2 (reqR (j+2) ++ ackR (j+1) ++ [(1,1)]) (enR j b) 0`. -/
def checkPipe2 (R : Route2) (n W : Nat) : Bool :=
  (List.range n).all (fun j => (List.range W).all (fun b =>
    (if j = 0 then race2 (R.reqR 1 ++ [(1, 1)]) (R.dat 0 b) 0
     else race2 (R.reqF (j + 1)) (R.dat j b) 0) &&
    race2 (R.dat j b ++ R.ackF j ++ [(1, 1)]) (R.enF j b) 0 &&
    race2 (R.reqR (j + 2) ++ R.ackR (j + 1) ++ [(1, 1)]) (R.enR j b) 0))

/-- The obligations in bound form. -/
structure Timing2 (n W : Nat) (P : Pipe2) : Prop where
  setup0 : 0 < n → ∀ b, b < W → (P.bD 0 b).2 ≤ (P.bR 1).rl + 1
  setup : ∀ j, 1 ≤ j → j < n → ∀ b, b < W → (P.bD j b).2 ≤ (P.bR (j + 1)).fl
  hold : ∀ j, j < n → ∀ b, b < W → (P.bG j b).fh ≤ (P.bD j b).1 + (P.bA j).fl + 1
  opn : ∀ j, j < n → ∀ b, b < W → (P.bG j b).rh ≤ (P.bR (j + 2)).rl + (P.bA (j + 1)).rl + 1

theorem timing2_of_check {R : Route2} {n W : Nat} (hc : checkPipe2 R n W = true)
    {P : Pipe2} (HR : Realizes2 R n W P) : Timing2 n W P := by
  simp only [checkPipe2, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  obtain ⟨Hreq, Hack, Hen, Hdat⟩ := HR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hn b hb
    have h := (hc 0 hn b hb).1.1
    simp only [ite_true] at h
    obtain ⟨⟨r, r1, r2⟩, _⟩ := Hreq 1 (by omega) (by omega)
    obtain ⟨_, ⟨d, d1, d2⟩⟩ := Hdat 0 hn b hb
    have := race2_sound h (inPath_append r1 (inPath_const 1)) d1
    simp at this; omega
  · intro j hj1 hj b hb
    have h := (hc j hj b hb).1.1
    rw [if_neg (show ¬ j = 0 by omega)] at h
    obtain ⟨_, ⟨r, r1, r2⟩⟩ := Hreq (j + 1) (by omega) (by omega)
    obtain ⟨_, ⟨d, d1, d2⟩⟩ := Hdat j hj b hb
    have := race2_sound h r1 d1
    omega
  · intro j hj b hb
    have h := (hc j hj b hb).1.2
    obtain ⟨⟨d, d1, d2⟩, _⟩ := Hdat j hj b hb
    obtain ⟨_, ⟨a, a1, a2⟩⟩ := Hack j (by omega)
    obtain ⟨_, ⟨g, g1, g2⟩⟩ := Hen j hj b hb
    have := race2_sound h (inPath_append (inPath_append d1 a1) (inPath_const 1)) g1
    simp at this; omega
  · intro j hj b hb
    have h := (hc j hj b hb).2
    obtain ⟨⟨r, r1, r2⟩, _⟩ := Hreq (j + 2) (by omega) (by omega)
    obtain ⟨⟨a, a1, a2⟩, _⟩ := Hack (j + 1) (by omega)
    obtain ⟨⟨g, g1, g2⟩, _⟩ := Hen j hj b hb
    have := race2_sound h (inPath_append (inPath_append r1 a1) (inPath_const 1)) g1
    simp at this; omega

/-! ## From the run to 8a's per-link model -/

/-- 8a's channels at the nodes (as in 8e). -/
def ch2 (W : Nat) (P : Pipe2) (j : Nat) : Chan :=
  ⟨P.x j, P.x (j + 1), fun t => enc W (fun b => P.Q j b t)⟩

/-- Per-link margins, read off the run's bounds. -/
def mOf (P : Pipe2) (j : Nat) : Nat := if j = 0 then (P.bR 1).rl + 2 else (P.bR (j + 1)).fl + 1
def hOf (P : Pipe2) (j : Nat) : Nat := (P.bA j).fl + 1

theorem links2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P) :
    ∀ k, k ≤ n → ELink (P.x k) (P.x (k + 1)) (P.pR (k + 1)) (P.pA k)
      (P.bR (k + 1)).lo (P.bR (k + 1)).hi (P.bA k).lo (P.bA k).hi := by
  intro k hk
  refine ⟨H.H_RESET k (by omega), H.H_RESET (k + 1) (by omega), ?_, ?_, ?_, H.H_PIN_A k hk⟩
  · intro t hmv
    by_cases hk0 : k = 0
    · subst hk0; exact H.H_SRC t hmv
    · rcases H.H_CEL k (by omega) hk t with h | h
      · exact absurd h hmv
      · exact (cel_change _ _ _ _ (Or.inr h) hmv).2
  · intro t hmv
    by_cases hkn : k = n
    · subst hkn; exact H.H_SNK t hmv
    · rcases H.H_CEL (k + 1) (by omega) (by omega) t with h | h
      · exact absurd h hmv
      · exact (cel_change _ _ _ _ (Or.inr h) hmv).1
  · have := H.H_PIN_R (k + 1) (by omega) (by omega)
    rwa [show k + 1 - 1 = k by omega] at this

theorem protocols2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P) :
    ∀ k, k ≤ n → Protocol (ch2 W P k) := fun k hk => (links2 H k hk).protocol _

theorem cel_si2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P) {j : Nat} (hj : j < n) :
    ∀ t, P.x (j + 1) (t + 1) = P.x (j + 1) t ∨
      P.x (j + 1) (t + 1) = celN (P.x j t) (P.x (j + 2) t) (P.x (j + 1) t) := by
  intro t
  by_cases hmv : P.x (j + 1) (t + 1) = P.x (j + 1) t
  · exact Or.inl hmv
  · right
    have r := ((protocols2 H j (by omega)).2 t).2 hmv
    have s := ((protocols2 H (j + 1) (by omega)).2 t).1 hmv
    simp only [ch2] at r s
    rw [celN_excited _ _ _ r s]
    exact flip hmv

theorem odd_of_true {s : Trace} (h0 : s 0 = false) {t : Nat} (h : s t = true) : N s t % 2 = 1 := by
  have := parity h0 t; rw [h] at this; simpa using this.symm

theorem even_of_false {s : Trace} (h0 : s 0 = false) {t : Nat} (h : s t = false) : N s t % 2 = 0 := by
  have := parity h0 t; rw [h] at this
  have : ¬ N s t % 2 = 1 := by simpa using this.symm
  omega

/-- 8a's `H_LATCH` for stage `j`, with the margins of link `j`. -/
theorem latch_contract2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P) (T : Timing2 n W P)
    {j : Nat} (hj : j < n) :
    ∀ e, fallB (ch2 W P j).ack e = true →
      (∀ s, e + 1 - mOf P j ≤ s → s ≤ e + hOf P j → (ch2 W P j).dat s = (ch2 W P j).dat e) →
      ∀ s, e < s → (∀ u, e < u → u ≤ s → (ch2 W P j).ack u = false) →
        (ch2 W P (j + 1)).dat s = (ch2 W P j).dat e := by
  intro e hf hsh s hs hlow
  simp only [ch2] at hf hsh hlow ⊢
  simp [fallB] at hf
  obtain ⟨hf1, hf2⟩ := hf
  have hx0 := H.H_RESET (j + 1) (by omega)
  obtain ⟨r, hre, hr0, hr1, hopen⟩ := last_rise (P.x (j + 1)) hx0 e hf1
  have L := links2 H (j + 1) (by omega)
  have hw := L.openWidth hr0 hr1 hf2 hopen hre
  have hev := even_of_false hx0 hr0
  have hodd := odd_of_true hx0 hf1
  have hNe : N (P.x (j + 1)) e = N (P.x (j + 1)) r + 1 := by
    have := N_move (show P.x (j + 1) (r + 1) ≠ P.x (j + 1) r by rw [hr0, hr1]; decide)
    have c := N_const (s := P.x (j + 1)) (a := r + 1) (e - (r + 1)) (fun u hu1 hu2 => by
      rw [hopen u (by omega) (by omega), hopen (u + 1) (by omega) (by omega)])
    rw [show r + 1 + (e - (r + 1)) = e by omega] at c
    omega
  simp only [EB.lo, ed_even hev, show j + 1 + 1 = j + 2 by omega] at hw
  apply enc_congr
  intro b hb
  have hDb : ∀ s', e + 1 - mOf P j ≤ s' → s' ≤ e + hOf P j → P.Q j b s' = P.Q j b e :=
    fun s' h1 h2 => enc_inj W _ _ (hsh s' h1 h2) b hb
  have G := H.H_PIN_G j hj b hb
  have hcell := H.H_LATCH_CELL j hj b hb
  have hm : (P.bD j b).2 + 1 ≤ mOf P j := by
    by_cases hj0 : j = 0
    · subst hj0; have := T.setup0 (by omega) b hb; simp [mOf]; omega
    · have := T.setup j (by omega) hj b hb; simp [mOf, hj0]; omega
  exact latch_bit2 hcell G (H.H_PIN_D j hj b hb) hx0 hr0 hr1 hopen hre hf2
    (by simp only [EB.hi]; rw [hNe, show N (P.x (j + 1)) r + 1 - 1 = N (P.x (j + 1)) r by omega,
          ed_even hev]; have := T.opn j hj b hb; omega)
    (H.H_DBAND j hj b hb) hm
    (by simp only [EB.hi]; rw [ed_odd hodd]; have := T.hold j hj b hb; simp [hOf]; omega)
    hDb s hs hlow

theorem src_setupHold2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P) :
    SetupHold (mOf P 0) (hOf P 0) (ch2 W P 0) := by
  intro e hf s h1 h2
  simp only [ch2] at hf ⊢
  simp [fallB] at hf
  have L : ELink (P.x 0) (P.x 1) (P.pR 1) (P.pA 0)
      (P.bR 1).lo (P.bR 1).hi (P.bA 0).lo (P.bA 0).hi := links2 H 0 (by omega)
  have hodd := odd_of_true (H.H_RESET 1 (by omega)) hf.1
  have hm : mOf P 0 ≤ (P.bR 1).lo (N (P.x 1) e - 1) + 2 := by
    simp only [EB.lo, mOf, ite_true]; rw [ed_even (by omega)]; exact Nat.le_refl _
  have hh : hOf P 0 ≤ (P.bA 0).lo (N (P.x 1) e) + 1 := by
    simp only [EB.lo, hOf]; rw [ed_odd hodd]; exact Nat.le_refl _
  apply enc_congr
  intro b hb
  exact L.srcData (H.H_SRC_DATA b hb) hf.1 hf.2 (by simp [mOf]) hm hh s h1 h2

theorem sep_ok2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P)
    {j : Nat} (hj : j + 1 < n) : Sep (mOf P (j + 1)) (ch2 W P j) (ch2 W P (j + 1)) := by
  intro e e' hf hf' hlt hl
  simp only [ch2] at hf hf' hl
  simp [fallB] at hf hf'
  have L := links2 H (j + 1) (by omega)
  have hodd := odd_of_true (H.H_RESET (j + 1) (by omega)) hf.1
  have := L.sep hf.1 hf.2 hl (by rw [hf'.1, hf'.2]; decide) hlt
  simp only [EB.lo, ed_odd hodd] at this
  simp only [mOf, show j + 1 ≠ 0 by omega, ite_false, show j + 1 + 1 = j + 2 by omega]
  omega

theorem hold_ok2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P)
    {j : Nat} (hj : j + 1 < n) : Hold (hOf P (j + 1)) (ch2 W P j) (ch2 W P (j + 1)) := by
  intro e' s hf' h1 h2
  simp only [ch2] at hf' ⊢
  simp [fallB] at hf'
  have L := links2 H (j + 1) (by omega)
  have hodd := odd_of_true (H.H_RESET (j + 2) (by omega)) hf'.1
  exact L.hold hf'.1 hf'.2 s h1 (by simp only [EB.lo, hOf] at h2 ⊢; rw [ed_odd hodd]; omega)

theorem stage2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P) (T : Timing2 n W P)
    {j : Nat} (hj : j < n) : MullerStage (mOf P j) (hOf P j) (ch2 W P j) (ch2 W P (j + 1)) where
  H_NODE := fun _ => rfl
  H_RESET := H.H_RESET (j + 1) (by omega)
  H_CEL_SI := cel_si2 H hj
  H_LATCH := latch_contract2 H T hj

theorem fifo_of_timing2 {n W : Nat} {P : Pipe2} (H : PipeRun2 n W P) (T : Timing2 n W P)
    (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch2 W P j)) ∧
    (∀ t, cnt (fallB (ch2 W P n).ack) t ≤ cnt (fallB (ch2 W P 0).ack) t) ∧
    (∀ k e', TokAt (ch2 W P n) k e' →
      ∃ e, e < e' ∧ TokAt (ch2 W P 0) k e ∧ (ch2 W P n).dat e' = (ch2 W P 0).dat e) :=
  muller_pipeline2 (m := mOf P) (h := hOf P) (fun j hj => stage2 H T hj)
    (H.H_RESET 0 (by omega)) (H.H_RESET (n + 1) (Nat.le_refl _))
    (fun t _ => ((protocols2 H 0 (by omega)).2 t).1)
    (fun t _ => ((protocols2 H n (Nat.le_refl _)).2 t).2)
    (src_setupHold2 H) (fun j hj => sep_ok2 H hj) (fun j hj => hold_ok2 H hj) hn

/-- **End to end, per link.** If the verified checker accepts the routed
netlist (`checkPipe2 R n W = true`: three two-path races per stage and bit,
no free margin), then every run of the pipeline whose control pins are
ordered per-event, per-edge delayed copies (`EPin`) and whose data pins are
glitch-tolerant delayed copies (`DPin`) of their sources, with bounds inside
the routed intervals, obeys the four-phase protocol on every link and is a
FIFO. -/
theorem end_to_end2 {R : Route2} {n W : Nat} (hc : checkPipe2 R n W = true)
    {P : Pipe2} (H : PipeRun2 n W P) (HR : Realizes2 R n W P) (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch2 W P j)) ∧
    (∀ t, cnt (fallB (ch2 W P n).ack) t ≤ cnt (fallB (ch2 W P 0).ack) t) ∧
    (∀ k e', TokAt (ch2 W P n) k e' →
      ∃ e, e < e' ∧ TokAt (ch2 W P 0) k e ∧ (ch2 W P n).dat e' = (ch2 W P 0).dat e) :=
  fifo_of_timing2 H (timing2_of_check hc HR) hn

/-! ## 8e's fixed-delay runs are a special case -/

/-- A symmetric 8e route read as a `Route2` (same intervals for both edges). -/
def symR (R : Route) : Route2 :=
  ⟨R.req, R.req, R.ack, R.ack, R.en, R.en, R.dat⟩

/-- 8e's run, with its exact-shift pins made explicit. -/
def toP2 (P : Pipe) : Pipe2 where
  x := P.x
  Q := P.Q
  pR := fun k => shift (P.dR k) (P.x (k - 1))
  pA := fun k => shift (P.dA k) (P.x (k + 1))
  pG := fun j b => shift (P.dG j b) (P.x (j + 1))
  pD := fun j b => shift (P.dD j b) (P.Q j b)
  bR := fun k => ⟨P.dR k, P.dR k, P.dR k, P.dR k⟩
  bA := fun k => ⟨P.dA k, P.dA k, P.dA k, P.dA k⟩
  bG := fun j b => ⟨P.dG j b, P.dG j b, P.dG j b, P.dG j b⟩
  bD := fun j b => (P.dD j b, P.dD j b)

theorem ed_same (d k : Nat) : ed d d k = d := by unfold ed; split <;> rfl
theorem ed_same_fun (d : Nat) : ed d d = fun _ => d := funext (ed_same d)

theorem pipeRun2_of {n W : Nat} {P : Pipe} (H : PipeRun n W P) : PipeRun2 n W (toP2 P) where
  H_RESET := H.H_RESET
  H_CEL := H.H_CEL
  H_SRC := H.H_SRC
  H_SNK := H.H_SNK
  H_SRC_DATA := H.H_SRC_DATA
  H_LATCH_CELL := H.H_LATCH_CELL
  H_PIN_R := fun k h1 h2 => by
    have := shift_epin (d := P.dR k) (H.H_RESET (k - 1) (by omega))
    simp only [toP2, EB.lo, EB.hi]; rw [ed_same_fun]; exact this
  H_PIN_A := fun k hk => by
    have := shift_epin (d := P.dA k) (H.H_RESET (k + 1) (by omega))
    simp only [toP2, EB.lo, EB.hi]; rw [ed_same_fun]; exact this
  H_PIN_G := fun j hj b _ => by
    have := shift_epin (d := P.dG j b) (H.H_RESET (j + 1) (by omega))
    simp only [toP2, EB.lo, EB.hi]; rw [ed_same_fun]; exact this
  H_PIN_D := fun j _ b _ => shift_dpin _ _
  H_DBAND := fun _ _ _ _ => Nat.le_refl _

theorem realizes2_of {R : Route} {n W : Nat} {P : Pipe} (HR : Realizes R n W P) :
    Realizes2 (symR R) n W (toP2 P) := by
  obtain ⟨a, b, c, d⟩ := HR
  exact ⟨fun k h1 h2 => ⟨a k h1 h2, a k h1 h2⟩, fun k h => ⟨b k h, b k h⟩,
    fun j h1 b' h2 => ⟨c j h1 b' h2, c j h1 b' h2⟩, fun j h1 b' h2 => ⟨d j h1 b' h2, d j h1 b' h2⟩⟩

/-- **8e's setting with the per-link check**: fixed-delay runs of a symmetric
route. Same conclusion as `end_to_end`, with `checkPipe2` (no margins). -/
theorem end_to_end_fixed {R : Route} {n W : Nat} (hc : checkPipe2 (symR R) n W = true)
    {P : Pipe} (H : PipeRun n W P) (HR : Realizes R n W P) (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch W P j)) ∧
    (∀ t, cnt (fallB (ch W P n).ack) t ≤ cnt (fallB (ch W P 0).ack) t) ∧
    (∀ k e', TokAt (ch W P n) k e' →
      ∃ e, e < e' ∧ TokAt (ch W P 0) k e ∧ (ch W P n).dat e' = (ch W P 0).dat e) :=
  end_to_end2 hc (pipeRun2_of H) (realizes2_of HR) hn

end Formal.Net.PerLink
