import Formal.Net.EndToEnd

/-!
# Probe C-8h, part 2: pins as edge-indexed delayed copies

8e's `PinLink` has every pin an exact shift of its source (H_FIXED_DELAY).
Here a control pin is any trace related to its source by

    `EPin lo hi s π`: the k-th change of `π` comes at least `lo k` and at
    most `hi k` ticks after the k-th change of `s` (count form, below).

`lo`, `hi` are indexed by the change number `k`. For a trace that starts low,
even `k` are rises and odd `k` are falls, so `ed r f k` (rise bound `r`,
fall bound `f`) gives **rise/fall-asymmetric** pins, and the bounds may
differ from event to event inside them: `EPin` is the **ordered per-event
transport channel**. Instances:

* `shift_epin`: an exact shift by `d` (8e's pins) is `EPin d d`;
* `epin_comp`: pins compose along a path (bounds add);
* `PerLinkEvent.event_epin`: a per-event delay `D σ ∈ [lo, hi]` on each input
  change, under a pulse-width condition, is an `EPin`;
* `PerLinkEvent.or2_epin`: a FASTRISE delay line (OR of a fast and a slow
  shift) is `EPin` with rise delay `d1` and fall delay `d2`, under a
  low-pulse-width condition.

`ELink` generalises `PinLink` to such pins. Every lemma 8e needed survives:
the change-count invariant (`ELink.inv`), the protocol, `sep`, `hold`,
`openWidth`, `srcData`, with the delay of each event replaced by the `lo`
bound OF THAT EDGE.

Data pins are weaker still (`DPin lo hi D π`): the pin equals the source
`lo` ticks ago whenever the source was stable over `[t-hi, t-lo]`. That
allows arbitrary glitches while the source moves (BoundedDelay-like, per
event), and it is all the latch needs (`latch_bit2`).
-/

namespace Formal.Net.PerLink
open Formal.Net Formal.Net.Handshake Formal.Net.EndToEnd Formal.Timing

/-- Edge-indexed bound: change `k` of a trace that starts low is a rise for
even `k`, a fall for odd `k`. -/
def ed (r f : Nat) (k : Nat) : Nat := if k % 2 = 0 then r else f

theorem ed_even {r f k : Nat} (h : k % 2 = 0) : ed r f k = r := by simp [ed, h]
theorem ed_odd {r f k : Nat} (h : k % 2 = 1) : ed r f k = f := by simp [ed, h]

/-- **H_PIN (control pin).** `π` is an ordered, edge-indexed delayed copy of
`s`: change `k` of `π` is at least `lo k` and at most `hi k` after change `k`
of `s`. Count form: `π` has done `k+1` changes by `t` only if `s` had by
`t - lo k`, and `s` having done `k+1` by `t - hi k` forces `π` to have by `t`. -/
structure EPin (lo hi : Nat → Nat) (s π : Trace) : Prop where
  z : π 0 = false
  early : ∀ k t, k < N π t → k < N s (t - lo k)
  late : ∀ k t, k < N s (t - hi k) → k < N π t

theorem EPin.le {lo hi : Nat → Nat} {s π : Trace} (P : EPin lo hi s π) (t : Nat) :
    N π t ≤ N s t := by
  cases h : N π t with
  | zero => exact Nat.zero_le _
  | succ k =>
    have := P.early k t (by omega)
    have : N s (t - lo k) ≤ N s t := N_mono (by omega)
    omega

/-- Exact shift: `N (shift d s) t = N s (t - d)`. -/
theorem N_shift (d : Nat) (s : Trace) : ∀ t, N (shift d s) t = N s (t - d) := by
  intro t
  induction t with
  | zero => rw [Nat.zero_sub]; rfl
  | succ t ih =>
    by_cases ht : t < d
    · have e1 : shift d s (t + 1) = shift d s t := by
        rw [shift_eq, shift_eq, show t + 1 - d = 0 by omega, show t - d = 0 by omega]
      rw [N_stay e1, ih, show t + 1 - d = 0 by omega, show t - d = 0 by omega]
    · have e : t + 1 - d = (t - d) + 1 := by omega
      by_cases hc : s (t - d + 1) = s (t - d)
      · have e1 : shift d s (t + 1) = shift d s t := by rw [shift_eq, shift_eq, e, hc]
        rw [N_stay e1, ih, e, N_stay hc]
      · have e1 : shift d s (t + 1) ≠ shift d s t := by rw [shift_eq, shift_eq, e]; exact hc
        rw [N_move e1, ih, e, N_move hc]

/-- 8e's pins are `EPin`s with `lo = hi = d`. -/
theorem shift_epin {d : Nat} {s : Trace} (h0 : s 0 = false) :
    EPin (fun _ => d) (fun _ => d) s (shift d s) where
  z := by rw [shift_eq, Nat.zero_sub]; exact h0
  early := fun k t h => by rw [N_shift] at h; exact h
  late := fun k t h => by rw [N_shift]; exact h

/-- Pins compose along a path: the bounds add, edge by edge. -/
theorem epin_comp {l1 h1 l2 h2 : Nat → Nat} {s π1 π2 : Trace}
    (P1 : EPin l1 h1 s π1) (P2 : EPin l2 h2 π1 π2) :
    EPin (fun k => l1 k + l2 k) (fun k => h1 k + h2 k) s π2 where
  z := P2.z
  early := fun k t h => by
    have := P1.early k _ (P2.early k t h)
    rwa [Nat.sub_sub, Nat.add_comm (l2 k)] at this
  late := fun k t h => by
    apply P2.late k t
    apply P1.late k
    rwa [Nat.sub_sub, Nat.add_comm (h2 k)]

/-! ## A link whose two ends read each other through `EPin`s -/

/-- Sender node `p`, receiver node `q`; the receiver's pin `πR` is an `EPin`
of `p`, the sender's pin `πA` an `EPin` of `q`. Each party moves only when
its pin view allows (sender: equal; receiver: different). -/
structure ELink (p q πR πA : Trace) (loR hiR loA hiA : Nat → Nat) : Prop where
  p0 : p 0 = false
  q0 : q 0 = false
  send : ∀ t, p (t + 1) ≠ p t → p t = πA t
  recv : ∀ t, q (t + 1) ≠ q t → q t ≠ πR t
  R : EPin loR hiR p πR
  A : EPin loA hiA q πA

theorem N_after_fall {s : Trace} {e e' : Nat} (h1 : s e = true) (h2 : s (e + 1) = false)
    (hl : ∀ u, e < u → u ≤ e' → s u = false) (hle : e < e') : N s e' = N s e + 1 := by
  have hm : s (e + 1) ≠ s e := by rw [h1, h2]; decide
  have c := N_const (s := s) (a := e + 1) (e' - (e + 1)) (fun u hu1 hu2 => by
    rw [hl u (by omega) (by omega), hl (u + 1) (by omega) (by omega)])
  rw [show e + 1 + (e' - (e + 1)) = e' by omega, N_move hm] at c
  exact c

namespace ELink
variable {p q πR πA : Trace} {loR hiR loA hiA : Nat → Nat}

/-- **Count invariant**, per-event form: the receiver has never done more
changes than its pin has shown, the sender at most one more than its pin. -/
theorem inv (L : ELink p q πR πA loR hiR loA hiA) :
    ∀ t, N q t ≤ N πR t ∧ N p t ≤ N πA t + 1 := by
  intro t
  induction t with
  | zero => simp [N_zero]
  | succ t ih =>
    have mR : N πR t ≤ N πR (t + 1) := N_mono (by omega)
    have mA : N πA t ≤ N πA (t + 1) := N_mono (by omega)
    constructor
    · by_cases hq : q (t + 1) = q t
      · rw [N_stay hq]; omega
      · rw [N_move hq]
        have := par_ne L.q0 L.R.z (L.recv t hq)
        omega
    · by_cases hp : p (t + 1) = p t
      · rw [N_stay hp]; omega
      · rw [N_move hp]
        have := par_eq L.p0 L.A.z (L.send t hp)
        omega

theorem bounds (L : ELink p q πR πA loR hiR loA hiA) (t : Nat) :
    N q t ≤ N p t ∧ N p t ≤ N q t + 1 := by
  have i := L.inv t
  have a := L.R.le t
  have b := L.A.le t
  omega

theorem send_eq (L : ELink p q πR πA loR hiR loA hiA) {t : Nat} (hp : p (t + 1) ≠ p t) :
    N p t = N q t ∧ N p t = N πA t := by
  have i := L.inv t
  have b := L.A.le t
  have bo := L.bounds t
  have := par_eq L.p0 L.A.z (L.send t hp)
  omega

theorem at_recv (L : ELink p q πR πA loR hiR loA hiA) {t : Nat} (hq : q (t + 1) ≠ q t) :
    N p t = N q t + 1 ∧ N q t < N πR t := by
  have i := L.inv t
  have a := L.R.le t
  have bo := L.bounds t
  have := par_ne L.q0 L.R.z (L.recv t hq)
  omega

/-- The node pair obeys 8a's four-phase protocol. -/
theorem protocol (L : ELink p q πR πA loR hiR loA hiA) (d : Nat → Nat) : Protocol ⟨p, q, d⟩ := by
  refine ⟨⟨L.p0, L.q0⟩, fun t => ⟨fun hp => ?_, fun hq => ?_⟩⟩
  · exact val_eq L.p0 L.q0 (by have := (L.send_eq hp).1; omega)
  · have := (L.at_recv hq).1
    intro he
    have := par_eq L.q0 L.p0 he
    omega

/-- `Sep`: after a sender fall at `e`, with the sender low on `(e, e']`, a
receiver move at `e'` is at least `loR (N p e) + 1` later (the fall bound of
the receiver's pin). -/
theorem sep (L : ELink p q πR πA loR hiR loA hiA) {e e' : Nat}
    (h1 : p e = true) (h2 : p (e + 1) = false) (hl : ∀ u, e < u → u ≤ e' → p u = false)
    (he' : q (e' + 1) ≠ q e') (hlt : e < e') : e + loR (N p e) + 1 ≤ e' := by
  have hc := N_after_fall h1 h2 hl hlt
  have ⟨a1, a2⟩ := L.at_recv he'
  have := L.R.early (N q e') e' a2
  apply Classical.byContradiction; intro hn
  have : N p (e' - loR (N q e')) ≤ N p e := N_mono (by
    have : N q e' = N p e := by omega
    rw [this]; omega)
  omega

/-- `Hold`: after a receiver fall at `e'`, the sender stays low for
`loA (N q e') + 1` ticks (the fall bound of the sender's pin). -/
theorem hold (L : ELink p q πR πA loR hiR loA hiA) {e' : Nat}
    (hq1 : q e' = true) (hq2 : q (e' + 1) = false) :
    ∀ s, e' < s → s ≤ e' + loA (N q e') + 1 → p s = false := by
  have hmv : q (e' + 1) ≠ q e' := by rw [hq1, hq2]; decide
  have ⟨ha, _⟩ := L.at_recv hmv
  have hodd : N q e' % 2 = 1 := by
    have := parity L.q0 e'; rw [hq1] at this; simpa using this.symm
  have key : ∀ k, k ≤ loA (N q e') + 1 → N p (e' + k) = N p e' := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      by_cases hp : p (e' + k + 1) = p (e' + k)
      · rw [← Nat.add_assoc, N_stay hp]; exact ih (by omega)
      · have ⟨_, s2⟩ := L.send_eq hp
        have i1 := ih (by omega)
        have := L.A.early (N q e') (e' + k) (by omega)
        have : N q (e' + k - loA (N q e')) ≤ N q e' := N_mono (by omega)
        omega
  intro s h1 h2
  have := key (s - e') (by omega)
  rw [show e' + (s - e') = s by omega] at this
  rw [parity L.p0 s, this]
  simp; omega

/-- Open width: a sender high phase `(r, e]` lasts at least
`loR k + loA k + 2` where `k = N p r` (the rise bounds of both pins). -/
theorem openWidth (L : ELink p q πR πA loR hiR loA hiA) {r e : Nat}
    (hr0 : p r = false) (hr1 : p (r + 1) = true) (he1 : p (e + 1) = false)
    (hopen : ∀ u, r < u → u ≤ e → p u = true) (hre : r < e) :
    r + loR (N p r) + loA (N p r) + 2 ≤ e := by
  have hmr : p (r + 1) ≠ p r := by rw [hr0, hr1]; decide
  have h1 := N_move hmr
  have h2 : N p (r + 1 + (e - (r + 1))) = N p (r + 1) :=
    N_const _ (fun u hu1 hu2 => by rw [hopen u (by omega) (by omega), hopen (u + 1) (by omega) (by omega)])
  rw [show r + 1 + (e - (r + 1)) = e by omega] at h2
  have hme : p (e + 1) ≠ p e := by rw [he1, hopen e hre (Nat.le_refl _)]; decide
  have ⟨s1, s2⟩ := L.send_eq hme
  have hA := L.A.early (N p r) e (by omega)
  have hb : N q (e - loA (N p r)) ≤ N q e := N_mono (by omega)
  obtain ⟨r2, hr2, hc2, hn2⟩ := cnt_witness (chg q) (e - loA (N p r)) (N p r) (by
    show N q (e - loA (N p r)) = N p r + 1; omega)
  have hq2 : q (r2 + 1) ≠ q r2 := by simpa [chg] using hc2
  have hn2' : N q r2 = N p r := hn2
  have ⟨_, h4⟩ := L.at_recv hq2
  have := L.R.early (N p r) r2 (by omega)
  apply Classical.byContradiction; intro hc
  have : N p (r2 - loR (N p r)) ≤ N p r := N_mono (by omega)
  omega

/-- Source data: if the sender's data `D` changes only at sender rises, it is
stable on `[e+1-m, e+h]` around every receiver fall `e`, for
`m ≤ loR (N q e - 1) + 2` (rise bound of the receiver's pin) and
`h ≤ loA (N q e) + 1` (fall bound of the sender's pin). -/
theorem srcData (L : ELink p q πR πA loR hiR loA hiA) {D : Trace}
    (hD : ∀ t, D (t + 1) ≠ D t → p t = false ∧ p (t + 1) = true)
    {m h e : Nat} (hq1 : q e = true) (hq2 : q (e + 1) = false) (hm1 : 0 < m)
    (hm : m ≤ loR (N q e - 1) + 2) (hh : h ≤ loA (N q e) + 1) :
    ∀ s, e + 1 - m ≤ s → s ≤ e + h → D s = D e := by
  have hmv : q (e + 1) ≠ q e := by rw [hq1, hq2]; decide
  have ⟨ha, _⟩ := L.at_recv hmv
  have hodd : N q e % 2 = 1 := by
    have := parity L.q0 e; rw [hq1] at this; simpa using this.symm
  have noch : ∀ t, e + 1 - m ≤ t → t < e + h → D (t + 1) = D t := by
    intro t ht1 ht2
    apply Classical.byContradiction; intro hc
    obtain ⟨hp0, hp1⟩ := hD t hc
    have hmp : p (t + 1) ≠ p t := by rw [hp0, hp1]; decide
    have hev : N p t % 2 = 0 := by
      have := parity L.p0 t; rw [hp0] at this
      have : ¬ N p t % 2 = 1 := by simpa using this.symm
      omega
    by_cases hte : e ≤ t
    · have ⟨_, s2⟩ := L.send_eq hmp
      have h2 : N p e ≤ N p t := N_mono hte
      have := L.A.early (N q e) t (by omega)
      by_cases hle : t - loA (N q e) ≤ e
      · have : N q (t - loA (N q e)) ≤ N q e := N_mono hle
        omega
      · omega
    · have h1 := N_move hmp
      have h2 : N p (t + 1) ≤ N p e := N_mono (by omega)
      obtain ⟨r1, hr1, hc1, hn1⟩ := cnt_witness (chg q) e (N q e - 1) (by
        show N q e = N q e - 1 + 1; omega)
      have hq' : q (r1 + 1) ≠ q r1 := by simpa [chg] using hc1
      have hn1' : N q r1 = N q e - 1 := hn1
      have ⟨_, h3⟩ := L.at_recv hq'
      have := L.R.early (N q e - 1) r1 (by omega)
      by_cases hle : r1 - loR (N q e - 1) ≤ t
      · have : N p (r1 - loR (N q e - 1)) ≤ N p t := N_mono hle
        omega
      · omega
  intro s h1 h2
  rw [stable_of noch s h1 h2, stable_of noch e (by omega) (by omega)]

end ELink

/-! ## Data pins and the latch -/

/-- **H_DPIN (data pin).** Whenever the source was stable over
`[t - hi, t - lo]`, the pin shows that value at `t`. Nothing is said while the
source moves: the pin may glitch arbitrarily (per-event delay, runts). -/
def DPin (lo hi : Nat) (D π : Trace) : Prop :=
  ∀ t, (∀ u, t - hi ≤ u → u ≤ t - lo → D u = D (t - lo)) → π t = D (t - lo)

theorem shift_dpin (d : Nat) (D : Trace) : DPin d d D (shift d D) :=
  fun t _ => shift_eq d D t

/-- **Latch bit with general pins.** Enable pin `πG` an `EPin` of the node `x`,
D pin `πD` a `DPin` of `D`. The node closes at `e` (after an open phase from
`r`); if the enable pin's rise bound fits the open phase
(`r + gh (k-1) + 1 ≤ e`), the data pin's hi bound fits the setup
(`dh + 1 ≤ m`) and the enable pin's fall bound fits the hold
(`gh k ≤ dl + h`), with `k = N x e`, then the latch output is `D e` from
`e + 1` until the node reopens. -/
theorem latch_bit2 {x πG πD D O : Trace} {gl gh : Nat → Nat} {dl dh m h e r : Nat}
    (hcell : ∀ t, O (t + 1) = latchF (πD t) (πG t) (O t))
    (G : EPin gl gh x πG) (Dp : DPin dl dh D πD) (hx0 : x 0 = false)
    (hr0 : x r = false) (hr1 : x (r + 1) = true)
    (hopen : ∀ u, r < u → u ≤ e → x u = true) (hre : r < e) (he1 : x (e + 1) = false)
    (how : r + gh (N x e - 1) + 1 ≤ e) (hdl : dl ≤ dh) (hm : dh + 1 ≤ m) (hg : gh (N x e) ≤ dl + h)
    (hD : ∀ s, e + 1 - m ≤ s → s ≤ e + h → D s = D e) :
    ∀ s, e < s → (∀ u, e < u → u ≤ s → x u = false) → O s = D e := by
  have hmr : x (r + 1) ≠ x r := by rw [hr0, hr1]; decide
  have hNr := N_move hmr
  have hNe : N x e = N x (r + 1) := by
    have := N_const (s := x) (a := r + 1) (e - (r + 1)) (fun u hu1 hu2 => by
      rw [hopen u (by omega) (by omega), hopen (u + 1) (by omega) (by omega)])
    rwa [show r + 1 + (e - (r + 1)) = e by omega] at this
  have hodd : N x e % 2 = 1 := by
    have := parity hx0 e; rw [hopen e hre (Nat.le_refl _)] at this; simpa using this.symm
  -- the enable pin is high at e
  have hGe : N πG e = N x e := by
    have a := G.late (N x e - 1) e (by
      have : N x (r + 1) ≤ N x (e - gh (N x e - 1)) := N_mono (by omega)
      omega)
    have b := G.le e
    omega
  have hG_e : πG e = true := by rw [parity G.z e, hGe]; simp [hodd]
  intro s hs hlow
  have hNs : ∀ t, e < t → t ≤ s → N x t = N x e + 1 := fun t h1 h2 =>
    N_after_fall (hopen e hre (Nat.le_refl _)) he1 (fun u hu1 hu2 => hlow u hu1 (by omega)) h1
  -- while the enable pin is still high, the D pin shows D e
  have hDpin : ∀ t, e ≤ t → t < s → πG t = true → πD t = D e := by
    intro t h1 h2 hG
    have hle : t ≤ e + gh (N x e) := by
      have hp : N πG t % 2 = 1 := by
        have := parity G.z t; rw [hG] at this; simpa using this.symm
      have hb : N πG t ≤ N x t := G.le t
      have hxt : N x t ≤ N x e + 1 := by
        rcases Nat.lt_or_eq_of_le h1 with h1 | h1
        · have := hNs t h1 (by omega); omega
        · rw [← h1]; omega
      apply Classical.byContradiction; intro hc
      have := G.late (N x e) t (by
        rw [hNs (t - gh (N x e)) (by omega) (by omega)]; omega)
      omega
    have hw : ∀ u, t - dh ≤ u → u ≤ t - dl → D u = D (t - dl) := by
      intro u u1 u2
      rw [hD u (by omega) (by omega), hD (t - dl) (by omega) (by omega)]
    rw [Dp t hw, hD (t - dl) (by omega) (by omega)]
  have key : ∀ j, e + j + 1 ≤ s → O (e + j + 1) = D e := by
    intro j
    induction j with
    | zero =>
      intro hj
      rw [hcell, latchF_eq, hG_e]
      simp only [ite_true]
      exact hDpin e (Nat.le_refl _) (by omega) hG_e
    | succ j ih =>
      intro hj
      rw [show e + (j + 1) + 1 = (e + j + 1) + 1 by omega, hcell, latchF_eq]
      by_cases hG : πG (e + j + 1) = true
      · rw [hG]; simp only [ite_true]
        exact hDpin _ (by omega) (by omega) hG
      · have : πG (e + j + 1) = false := by simpa using hG
        rw [this]; simp only [Bool.false_eq_true, ite_false]
        exact ih (by omega)
  have := key (s - e - 1) (by omega)
  rwa [show e + (s - e - 1) + 1 = s by omega] at this

end Formal.Net.PerLink
