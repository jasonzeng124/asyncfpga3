import Formal.Core.XAudit.Events5

/-!
# Formal.Core.XAudit.Events7Core — `Beh7`: guarded pins with many copies (probe A-events7)

See `formal/notes/A-events7.md` (rebuilt in probe E7r).

`Events5.Net4.OK` forces a guarded pin (`PK.guard`) to ONE copy. On gcd the
acknowledges of `umux3/4/5` (`x_ack = C(j0, z_ack)`) read their guarded input
`z_ack` through a FASTFALL / FASTRISE delay line: a guarded pin with several
copies. Here:

* `Net4.OK7`: `Net4.OK` without the one-copy condition for guard pins (plain and
  filtered pins still have one copy).
* `Beh7`: `Events5.Beh4` with one change: a `guard` pin's `hpin` reads the AND
  (`op = true`, FASTFALL) or the OR of ALL its copies, exactly as a `multi` pin.
  Every other field, the counts `M` (a guarded pin counts `gc`) and the
  count-level facts `SelOK`, `LineOK`, `PinOK`, `ExclOK`, `GuardOK` are Beh4's.
* **`Beh7.safe`**: Beh4's integration theorem, with the same proof: `safe`'s
  guard case never uses `hpin` (GuardOK states the pin's value directly).
* the count lemmas used by the certificate checker (`P_le`, `M_le_pin`,
  `P_filt_le`, `M_merge`, `P_zero_merge`, ...), restated for `Beh7`.
-/

namespace Formal.Core.XAudit.Events5.Net4
variable {N : Nat} (net : Net4 N)

/-- **`Net4.OK7`**: `Net4.OK` with guarded pins allowed to have several copies
(plain and filtered pins have exactly one copy). -/
def OK7 : Prop :=
  ∀ j p, ((net.pk j p ≠ PK.multi ∧ net.pk j p ≠ PK.guard) → net.nc j p = 1) ∧
    ((net.pk j p = PK.multi ∨ net.pk j p = PK.filt) → net.v (net.src j p) = false) ∧
    (net.pk j p = PK.filt → net.inv j p = false) ∧
    (net.mg j = true → net.v j = false ∧ net.neg j p = false ∧ net.pk j p ≠ PK.guard ∧ net.off j p = 0) ∧
    (net.pk j p = PK.guard → net.mg j = false ∧ net.pk j (net.gp j p) ≠ PK.guard)

/-- `OK` implies `OK7` (OK7 only drops a condition). -/
theorem OK.ok7 (h : net.OK) : net.OK7 := by
  intro j p
  obtain ⟨h1, h2, h3, h4, h5⟩ := h j p
  exact ⟨fun hk => h1 hk.1, h2, h3, h4, h5⟩

end Formal.Core.XAudit.Events5.Net4

namespace Formal.Core.XAudit.Events7

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph ph_zero ph_off offB offB_le)
open Formal.Core.XAudit.Events2 (cel cel_hold cel_ph cel_all fmin fmin_le le_fmin fmin_mono fmin_mem ph_xor)
open Formal.Core.XAudit.Events3 (filt filt_add filt_mono ph_false_eq steer_val)
open Formal.Core.XAudit.Events4 (andCnt orCnt filt_le)
open Formal.Core.XAudit.Events5

/-- **`Beh7`**: a behaviour of a `Net4` in its bands, as `Events5.Beh4`, except
that a guarded pin reads the AND / OR (`op`) of all its copies. -/
structure Beh7 {N : Nat} (net : Net4 N) (b : Bands4 net) (sel : Nat → Nat → Bool) where
  c : Fin N → Sig
  pin : (j : Fin N) → Fin (net.ar j) → Sig
  q : Fin N → Sig
  r : Fin N → Sig
  sv : (j : Fin N) → Fin (net.ar j) → Sig
  gc : (j : Fin N) → Fin (net.ar j) → Nat → Nat
  F : Fin N → Nat → Nat
  G : (j : Fin N) → (p : Fin (net.ar j)) → Fin (net.nc j p) → Nat → Nat
  Q : Fin N → Nat → Nat
  wF : ∀ j, Warp (b.loF j) (b.hiF j) (F j)
  wG : ∀ j p i, Warp (b.loC j p i) (b.hiC j p i) (G j p i)
  wQ : ∀ j, Warp (b.loQ j) (b.hiQ j) (Q j)
  loF1 : ∀ j, 1 ≤ b.loF j
  loC1 : ∀ j p i, 1 ≤ b.loC j p i
  loQ1 : ∀ j, 1 ≤ b.loQ j
  hc : ∀ j t, c j t =
    if net.mg j then fany (net.ar j) (fun p => pin j p (F j t))
    else if r j (F j t) then net.v j else cel (fun p => pin j p (F j t) ^^ net.neg j p) (q j (F j t))
  /-- what a pin reads: a line (`multi`) AND a guarded pin (`guard`) read the
  AND / OR of all copies; a filtered pin one copy through a steer AND; a plain
  pin its copy -/
  hpin : ∀ j p t, pin j p t = (net.inv j p ^^
    match net.pk j p with
    | PK.multi => if net.op j p then fall (net.nc j p) (fun i => c (net.src j p) (G j p i t))
                  else fany (net.nc j p) (fun i => c (net.src j p) (G j p i t))
    | PK.guard => if net.op j p then fall (net.nc j p) (fun i => c (net.src j p) (G j p i t))
                  else fany (net.nc j p) (fun i => c (net.src j p) (G j p i t))
    | PK.filt => fany (net.nc j p) (fun i => c (net.src j p) (G j p i t) && (sv j p t == net.br j p))
    | PK.plain => fany (net.nc j p) (fun i => c (net.src j p) (G j p i t)))
  hq : ∀ j t, q j t = c j (Q j t)
  r0 : ∀ j, r j 0 = true
  ranti : ∀ j a b, a ≤ b → r j b = true → r j a = true
  hskew : ∀ j p (i i' : Fin (net.nc j p)), i'.val = i.val + 1 → ∀ s,
    G j p i s ≤ G j p i' s + b.dw j p i.val ∧ G j p i' s ≤ G j p i s + b.dw j p i.val
  mg0 : ∀ j, net.mg j = true → c j 0 = false
  gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s

namespace Beh7
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

theorem F_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.F j t < t := by
  have := (x.wF j).le_late t; have := x.loF1 j; omega

theorem G_lt (j : Fin N) (p : Fin (net.ar j)) (i : Fin (net.nc j p)) (t : Nat) (ht : 1 ≤ t) : x.G j p i t < t := by
  have := (x.wG j p i).le_late t; have := x.loC1 j p i; omega

theorem Q_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.Q j t < t := by
  have := (x.wQ j).le_late t; have := x.loQ1 j; omega

theorem F_zero (j : Fin N) : x.F j 0 = 0 := by have := (x.wF j).le_late 0; omega

/-- The count of a pin from the copies' source counts (as `Beh4.pc`). -/
def pc (j : Fin N) (p : Fin (net.ar j)) (s : Nat) (m : Fin (net.nc j p) → Nat) : Nat :=
  match net.pk j p with
  | PK.multi => if net.op j p then andCnt (fmin _ m) (fmax _ m) else orCnt (fmin _ m) (fmax _ m)
  | PK.filt => filt (sel (net.grp j p)) (net.br j p) (fmax _ m)
  | PK.guard => x.gc j p s
  | PK.plain => fmax _ m

theorem pc_mono (j : Fin N) (p : Fin (net.ar j)) (hn : 0 < net.nc j p) {a s : Nat} (has : a ≤ s)
    {m m' : Fin (net.nc j p) → Nat} (h : ∀ i, m i ≤ m' i) : x.pc j p a m ≤ x.pc j p s m' := by
  have h1 := fmin_mono _ _ _ hn h
  have h2 := fmax_mono _ _ _ hn h
  unfold pc
  split
  · split
    · unfold andCnt; omega
    · unfold orCnt; omega
  · exact filt_mono _ _ h2
  · exact x.gcmono j p a s has
  · exact h2

/-- **The counts** (as `Beh4.M`). -/
def M (t : Nat) (j : Fin N) : Nat :=
  if h : x.F j t < t then
    if net.mg j then
      fsum (net.ar j) (fun p => x.pc j p (x.F j t) (fun i =>
        if h0 : x.G j p i (x.F j t) < x.F j t then M (x.G j p i (x.F j t)) (net.src j p) else 0) + net.off j p)
    else if x.r j (x.F j t) then 0 else
      fmin (net.ar j) (fun p => x.pc j p (x.F j t) (fun i =>
        if h0 : x.G j p i (x.F j t) < x.F j t then M (x.G j p i (x.F j t)) (net.src j p) else 0) + net.off j p)
  else 0
termination_by t

def cm (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : Fin (net.nc j p) → Nat :=
  fun i => x.M (x.G j p i s) (net.src j p)

def P (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : Nat := x.pc j p s (x.cm j p s) + net.off j p

def E (j : Fin N) (s : Nat) : Nat :=
  if net.mg j then fsum (net.ar j) (fun p => x.P j p s)
  else if x.r j s then 0 else fmin (net.ar j) (fun p => x.P j p s)

theorem M_eq (t : Nat) (j : Fin N) (ht : 1 ≤ t) : x.M t j = x.E j (x.F j t) := by
  rw [M, dif_pos (x.F_lt j t ht)]
  unfold E P cm
  by_cases hs : 1 ≤ x.F j t
  · have e : ∀ p, (fun i => if h0 : x.G j p i (x.F j t) < x.F j t then x.M (x.G j p i (x.F j t)) (net.src j p) else 0)
        = (fun i => x.M (x.G j p i (x.F j t)) (net.src j p)) := by
      intro p; funext i; rw [dif_pos (x.G_lt j p i _ hs)]
    simp only [e]
  · have h0 : x.F j t = 0 := by omega
    have e : ∀ p, (fun i => if h0 : x.G j p i (x.F j t) < x.F j t then x.M (x.G j p i (x.F j t)) (net.src j p) else 0)
        = (fun i => x.M (x.G j p i (x.F j t)) (net.src j p)) := by
      intro p; funext i
      have : x.G j p i (x.F j t) = 0 := by have := (x.wG j p i).le_late (x.F j t); omega
      rw [dif_neg (by omega), this]
      rw [M]; rw [dif_neg (by have := (x.wF (net.src j p)).le_late 0; omega)]
    simp only [e]

theorem M_zero (j : Fin N) : x.M 0 j = 0 := by
  rw [M, dif_neg (by rw [x.F_zero]; exact Nat.lt_irrefl 0)]

theorem pc_le (j : Fin N) (p : Fin (net.ar j)) {a s : Nat} (has : a ≤ s) (hn : 0 < net.nc j p)
    (h : ∀ i, x.cm j p a i ≤ x.cm j p s i) : x.P j p a ≤ x.P j p s := by
  unfold P; have := x.pc_mono j p hn has h; omega

theorem M_mono : ∀ (n : Nat) (j : Fin N) (a : Nat), a ≤ n → x.M a j ≤ x.M n j := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro j a han
    rcases Nat.eq_zero_or_pos a with ha0 | ha1
    · subst ha0; rw [x.M_zero]; exact Nat.zero_le _
    rcases Nat.lt_or_ge a n with hlt | hge
    · have hn : 1 ≤ n := by omega
      rw [x.M_eq a j ha1, x.M_eq n j hn]
      have hFa := (x.wF j).mono a n (Nat.le_of_lt hlt)
      have hFn := x.F_lt j n hn
      have hP : ∀ p, x.P j p (x.F j a) ≤ x.P j p (x.F j n) := by
        intro p
        refine x.pc_le j p hFa (net.nc_pos j p) (fun i => ?_)
        unfold cm
        have hG := (x.wG j p i).le_late (x.F j n)
        exact ih (x.G j p i (x.F j n)) (by omega) (net.src j p) _ ((x.wG j p i).mono _ _ hFa)
      unfold E
      by_cases hm : net.mg j = true
      · simp only [hm, ite_true]; exact fsum_mono _ _ _ hP
      · simp only [hm, Bool.false_eq_true, ite_false]
        by_cases hrn : x.r j (x.F j n) = true
        · have := x.ranti j _ _ hFa hrn; simp [hrn, this]
        · by_cases hra : x.r j (x.F j a) = true
          · simp [hra]
          · simp only [hra, hrn, ite_false, Bool.false_eq_true]
            exact fmin_mono _ _ _ (net.ar_pos j) hP
    · have : a = n := by omega
      subst this; exact Nat.le_refl _

theorem E_mono (j : Fin N) (a s : Nat) (h : a ≤ s) : x.E j a ≤ x.E j s := by
  have hP : ∀ p, x.P j p a ≤ x.P j p s := fun p =>
    x.pc_le j p h (net.nc_pos j p) (fun i => x.M_mono _ _ _ ((x.wG j p i).mono _ _ h))
  unfold E
  by_cases hm : net.mg j = true
  · simp only [hm, ite_true]; exact fsum_mono _ _ _ hP
  · simp only [hm, Bool.false_eq_true, ite_false]
    by_cases hrs : x.r j s = true
    · have := x.ranti j _ _ h hrs; simp [hrs, this]
    · by_cases hra : x.r j a = true
      · simp [hra]
      · simp only [hra, hrs, ite_false, Bool.false_eq_true]
        exact fmin_mono _ _ _ (net.ar_pos j) hP

theorem q_le_P (j : Fin N) (hm : net.mg j = false) (s : Nat) (hr : x.r j s = false) (p : Fin (net.ar j)) :
    x.M (x.Q j s) j ≤ x.P j p s := by
  rcases Nat.eq_zero_or_pos (x.Q j s) with h0 | h1
  · rw [h0, x.M_zero]; exact Nat.zero_le _
  · rw [x.M_eq _ j h1]
    have a1 := (x.wF j).le_late (x.Q j s)
    have a2 := (x.wQ j).le_late s
    have h3 := x.E_mono j (x.F j (x.Q j s)) s (by omega)
    have e : x.E j s = fmin (net.ar j) (fun p => x.P j p s) := by
      unfold E; simp [hm, hr]
    rw [e] at h3
    exact Nat.le_trans h3 (fmin_le (net.ar j) (fun p => x.P j p s) p)

/-! ### The count-level facts (as for `Beh4`) -/

def SelOK : Prop :=
  ∀ j p s (i : Fin (net.nc j p)), net.pk j p = PK.filt → x.M (x.G j p i s) (net.src j p) % 2 = 1 →
    x.sv j p s = sel (net.grp j p) (x.M (x.G j p i s) (net.src j p) / 2)

def LineOK : Prop :=
  ∀ j p s, net.pk j p = PK.multi → ContigF (net.nc j p) (x.cm j p s)

def PinOK : Prop :=
  ∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → x.P j p s ≤ x.M (x.Q j s) j + 1

def ExclOK : Prop :=
  ∀ j s, net.mg j = true → fodd (net.ar j) (fun p => x.P j p s) ≤ 1

/-- **GuardOK** (W-E4g, a NAMED hypothesis, as `Beh4.GuardOK`): a guarded pin's
count is at most one ahead of the feedback, and the pin (the AND / OR of its
copies) reads it once its guard has advanced. -/
def GuardOK : Prop :=
  ∀ j p s, net.mg j = false → net.pk j p = PK.guard → x.r j s = false →
    x.P j p s ≤ x.M (x.Q j s) j + 1 ∧
    (x.P j (net.gp j p) s = x.M (x.Q j s) j + 1 → (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s))

theorem pin_val (hOK : net.OK7) (hsel : x.SelOK) (hline : x.LineOK) (j : Fin N) (p : Fin (net.ar j))
    (s : Nat) (hk : net.pk j p ≠ PK.guard)
    (ih : ∀ i, x.c (net.src j p) (x.G j p i s) = ph (net.v (net.src j p)) (x.cm j p s i)) :
    (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s) := by
  obtain ⟨hnc, hv, hinv, _, _⟩ := hOK j p
  rw [x.hpin j p s]
  unfold P pc Net4.off
  cases hpk : net.pk j p with
  | guard => exact absurd hpk hk
  | plain =>
    have h1 := hnc (by rw [hpk]; decide)
    simp only [hpk]
    rw [Beh4.fany_one h1, Beh4.fmax_one h1, ih, ph_xor]
    exact ph_off _ _ _
  | filt =>
    have h1 := hnc (by rw [hpk]; decide)
    have hvs := hv (Or.inr hpk)
    have hi := hinv hpk
    simp only [hpk]
    rw [Beh4.fany_one h1, Beh4.fmax_one h1, ih, hvs, hi]
    have st := steer_val (sel (net.grp j p)) (net.br j p) (x.cm j p s ⟨0, by omega⟩) (x.sv j p s)
      (fun h => hsel j p s ⟨0, by omega⟩ hpk h)
    rw [st, ph_xor]
    exact ph_off _ _ _
  | multi =>
    have hvs := hv (Or.inl hpk)
    have hc := hline j p s hpk
    simp only [hpk]
    have e : (fun i => x.c (net.src j p) (x.G j p i s)) = (fun i => ph false (x.cm j p s i)) := by
      funext i; rw [ih, hvs]
    rw [e]
    cases net.op j p
    · simp only [Bool.false_eq_true, ite_false]
      rw [orF_val _ (net.nc_pos j p) _ hc, ph_xor, hvs]; exact ph_off _ _ _
    · simp only [ite_true]
      rw [andF_val _ (net.nc_pos j p) _ hc, ph_xor, hvs]; exact ph_off _ _ _

/-- **`Beh7.safe`**: `Events5.Beh4.safe` for `Beh7` (same proof; the guard case
never uses `hpin`). -/
theorem safe (hOK : net.OK7) (hsel : x.SelOK) (hline : x.LineOK) (hpinok : x.PinOK) (hexcl : x.ExclOK)
    (hguard : x.GuardOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    rcases Nat.eq_zero_or_pos t with ht0 | ht1
    · subst ht0
      rw [x.M_zero, ph_zero]
      by_cases hm : net.mg j = true
      · rw [x.mg0 j hm]; exact ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1.symm
      · rw [x.hc j 0, x.F_zero, x.r0]; simp [hm]
    · have hst : x.F j t < t := x.F_lt j t ht1
      rw [x.hc j t, x.M_eq t j ht1]
      generalize x.F j t = s at hst ⊢
      have hpv : ∀ p, net.pk j p ≠ PK.guard → (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s) :=
        fun p hk => x.pin_val hOK hsel hline j p s hk (fun i => by
          unfold cm
          rcases Nat.eq_zero_or_pos s with hs0 | hs1
          · have : x.G j p i s = 0 := by have := (x.wG j p i).le_late s; omega
            rw [this]; exact ih 0 (by omega) _
          · exact ih _ (Nat.lt_trans (x.G_lt j p i s hs1) hst) _)
      unfold E
      by_cases hm : net.mg j = true
      · simp only [hm, ite_true]
        have hv0 := ((hOK j ⟨0, net.ar_pos j⟩).2.2.2.1 hm).1
        have e : (fun p => x.pin j p s) = (fun p => ph false (x.P j p s)) := by
          funext p
          obtain ⟨hvj, hng, hkg, _⟩ := (hOK j p).2.2.2.1 hm
          have := hpv p hkg
          rw [hng, Bool.xor_false, hvj] at this; exact this
        rw [e, fany_sum _ _ (hexcl j s hm), hv0]
      · have hm' : net.mg j = false := by simpa using hm
        simp only [hm, Bool.false_eq_true, ite_false]
        by_cases hr : x.r j s = true
        · simp [hr, ph_zero]
        · have hr' : x.r j s = false := by simpa using hr
          simp only [hr, ite_false, Bool.false_eq_true]
          have hs1 : 1 ≤ s := by
            rcases Nat.eq_zero_or_pos s with h | h
            · rw [h, x.r0] at hr'; exact absurd hr' (by decide)
            · exact h
          have hq : x.q j s = ph (net.v j) (x.M (x.Q j s) j) := by
            rw [x.hq j s]; exact ih _ (Nat.lt_trans (x.Q_lt j s hs1) hst) _
          rw [hq]
          refine cel_guards (net.v j) (net.ar j) (net.ar_pos j) (fun p => x.P j p s) _ _
            (fun p => decide (net.pk j p = PK.guard)) (net.gp j) ?_ ?_ ?_ ?_ ?_
          · intro p hp
            have := ((hOK j p).2.2.2.2 (of_decide_eq_true hp)).2
            simpa using this
          · intro p hp
            exact hpv p (by simpa using hp)
          · intro p; exact x.q_le_P j hm' s hr' p
          · intro p
            by_cases hk : net.pk j p = PK.guard
            · exact (hguard j p s hm' hk hr').1
            · exact hpinok j p s hm' hk
          · intro p hp hadv
            exact (hguard j p s hm' (of_decide_eq_true hp) hr').2 hadv

/-! ### Count lemmas for the certificate checker -/

theorem P_le (hOK : net.OK7) (j : Fin N) (p : Fin (net.ar j)) (hk : net.pk j p ≠ PK.guard) (s : Nat) :
    x.P j p s ≤ x.M (s - b.loP j p) (net.src j p) + net.off j p := by
  have hn := net.nc_pos j p
  have hcm : ∀ i, x.cm j p s i ≤ x.M (s - b.loP j p) (net.src j p) := by
    intro i; unfold cm
    have := (x.wG j p i).le_late s
    have := fmin_le (net.nc j p) (b.loC j p) i
    exact x.M_mono _ _ _ (by unfold Bands4.loP; omega)
  have hmax := fmax_le _ _ hn _ hcm
  have hmm : fmin _ (x.cm j p s) ≤ fmax _ (x.cm j p s) := by
    obtain ⟨i, hi⟩ := fmin_mem _ (x.cm j p s) hn; rw [hi]; exact le_fmax _ _ i
  unfold P pc
  cases hpk : net.pk j p with
  | guard => exact absurd hpk hk
  | plain => simp only; omega
  | filt => simp only; have := filt_le (sel (net.grp j p)) (net.br j p) (fmax _ (x.cm j p s)); omega
  | multi =>
    simp only
    cases net.op j p
    · simp only [Bool.false_eq_true, ite_false]; unfold orCnt; omega
    · simp only [ite_true]; unfold andCnt; omega

theorem M_le_pin (k : Fin N) (hm : net.mg k = false) (p : Fin (net.ar k)) (u : Nat) :
    x.M u k ≤ x.P k p (x.F k u) := by
  rcases Nat.eq_zero_or_pos u with h0 | h1
  · rw [h0, x.M_zero]; exact Nat.zero_le _
  · rw [x.M_eq u k h1]; unfold E
    simp only [hm, Bool.false_eq_true, ite_false]
    split
    · exact Nat.zero_le _
    · exact fmin_le (net.ar k) (fun p => x.P k p (x.F k u)) p

theorem P_mono (j : Fin N) (p : Fin (net.ar j)) {a s : Nat} (h : a ≤ s) : x.P j p a ≤ x.P j p s :=
  x.pc_le j p h (net.nc_pos j p) (fun i => x.M_mono _ _ _ ((x.wG j p i).mono _ _ h))

theorem P_filt_le (j : Fin N) (p : Fin (net.ar j)) (hk : net.pk j p = PK.filt) (s : Nat) :
    x.P j p s ≤ filt (sel (net.grp j p)) (net.br j p) (x.M (s - b.loP j p) (net.src j p)) + net.off j p := by
  have hcm : ∀ i, x.cm j p s i ≤ x.M (s - b.loP j p) (net.src j p) := by
    intro i; unfold cm
    have := (x.wG j p i).le_late s
    have := fmin_le (net.nc j p) (b.loC j p) i
    exact x.M_mono _ _ _ (by unfold Bands4.loP; omega)
  have hmax := fmax_le _ _ (net.nc_pos j p) _ hcm
  unfold P pc
  simp only [hk]
  have := filt_mono (sel (net.grp j p)) (net.br j p) hmax
  omega

theorem P_zero_merge (hOK : net.OK7) (xm : Fin N) (hm : net.mg xm = true) (a : Fin (net.ar xm)) :
    x.P xm a 0 = 0 := by
  obtain ⟨_, _, hkg, hoffa⟩ := (hOK xm a).2.2.2.1 hm
  have hcm : x.cm xm a 0 = fun _ => 0 := by
    funext i; unfold cm
    have : x.G xm a i 0 = 0 := by have := (x.wG xm a i).le_late 0; omega
    rw [this, x.M_zero]
  unfold P pc; rw [hcm, hoffa]
  have h0 : fmax (net.nc xm a) (fun _ => 0) = 0 := fmax_le _ _ (net.nc_pos xm a) 0 (fun _ => Nat.le_refl 0) |> Nat.le_zero.mp
  have h1 : fmin (net.nc xm a) (fun _ => 0) = 0 := Nat.le_zero.mp (fmin_le _ _ ⟨0, net.nc_pos xm a⟩)
  cases hpk : net.pk xm a with
  | guard => exact absurd hpk hkg
  | plain => simp only [h0]
  | filt => simp only [h0]; rfl
  | multi => simp only [h0, h1]; cases net.op xm a <;> simp [andCnt, orCnt]

/-- A merge's count (any arity) at a positive time is the sum of its pins at its sample. -/
theorem M_merge (xm : Fin N) (hm : net.mg xm = true) (u : Nat) (hu : 1 ≤ u) :
    x.M u xm = fsum (net.ar xm) (fun p => x.P xm p (x.F xm u)) := by
  rw [x.M_eq u xm hu]; unfold E; simp only [hm, ite_true]

/-- A merge pin (never guarded, offset 0 under OK7) counts at most its source `loP` earlier. -/
theorem P_merge_le (hOK : net.OK7) (xm : Fin N) (hm : net.mg xm = true) (a : Fin (net.ar xm)) (s : Nat) :
    x.P xm a s ≤ x.M (s - b.loP xm a) (net.src xm a) := by
  obtain ⟨_, _, hkg, hoffa⟩ := (hOK xm a).2.2.2.1 hm
  have := x.P_le hOK xm a hkg s; omega

end Beh7

/-- NEGATIVE CONTROL (why OK7 keeps one copy for PLAIN pins): a plain pin reads
the OR of its copies but counts the MAX of their counts; with two copies at
counts 1 and 2 the OR is high while the count 2 says low. -/
theorem plain_two_neg :
    fany 2 (fun i => ph false (if i.val = 0 then 1 else 2)) = true ∧
    ph false (fmax 2 (fun i => if i.val = 0 then 1 else 2)) = false := by
  decide

end Formal.Core.XAudit.Events7
