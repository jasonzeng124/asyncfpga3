import Formal.Core.XAudit.Events5Line

/-!
# Formal.Core.XAudit.Events5 — the integrated counter domain `Beh4` (probe A-events5)

See `formal/notes/A-events5.md`. This closes W-E4i of `Wip/Events4.lean` in the
following form.

**One network, four pin kinds and two node kinds** (`Net4`):
* node kinds: C-element stages (`mg j = false`: reset, own feedback, the
  n-input `cel` over bubbled pins) and MERGES (`mg j = true`: a stateless OR of
  its pins, reset value 0, no feedback — bd_mux's `z = j0 + j1`, the cond_br
  acknowledge OR, nested ORs, H_ARB's virtual `R0`);
* pin kinds (`PK`): `plain` (one transport channel from `src`), `filt` (a steer
  AND: the channel AND `[sel = br]`, the select sequence of the pin's GROUP
  `grp j p`), `multi` (a FASTFALL AND / FASTRISE OR tree of `nc j p` copies of one
  source, each copy its own warp), `guard` (a guarded pin, `bd_mux`'s
  `x_ack = C(j0, z_ack)` and the arbiter's `A_b = C(g_b, A0)`).

**The count recursion** `Beh4.M`: a stage counts `fmin` of its pin counts, a
merge the SUM `fsum` of its pin counts; a filtered pin `filt sel br`, a line
`andCnt / orCnt` of its extreme copy counts, a guarded pin the count `gc` that
the behaviour supplies (see GuardOK).

**`Beh4.safe`** (the integration theorem): every node of every behaviour reads
`ph v (M t j)` at every time, from five COUNT-LEVEL facts —
`PinOK` (each stage pin is at most one ahead of the stage's own feedback: what
the Back walks certify), `ExclOK` (at most one arm of a merge is high),
`LineOK` (the copies of a line have contiguous counts), `SelOK` (bundling of the
select, E6), `GuardOK` (the guarded-pin timing obligation, W-E4g, still a named
hypothesis) — and the structural side conditions `Net4.OK`.

**Discharging the count-level facts from certificates** (`Beh4.pinOK_of_back`,
`Beh4.lineOK_of_cert`, `Beh4.exclOK_of_cert`, `Beh4.ubound`): Back walks through
stage pins of every non-guard kind (`walk_le`), the per-window bound
(`cycle_le` ⇒ `OneEvent`), the line certificate (`LineCert`: every hop window ≤
the source's per-window bound, with the hop windows carried by the behaviour as
`hskew`, Events5Line.hop_skew), and merge exclusivity (`merge_excl` from
U-bounds `UCert` and a ≤ 1-token walk from the steer source to the merge).

What is NOT in this file: W-E4g (GuardOK from the ENTRY/EXIT inequalities),
W-E4n (`design_beh4`: the parsed netlist's behaviours are `Beh4`s, with `hskew`
derived by `hop_skew`/`prefix_skew` from the per-arc bands) and the R3/SUB walk
steps through merges (walks here step through stages only; Back certificates
that need R3/SUB are not yet covered). See the notes.
-/

namespace Formal.Core.XAudit.Events5

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph ph_zero ph_off offB offB_le)
open Formal.Core.XAudit.Events2 (cel cel_hold cel_ph cel_all fmin fmin_le le_fmin fmin_mono fmin_mem ph_xor)
open Formal.Core.XAudit.Events3 (filt filt_add filt_mono ph_false_eq steer_val)
open Formal.Core.XAudit.Events4 (andCnt orCnt merge_excl filt_le)

/-! ## 1. Sums, any, max over `Fin n` -/

def fsum : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + fsum n (fun i => f i.succ)

def fany : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => false
  | n + 1, f => f 0 || fany n (fun i => f i.succ)

def fall : (n : Nat) → (Fin n → Bool) → Bool
  | 0, _ => true
  | n + 1, f => f 0 && fall n (fun i => f i.succ)

/-- Number of odd entries (arms high). -/
def fodd : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => (if f 0 % 2 = 1 then 1 else 0) + fodd n (fun i => f i.succ)

def fmax : (n : Nat) → (Fin n → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => max (f 0) (fmax n (fun i => f i.succ))

theorem fsum_even : ∀ (n : Nat) (f : Fin n → Nat), fodd n f = 0 → fsum n f % 2 = 0
  | 0, _, _ => rfl
  | n + 1, f, h => by
      simp only [fodd] at h; simp only [fsum]
      have h0 : ¬ f 0 % 2 = 1 := by intro h'; rw [if_pos h'] at h; omega
      rw [if_neg h0] at h
      have := fsum_even n (fun i => f i.succ) (by omega); omega

theorem fany_false : ∀ (n : Nat) (f : Fin n → Nat), fodd n f = 0 → fany n (fun i => ph false (f i)) = false
  | 0, _, _ => rfl
  | n + 1, f, h => by
      simp only [fodd] at h; simp only [fany]
      have h0 : ¬ f 0 % 2 = 1 := by intro h'; rw [if_pos h'] at h; omega
      rw [if_neg h0] at h
      rw [fany_false n (fun i => f i.succ) (by omega), ph_false_eq]; simp [h0]

/-- **An n-ary merge with at most one arm high reads the summed count.** -/
theorem fany_sum : ∀ (n : Nat) (f : Fin n → Nat), fodd n f ≤ 1 →
    fany n (fun i => ph false (f i)) = ph false (fsum n f)
  | 0, _, _ => by simp [fany, fsum, ph_false_eq]
  | n + 1, f, h => by
      simp only [fodd] at h; simp only [fany, fsum]
      by_cases h0 : f 0 % 2 = 1
      · rw [if_pos h0] at h
        rw [fany_false n (fun i => f i.succ) (by omega)]
        have := fsum_even n (fun i => f i.succ) (by omega)
        rw [ph_false_eq, ph_false_eq]
        have : (f 0 + fsum n (fun i => f i.succ)) % 2 = 1 := by omega
        simp [h0, this]
      · rw [if_neg h0] at h
        rw [fany_sum n (fun i => f i.succ) (by omega), ph_false_eq, ph_false_eq, ph_false_eq]
        by_cases hs : fsum n (fun i => f i.succ) % 2 = 1
        · have : (f 0 + fsum n (fun i => f i.succ)) % 2 = 1 := by omega
          simp [h0, hs, this]
        · have : ¬ (f 0 + fsum n (fun i => f i.succ)) % 2 = 1 := by omega
          simp [h0, hs, this]

theorem le_fsum : ∀ (n : Nat) (f : Fin n → Nat) (i : Fin n), f i ≤ fsum n f
  | 0, _, i => i.elim0
  | n + 1, f, i => by
      simp only [fsum]
      refine Fin.cases ?_ (fun k => ?_) i
      · omega
      · have := le_fsum n (fun i => f i.succ) k; omega

theorem fsum_mono : ∀ (n : Nat) (f g : Fin n → Nat), (∀ i, f i ≤ g i) → fsum n f ≤ fsum n g
  | 0, _, _, _ => Nat.le_refl _
  | n + 1, f, g, h => by
      simp only [fsum]
      have := fsum_mono n (fun i => f i.succ) (fun i => g i.succ) (fun i => h i.succ)
      have := h 0; omega

theorem le_fmax : ∀ (n : Nat) (f : Fin n → Nat) (i : Fin n), f i ≤ fmax n f
  | 0, _, i => i.elim0
  | n + 1, f, i => by
      simp only [fmax]
      refine Fin.cases ?_ (fun k => ?_) i
      · exact Nat.le_max_left _ _
      · exact Nat.le_trans (le_fmax n (fun i => f i.succ) k) (Nat.le_max_right _ _)

theorem fmax_mem : ∀ (n : Nat) (f : Fin n → Nat), 0 < n → ∃ i, fmax n f = f i
  | 0, _, h => absurd h (Nat.lt_irrefl 0)
  | 1, f, _ => ⟨0, by simp [fmax]⟩
  | n + 2, f, _ => by
      show ∃ i, max (f 0) (fmax (n + 1) (fun i => f i.succ)) = f i
      obtain ⟨k, hk⟩ := fmax_mem (n + 1) (fun i => f i.succ) (Nat.succ_pos _)
      by_cases h : fmax (n + 1) (fun i => f i.succ) ≤ f 0
      · exact ⟨0, Nat.max_eq_left h⟩
      · exact ⟨k.succ, by rw [Nat.max_eq_right (by omega)]; exact hk⟩

theorem fmax_le (n : Nat) (f : Fin n → Nat) (hn : 0 < n) (c : Nat) (h : ∀ i, f i ≤ c) : fmax n f ≤ c := by
  obtain ⟨i, hi⟩ := fmax_mem n f hn; rw [hi]; exact h i

theorem fmax_mono (n : Nat) (f g : Fin n → Nat) (hn : 0 < n) (h : ∀ i, f i ≤ g i) : fmax n f ≤ fmax n g :=
  fmax_le n f hn _ (fun i => Nat.le_trans (h i) (le_fmax n g i))

theorem fall_eq : ∀ (n : Nat) (f : Fin n → Bool), fall n f = true ↔ ∀ i, f i = true
  | 0, _ => ⟨fun _ i => i.elim0, fun _ => rfl⟩
  | n + 1, f => by
      simp only [fall, Bool.and_eq_true, fall_eq n]
      constructor
      · rintro ⟨h0, h⟩ i; exact Fin.cases h0 h i
      · intro h; exact ⟨h 0, fun i => h i.succ⟩

theorem fany_eq : ∀ (n : Nat) (f : Fin n → Bool), fany n f = true ↔ ∃ i, f i = true
  | 0, _ => by simp [fany]
  | n + 1, f => by
      simp only [fany, Bool.or_eq_true, fany_eq n]
      constructor
      · rintro (h | ⟨i, h⟩)
        · exact ⟨0, h⟩
        · exact ⟨i.succ, h⟩
      · rintro ⟨i, h⟩
        refine Fin.cases (fun h => Or.inl h) (fun k h => Or.inr ⟨k, h⟩) i h

/-! ## 2. Delay lines over `Fin n` (the `Events4.and_val` / `or_val'` of an indexed family) -/

/-- The copies' counts miss no value between their minimum and maximum. -/
def ContigF (n : Nat) (f : Fin n → Nat) : Prop :=
  ∀ k, fmin n f ≤ k → k ≤ fmax n f → ∃ i, f i = k

theorem andF_val (n : Nat) (hn : 0 < n) (f : Fin n → Nat) (h : ContigF n f) :
    fall n (fun i => ph false (f i)) = ph false (andCnt (fmin n f) (fmax n f)) := by
  have hlh : fmin n f ≤ fmax n f := by
    obtain ⟨i, hi⟩ := fmin_mem n f hn; rw [hi]; exact le_fmax n f i
  have lowF : ∀ k, (∃ i, f i = k) → k % 2 = 0 → fall n (fun i => ph false (f i)) = false := by
    rintro k ⟨i, hi⟩ he
    cases hb : fall n (fun i => ph false (f i))
    · rfl
    · have := ((fall_eq n _).mp hb) i; rw [hi, ph_false_eq] at this; simp at this; omega
  unfold andCnt
  by_cases he : fmin n f % 2 = 0
  · rw [lowF _ (by obtain ⟨i, hi⟩ := fmin_mem n f hn; exact ⟨i, hi.symm⟩) he, show min (fmax n f) (fmin n f + fmin n f % 2) = fmin n f by omega,
      ph_false_eq]; simp [he]
  · by_cases heq : fmax n f = fmin n f
    · have hall : fall n (fun i => ph false (f i)) = true := by
        rw [fall_eq]; intro i
        have := fmin_le n f i; have := le_fmax n f i
        rw [ph_false_eq]; simp; omega
      rw [hall, show min (fmax n f) (fmin n f + fmin n f % 2) = fmin n f by omega, ph_false_eq]; simp; omega
    · rw [lowF (fmin n f + 1) (h _ (by omega) (by omega)) (by omega),
        show min (fmax n f) (fmin n f + fmin n f % 2) = fmin n f + 1 by omega, ph_false_eq]
      simp; omega

theorem orF_val (n : Nat) (hn : 0 < n) (f : Fin n → Nat) (h : ContigF n f) :
    fany n (fun i => ph false (f i)) = ph false (orCnt (fmin n f) (fmax n f)) := by
  have hlh : fmin n f ≤ fmax n f := by
    obtain ⟨i, hi⟩ := fmin_mem n f hn; rw [hi]; exact le_fmax n f i
  have highT : ∀ k, (∃ i, f i = k) → k % 2 = 1 → fany n (fun i => ph false (f i)) = true := by
    rintro k ⟨i, hi⟩ ho
    rw [fany_eq]; exact ⟨i, by rw [hi, ph_false_eq]; simp [ho]⟩
  unfold orCnt
  by_cases ho : fmax n f % 2 = 1
  · rw [highT _ (by obtain ⟨i, hi⟩ := fmax_mem n f hn; exact ⟨i, hi.symm⟩) ho, show max (fmin n f) (fmax n f - 1 + fmax n f % 2) = fmax n f by omega,
      ph_false_eq]; simp [ho]
  · by_cases heq : fmax n f = fmin n f
    · have hall : fany n (fun i => ph false (f i)) = false := by
        cases hb : fany n (fun i => ph false (f i))
        · rfl
        · obtain ⟨i, hi⟩ := (fany_eq n _).mp hb
          have := fmin_le n f i; have := le_fmax n f i
          rw [ph_false_eq] at hi; simp at hi; omega
      rw [hall, show max (fmin n f) (fmax n f - 1 + fmax n f % 2) = fmax n f by omega, ph_false_eq]; simp [ho]
    · rw [highT (fmax n f - 1) (h _ (by omega) (by omega)) (by omega),
        show max (fmin n f) (fmax n f - 1 + fmax n f % 2) = fmax n f - 1 by omega, ph_false_eq]
      simp; omega

/-- A chain of copies with consecutive counts at most one apart is contiguous
(the linear case of `Events5Line.tree_contig`). -/
theorem contigF_chain : ∀ (n : Nat) (f : Fin n → Nat), 0 < n →
    (∀ i : Fin n, ∀ h : i.val + 1 < n, f i ≤ f ⟨i.val + 1, h⟩ + 1 ∧ f ⟨i.val + 1, h⟩ ≤ f i + 1) →
    ContigF n f
  | 0, _, h, _ => absurd h (Nat.lt_irrefl 0)
  | 1, f, _, _ => by
      intro k h1 h2; simp [fmin, fmax] at h1 h2; exact ⟨0, by omega⟩
  | n + 2, f, _, hc => by
      intro k h1 h2
      have ih := contigF_chain (n + 1) (fun i => f i.succ) (Nat.succ_pos _)
        (fun i h => hc i.succ (by simp; omega))
      have e1 : fmin (n + 2) f = min (f 0) (fmin (n + 1) (fun i => f i.succ)) := rfl
      have e2 : fmax (n + 2) f = max (f 0) (fmax (n + 1) (fun i => f i.succ)) := rfl
      have c01 : f 0 ≤ f (Fin.succ 0) + 1 ∧ f (Fin.succ 0) ≤ f 0 + 1 := hc 0 (by simp)
      -- f 1 lies in the tail's range
      have t1 := fmin_le (n + 1) (fun i => f i.succ) 0
      have t2 := le_fmax (n + 1) (fun i => f i.succ) 0
      by_cases hk : fmin (n + 1) (fun i => f i.succ) ≤ k ∧ k ≤ fmax (n + 1) (fun i => f i.succ)
      · obtain ⟨i, hi⟩ := ih k hk.1 hk.2; exact ⟨i.succ, hi⟩
      · refine ⟨0, ?_⟩
        rw [e1] at h1; rw [e2] at h2
        omega

/-! ## 3. Networks -/

inductive PK where
  | plain | filt | multi | guard
  deriving DecidableEq

structure Net4 (N : Nat) where
  /-- reset value (merges: false) -/
  v : Fin N → Bool
  /-- merge node (stateless OR of its pins) -/
  mg : Fin N → Bool
  ar : Fin N → Nat
  ar_pos : ∀ j, 0 < ar j
  src : (j : Fin N) → Fin (ar j) → Fin N
  inv : (j : Fin N) → Fin (ar j) → Bool
  neg : (j : Fin N) → Fin (ar j) → Bool
  pk : (j : Fin N) → Fin (ar j) → PK
  /-- number of copies (a line's taps; 1 for the other kinds) -/
  nc : (j : Fin N) → Fin (ar j) → Nat
  nc_pos : ∀ j p, 0 < nc j p
  /-- line operator: true = AND (FASTFALL), false = OR (FASTRISE) -/
  op : (j : Fin N) → Fin (ar j) → Bool
  /-- steer group and branch of a filtered pin -/
  grp : (j : Fin N) → Fin (ar j) → Nat
  br : (j : Fin N) → Fin (ar j) → Bool
  /-- the guard pin of a guarded pin (a non-guard pin of the same stage) -/
  gp : (j : Fin N) → Fin (ar j) → Fin (ar j)

namespace Net4
variable {N : Nat} (net : Net4 N)

def off (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  offB (net.v (net.src j p) ^^ net.inv j p ^^ net.neg j p) (net.v j)

/-- Structural side conditions (all decidable): lines and steers read 4-phase
requests with reset 0; a pin other than a line has exactly one copy; merges have reset 0, no bubbles, no guarded pins, and every pin offset 0;
the guard of a guarded pin is a non-guard pin of a stage. -/
def OK : Prop :=
  ∀ j p, (net.pk j p ≠ PK.multi → net.nc j p = 1) ∧
    ((net.pk j p = PK.multi ∨ net.pk j p = PK.filt) → net.v (net.src j p) = false) ∧
    (net.pk j p = PK.filt → net.inv j p = false) ∧
    (net.mg j = true → net.v j = false ∧ net.neg j p = false ∧ net.pk j p ≠ PK.guard ∧ net.off j p = 0) ∧
    (net.pk j p = PK.guard → net.mg j = false ∧ net.pk j (net.gp j p) ≠ PK.guard)

end Net4

/-- Delay bands: LUT, every copy of every pin, feedback. -/
structure Bands4 {N : Nat} (net : Net4 N) where
  loF : Fin N → Nat
  hiF : Fin N → Nat
  loC : (j : Fin N) → (p : Fin (net.ar j)) → Fin (net.nc j p) → Nat
  hiC : (j : Fin N) → (p : Fin (net.ar j)) → Fin (net.nc j p) → Nat
  loQ : Fin N → Nat
  hiQ : Fin N → Nat
  /-- hop windows of a line: copies `i` and `i+1` are sampled within `dw` -/
  dw : (j : Fin N) → (p : Fin (net.ar j)) → Nat → Nat

/-- A behaviour. `sv j p t`: the select seen by a filtered pin's steer gate;
`gc j p s`: the count a guarded pin is held to (GuardOK). -/
structure Beh4 {N : Nat} (net : Net4 N) (b : Bands4 net) (sel : Nat → Nat → Bool) where
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
  /-- stages: reset value under reset, else the C-element of the bubbled pins;
  merges: the OR of the pins -/
  hc : ∀ j t, c j t =
    if net.mg j then fany (net.ar j) (fun p => pin j p (F j t))
    else if r j (F j t) then net.v j else cel (fun p => pin j p (F j t) ^^ net.neg j p) (q j (F j t))
  /-- what a pin reads: one copy (plain / guard), one copy through a steer AND
  (filt), or the AND / OR of all copies (multi); then the channel inversion -/
  hpin : ∀ j p t, pin j p t = (net.inv j p ^^
    match net.pk j p with
    | PK.multi => if net.op j p then fall (net.nc j p) (fun i => c (net.src j p) (G j p i t))
                  else fany (net.nc j p) (fun i => c (net.src j p) (G j p i t))
    | PK.filt => fany (net.nc j p) (fun i => c (net.src j p) (G j p i t) && (sv j p t == net.br j p))
    | _ => fany (net.nc j p) (fun i => c (net.src j p) (G j p i t)))
  hq : ∀ j t, q j t = c j (Q j t)
  r0 : ∀ j, r j 0 = true
  ranti : ∀ j a b, a ≤ b → r j b = true → r j a = true
  /-- the hop windows of every line, as a property of the behaviour's warps
  (`Events5Line.hop_skew` derives it from the per-element bands of the two tap
  paths; the netlist link W-E4n states it per gate) -/
  hskew : ∀ j p (i i' : Fin (net.nc j p)), i'.val = i.val + 1 → ∀ s,
    G j p i s ≤ G j p i' s + b.dw j p i.val ∧ G j p i' s ≤ G j p i s + b.dw j p i.val
  /-- a merge (stateless OR of reset-low requests) is low at time 0; for
  stages this follows from `r0` and `hc`, for merges it is the acyclicity of
  the OR gates (no OR loop), stated -/
  mg0 : ∀ j, net.mg j = true → c j 0 = false
  /-- guarded counts are monotone -/
  gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

theorem F_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.F j t < t := by
  have := (x.wF j).le_late t; have := x.loF1 j; omega

theorem G_lt (j : Fin N) (p : Fin (net.ar j)) (i : Fin (net.nc j p)) (t : Nat) (ht : 1 ≤ t) : x.G j p i t < t := by
  have := (x.wG j p i).le_late t; have := x.loC1 j p i; omega

theorem Q_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.Q j t < t := by
  have := (x.wQ j).le_late t; have := x.loQ1 j; omega

theorem F_zero (j : Fin N) : x.F j 0 = 0 := by have := (x.wF j).le_late 0; omega

/-- The count of a pin from the copies' source counts `m` (before the offset). -/
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

/-- **The counts.** -/
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

/-- Count of the copies of pin `p` at LUT sample time `s`. -/
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
  · -- F j t = 0: stage under reset (r0); a merge reads copies at time 0
    have h0 : x.F j t = 0 := by omega
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

/-- The stage's own feedback count is never ahead of any pin. -/
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

end Beh4

/-- **A C-element with guarded pins.** Unguarded pins read their counts; each
guarded pin `i` has a guard `g i` (unguarded) and reads its count whenever its
guard has advanced past the feedback. Then the stage is the C-element of the
counts (generalises `Events4.cel_guard_ph` to any number of guarded pins). -/
theorem cel_guards (v : Bool) (n : Nat) (hn : 0 < n) (p : Fin n → Nat) (x : Fin n → Bool) (mq : Nat)
    (isg : Fin n → Bool) (g : Fin n → Fin n) (hg : ∀ i, isg i = true → isg (g i) = false)
    (hx : ∀ i, isg i = false → x i = ph v (p i)) (h1 : ∀ i, mq ≤ p i) (h2 : ∀ i, p i ≤ mq + 1)
    (hguard : ∀ i, isg i = true → p (g i) = mq + 1 → x i = ph v (p i)) :
    cel x (ph v mq) = ph v (fmin n p) := by
  by_cases hex : ∃ i, isg i = true ∧ p (g i) = mq
  · obtain ⟨i, hi, hpi⟩ := hex
    have hm : fmin n p = mq := by
      have := fmin_le n p (g i); have := le_fmin n p hn mq h1; omega
    rw [hm]
    exact cel_hold _ _ ⟨g i, by rw [hx (g i) (hg i hi), hpi]⟩
  · have hall : ∀ i, x i = ph v (p i) := by
      intro i
      cases hgi : isg i
      · exact hx i hgi
      · by_cases hpg : p (g i) = mq
        · exact absurd ⟨i, hgi, hpg⟩ hex
        · exact hguard i hgi (by have := h1 (g i); have := h2 (g i); omega)
    rw [show x = fun i => ph v (p i) from funext hall]
    exact cel_ph v n hn p mq h1 h2

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

/-- The BUNDLING hypothesis on the selects (E6, as `Events3.SelOK`). -/
def SelOK : Prop :=
  ∀ j p s (i : Fin (net.nc j p)), net.pk j p = PK.filt → x.M (x.G j p i s) (net.src j p) % 2 = 1 →
    x.sv j p s = sel (net.grp j p) (x.M (x.G j p i s) (net.src j p) / 2)

/-- Every delay line's copies have contiguous counts (discharged by `lineOK_of_cert`). -/
def LineOK : Prop :=
  ∀ j p s, net.pk j p = PK.multi → ContigF (net.nc j p) (x.cm j p s)

/-- Every unguarded stage pin is at most one ahead of the own feedback
(discharged by `pinOK_of_back`). -/
def PinOK : Prop :=
  ∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → x.P j p s ≤ x.M (x.Q j s) j + 1

/-- At most one arm of a merge is high (discharged by `exclOK_of_cert`). -/
def ExclOK : Prop :=
  ∀ j s, net.mg j = true → fodd (net.ar j) (fun p => x.P j p s) ≤ 1

/-- **GuardOK** (W-E4g, a NAMED hypothesis): a guarded pin's count `gc` is at
most one ahead of the feedback, and the pin reads it once its guard has
advanced. Its discharge from the ENTRY/EXIT inequalities is open. -/
def GuardOK : Prop :=
  ∀ j p s, net.mg j = false → net.pk j p = PK.guard → x.r j s = false →
    x.P j p s ≤ x.M (x.Q j s) j + 1 ∧
    (x.P j (net.gp j p) s = x.M (x.Q j s) j + 1 → (x.pin j p s ^^ net.neg j p) = ph (net.v j) (x.P j p s))

theorem fany_one {n : Nat} (h : n = 1) (f : Fin n → Bool) : fany n f = f ⟨0, by omega⟩ := by
  subst h; simp [fany]
theorem fmax_one {n : Nat} (h : n = 1) (f : Fin n → Nat) : fmax n f = f ⟨0, by omega⟩ := by
  subst h; simp [fmax]

/-- **The value of an unguarded pin** from the source values at the copies'
sample times. -/
theorem pin_val (hOK : net.OK) (hsel : x.SelOK) (hline : x.LineOK) (j : Fin N) (p : Fin (net.ar j))
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
    rw [fany_one h1, fmax_one h1, ih, ph_xor]
    exact ph_off _ _ _
  | filt =>
    have h1 := hnc (by rw [hpk]; decide)
    have hvs := hv (Or.inr hpk)
    have hi := hinv hpk
    simp only [hpk]
    rw [fany_one h1, fmax_one h1, ih, hvs, hi]
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

/-- **W-E4i: soundness of the integrated counter domain.** Under the structural
conditions `Net4.OK`, for every select sequence satisfying the bundling
hypothesis `SelOK`, if the delay lines are contiguous (`LineOK`), the merges
exclusive (`ExclOK`), every unguarded stage pin within one event of the own
feedback (`PinOK`) and the guarded pins satisfy `GuardOK`, then every node of
the behaviour (stage or merge) equals its reset value flipped `M t j` times,
at every time. -/
theorem safe (hOK : net.OK) (hsel : x.SelOK) (hline : x.LineOK) (hpinok : x.PinOK) (hexcl : x.ExclOK)
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
      -- every unguarded pin of `j` at `s`
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

end Beh4

/-! ## 4. Certificates: walks, the per-window bound, lines, merge exclusivity -/

/-- Fastest copy of a pin. -/
def Bands4.loP {N : Nat} {net : Net4 N} (b : Bands4 net) (j : Fin N) (p : Fin (net.ar j)) : Nat :=
  fmin (net.nc j p) (b.loC j p)

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

/-- A pin's count is at most its source's count `loP` earlier (any unguarded kind). -/
theorem P_le (hOK : net.OK) (j : Fin N) (p : Fin (net.ar j)) (hk : net.pk j p ≠ PK.guard) (s : Nat) :
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

end Beh4

/-- An arc of the counter graph (a stage pin). -/
abbrev Arc4 {N : Nat} (net : Net4 N) := (k : Fin N) × Fin (net.ar k)

/-- `walk4OK a b w`: stepping upstream through the STAGE pins of `w` (no merge,
no guarded pin) from `a` reaches `b`. -/
def walk4OK {N : Nat} (net : Net4 N) : Fin N → Fin N → List (Arc4 net) → Bool
  | a, b, [] => a == b
  | a, b, ⟨k, p⟩ :: w => k == a && !net.mg k && !(net.pk k p == PK.guard) && walk4OK net (net.src k p) b w

def wTok4 {N : Nat} (net : Net4 N) : List (Arc4 net) → Nat
  | [] => 0
  | ⟨k, p⟩ :: w => net.off k p + wTok4 net w

def wLo4 {N : Nat} {net : Net4 N} (b : Bands4 net) : List (Arc4 net) → Nat
  | [] => 0
  | ⟨k, p⟩ :: w => b.loF k + b.loP k p + wLo4 b w

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

/-- **Walk bound** (min-plus, R1 steps through stage pins of every unguarded kind). -/
theorem walk_le (hOK : net.OK) : ∀ (w : List (Arc4 net)) (a bb : Fin N), walk4OK net a bb w = true →
    ∀ u, x.M u a ≤ x.M (u - wLo4 b w) bb + wTok4 net w
  | [], a, bb, h, u => by
      simp only [walk4OK, beq_iff_eq] at h; subst h; simp [wLo4, wTok4]
  | ⟨k, p⟩ :: w, a, bb, h, u => by
      simp only [walk4OK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨hk, hm⟩, hg⟩, hw⟩ := h
      subst hk
      have hg' : net.pk k p ≠ PK.guard := by intro h'; rw [h'] at hg; exact absurd hg (by decide)
      have h1 := x.M_le_pin k hm p u
      have h2 := x.P_le hOK k p hg' (x.F k u)
      have a1 := (x.wF k).le_late u
      have h3 := x.M_mono (u - b.loF k - b.loP k p) (net.src k p) (x.F k u - b.loP k p) (by omega)
      have h4 := walk_le hOK w (net.src k p) bb hw (u - b.loF k - b.loP k p)
      have e : u - b.loF k - b.loP k p - wLo4 b w = u - wLo4 b (⟨k, p⟩ :: w) := by
        simp only [wLo4]; omega
      rw [e] at h4
      simp only [wTok4]
      omega

/-- **Per-window bound**: a closed walk with at most one token: the node fires
at most once in any window of `wLo4` (Events3.cycle_le for `Beh4`). -/
theorem cycle_le (hOK : net.OK) (w : List (Arc4 net)) (j : Fin N) (hw : walk4OK net j j w = true) (t : Nat) :
    x.M (t + wLo4 b w) j ≤ x.M t j + wTok4 net w := by
  have := x.walk_le hOK w j j hw (t + wLo4 b w)
  rwa [Nat.add_sub_cancel] at this

theorem oneEvent (hOK : net.OK) (w : List (Arc4 net)) (j : Fin N) (hw : walk4OK net j j w = true)
    (ht : wTok4 net w ≤ 1) : OneEvent (fun t => x.M t j) (wLo4 b w) := by
  intro t; have := x.cycle_le hOK w j hw t; simp only; omega

end Beh4

/-- **Back** for `Beh4` (decidable): for every unguarded stage pin, a walk from
its source back to the stage with (pin + walk) at most one token, no faster
than the stage's slowest own feedback. -/
def Back4 {N : Nat} {net : Net4 N} (b : Bands4 net) (back : (j : Fin N) → Fin (net.ar j) → List (Arc4 net)) : Prop :=
  ∀ j p, net.mg j = false → net.pk j p ≠ PK.guard →
    walk4OK net (net.src j p) j (back j p) = true ∧ wTok4 net (back j p) + net.off j p ≤ 1 ∧
    b.hiQ j ≤ b.loP j p + wLo4 b (back j p)

/-- **The line certificate** (decidable; what `contig5` checks): every
multi-copy pin's source has a closed walk with at most one token whose fastest
traversal is at least every hop window of the line. -/
def LineCert {N : Nat} {net : Net4 N} (b : Bands4 net) (cyc : Fin N → List (Arc4 net)) : Prop :=
  ∀ j p, net.pk j p = PK.multi →
    walk4OK net (net.src j p) (net.src j p) (cyc (net.src j p)) = true ∧
    wTok4 net (cyc (net.src j p)) ≤ 1 ∧
    ∀ i, i + 1 < net.nc j p → b.dw j p i ≤ wLo4 b (cyc (net.src j p))

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

theorem pinOK_of_back (hOK : net.OK) {back : (j : Fin N) → Fin (net.ar j) → List (Arc4 net)}
    (hB : Back4 b back) : x.PinOK := by
  intro j p s hm hk
  obtain ⟨hw, htok, hrace⟩ := hB j p hm hk
  have h0 := x.P_le hOK j p hk s
  have h1 := x.walk_le hOK (back j p) _ _ hw (s - b.loP j p)
  have a4 := (x.wQ j).early_le s
  have := x.M_mono (x.Q j s) j (s - b.loP j p - wLo4 b (back j p)) (by omega)
  omega

theorem lineOK_of_cert (hOK : net.OK) {cyc : Fin N → List (Arc4 net)} (hL : LineCert b cyc) : x.LineOK := by
  intro j p s hk
  obtain ⟨hw, htok, hdw⟩ := hL j p hk
  have hev := x.oneEvent hOK _ _ hw htok
  have hmono : MonoC (fun t => x.M t (net.src j p)) := fun a c h => x.M_mono _ _ _ h
  apply contigF_chain _ _ (net.nc_pos j p)
  intro i hi
  have hsk := x.hskew j p i ⟨i.val + 1, hi⟩ rfl s
  have hd := hdw i.val hi
  have := close_of_window (fun t => x.M t (net.src j p)) _ hmono hev (x.G j p i s) (x.G j p ⟨i.val + 1, hi⟩ s)
    (by omega) (by omega)
  exact this

end Beh4

/-! ## 5. Merge exclusivity from certificates (binary merges; W-E5a) -/

theorem fin2_sum {n : Nat} (h : n = 2) (f : Fin n → Nat) (a0 a1 : Fin n) (hne : a0 ≠ a1) :
    fsum n f = f a0 + f a1 ∧ (¬ (f a0 % 2 = 1 ∧ f a1 % 2 = 1) → fodd n f ≤ 1) := by
  subst h
  have hs : fsum 2 f = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ := rfl
  have ho : fodd 2 f = (if f ⟨0, by omega⟩ % 2 = 1 then 1 else 0) + ((if f ⟨1, by omega⟩ % 2 = 1 then 1 else 0) + 0) := rfl
  have h0 := a0.isLt; have h1 := a1.isLt
  have hv : a0.val ≠ a1.val := fun e => hne (Fin.ext e)
  rw [hs, ho]
  rcases (show a0.val = 0 ∨ a0.val = 1 by omega) with ha | ha <;>
  rcases (show a1.val = 0 ∨ a1.val = 1 by omega) with hb | hb
  · omega
  · rw [show a0 = ⟨0, by omega⟩ from Fin.ext ha, show a1 = ⟨1, by omega⟩ from Fin.ext hb]
    exact ⟨rfl, fun hn => by split <;> split <;> omega⟩
  · rw [show a0 = ⟨1, by omega⟩ from Fin.ext ha, show a1 = ⟨0, by omega⟩ from Fin.ext hb]
    exact ⟨Nat.add_comm _ _, fun hn => by split <;> split <;> omega⟩
  · omega

theorem fodd_le : ∀ (n : Nat) (f : Fin n → Nat), fodd n f ≤ n
  | 0, _ => Nat.le_refl _
  | n + 1, f => by
      simp only [fodd]; have := fodd_le n (fun i => f i.succ); split <;> omega

/-- The arm `a` of merge `x` fires only in branch `β` of group `g`'s source `S`:
a token-free walk from the arm's source to a stage `T` whose filtered pin `q`
(group `g`, branch `β`) reads `S` (the U-bound of the analysis). -/
def UArm {N : Nat} {net : Net4 N} (x : Fin N) (a : Fin (net.ar x)) (S : Fin N) (g : Nat) (β : Bool) : Prop :=
  ∃ (T : Fin N) (q : Fin (net.ar T)) (w : List (Arc4 net)),
    walk4OK net (net.src x a) T w = true ∧ wTok4 net w = 0 ∧ net.mg T = false ∧
    net.pk T q = PK.filt ∧ net.grp T q = g ∧ net.br T q = β ∧ net.src T q = S ∧ net.off T q = 0

/-- **Exclusivity certificate** of every merge: at most two arms; two arms are
distinct branches (`false`, `true`) of one steer group `g` of one source `S`,
and `S` cannot start again before the merge has seen the previous transaction
(a walk `S → x` with at most one token). -/
def ExclCert {N : Nat} (net : Net4 N) : Prop :=
  ∀ x, net.mg x = true → net.ar x ≤ 2 ∧ (net.ar x = 2 →
    ∃ (S : Fin N) (g : Nat) (a0 a1 : Fin (net.ar x)) (ew : List (Arc4 net)),
      a0 ≠ a1 ∧ walk4OK net S x ew = true ∧ wTok4 net ew ≤ 1 ∧
      UArm x a0 S g false ∧ UArm x a1 S g true)

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

theorem P_mono (j : Fin N) (p : Fin (net.ar j)) {a s : Nat} (h : a ≤ s) : x.P j p a ≤ x.P j p s :=
  x.pc_le j p h (net.nc_pos j p) (fun i => x.M_mono _ _ _ ((x.wG j p i).mono _ _ h))

/-- A filtered pin counts at most the branch count of its source `loP` earlier. -/
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

/-- **U-bound**: an arm with a `UArm` certificate counts at most its branch
count of `S`, a fixed delay `d` earlier. -/
theorem ubound (hOK : net.OK) (xm : Fin N) (hm : net.mg xm = true) (a : Fin (net.ar xm)) (S : Fin N)
    (g : Nat) (β : Bool) (hU : UArm xm a S g β) :
    ∃ d, ∀ s, x.P xm a s ≤ filt (sel g) β (x.M (s - d) S) := by
  obtain ⟨T, q, w, hw, htok, hmT, hk, hg, hb, hsrc, hoff⟩ := hU
  subst hsrc; subst hg; subst hb
  obtain ⟨_, _, hkg, hoffa⟩ := (hOK xm a).2.2.2.1 hm
  refine ⟨b.loP xm a + wLo4 b w + b.loF T + b.loP T q, fun s => ?_⟩
  have h1 := x.P_le hOK xm a hkg s
  have h2 := x.walk_le hOK w _ _ hw (s - b.loP xm a)
  have h3 := x.M_le_pin T hmT q (s - b.loP xm a - wLo4 b w)
  have h4 := x.P_filt_le T q hk (x.F T (s - b.loP xm a - wLo4 b w))
  have a1 := (x.wF T).le_late (s - b.loP xm a - wLo4 b w)
  have h5 := x.M_mono (s - (b.loP xm a + wLo4 b w + b.loF T + b.loP T q)) (net.src T q)
    (x.F T (s - b.loP xm a - wLo4 b w) - b.loP T q) (by omega)
  have h6 := filt_mono (sel (net.grp T q)) (net.br T q) h5
  omega

theorem P_zero_merge (hOK : net.OK) (xm : Fin N) (hm : net.mg xm = true) (a : Fin (net.ar xm)) :
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

/-- **W-E5a integrated: merge exclusivity of every behaviour from the
certificate** (no timing condition on the arms: `Events4.merge_excl`). -/
theorem exclOK_of_cert (hOK : net.OK) (hX : ExclCert net) : x.ExclOK := by
  intro xm s hm
  obtain ⟨hle, h2⟩ := hX xm hm
  rcases Nat.lt_or_ge (net.ar xm) 2 with hlt | hge
  · have := fodd_le (net.ar xm) (fun p => x.P xm p s); omega
  have har : net.ar xm = 2 := by omega
  obtain ⟨S, g, a0, a1, ew, hne, hew, htok, hU0, hU1⟩ := h2 har
  obtain ⟨d0, hd0⟩ := x.ubound hOK xm hm a0 S g false hU0
  obtain ⟨d1, hd1⟩ := x.ubound hOK xm hm a1 S g true hU1
  let dm := min d0 d1
  let L := wLo4 b ew
  let σ : Nat → Nat := fun s => if 1 ≤ s - dm - L then x.F xm (s - dm - L) else 0
  have hσ : ∀ t, 0 < t → σ t < t := by
    intro t ht; simp only [σ]; split
    · have := x.F_lt xm (t - dm - L) (by omega); omega
    · exact ht
  have key := merge_excl (sel g) (fun s => x.P xm a0 s) (fun s => x.P xm a1 s)
    (fun s => x.M (s - dm) S) σ hσ
    (fun a c h => x.P_mono xm a0 h) (fun a c h => x.P_mono xm a1 h)
    (fun t => Nat.le_trans (hd0 t) (filt_mono _ _ (x.M_mono _ _ _ (by omega))))
    (fun t => Nat.le_trans (hd1 t) (filt_mono _ _ (x.M_mono _ _ _ (by omega))))
    (by
      intro t _
      have hw := x.walk_le hOK ew S xm hew (t - dm)
      simp only [σ]
      split
      · rename_i hv
        rw [x.M_eq _ xm hv] at hw
        unfold E at hw; simp only [hm, ite_true] at hw
        rw [(fin2_sum har (fun p => x.P xm p (x.F xm (t - dm - L))) a0 a1 hne).1] at hw
        have : t - dm - wLo4 b ew = t - dm - L := rfl
        omega
      · rename_i hv
        have : t - dm - wLo4 b ew = 0 := by simp only [L] at hv; omega
        rw [this, x.M_zero] at hw
        omega)
    (x.P_zero_merge hOK xm hm a0) (x.P_zero_merge hOK xm hm a1) s
  exact (fin2_sum har (fun p => x.P xm p s) a0 a1 hne).2 key

/-- **The verdict as a theorem.** For a network that satisfies the structural
side conditions and whose Back, line and merge certificates check, every
behaviour in the bands, for every select sequence satisfying the bundling
hypothesis, with the guarded pins satisfying `GuardOK`, has every node equal to
its reset value flipped `M t j` times at every time: no stage fires out of
turn, no merge loses a token, no delay line skips its matched delay. -/
theorem verdict (hOK : net.OK) {back : (j : Fin N) → Fin (net.ar j) → List (Arc4 net)} (hB : Back4 b back)
    {cyc : Fin N → List (Arc4 net)} (hL : LineCert b cyc) (hX : ExclCert net)
    (hsel : x.SelOK) (hguard : x.GuardOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) :=
  x.safe hOK hsel (x.lineOK_of_cert hOK hL) (x.pinOK_of_back hOK hB) (x.exclOK_of_cert hOK hX) hguard

end Beh4


/-! ## 7. Branch-aware Back walks: R1, R3 and SUB (W-E5c/d integrated) -/

/-- `UArm` with its delay made explicit (the U-bound's delay `d`). -/
def UArmD {N : Nat} {net : Net4 N} (b : Bands4 net) (x : Fin N) (a : Fin (net.ar x)) (S : Fin N) (g : Nat)
    (β : Bool) (d : Nat) : Prop :=
  ∃ (T : Fin N) (q : Fin (net.ar T)) (w : List (Arc4 net)),
    walk4OK net (net.src x a) T w = true ∧ wTok4 net w = 0 ∧ net.mg T = false ∧
    net.pk T q = PK.filt ∧ net.grp T q = g ∧ net.br T q = β ∧ net.src T q = S ∧ net.off T q = 0 ∧
    d = b.loP x a + wLo4 b w + b.loF T + b.loP T q

/-- **Branch-aware walk derivations** (a certificate about the network and its
bands only). `WD a none bb d t`: `a`'s count is at most `bb`'s `d` earlier plus
`t`; `WD S (some (g, β)) bb d t`: the branch-`β` count (group `g`) of `S` is.
Steps: `r1` through a stage pin, `fpin` through a filtered stage pin (enters the
branch context), `r3` across a merge whose arms are the two branches of one
source (`Events4.reconv`), `sub` from a source through its acknowledge merge
into the branch-`β` arm (`Events4.sub_step`), `lift` (a branch count is at most
the count). -/
inductive WD {N : Nat} {net : Net4 N} (b : Bands4 net) : Fin N → Option (Nat × Bool) → Fin N → Nat → Nat → Prop
  | refl (a : Fin N) : WD b a none a 0 0
  | r1 (k : Fin N) (p : Fin (net.ar k)) (bb : Fin N) (d t : Nat) :
      net.mg k = false → net.pk k p ≠ PK.guard → WD b (net.src k p) none bb d t →
      WD b k none bb (b.loF k + b.loP k p + d) (net.off k p + t)
  | fpin (k : Fin N) (p : Fin (net.ar k)) (bb : Fin N) (d t : Nat) :
      net.mg k = false → net.pk k p = PK.filt → WD b (net.src k p) (some (net.grp k p, net.br k p)) bb d t →
      WD b k none bb (b.loF k + b.loP k p + d) (net.off k p + t)
  | r3 (x S : Fin N) (g : Nat) (a0 a1 : Fin (net.ar x)) (d0 d1 : Nat) (bb : Fin N) (d t : Nat) :
      net.mg x = true → net.ar x = 2 → a0 ≠ a1 → UArmD b x a0 S g false d0 → UArmD b x a1 S g true d1 →
      WD b S none bb d t → WD b x none bb (b.loF x + min d0 d1 + d) t
  | lift (S : Fin N) (g : Nat) (β : Bool) (bb : Fin N) (d t : Nat) :
      WD b S none bb d t → WD b S (some (g, β)) bb d t
  | sub (S x : Fin N) (g : Nat) (β : Bool) (aβ aν : Fin (net.ar x)) (d1 t1 d' d2 t2 : Nat) (bb : Fin N) :
      net.mg x = true → net.ar x = 2 → aβ ≠ aν → WD b S none x d1 t1 → UArmD b x aν S g (!β) d' →
      WD b (net.src x aβ) none bb d2 t2 → WD b S (some (g, β)) bb (d1 + b.loF x + b.loP x aβ + d2) (t1 + t2)

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

/-- Semantics of a walk derivation. -/
def Sem (a : Fin N) (c : Option (Nat × Bool)) (bb : Fin N) (d t : Nat) : Prop :=
  match c with
  | none => ∀ u, x.M u a ≤ x.M (u - d) bb + t
  | some (g, β) => ∀ u, filt (sel g) β (x.M u a) ≤ x.M (u - d) bb + t

theorem ubound_d (hOK : net.OK) (xm : Fin N) (hm : net.mg xm = true) (a : Fin (net.ar xm)) (S : Fin N)
    (g : Nat) (β : Bool) (d : Nat) (hU : UArmD b xm a S g β d) :
    ∀ s, x.P xm a s ≤ filt (sel g) β (x.M (s - d) S) := by
  obtain ⟨T, q, w, hw, htok, hmT, hk, hg, hb, hsrc, hoff, hd⟩ := hU
  subst hsrc; subst hg; subst hb; subst hd
  obtain ⟨_, _, hkg, hoffa⟩ := (hOK xm a).2.2.2.1 hm
  intro s
  have h1 := x.P_le hOK xm a hkg s
  have h2 := x.walk_le hOK w _ _ hw (s - b.loP xm a)
  have h3 := x.M_le_pin T hmT q (s - b.loP xm a - wLo4 b w)
  have h4 := x.P_filt_le T q hk (x.F T (s - b.loP xm a - wLo4 b w))
  have a1 := (x.wF T).le_late (s - b.loP xm a - wLo4 b w)
  have h5 := x.M_mono (s - (b.loP xm a + wLo4 b w + b.loF T + b.loP T q)) (net.src T q)
    (x.F T (s - b.loP xm a - wLo4 b w) - b.loP T q) (by omega)
  have h6 := filt_mono (sel (net.grp T q)) (net.br T q) h5
  omega

/-- The count of a binary merge at a positive time is the sum of its arms at its sample. -/
theorem M_merge (xm : Fin N) (hm : net.mg xm = true) (har : net.ar xm = 2) (a0 a1 : Fin (net.ar xm))
    (hne : a0 ≠ a1) (u : Nat) (hu : 1 ≤ u) :
    x.M u xm = x.P xm a0 (x.F xm u) + x.P xm a1 (x.F xm u) := by
  rw [x.M_eq u xm hu]; unfold E; simp only [hm, ite_true]
  exact (fin2_sum har _ a0 a1 hne).1

/-- **Soundness of the branch-aware walk derivations.** -/
theorem wd_sound (hOK : net.OK) {a : Fin N} {c : Option (Nat × Bool)} {bb : Fin N} {d t : Nat}
    (h : WD b a c bb d t) : x.Sem a c bb d t := by
  induction h with
  | refl a => intro u; simp
  | r1 k p bb d t hm hk _ ih =>
    intro u
    have h1 := x.M_le_pin k hm p u
    have h2 := x.P_le hOK k p hk (x.F k u)
    have a1 := (x.wF k).le_late u
    have h3 := x.M_mono (u - b.loF k - b.loP k p) (net.src k p) (x.F k u - b.loP k p) (by omega)
    have h4 := ih (u - b.loF k - b.loP k p)
    have e : u - b.loF k - b.loP k p - d = u - (b.loF k + b.loP k p + d) := by omega
    rw [e] at h4; omega
  | fpin k p bb d t hm hk _ ih =>
    intro u
    have h1 := x.M_le_pin k hm p u
    have h2 := x.P_filt_le k p hk (x.F k u)
    have a1 := (x.wF k).le_late u
    have h3 := x.M_mono (u - b.loF k - b.loP k p) (net.src k p) (x.F k u - b.loP k p) (by omega)
    have h3' := filt_mono (sel (net.grp k p)) (net.br k p) h3
    have h4 := ih (u - b.loF k - b.loP k p)
    have e : u - b.loF k - b.loP k p - d = u - (b.loF k + b.loP k p + d) := by omega
    rw [e] at h4; omega
  | r3 xm S g a0 a1 d0 d1 bb d t hm har hne hU0 hU1 _ ih =>
    intro u
    rcases Nat.eq_zero_or_pos u with hu0 | hu1
    · subst hu0; rw [x.M_zero]; exact Nat.zero_le _
    have hs := x.M_merge xm hm har a0 a1 hne u hu1
    have u0 := x.ubound_d hOK xm hm a0 S g false d0 hU0 (x.F xm u)
    have u1 := x.ubound_d hOK xm hm a1 S g true d1 hU1 (x.F xm u)
    have a1 := (x.wF xm).le_late u
    have rc := Formal.Core.XAudit.Events4.reconv (sel g) _ _ _ _ (x.M (u - b.loF xm - min d0 d1) S) u0 u1
      (x.M_mono _ _ _ (by omega)) (x.M_mono _ _ _ (by omega))
    have h4 := ih (u - b.loF xm - min d0 d1)
    have e : u - b.loF xm - min d0 d1 - d = u - (b.loF xm + min d0 d1 + d) := by omega
    rw [e] at h4; omega
  | lift S g β bb d t _ ih =>
    intro u
    have := filt_le (sel g) β (x.M u S); have := ih u; omega
  | sub S xm g β aβ aν d1 t1 d' d2 t2 bb hm har hne _ hU _ ih1 ih2 =>
    intro u
    have hw := ih1 u
    have e : u - (d1 + b.loF xm + b.loP xm aβ + d2) = u - d1 - b.loF xm - b.loP xm aβ - d2 := by omega
    rw [e]
    obtain ⟨_, _, hkg, hoffa⟩ := (hOK xm aβ).2.2.2.1 hm
    rcases Nat.eq_zero_or_pos (u - d1) with hv0 | hv1
    · rw [hv0, x.M_zero] at hw
      have := filt_le (sel g) β (x.M u S); omega
    have hs := x.M_merge xm hm har aβ aν hne (u - d1) hv1
    have a1 := (x.wF xm).le_late (u - d1)
    have uν := x.ubound_d hOK xm hm aν S g (!β) d' hU (x.F xm (u - d1))
    have mle : x.M (x.F xm (u - d1) - d') S ≤ x.M u S := x.M_mono _ _ _ (by omega)
    have hpβ := x.P_le hOK xm aβ hkg (x.F xm (u - d1))
    have h3 := x.M_mono (u - d1 - b.loF xm - b.loP xm aβ) (net.src xm aβ) (x.F xm (u - d1) - b.loP xm aβ) (by omega)
    have h4 := ih2 (u - d1 - b.loF xm - b.loP xm aβ)
    have hadd := filt_add (sel g) (x.M u S)
    have hmν := filt_mono (sel g) (!β) mle
    cases β
    · simp only [Bool.not_false] at uν hmν; omega
    · simp only [Bool.not_true] at uν hmν; omega

end Beh4

/-- **Back with branch-aware walks** (R1 / R3 / SUB): every unguarded stage pin
has a walk derivation from its source (in the pin's branch context when it is
filtered) back to the stage, with (pin + walk) at most one token, no faster than
the slowest own feedback. -/
def BackW {N : Nat} {net : Net4 N} (b : Bands4 net) : Prop :=
  ∀ j p, net.mg j = false → net.pk j p ≠ PK.guard → ∃ d t,
    WD b (net.src j p) (if net.pk j p = PK.filt then some (net.grp j p, net.br j p) else none) j d t ∧
    t + net.off j p ≤ 1 ∧ b.hiQ j ≤ b.loP j p + d

namespace Beh4
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

theorem pinOK_of_backW (hOK : net.OK) (hB : BackW b) : x.PinOK := by
  intro j p s hm hk
  obtain ⟨d, t, hw, htok, hrace⟩ := hB j p hm hk
  have hsem := x.wd_sound hOK hw
  have a4 := (x.wQ j).early_le s
  have hq := x.M_mono (x.Q j s) j (s - b.loP j p - d) (by omega)
  by_cases hf : net.pk j p = PK.filt
  · simp only [Sem, hf, ite_true] at hsem
    have h0 := x.P_filt_le j p hf s
    have h1 := hsem (s - b.loP j p)
    omega
  · simp only [Sem, hf, ite_false] at hsem
    have h0 := x.P_le hOK j p hk s
    have h1 := hsem (s - b.loP j p)
    omega

/-- **The verdict with branch-aware Back walks.** -/
theorem verdictW (hOK : net.OK) (hB : BackW b)
    {cyc : Fin N → List (Arc4 net)} (hL : LineCert b cyc) (hX : ExclCert net)
    (hsel : x.SelOK) (hguard : x.GuardOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) :=
  x.safe hOK hsel (x.lineOK_of_cert hOK hL) (x.pinOK_of_backW hOK hB) (x.exclOK_of_cert hOK hX) hguard

end Beh4

/-! ## 6. Negative controls -/

/-- NEGATIVE CONTROL (line, indexed form): two copies with counts 1 and 3 (a
gap: `ContigF` fails) read AND = 1, while `andCnt 1 3 = 2` says low. -/
theorem andF_neg :
    fall 2 (fun i => ph false (if i.val = 0 then 1 else 3)) = true ∧
    ph false (andCnt (fmin 2 (fun i => if i.val = 0 then 1 else 3)) (fmax 2 (fun i => if i.val = 0 then 1 else 3))) = false ∧
    ¬ ContigF 2 (fun i => if i.val = 0 then 1 else 3) := by
  refine ⟨by decide, by decide, fun h => ?_⟩
  obtain ⟨i, hi⟩ := h 2 (by decide) (by decide)
  revert hi; revert i; decide

/-- NEGATIVE CONTROL (merge, indexed form): two arms high together read OR = 1
while the summed count 2 is even (`ExclOK` fails: `fodd = 2`). -/
theorem fany_neg :
    fany 2 (fun _ => ph false 1) = true ∧ ph false (fsum 2 (fun _ => 1)) = false ∧ fodd 2 (fun _ => 1) = 2 := by
  decide

/-- NEGATIVE CONTROL (guards): a guarded pin that still shows the previous
transaction's high while its guard has advanced fires the C-element; without
`hguard`, `cel_guards`' conclusion is false. -/
theorem cel_guards_neg :
    cel (n := 2) (fun _ => true) false = true ∧ ph false (fmin 2 (fun i => if i.val = 0 then 1 else 0)) = false := by
  decide

end Formal.Core.XAudit.Events5
