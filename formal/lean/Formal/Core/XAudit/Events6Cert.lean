import Formal.Core.XAudit.Events5

/-!
# Formal.Core.XAudit.Events6Cert — checkable certificates for `Beh4` and the verdict with residuals

Probe A-events6 (W-E4n, the certificate half). See `formal/notes/A-events6.md`.

`Events5.verdictW` needs `BackW`, `LineCert` and `ExclCert`, which quantify over
walk DERIVATIONS (`WD`, an inductive `Prop`). An executable cannot evaluate a
`Prop` with existentials; it can evaluate a Boolean checker over certificate DATA.
This file gives:

* `DW` (data) with `DW.valid` (a `Bool`) and **`DW.sound`**: a valid derivation is
  a `WD` derivation from `DW.st` to `DW.en` with delay `DW.d` and tokens `DW.tk`.
  `UA` (data) with `UA.ok` and **`UA.sound`**: a `UArmD` certificate.
* `ExclW` / `exclOK_one`: merge exclusivity with the walk `S → x` a `WD`
  derivation (R1/R3/SUB) instead of an R1-only walk (`Events5.ExclCert` asks
  `walk4OK`); the proof is `Events5.exclOK_of_cert`'s, through `wd_sound`.
* `LineW` / `contig_one`: delay-line contiguity from a closed `WD` walk with at
  most one token (the source's per-window bound), as `Events5.lineOK_of_cert`.
* **`verdictR`**: the verdict with RESIDUAL obligations. Each stage pin, merge
  and line pin is either certified (by the checker) or carries its count-level
  obligation as an explicit hypothesis. With no residual item this is
  `Events5.verdictW`'s conclusion; on gcd the residual items are the cascaded
  arbiter (H_ARB does not compose) and whatever fails a margin at that corner.
-/

namespace Formal.Core.XAudit.Events6

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (fmin)
open Formal.Core.XAudit.Events3 (filt filt_mono filt_add)
open Formal.Core.XAudit.Events4 (merge_excl filt_le)
open Formal.Core.XAudit.Events5

variable {N : Nat} {net : Net4 N}

/-! ## 1. Nat-indexed views of a network (for certificate data) -/

def loFn (b : Bands4 net) (k : Nat) : Nat := if h : k < N then b.loF ⟨k, h⟩ else 0

def loPn (b : Bands4 net) (k p : Nat) : Nat :=
  if h : k < N then if hp : p < net.ar ⟨k, h⟩ then b.loP ⟨k, h⟩ ⟨p, hp⟩ else 0 else 0

def offn (net : Net4 N) (k p : Nat) : Nat :=
  if h : k < N then if hp : p < net.ar ⟨k, h⟩ then net.off ⟨k, h⟩ ⟨p, hp⟩ else 0 else 0

/-- An R1 walk given by `(node, pin)` pairs (`walk4OK` on raw indices). -/
def walkN (net : Net4 N) : Nat → Nat → List (Nat × Nat) → Bool
  | a, bb, [] => a == bb
  | a, bb, (k, p) :: w =>
      if h : k < N then if hp : p < net.ar ⟨k, h⟩ then
        k == a && !net.mg ⟨k, h⟩ && !(net.pk ⟨k, h⟩ ⟨p, hp⟩ == PK.guard) &&
          walkN net (net.src ⟨k, h⟩ ⟨p, hp⟩).val bb w
      else false else false

def tokN (net : Net4 N) : List (Nat × Nat) → Nat
  | [] => 0
  | (k, p) :: w => offn net k p + tokN net w

def loN (b : Bands4 net) : List (Nat × Nat) → Nat
  | [] => 0
  | (k, p) :: w => loFn b k + loPn b k p + loN b w

theorem walkN_sound (b : Bands4 net) : ∀ (w : List (Nat × Nat)) (a bb : Fin N), walkN net a.val bb.val w = true →
    ∃ w' : List (Arc4 net), walk4OK net a bb w' = true ∧ wTok4 net w' = tokN net w ∧ wLo4 b w' = loN b w
  | [], a, bb, h => by
      simp only [walkN, beq_iff_eq] at h
      exact ⟨[], by simp [walk4OK, Fin.ext_iff, h], rfl, rfl⟩
  | (k, p) :: w, a, bb, h => by
      simp only [walkN] at h
      split at h
      · rename_i hk
        split at h
        · rename_i hp
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
          obtain ⟨⟨⟨hka, hm⟩, hg⟩, hw⟩ := h
          obtain ⟨w', h1, h2, h3⟩ := walkN_sound b w (net.src ⟨k, hk⟩ ⟨p, hp⟩) bb hw
          refine ⟨⟨⟨k, hk⟩, ⟨p, hp⟩⟩ :: w', ?_, ?_, ?_⟩
          · simp only [walk4OK, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true']
            exact ⟨⟨⟨Fin.ext hka, hm⟩, by simpa using hg⟩, h1⟩
          · simp only [wTok4, tokN, offn, dif_pos hk, dif_pos hp, h2]
          · simp only [wLo4, loN, loFn, loPn, dif_pos hk, dif_pos hp, h3]
        · exact absurd h (by decide)
      · exact absurd h (by decide)

/-! ## 2. U-arm certificates as data -/

/-- A `UArmD` witness: the stage `T`, its filtered pin `q`, the token-free walk. -/
structure UA where
  T : Nat
  q : Nat
  w : List (Nat × Nat)
  /-- direct: the merge arm is itself a filtered pin (no walk) -/
  dir : Bool := false
  deriving Repr, Inhabited

/-- `UA.ok u x a S g β`: decidable check of `UArmD`. -/
def UA.ok (net : Net4 N) (u : UA) (x a S g : Nat) (β : Bool) : Bool :=
  if u.dir then
    if hx : x < N then if ha : a < net.ar ⟨x, hx⟩ then
      net.pk ⟨x, hx⟩ ⟨a, ha⟩ == PK.filt && net.grp ⟨x, hx⟩ ⟨a, ha⟩ == g && net.br ⟨x, hx⟩ ⟨a, ha⟩ == β &&
        (net.src ⟨x, hx⟩ ⟨a, ha⟩).val == S && net.off ⟨x, hx⟩ ⟨a, ha⟩ == 0
    else false else false
  else
  if hx : x < N then if ha : a < net.ar ⟨x, hx⟩ then if hT : u.T < N then if hq : u.q < net.ar ⟨u.T, hT⟩ then
    walkN net (net.src ⟨x, hx⟩ ⟨a, ha⟩).val u.T u.w && tokN net u.w == 0 && !net.mg ⟨u.T, hT⟩ &&
      net.pk ⟨u.T, hT⟩ ⟨u.q, hq⟩ == PK.filt && net.grp ⟨u.T, hT⟩ ⟨u.q, hq⟩ == g &&
      net.br ⟨u.T, hT⟩ ⟨u.q, hq⟩ == β && (net.src ⟨u.T, hT⟩ ⟨u.q, hq⟩).val == S &&
      net.off ⟨u.T, hT⟩ ⟨u.q, hq⟩ == 0
  else false else false else false else false

/-- The U-bound's delay. -/
def UA.dl (b : Bands4 net) (u : UA) (x a : Nat) : Nat :=
  if u.dir then loPn b x a else loPn b x a + loN b u.w + loFn b u.T + loPn b u.T u.q

/-- A U-arm: `Events5.UArmD` (a walk to a filtered stage pin), or the arm is
itself a filtered pin of group `g`, branch `β`, source `S` (a steered merge arm:
`bd_cond_br`'s acknowledge OR reads the two steer halves directly). -/
def UArmX (b : Bands4 net) (x : Fin N) (a : Fin (net.ar x)) (S : Fin N) (g : Nat) (β : Bool) (d : Nat) : Prop :=
  UArmD b x a S g β d ∨
    (net.pk x a = PK.filt ∧ net.grp x a = g ∧ net.br x a = β ∧ net.src x a = S ∧ net.off x a = 0 ∧ d = b.loP x a)

theorem UA.sound (b : Bands4 net) (u : UA) (x : Fin N) (a : Fin (net.ar x)) (S : Fin N) (g : Nat) (β : Bool)
    (h : u.ok net x.val a.val S.val g β = true) : UArmX b x a S g β (u.dl b x.val a.val) := by
  unfold UA.ok at h
  cases hd : u.dir
  · rw [hd] at h; simp only [Bool.false_eq_true, ite_false] at h
    left
    rw [dif_pos x.isLt, dif_pos (show a.val < net.ar ⟨x.val, x.isLt⟩ from a.isLt)] at h
    split at h
    · rename_i hT
      split at h
      · rename_i hq
        simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨hw, htok⟩, hm⟩, hk⟩, hg⟩, hb⟩, hs⟩, ho⟩ := h
        obtain ⟨w', h1, h2, h3⟩ := walkN_sound b u.w (net.src x a) ⟨u.T, hT⟩ hw
        refine ⟨⟨u.T, hT⟩, ⟨u.q, hq⟩, w', h1, by rw [h2, htok], hm, hk, hg, hb, Fin.ext hs, ho, ?_⟩
        simp only [UA.dl, hd, Bool.false_eq_true, ite_false, loPn, loFn, dif_pos x.isLt, dif_pos a.isLt,
          dif_pos hT, dif_pos hq, h3]
      · exact absurd h (by decide)
    · exact absurd h (by decide)
  · rw [hd] at h; simp only [ite_true] at h
    right
    rw [dif_pos x.isLt, dif_pos (show a.val < net.ar ⟨x.val, x.isLt⟩ from a.isLt)] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨hk, hg⟩, hb⟩, hs⟩, ho⟩ := h
    refine ⟨hk, hg, hb, Fin.ext hs, ho, ?_⟩
    simp only [UA.dl, hd, ite_true, loPn, dif_pos x.isLt, dif_pos a.isLt]

/-- `Events5.WD` with `UArmX` arms (a steered merge arm is its own U-bound). -/
inductive WDX {N : Nat} {net : Net4 N} (b : Bands4 net) : Fin N → Option (Nat × Bool) → Fin N → Nat → Nat → Prop
  | refl (a : Fin N) : WDX b a none a 0 0
  | r1 (k : Fin N) (p : Fin (net.ar k)) (bb : Fin N) (d t : Nat) :
      net.mg k = false → net.pk k p ≠ PK.guard → WDX b (net.src k p) none bb d t →
      WDX b k none bb (b.loF k + b.loP k p + d) (net.off k p + t)
  | fpin (k : Fin N) (p : Fin (net.ar k)) (bb : Fin N) (d t : Nat) :
      net.mg k = false → net.pk k p = PK.filt → WDX b (net.src k p) (some (net.grp k p, net.br k p)) bb d t →
      WDX b k none bb (b.loF k + b.loP k p + d) (net.off k p + t)
  | r3 (x S : Fin N) (g : Nat) (a0 a1 : Fin (net.ar x)) (d0 d1 : Nat) (bb : Fin N) (d t : Nat) :
      net.mg x = true → net.ar x = 2 → a0 ≠ a1 → UArmX b x a0 S g false d0 → UArmX b x a1 S g true d1 →
      WDX b S none bb d t → WDX b x none bb (b.loF x + min d0 d1 + d) t
  | lift (S : Fin N) (g : Nat) (β : Bool) (bb : Fin N) (d t : Nat) :
      WDX b S none bb d t → WDX b S (some (g, β)) bb d t
  | sub (S x : Fin N) (g : Nat) (β : Bool) (aβ aν : Fin (net.ar x)) (d1 t1 d' d2 t2 : Nat) (bb : Fin N) :
      net.mg x = true → net.ar x = 2 → aβ ≠ aν → WDX b S none x d1 t1 → UArmX b x aν S g (!β) d' →
      WDX b (net.src x aβ) none bb d2 t2 → WDX b S (some (g, β)) bb (d1 + b.loF x + b.loP x aβ + d2) (t1 + t2)

namespace Beh4F
variable {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

theorem ubound_x (hOK : net.OK) (xm : Fin N) (hm : net.mg xm = true) (a : Fin (net.ar xm)) (S : Fin N)
    (g : Nat) (β : Bool) (d : Nat) (hU : UArmX b xm a S g β d) :
    ∀ s, x.P xm a s ≤ filt (sel g) β (x.M (s - d) S) := by
  rcases hU with hU | ⟨hk, hg, hb, hs, ho, hd⟩
  · exact x.ubound_d hOK xm hm a S g β d hU
  · intro s
    have := x.P_filt_le xm a hk s
    rw [hg, hb, hs, ho] at this; rw [hd]; omega

/-- Soundness of `WDX` (as `Events5.Beh4.wd_sound`). -/
theorem wdx_sound (hOK : net.OK) {a : Fin N} {c : Option (Nat × Bool)} {bb : Fin N} {d t : Nat}
    (h : WDX b a c bb d t) : x.Sem a c bb d t := by
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
    have u0 := ubound_x x hOK xm hm a0 S g false d0 hU0 (x.F xm u)
    have u1 := ubound_x x hOK xm hm a1 S g true d1 hU1 (x.F xm u)
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
    have uν := ubound_x x hOK xm hm aν S g (!β) d' hU (x.F xm (u - d1))
    have mle : x.M (x.F xm (u - d1) - d') S ≤ x.M u S := x.M_mono _ _ _ (by omega)
    have hpβ := x.P_le hOK xm aβ hkg (x.F xm (u - d1))
    have h3 := x.M_mono (u - d1 - b.loF xm - b.loP xm aβ) (net.src xm aβ) (x.F xm (u - d1) - b.loP xm aβ) (by omega)
    have h4 := ih2 (u - d1 - b.loF xm - b.loP xm aβ)
    have hadd := filt_add (sel g) (x.M u S)
    have hmν := filt_mono (sel g) (!β) mle
    cases β
    · simp only [Bool.not_false] at uν hmν; omega
    · simp only [Bool.not_true] at uν hmν; omega

end Beh4F

/-! ## 3. Walk derivations as data -/

/-- A branch-aware walk derivation (`Events5.WD`) as data. -/
inductive DW where
  | refl (a : Nat)
  | r1 (k p : Nat) (rest : DW)
  | fpin (k p : Nat) (rest : DW)
  | r3 (x S g a0 a1 : Nat) (u0 u1 : UA) (rest : DW)
  | lift (g : Nat) (β : Bool) (rest : DW)
  | sub (x g : Nat) (β : Bool) (aβ aν : Nat) (w1 : DW) (u : UA) (w2 : DW)
  deriving Repr, Inhabited

namespace DW

/-- start node -/
def st : DW → Nat
  | refl a => a
  | r1 k _ _ => k
  | fpin k _ _ => k
  | r3 x .. => x
  | lift _ _ r => r.st
  | sub _ _ _ _ _ w1 _ _ => w1.st

/-- end node -/
def en : DW → Nat
  | refl a => a
  | r1 _ _ r => r.en
  | fpin _ _ r => r.en
  | r3 _ _ _ _ _ _ _ r => r.en
  | lift _ _ r => r.en
  | sub _ _ _ _ _ _ _ w2 => w2.en

/-- branch context -/
def cx : DW → Option (Nat × Bool)
  | lift g β _ => some (g, β)
  | sub _ g β .. => some (g, β)
  | _ => none

def tk (net : Net4 N) : DW → Nat
  | refl _ => 0
  | r1 k p r => offn net k p + r.tk net
  | fpin k p r => offn net k p + r.tk net
  | r3 _ _ _ _ _ _ _ r => r.tk net
  | lift _ _ r => r.tk net
  | sub _ _ _ _ _ w1 _ w2 => w1.tk net + w2.tk net

def d (b : Bands4 net) : DW → Nat
  | refl _ => 0
  | r1 k p r => loFn b k + loPn b k p + r.d b
  | fpin k p r => loFn b k + loPn b k p + r.d b
  | r3 x _ _ a0 a1 u0 u1 r => loFn b x + min (u0.dl b x a0) (u1.dl b x a1) + r.d b
  | lift _ _ r => r.d b
  | sub x _ _ aβ _ w1 _ w2 => w1.d b + loFn b x + loPn b x aβ + w2.d b

def srcN (net : Net4 N) (k p : Nat) : Nat :=
  if h : k < N then if hp : p < net.ar ⟨k, h⟩ then (net.src ⟨k, h⟩ ⟨p, hp⟩).val else 0 else 0

/-- **The check.** -/
def valid (net : Net4 N) : DW → Bool
  | refl a => decide (a < N)
  | r1 k p r =>
      if h : k < N then if hp : p < net.ar ⟨k, h⟩ then
        !net.mg ⟨k, h⟩ && !(net.pk ⟨k, h⟩ ⟨p, hp⟩ == PK.guard) &&
          r.st == (net.src ⟨k, h⟩ ⟨p, hp⟩).val && r.cx == none && r.valid net
      else false else false
  | fpin k p r =>
      if h : k < N then if hp : p < net.ar ⟨k, h⟩ then
        !net.mg ⟨k, h⟩ && net.pk ⟨k, h⟩ ⟨p, hp⟩ == PK.filt &&
          r.st == (net.src ⟨k, h⟩ ⟨p, hp⟩).val &&
          r.cx == some (net.grp ⟨k, h⟩ ⟨p, hp⟩, net.br ⟨k, h⟩ ⟨p, hp⟩) && r.valid net
      else false else false
  | r3 x S g a0 a1 u0 u1 r =>
      if h : x < N then
        net.mg ⟨x, h⟩ && net.ar ⟨x, h⟩ == 2 && decide (a0 < 2) && decide (a1 < 2) && a0 != a1 &&
          decide (S < N) && u0.ok net x a0 S g false && u1.ok net x a1 S g true && r.st == S && r.cx == none && r.valid net
      else false
  | lift _ _ r => r.cx == none && r.valid net
  | sub x g β aβ aν w1 u w2 =>
      if h : x < N then
        net.mg ⟨x, h⟩ && net.ar ⟨x, h⟩ == 2 && decide (aβ < 2) && decide (aν < 2) && aβ != aν &&
          w1.cx == none && w1.en == x && w1.valid net && u.ok net x aν w1.st g (!β) &&
          w2.st == srcN net x aβ && w2.cx == none && w2.valid net
      else false

theorem cx_lt {D : DW} : D.cx = none ∨ ∃ g β, D.cx = some (g, β) := by
  cases h : D.cx with
  | none => exact Or.inl rfl
  | some v => exact Or.inr ⟨v.1, v.2, rfl⟩

/-- **Soundness of the derivation check.** -/
theorem sound (b : Bands4 net) : ∀ (D : DW), D.valid net = true → ∀ (a bb : Fin N), a.val = D.st → bb.val = D.en →
    WDX b a D.cx bb (D.d b) (D.tk net)
  | refl a', h, a, bb, ha, hb => by
      simp only [st, en] at ha hb
      have : a = bb := Fin.ext (by omega)
      subst this; exact WDX.refl a
  | r1 k p r, h, a, bb, ha, hb => by
      simp only [valid] at h
      split at h
      · rename_i hk
        split at h
        · rename_i hp
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
          obtain ⟨⟨⟨⟨hm, hg⟩, hs⟩, hc⟩, hv⟩ := h
          simp only [st] at ha; simp only [en] at hb
          have e : a = ⟨k, hk⟩ := Fin.ext ha
          subst e
          have ih := sound b r hv (net.src ⟨k, hk⟩ ⟨p, hp⟩) bb hs.symm hb
          rw [hc] at ih
          have hg' : net.pk ⟨k, hk⟩ ⟨p, hp⟩ ≠ PK.guard := by
            intro e; rw [e] at hg; exact absurd hg (by decide)
          have w := WDX.r1 ⟨k, hk⟩ ⟨p, hp⟩ bb _ _ hm hg' ih
          simp only [d, tk, cx, loFn, loPn, offn, dif_pos hk, dif_pos hp]
          exact w
        · exact absurd h (by decide)
      · exact absurd h (by decide)
  | fpin k p r, h, a, bb, ha, hb => by
      simp only [valid] at h
      split at h
      · rename_i hk
        split at h
        · rename_i hp
          simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at h
          obtain ⟨⟨⟨⟨hm, hg⟩, hs⟩, hc⟩, hv⟩ := h
          simp only [st] at ha; simp only [en] at hb
          have e : a = ⟨k, hk⟩ := Fin.ext ha
          subst e
          have ih := sound b r hv (net.src ⟨k, hk⟩ ⟨p, hp⟩) bb hs.symm hb
          rw [hc] at ih
          have w := WDX.fpin ⟨k, hk⟩ ⟨p, hp⟩ bb _ _ hm hg ih
          simp only [d, tk, cx, loFn, loPn, offn, dif_pos hk, dif_pos hp]
          exact w
        · exact absurd h (by decide)
      · exact absurd h (by decide)
  | r3 x S g a0 a1 u0 u1 r, h, a, bb, ha, hb => by
      simp only [valid] at h
      split at h
      · rename_i hx
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, har⟩, h0⟩, h1⟩, hne⟩, hS⟩, hu0⟩, hu1⟩, hs⟩, hc⟩, hv⟩ := h
        simp only [st] at ha; simp only [en] at hb
        have e : a = ⟨x, hx⟩ := Fin.ext ha
        subst e
        have ih := sound b r hv ⟨S, hS⟩ bb hs.symm hb
        rw [hc] at ih
        have h0' : a0 < net.ar ⟨x, hx⟩ := by omega
        have h1' : a1 < net.ar ⟨x, hx⟩ := by omega
        have U0 := UA.sound b u0 ⟨x, hx⟩ ⟨a0, h0'⟩ ⟨S, hS⟩ g false hu0
        have U1 := UA.sound b u1 ⟨x, hx⟩ ⟨a1, h1'⟩ ⟨S, hS⟩ g true hu1
        have w := WDX.r3 ⟨x, hx⟩ ⟨S, hS⟩ g ⟨a0, h0'⟩ ⟨a1, h1'⟩ _ _ bb _ _ hm har
          (fun e => hne (congrArg Fin.val e)) U0 U1 ih
        simp only [d, tk, cx, loFn, dif_pos hx]
        exact w
      · exact absurd h (by decide)
  | lift g β r, h, a, bb, ha, hb => by
      simp only [valid, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hc, hv⟩ := h
      simp only [st] at ha; simp only [en] at hb
      have ih := sound b r hv a bb ha hb
      rw [hc] at ih
      exact WDX.lift a g β bb _ _ ih
  | sub x g β aβ aν w1 u w2, h, a, bb, ha, hb => by
      simp only [valid] at h
      split at h
      · rename_i hx
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne, ne_eq] at h
        obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hm, har⟩, h0⟩, h1⟩, hne⟩, hc1⟩, hen⟩, hv1⟩, hu⟩, hs2⟩, hc2⟩, hv2⟩ := h
        simp only [st] at ha; simp only [en] at hb
        have ih1 := sound b w1 hv1 a ⟨x, hx⟩ ha hen.symm
        rw [hc1] at ih1
        have h0' : aβ < net.ar ⟨x, hx⟩ := by omega
        have h1' : aν < net.ar ⟨x, hx⟩ := by omega
        have ih2 := sound b w2 hv2 (net.src ⟨x, hx⟩ ⟨aβ, h0'⟩) bb
          (by rw [hs2]; simp [srcN, dif_pos hx, dif_pos h0']) hb
        rw [hc2] at ih2
        have U := UA.sound b u ⟨x, hx⟩ ⟨aν, h1'⟩ a g (!β) (by rw [ha]; exact hu)
        have w := WDX.sub a ⟨x, hx⟩ g β ⟨aβ, h0'⟩ ⟨aν, h1'⟩ _ _ _ _ _ bb hm har
          (fun e => hne (congrArg Fin.val e)) ih1 U ih2
        simp only [d, tk, cx, loFn, loPn, dif_pos hx, dif_pos h0']
        exact w
      · exact absurd h (by decide)

end DW

/-! ## 4. Exclusivity and contiguity from `WD` walks -/

/-- Merge exclusivity certificate with a `WD` walk `S → x`. -/
def ExclW (b : Bands4 net) (x : Fin N) : Prop :=
  net.ar x ≤ 1 ∨ (net.ar x = 2 ∧ ∃ (S : Fin N) (g : Nat) (a0 a1 : Fin (net.ar x)) (d t d0 d1 : Nat),
    a0 ≠ a1 ∧ WDX b S none x d t ∧ t ≤ 1 ∧ UArmX b x a0 S g false d0 ∧ UArmX b x a1 S g true d1)

/-- A line pin's certificate: a closed `WD` walk of its source with at most one
token, no faster than every hop window of the line. -/
def LineW (b : Bands4 net) (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  ∃ d t, WDX b (net.src j p) none (net.src j p) d t ∧ t ≤ 1 ∧ ∀ i, i + 1 < net.nc j p → b.dw j p i ≤ d

/-- A stage pin's Back certificate (`Events5.BackW`, per pin). -/
def BackW1 (b : Bands4 net) (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  ∃ d t, WDX b (net.src j p) (if net.pk j p = PK.filt then some (net.grp j p, net.br j p) else none) j d t ∧
    t + net.off j p ≤ 1 ∧ b.hiQ j ≤ b.loP j p + d

namespace Beh4F
variable {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh4 net b sel)

theorem pin_one (hOK : net.OK) (j : Fin N) (p : Fin (net.ar j)) (hk : net.pk j p ≠ PK.guard)
    (hB : BackW1 b j p) (s : Nat) : x.P j p s ≤ x.M (x.Q j s) j + 1 := by
  obtain ⟨d, t, hw, htok, hrace⟩ := hB
  have hsem := wdx_sound x hOK hw
  have a4 := (x.wQ j).early_le s
  have hq := x.M_mono (x.Q j s) j (s - b.loP j p - d) (by omega)
  by_cases hf : net.pk j p = PK.filt
  · simp only [Beh4.Sem, hf, ite_true] at hsem
    have h0 := x.P_filt_le j p hf s
    have h1 := hsem (s - b.loP j p)
    omega
  · simp only [Beh4.Sem, hf, ite_false] at hsem
    have h0 := x.P_le hOK j p hk s
    have h1 := hsem (s - b.loP j p)
    omega

theorem contig_one (hOK : net.OK) (j : Fin N) (p : Fin (net.ar j)) (hL : LineW b j p) (s : Nat) :
    ContigF (net.nc j p) (x.cm j p s) := by
  obtain ⟨d, t, hw, htok, hdw⟩ := hL
  have hsem := wdx_sound x hOK hw
  simp only [Beh4.Sem] at hsem
  have hev : OneEvent (fun t => x.M t (net.src j p)) d := by
    intro u; have := hsem (u + d); rw [Nat.add_sub_cancel] at this; simp only; omega
  have hmono : MonoC (fun t => x.M t (net.src j p)) := fun a c h => x.M_mono _ _ _ h
  apply contigF_chain _ _ (net.nc_pos j p)
  intro i hi
  have hsk := x.hskew j p i ⟨i.val + 1, hi⟩ rfl s
  have hd := hdw i.val hi
  exact close_of_window (fun t => x.M t (net.src j p)) _ hmono hev (x.G j p i s) (x.G j p ⟨i.val + 1, hi⟩ s)
    (by omega) (by omega)

theorem excl_one (hOK : net.OK) (xm : Fin N) (hm : net.mg xm = true) (hX : ExclW b xm) (s : Nat) :
    fodd (net.ar xm) (fun p => x.P xm p s) ≤ 1 := by
  rcases hX with hle | ⟨har, S, g, a0, a1, dW, tW, d0, d1, hne, hew, htok, hU0, hU1⟩
  · have := fodd_le (net.ar xm) (fun p => x.P xm p s); omega
  have hd0 := ubound_x x hOK xm hm a0 S g false d0 hU0
  have hd1 := ubound_x x hOK xm hm a1 S g true d1 hU1
  have hsem := wdx_sound x hOK hew
  simp only [Beh4.Sem] at hsem
  let dm := min d0 d1
  let L := dW
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
      have hw := hsem (t - dm)
      simp only [σ]
      split
      · rename_i hv
        rw [x.M_eq _ xm hv] at hw
        unfold Beh4.E at hw; simp only [hm, ite_true] at hw
        rw [(fin2_sum har (fun p => x.P xm p (x.F xm (t - dm - L))) a0 a1 hne).1] at hw
        omega
      · rename_i hv
        have : t - dm - dW = 0 := by simp only [L] at hv; omega
        rw [this, x.M_zero] at hw
        omega)
    (x.P_zero_merge hOK xm hm a0) (x.P_zero_merge hOK xm hm a1) s
  exact (fin2_sum har (fun p => x.P xm p s) a0 a1 hne).2 key

/-- **The verdict with residual obligations.** `cp`, `cx`, `cl` mark the stage
pins, merges and line pins the checker certified; every certified item carries
its certificate, every other item its count-level obligation as a hypothesis
(`rB`, `rX`, `rL`). Then every node (stage or merge) of the behaviour is its
reset value flipped `M t j` times at every time. With no residual item the
hypotheses `rB rX rL` are vacuous. -/
theorem verdictR (hOK : net.OK)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (hB : ∀ j p, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = true → BackW1 b j p)
    (hX : ∀ xm, net.mg xm = true → cxm xm = true → ExclW b xm)
    (hL : ∀ j p, net.pk j p = PK.multi → cl j p = true → LineW b j p)
    (rB : ∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → x.P j p s ≤ x.M (x.Q j s) j + 1)
    (rX : ∀ xm s, net.mg xm = true → cxm xm = false → fodd (net.ar xm) (fun p => x.P xm p s) ≤ 1)
    (rL : ∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (x.cm j p s))
    (hsel : x.SelOK) (hguard : x.GuardOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  refine x.safe hOK hsel ?_ ?_ ?_ hguard
  · intro j p s hk
    cases hc : cl j p
    · exact rL j p s hk hc
    · exact contig_one x hOK j p (hL j p hk hc) s
  · intro j p s hm hk
    cases hc : cp j p
    · exact rB j p s hm hk hc
    · exact pin_one x hOK j p hk (hB j p hm hk hc) s
  · intro xm s hm
    cases hc : cxm xm
    · exact rX xm s hm hc
    · exact excl_one x hOK xm hm (hX xm hm hc) s

end Beh4F

end Formal.Core.XAudit.Events6
