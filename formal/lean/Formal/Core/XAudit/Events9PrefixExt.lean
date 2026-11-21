import Formal.Core.XAudit.Events9Prefix

/-!
# Formal.Core.XAudit.Events9PrefixExt — behaviours that satisfy their equations only on a prefix

Probe E8Causal (shard A). Notes: `formal/notes/A-e8causal.md` §4.

`Events9Prefix.safe8_upto` concludes the link on `[0, t0]` for a full `Beh7`. A discharge of
H_ARB by induction on time (E8Arb's "uncontested" route) has, at stage `t0`, node signals that
satisfy the node equations only on `[0, t0]` (the virtual arbiter core is matched to the real
cell only up to `t0`). This file packages such a prefix behaviour and shows the link still
holds on `[0, t0]`, with counts that do not depend on `t0`:

* `Beh7P net b sel t0`: `Beh7`'s data with `hc`, `hpin`, `hq` required only at times `≤ t0`.
* `pinF`, `stepF`: the right-hand sides of `Beh7.hpin` / `Beh7.hc`.
* `cx`, **`Beh7P.ext`**: the extension of the signals after `t0` by the node equations (well
  founded: `F t < t`, `G s, Q s < t`); `ext` is a `Beh7` with the SAME warps, reset and guarded
  count, equal to the given signals on `[0, t0]` (`ext_c`).
* **`M_congr`**: two `Beh7` with the same `F`, `G`, `r`, `gc` have the same counts `M`. So
  every stage of an induction that keeps the warps fixed talks about ONE count function.
* **`link_upto_P`**: `safe8_upto` for a prefix behaviour: SelOK, LineOK, PinOK, ExclOK and the
  guard facts of the extension at the samples `< t0` give `c j t = ph (v j) (M t j)` for
  `t ≤ t0`, for the prefix behaviour's own signals.

NOT covered: building a `Beh7P` from SatPin plus a PREFIX form of H_ARB over a parsed netlist
(the real nodes' `ndReal7` read virtual sources through `hW` at all times), and the arbiter
argument itself (E8ArbFix's `core_of_settle` in prefix form).
-/

namespace Formal.Core.XAudit.Events9PrefixExt

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9Prefix

section
variable {N : Nat} (net : Net4 N)

/-- What a pin reads (the right-hand side of `Beh7.hpin`), for signals `cc`. -/
def pinF (cc : Fin N → Sig) (G : (j : Fin N) → (p : Fin (net.ar j)) → Fin (net.nc j p) → Nat → Nat)
    (sv : (j : Fin N) → Fin (net.ar j) → Sig) (j : Fin N) (p : Fin (net.ar j)) (t : Nat) : Bool :=
  net.inv j p ^^
    match net.pk j p with
    | PK.multi => if net.op j p then fall (net.nc j p) (fun i => cc (net.src j p) (G j p i t))
                  else fany (net.nc j p) (fun i => cc (net.src j p) (G j p i t))
    | PK.guard => if net.op j p then fall (net.nc j p) (fun i => cc (net.src j p) (G j p i t))
                  else fany (net.nc j p) (fun i => cc (net.src j p) (G j p i t))
    | PK.filt => fany (net.nc j p) (fun i => cc (net.src j p) (G j p i t) && (sv j p t == net.br j p))
    | PK.plain => fany (net.nc j p) (fun i => cc (net.src j p) (G j p i t))

/-- A node's value from its pins, feedback and reset reads (the right-hand side of `Beh7.hc`). -/
def stepF (j : Fin N) (pv : Fin (net.ar j) → Bool) (qv rv : Bool) : Bool :=
  if net.mg j then fany (net.ar j) pv
  else if rv then net.v j else cel (fun p => pv p ^^ net.neg j p) qv

theorem pinF_congr {cc cc' : Fin N → Sig} {G : (j : Fin N) → (p : Fin (net.ar j)) → Fin (net.nc j p) → Nat → Nat}
    {sv : (j : Fin N) → Fin (net.ar j) → Sig} {j : Fin N} {p : Fin (net.ar j)} {t : Nat}
    (h : ∀ i, cc (net.src j p) (G j p i t) = cc' (net.src j p) (G j p i t)) :
    pinF net cc G sv j p t = pinF net cc' G sv j p t := by
  unfold pinF
  simp only [h]

end

/-- **A prefix behaviour**: `Beh7`'s data, with the node equations `hc`, `hpin`, `hq` only at
times `≤ t0` (warps, reset, skew, guarded count: at all times). -/
structure Beh7P {N : Nat} (net : Net4 N) (b : Bands4 net) (sel : Nat → Nat → Bool) (t0 : Nat) where
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
  hc : ∀ j t, t ≤ t0 → c j t = stepF net j (fun p => pin j p (F j t)) (q j (F j t)) (r j (F j t))
  hpin : ∀ j p t, t ≤ t0 → pin j p t = pinF net c G sv j p t
  hq : ∀ j t, t ≤ t0 → q j t = c j (Q j t)
  r0 : ∀ j, r j 0 = true
  ranti : ∀ j a b, a ≤ b → r j b = true → r j a = true
  hskew : ∀ j p (i i' : Fin (net.nc j p)), i'.val = i.val + 1 → ∀ s,
    G j p i s ≤ G j p i' s + b.dw j p i.val ∧ G j p i' s ≤ G j p i s + b.dw j p i.val
  mg0 : ∀ j, net.mg j = true → c j 0 = false
  gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s

namespace Beh7P
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} {t0 : Nat} (x : Beh7P net b sel t0)

/-- The extended signals: the given ones on `[0, t0]`, the node equations after `t0`. -/
noncomputable def cx : Nat → Fin N → Bool
  | t, j =>
    if t ≤ t0 then x.c j t else
      stepF net j
        (fun p => pinF net (fun k u => if u < t then cx u k else false) x.G x.sv j p (x.F j t))
        (if x.Q j (x.F j t) < t then cx (x.Q j (x.F j t)) j else false) (x.r j (x.F j t))
termination_by t => t
decreasing_by all_goals assumption

theorem cx_le {t : Nat} (ht : t ≤ t0) (j : Fin N) : x.cx t j = x.c j t := by
  rw [cx]; simp [ht]

theorem F_lt (j : Fin N) (t : Nat) (ht : 1 ≤ t) : x.F j t < t := by
  have := (x.wF j).le_late t; have := x.loF1 j; omega

theorem F_le (j : Fin N) (t : Nat) : x.F j t ≤ t := by
  have := (x.wF j).le_late t; omega

theorem G_le (j : Fin N) (p : Fin (net.ar j)) (i : Fin (net.nc j p)) (s : Nat) : x.G j p i s ≤ s := by
  have := (x.wG j p i).le_late s; omega

theorem Q_le (j : Fin N) (s : Nat) : x.Q j s ≤ s := by
  have := (x.wQ j).le_late s; omega

theorem cx_gt {t : Nat} (ht : t0 < t) (j : Fin N) :
    x.cx t j = stepF net j (fun p => pinF net (fun k u => x.cx u k) x.G x.sv j p (x.F j t))
      (x.cx (x.Q j (x.F j t)) j) (x.r j (x.F j t)) := by
  have hF := x.F_lt j t (by omega)
  rw [cx, if_neg (by omega)]
  have hQ : x.Q j (x.F j t) < t := Nat.lt_of_le_of_lt (x.Q_le j _) hF
  rw [if_pos hQ]
  congr 1
  funext p
  apply pinF_congr
  intro i
  have := x.G_le j p i (x.F j t)
  simp only [show x.G j p i (x.F j t) < t by omega, ite_true]

/-- **The extension**: a full `Beh7` with the prefix behaviour's warps, reset, select reads
and guarded count, whose signals are the extended ones. -/
noncomputable def ext : Beh7 net b sel where
  c := fun j t => x.cx t j
  pin := fun j p t => pinF net (fun k u => x.cx u k) x.G x.sv j p t
  q := fun j t => x.cx (x.Q j t) j
  r := x.r
  sv := x.sv
  gc := x.gc
  F := x.F
  G := x.G
  Q := x.Q
  wF := x.wF
  wG := x.wG
  wQ := x.wQ
  loF1 := x.loF1
  loC1 := x.loC1
  loQ1 := x.loQ1
  hc := fun j t => by
    show x.cx t j = stepF net j (fun p => pinF net (fun k u => x.cx u k) x.G x.sv j p (x.F j t))
      (x.cx (x.Q j (x.F j t)) j) (x.r j (x.F j t))
    by_cases ht : t ≤ t0
    · rw [x.cx_le ht, x.hc j t ht]
      have hFt : x.F j t ≤ t0 := Nat.le_trans (x.F_le j t) ht
      have hQt : x.Q j (x.F j t) ≤ t0 := Nat.le_trans (x.Q_le j _) hFt
      rw [x.hq j _ hFt, ← x.cx_le hQt]
      congr 1
      funext p
      rw [x.hpin j p _ hFt]
      apply pinF_congr
      intro i
      exact (x.cx_le (Nat.le_trans (x.G_le j p i _) hFt) _).symm
    · exact x.cx_gt (by omega) j
  hpin := fun j p t => rfl
  hq := fun j t => rfl
  r0 := x.r0
  ranti := x.ranti
  hskew := x.hskew
  mg0 := fun j hm => by
    show x.cx 0 j = false
    rw [x.cx_le (Nat.zero_le _)]; exact x.mg0 j hm
  gcmono := x.gcmono

theorem ext_c {t : Nat} (ht : t ≤ t0) (j : Fin N) : x.ext.c j t = x.c j t := x.cx_le ht j

theorem ext_F : x.ext.F = x.F := rfl
theorem ext_G : x.ext.G = x.G := rfl
theorem ext_Q : x.ext.Q = x.Q := rfl
theorem ext_r : x.ext.r = x.r := rfl
theorem ext_gc : x.ext.gc = x.gc := rfl

end Beh7P

/-! ## Counts depend only on warps, reset and guarded count -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool}

/-- **`M_congr`**: two behaviours with the same sample warps `F`, copy warps `G`, reset reads
`r` and guarded counts `gc` have the same counts. -/
theorem M_congr (x y : Beh7 net b sel) (hF : x.F = y.F) (hG : x.G = y.G) (hr : x.r = y.r)
    (hgc : x.gc = y.gc) : ∀ t j, x.M t j = y.M t j := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    rcases Nat.eq_zero_or_pos t with h0 | h1
    · subst h0; rw [x.M_zero, y.M_zero]
    · rw [x.M_eq t j h1, y.M_eq t j h1]
      have hs : x.F j t = y.F j t := by rw [hF]
      have hlt : x.F j t < t := x.F_lt j t h1
      have hcm : ∀ p, x.cm j p (x.F j t) = y.cm j p (y.F j t) := by
        intro p; funext i
        unfold Beh7.cm
        rw [← hs]
        have hGe : x.G j p i (x.F j t) = y.G j p i (x.F j t) := by rw [hG]
        rw [← hGe]
        exact ih _ (Nat.lt_of_le_of_lt (by have := (x.wG j p i).le_late (x.F j t); omega) hlt) _
      have hP : ∀ p, x.P j p (x.F j t) = y.P j p (y.F j t) := by
        intro p
        unfold Beh7.P Beh7.pc
        rw [hcm p, ← hs, hgc]
      unfold Beh7.E
      simp only [hP, ← hs, hr]

end

/-! ## The link on the prefix -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} {t0 : Nat}

/-- **`link_upto_P`**: `safe8_upto` for a prefix behaviour. If its extension satisfies SelOK,
LineOK, PinOK, ExclOK and the guard facts at the samples `< t0` (count facts of the extension,
whose counts depend only on the warps, `r` and `gc`: `M_congr`), then the prefix behaviour's
own signals satisfy the count/wire link on `[0, t0]`. -/
theorem link_upto_P (x : Beh7P net b sel t0) (hOK : net.OK7)
    (hsel : ∀ s, s < t0 → SelAt x.ext s)
    (hline : ∀ j p s, s < t0 → net.pk j p = PK.multi → ContigF (net.nc j p) (x.ext.cm j p s))
    (hpinok : ∀ j p s, s < t0 → net.mg j = false → net.pk j p ≠ PK.guard →
      x.ext.P j p s ≤ x.ext.M (x.ext.Q j s) j + 1)
    (hexcl : ∀ j s, s < t0 → net.mg j = true → fodd (net.ar j) (fun p => x.ext.P j p s) ≤ 1)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.ext.gc j p s = gcnt net sel j p (x.ext.cm j p s))
    (hcert : ∀ j p, net.pk j p = PK.guard → cg j p = true → GStruct net j p ∧ GuardCntB x.ext t0 j p)
    (hres : ∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPinB x.ext t0 j p) :
    ∀ t, t ≤ t0 → ∀ j, x.c j t = ph (net.v j) (x.ext.M t j) := by
  intro t ht j
  rw [← x.ext_c ht j]
  exact safe8_upto x.ext hOK t0 hsel hline hpinok hexcl cg hgc hcert hres t ht j

end

end Formal.Core.XAudit.Events9PrefixExt
