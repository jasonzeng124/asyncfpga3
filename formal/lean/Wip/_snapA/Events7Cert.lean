import Formal.Core.XAudit.Events7Excl

/-!
# Formal.Core.XAudit.Events7Cert — the derivation LOG, its soundness, and the verdict

Probe A-events7 (rebuilt in E7r). See `formal/notes/A-events7.md`.

A certificate's walk derivations are a flat LOG: line `i` (`Ln`) derives one
judgement (`Jd`) from EARLIER lines (references are indices `< i`). Two kinds:

* **walk** `(false, a, c, bb, d, t)`: `M u a ≤ M (u − d) bb + t` (`c = none`), or
  `filt (sel g) β (M u a) ≤ M (u − d) bb + t` (`c = some (g, β)`);
* **U-bound** `(true, a, some (g, β), bb, d, _)`: `M u a ≤ filt (sel g) β (M (u − d) bb)`.

Rules (`concl` computes the conclusion of a line or rejects it):
`refl`, `r1` (a stage pin, not guarded), `fpin` (a filtered stage pin enters its
label), `lift` (a branch count is at most the count), `uT` (a stage's filtered
pin, offset 0, is a U-bound), `uW` (a token-free walk followed by a U-bound is a
U-bound: so a U-label passes THROUGH a merge's `r3` line, U3), `r3` (a merge of
ANY arity whose arms carry pairwise exclusive labels of one source `S`, each arm
U-bounded directly — a steered arm — or by a U-bound line), `sub` (SUB at a merge
of any arity: from `S` through the merge into one arm, the other arms U-bounded
by labels exclusive with the context label).

* `concl_sound`: if every earlier line holds for a behaviour `x : Beh7`, the
  new line holds (under `Net4.OK7` and SelPart).
* **`runLog_sound`**: every line of an accepted log holds, for every behaviour.
* `backOK7` / `lineOK7` / `exclOK7` (Bool, STRICT margins) with soundness, and
  **`verdict7`** (`Beh7.safe` with each item certified from the log or carried
  as its count-level obligation).
-/

namespace Formal.Core.XAudit.Events7

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (fmin)
open Formal.Core.XAudit.Events3 (filt filt_mono filt_add)
open Formal.Core.XAudit.Events4 (filt_le)
open Formal.Core.XAudit.Events5

/-! ## 1. Data -/

/-- A judgement: `u` (U-bound or walk), start `a`, label context `c`, end `bb`,
delay `d`, tokens `t`. -/
structure Jd where
  u : Bool
  a : Nat
  c : Option (Nat × Bool)
  bb : Nat
  d : Nat
  t : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A merge arm in an `r3` / `sub` line or an exclusivity certificate: its label
`(g, b)`, and either `dir` (the arm is itself a filtered pin with that label) or
`ref`, the log line of its source's U-bound. -/
structure Arm where
  g : Nat
  b : Bool
  dir : Bool
  ref : Nat
  deriving Repr, Inhabited

/-- A log line. -/
inductive Ln where
  | refl (a : Nat)
  | r1 (n p r : Nat)
  | fpin (n p r : Nat)
  | r3 (x S : Nat) (arms : List Arm) (r : Nat)
  | lift (g : Nat) (b : Bool) (r : Nat)
  | sub (x S ab : Nat) (arms : List Arm) (w1 w2 : Nat)
  | uT (T q : Nat)
  | uW (w u : Nat)
  deriving Repr, Inhabited

def labA (arms : List Arm) (i : Nat) : Lab := ((arms.getD i default).g, (arms.getD i default).b)

/-- Minimum of a list (0 for the empty list). -/
def fminL : List Nat → Nat
  | [] => 0
  | [a] => a
  | a :: c :: l => min a (fminL (c :: l))

theorem fminL_le : ∀ (l : List Nat) (a : Nat), a ∈ l → fminL l ≤ a
  | [], _, h => absurd h (by simp)
  | [c], a, h => by simp at h; subst h; simp [fminL]
  | c :: e :: l, a, h => by
      simp only [fminL]
      rcases List.mem_cons.mp h with h | h
      · subst h; exact Nat.min_le_left _ _
      · exact Nat.le_trans (Nat.min_le_right _ _) (fminL_le (e :: l) a h)

section
variable {N : Nat} (net : Net4 N) (b : Bands4 net) (parts : List (List Nat))

/-- The delay of arm `i` of merge `xm` (bounded by source `S`), or `none`. -/
def armD (J : Array Jd) (xm : Fin N) (i : Fin (net.ar xm)) (S : Nat) (a : Arm) : Option Nat :=
  if a.dir then
    if net.pk xm i = PK.filt ∧ net.grp xm i = a.g ∧ net.br xm i = a.b ∧ (net.src xm i).val = S ∧ net.off xm i = 0
    then some (b.loP xm i) else none
  else if hr : a.ref < J.size then
    if J[a.ref].u = true ∧ J[a.ref].c = some (a.g, a.b) ∧ J[a.ref].a = (net.src xm i).val ∧ J[a.ref].bb = S
    then some (b.loP xm i + J[a.ref].d) else none
  else none

def armDl (J : Array Jd) (xm : Fin N) (S : Nat) (arms : List Arm) (i : Fin (net.ar xm)) : Nat :=
  (armD net b J xm i S (arms.getD i.val default)).getD 0

/-- The arms of merge `xm` (all but `skip`) are bounded, with pairwise exclusive labels. -/
def ArmsOK (J : Array Jd) (xm : Fin N) (S : Nat) (arms : List Arm) (skip : Option Nat) : Prop :=
  arms.length = net.ar xm ∧
  (∀ i : Fin (net.ar xm), skip ≠ some i.val → (armD net b J xm i S (arms.getD i.val default)).isSome = true) ∧
  (∀ i i' : Fin (net.ar xm), i ≠ i' → lx parts (labA arms i.val) (labA arms i'.val) = true)

instance (J : Array Jd) (xm : Fin N) (S : Nat) (arms : List Arm) (skip : Option Nat) :
    Decidable (ArmsOK net b parts J xm S arms skip) := by
  unfold ArmsOK; exact inferInstance

def dminA (J : Array Jd) (xm : Fin N) (S : Nat) (arms : List Arm) : Nat :=
  fminL ((List.finRange (net.ar xm)).map (armDl net b J xm S arms))

/-- **The conclusion of a log line** given the judgements `J` of the earlier lines. -/
def concl (J : Array Jd) : Ln → Option Jd
  | .refl a => if a < N then some ⟨false, a, none, a, 0, 0⟩ else none
  | .r1 n p r =>
    if h : n < N then if hp : p < net.ar ⟨n, h⟩ then if hr : r < J.size then
      if net.mg ⟨n, h⟩ = false ∧ net.pk ⟨n, h⟩ ⟨p, hp⟩ ≠ PK.guard ∧ J[r].u = false ∧ J[r].c = none ∧
          J[r].a = (net.src ⟨n, h⟩ ⟨p, hp⟩).val
      then some ⟨false, n, none, J[r].bb, b.loF ⟨n, h⟩ + b.loP ⟨n, h⟩ ⟨p, hp⟩ + J[r].d,
        net.off ⟨n, h⟩ ⟨p, hp⟩ + J[r].t⟩
      else none else none else none else none
  | .fpin n p r =>
    if h : n < N then if hp : p < net.ar ⟨n, h⟩ then if hr : r < J.size then
      if net.mg ⟨n, h⟩ = false ∧ net.pk ⟨n, h⟩ ⟨p, hp⟩ = PK.filt ∧ J[r].u = false ∧
          J[r].c = some (net.grp ⟨n, h⟩ ⟨p, hp⟩, net.br ⟨n, h⟩ ⟨p, hp⟩) ∧ J[r].a = (net.src ⟨n, h⟩ ⟨p, hp⟩).val
      then some ⟨false, n, none, J[r].bb, b.loF ⟨n, h⟩ + b.loP ⟨n, h⟩ ⟨p, hp⟩ + J[r].d,
        net.off ⟨n, h⟩ ⟨p, hp⟩ + J[r].t⟩
      else none else none else none else none
  | .lift g β r =>
    if hr : r < J.size then
      if J[r].u = false ∧ J[r].c = none then some ⟨false, J[r].a, some (g, β), J[r].bb, J[r].d, J[r].t⟩ else none
    else none
  | .uT T q =>
    if h : T < N then if hq : q < net.ar ⟨T, h⟩ then
      if net.mg ⟨T, h⟩ = false ∧ net.pk ⟨T, h⟩ ⟨q, hq⟩ = PK.filt ∧ net.off ⟨T, h⟩ ⟨q, hq⟩ = 0
      then some ⟨true, T, some (net.grp ⟨T, h⟩ ⟨q, hq⟩, net.br ⟨T, h⟩ ⟨q, hq⟩), (net.src ⟨T, h⟩ ⟨q, hq⟩).val,
        b.loF ⟨T, h⟩ + b.loP ⟨T, h⟩ ⟨q, hq⟩, 0⟩
      else none else none else none
  | .uW w u =>
    if hw : w < J.size then if hu : u < J.size then
      if J[w].u = false ∧ J[w].c = none ∧ J[w].t = 0 ∧ J[u].u = true ∧ J[u].c.isSome ∧ J[u].a = J[w].bb
      then some ⟨true, J[w].a, J[u].c, J[u].bb, J[w].d + J[u].d, 0⟩ else none
    else none else none
  | .r3 xm S arms r =>
    if h : xm < N then if hr : r < J.size then
      if net.mg ⟨xm, h⟩ = true ∧ ArmsOK net b parts J ⟨xm, h⟩ S arms none ∧
          J[r].u = false ∧ J[r].c = none ∧ J[r].a = S
      then some ⟨false, xm, none, J[r].bb, b.loF ⟨xm, h⟩ + dminA net b J ⟨xm, h⟩ S arms + J[r].d, J[r].t⟩
      else none else none else none
  | .sub xm S ab arms w1 w2 =>
    if h : xm < N then if hab : ab < net.ar ⟨xm, h⟩ then if h1 : w1 < J.size then if h2 : w2 < J.size then
      if net.mg ⟨xm, h⟩ = true ∧ ArmsOK net b parts J ⟨xm, h⟩ S arms (some ab) ∧
          J[w1].u = false ∧ J[w1].c = none ∧ J[w1].a = S ∧ J[w1].bb = xm ∧
          J[w2].u = false ∧ J[w2].c = none ∧ J[w2].a = (net.src ⟨xm, h⟩ ⟨ab, hab⟩).val
      then some ⟨false, S, some (labA arms ab), J[w2].bb,
        J[w1].d + b.loF ⟨xm, h⟩ + b.loP ⟨xm, h⟩ ⟨ab, hab⟩ + J[w2].d, J[w1].t + J[w2].t⟩
      else none else none else none else none else none

/-- Run the log: `some J` (one judgement per line) iff every line is accepted. -/
def runFrom (J : Array Jd) : List Ln → Option (Array Jd)
  | [] => some J
  | ln :: l => match concl net b parts J ln with
    | some j => runFrom (J.push j) l
    | none => none

def runLog (log : List Ln) : Option (Array Jd) := runFrom net b parts #[] log

end

/-! ## 2. Semantics -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool}

/-- `M` on raw node indices (0 outside the network). -/
def Mn (x : Beh7 net b sel) (u k : Nat) : Nat := if h : k < N then x.M u ⟨k, h⟩ else 0

theorem Mn_fin (x : Beh7 net b sel) (u : Nat) (k : Fin N) : Mn x u k.val = x.M u k := by
  simp only [Mn, dif_pos k.isLt]

theorem Mn_mono (x : Beh7 net b sel) (k : Nat) {a c : Nat} (h : a ≤ c) : Mn x a k ≤ Mn x c k := by
  unfold Mn; split
  · exact x.M_mono _ _ _ h
  · exact Nat.le_refl _

theorem Mn_zero (x : Beh7 net b sel) (k : Nat) : Mn x 0 k = 0 := by
  unfold Mn; split
  · exact x.M_zero _
  · rfl

def HoldsC (x : Beh7 net b sel) : Bool → Option (Nat × Bool) → Nat → Nat → Nat → Nat → Prop
  | false, none, a, bb, d, t => ∀ u, Mn x u a ≤ Mn x (u - d) bb + t
  | false, some (g, β), a, bb, d, t => ∀ u, filt (sel g) β (Mn x u a) ≤ Mn x (u - d) bb + t
  | true, some (g, β), a, bb, d, _ => ∀ u, Mn x u a ≤ filt (sel g) β (Mn x (u - d) bb)
  | true, none, _, _, _, _ => False

/-- What a judgement means for a behaviour. -/
def Holds (x : Beh7 net b sel) (J : Jd) : Prop :=
  J.a < N ∧ J.bb < N ∧ HoldsC x J.u J.c J.a J.bb J.d J.t

/-- Every judgement of `J` holds. -/
def AllH (x : Beh7 net b sel) (J : Array Jd) : Prop := ∀ i (h : i < J.size), Holds x J[i]

variable (x : Beh7 net b sel)

theorem holds_w {J : Jd} (h : Holds x J) (hu : J.u = false) (hc : J.c = none) :
    J.a < N ∧ J.bb < N ∧ ∀ u, Mn x u J.a ≤ Mn x (u - J.d) J.bb + J.t := by
  obtain ⟨ha, hb, hs⟩ := h; rw [hu, hc] at hs; exact ⟨ha, hb, hs⟩

theorem holds_wc {J : Jd} {g : Nat} {β : Bool} (h : Holds x J) (hu : J.u = false) (hc : J.c = some (g, β)) :
    J.a < N ∧ J.bb < N ∧ ∀ u, filt (sel g) β (Mn x u J.a) ≤ Mn x (u - J.d) J.bb + J.t := by
  obtain ⟨ha, hb, hs⟩ := h; rw [hu, hc] at hs; exact ⟨ha, hb, hs⟩

theorem holds_U {J : Jd} {g : Nat} {β : Bool} (h : Holds x J) (hu : J.u = true) (hc : J.c = some (g, β)) :
    J.a < N ∧ J.bb < N ∧ ∀ u, Mn x u J.a ≤ filt (sel g) β (Mn x (u - J.d) J.bb) := by
  obtain ⟨ha, hb, hs⟩ := h; rw [hu, hc] at hs; exact ⟨ha, hb, hs⟩

/-! ## 3. Soundness of the rules -/

theorem allH_push {J : Array Jd} {j : Jd} (hJ : AllH x J) (hj : Holds x j) : AllH x (J.push j) := by
  intro i hi
  rw [Array.getElem_push]
  split
  · exact hJ i _
  · exact hj


variable (hOK : net.OK7)
include hOK

/-- An arm with an accepted bound: `P xm i s ≤ filt (sel g) β (M (s − d) S)`. -/
theorem armD_sound {J : Array Jd} (hJ : AllH x J) (xm : Fin N) (hm : net.mg xm = true) (i : Fin (net.ar xm))
    (S : Nat) (a : Arm) (d : Nat) (h : armD net b J xm i S a = some d) :
    ∀ s, x.P xm i s ≤ filt (sel a.g) a.b (Mn x (s - d) S) := by
  intro s
  unfold armD at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨hk, hg, hb, hs, ho⟩ := hc
      cases h
      have := x.P_filt_le xm i hk s
      rw [hg, hb, ho, ← Mn_fin x _ (net.src xm i), hs] at this; omega
    · simp at h
  · split at h
    · rename_i hr
      split at h
      · rename_i hc
        obtain ⟨hu, hcc, ha, hbb⟩ := hc
        cases h
        obtain ⟨_, _, hU⟩ := holds_U x (hJ _ hr) hu hcc
        have h1 := x.P_merge_le hOK xm hm i s
        have h2 := hU (s - b.loP xm i)
        rw [ha, Mn_fin, hbb] at h2
        have e : s - b.loP xm i - J[a.ref].d = s - (b.loP xm i + J[a.ref].d) := by omega
        rw [e] at h2; omega
      · simp at h
    · simp at h

theorem armsOK_sound {parts : List (List Nat)} (hp : SelPart sel parts) {J : Array Jd} (hJ : AllH x J)
    (xm : Fin N) (hm : net.mg xm = true) (S : Nat) (arms : List Arm) (skip : Option Nat)
    (h : ArmsOK net b parts J xm S arms skip) :
    (∀ i : Fin (net.ar xm), skip ≠ some i.val → ∀ s,
      x.P xm i s ≤ filt (sel (labA arms i.val).1) (labA arms i.val).2 (Mn x (s - armDl net b J xm S arms i) S) ∧
      dminA net b J xm S arms ≤ armDl net b J xm S arms i) ∧
    (∀ i i' : Fin (net.ar xm), i ≠ i' → Excl sel (labA arms i.val) (labA arms i'.val)) := by
  obtain ⟨_, hA, hX⟩ := h
  refine ⟨fun i hs s => ⟨?_, ?_⟩, fun i i' hne => lx_sound hp (hX i i' hne)⟩
  · have hi := hA i hs
    obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hi
    have := armD_sound x hOK hJ xm hm i S _ d hd s
    unfold armDl; rw [hd]; exact this
  · exact fminL_le _ _ (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)

variable {parts : List (List Nat)} (hp : SelPart sel parts)
include hp

/-- **Soundness of one line.** -/
theorem concl_sound {J : Array Jd} (hJ : AllH x J) (ln : Ln) {j : Jd} (hc : concl net b parts J ln = some j) :
    Holds x j := by
  cases ln with
  | refl a =>
    simp only [concl] at hc
    split at hc
    · rename_i ha; cases hc
      exact ⟨ha, ha, fun u => by simp⟩
    · simp at hc
  | r1 n p r =>
    simp only [concl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hp'
        split at hc
        · rename_i hr
          split at hc
          · rename_i hcd
            obtain ⟨hm, hk, hu, hcc, ha⟩ := hcd
            cases hc
            obtain ⟨_, hbb, hw⟩ := holds_w x (hJ r hr) hu hcc
            refine ⟨h, hbb, fun u => ?_⟩
            have h1 := x.M_le_pin ⟨n, h⟩ hm ⟨p, hp'⟩ u
            have h2 := x.P_le hOK ⟨n, h⟩ ⟨p, hp'⟩ hk (x.F ⟨n, h⟩ u)
            have a1 := (x.wF ⟨n, h⟩).le_late u
            have h3 := x.M_mono (u - b.loF ⟨n, h⟩ - b.loP ⟨n, h⟩ ⟨p, hp'⟩) (net.src ⟨n, h⟩ ⟨p, hp'⟩)
              (x.F ⟨n, h⟩ u - b.loP ⟨n, h⟩ ⟨p, hp'⟩) (by omega)
            have h4 := hw (u - b.loF ⟨n, h⟩ - b.loP ⟨n, h⟩ ⟨p, hp'⟩)
            rw [ha, Mn_fin] at h4
            have e : u - b.loF ⟨n, h⟩ - b.loP ⟨n, h⟩ ⟨p, hp'⟩ - J[r].d =
                u - (b.loF ⟨n, h⟩ + b.loP ⟨n, h⟩ ⟨p, hp'⟩ + J[r].d) := by omega
            rw [e] at h4
            have hMn : Mn x u n = x.M u ⟨n, h⟩ := Mn_fin x u ⟨n, h⟩
            dsimp only
            rw [hMn]
            omega
          · simp at hc
        · simp at hc
      · simp at hc
    · simp at hc
  | fpin n p r =>
    simp only [concl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hp'
        split at hc
        · rename_i hr
          split at hc
          · rename_i hcd
            obtain ⟨hm, hk, hu, hcc, ha⟩ := hcd
            cases hc
            obtain ⟨_, hbb, hw⟩ := holds_wc x (hJ r hr) hu hcc
            refine ⟨h, hbb, fun u => ?_⟩
            have h1 := x.M_le_pin ⟨n, h⟩ hm ⟨p, hp'⟩ u
            have h2 := x.P_filt_le ⟨n, h⟩ ⟨p, hp'⟩ hk (x.F ⟨n, h⟩ u)
            have a1 := (x.wF ⟨n, h⟩).le_late u
            have h3 := x.M_mono (u - b.loF ⟨n, h⟩ - b.loP ⟨n, h⟩ ⟨p, hp'⟩) (net.src ⟨n, h⟩ ⟨p, hp'⟩)
              (x.F ⟨n, h⟩ u - b.loP ⟨n, h⟩ ⟨p, hp'⟩) (by omega)
            have h3' := filt_mono (sel (net.grp ⟨n, h⟩ ⟨p, hp'⟩)) (net.br ⟨n, h⟩ ⟨p, hp'⟩) h3
            have h4 := hw (u - b.loF ⟨n, h⟩ - b.loP ⟨n, h⟩ ⟨p, hp'⟩)
            rw [ha, Mn_fin] at h4
            have e : u - b.loF ⟨n, h⟩ - b.loP ⟨n, h⟩ ⟨p, hp'⟩ - J[r].d =
                u - (b.loF ⟨n, h⟩ + b.loP ⟨n, h⟩ ⟨p, hp'⟩ + J[r].d) := by omega
            rw [e] at h4
            have hMn : Mn x u n = x.M u ⟨n, h⟩ := Mn_fin x u ⟨n, h⟩
            dsimp only
            rw [hMn]
            omega
          · simp at hc
        · simp at hc
      · simp at hc
    · simp at hc
  | lift g β r =>
    simp only [concl] at hc
    split at hc
    · rename_i hr
      split at hc
      · rename_i hcd
        obtain ⟨hu, hcc⟩ := hcd
        cases hc
        obtain ⟨ha, hbb, hw⟩ := holds_w x (hJ r hr) hu hcc
        refine ⟨ha, hbb, fun u => ?_⟩
        dsimp only
        have := filt_le (sel g) β (Mn x u J[r].a); have := hw u; omega
      · simp at hc
    · simp at hc
  | uT T q =>
    simp only [concl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hq
        split at hc
        · rename_i hcd
          obtain ⟨hm, hk, ho⟩ := hcd
          cases hc
          refine ⟨h, (net.src ⟨T, h⟩ ⟨q, hq⟩).isLt, fun u => ?_⟩
          have hMn : Mn x u T = x.M u ⟨T, h⟩ := Mn_fin x u ⟨T, h⟩
          dsimp only
          rw [hMn, Mn_fin]
          have h1 := x.M_le_pin ⟨T, h⟩ hm ⟨q, hq⟩ u
          have h2 := x.P_filt_le ⟨T, h⟩ ⟨q, hq⟩ hk (x.F ⟨T, h⟩ u)
          have a1 := (x.wF ⟨T, h⟩).le_late u
          have h3 := x.M_mono (u - (b.loF ⟨T, h⟩ + b.loP ⟨T, h⟩ ⟨q, hq⟩)) (net.src ⟨T, h⟩ ⟨q, hq⟩)
            (x.F ⟨T, h⟩ u - b.loP ⟨T, h⟩ ⟨q, hq⟩) (by omega)
          have h3' := filt_mono (sel (net.grp ⟨T, h⟩ ⟨q, hq⟩)) (net.br ⟨T, h⟩ ⟨q, hq⟩) h3
          omega
        · simp at hc
      · simp at hc
    · simp at hc
  | uW w u =>
    simp only [concl] at hc
    split at hc
    · rename_i hw
      split at hc
      · rename_i hu
        split at hc
        · rename_i hcd
          obtain ⟨hwu, hwc, hwt, huu, hus, hua⟩ := hcd
          cases hc
          obtain ⟨⟨g, β⟩, hcg⟩ := Option.isSome_iff_exists.mp hus
          obtain ⟨ha, _, hW⟩ := holds_w x (hJ w hw) hwu hwc
          obtain ⟨_, hbb, hU⟩ := holds_U x (hJ u hu) huu hcg
          refine ⟨ha, hbb, ?_⟩
          show HoldsC x true J[u].c J[w].a J[u].bb (J[w].d + J[u].d) 0
          rw [hcg]
          intro v
          have h1 := hW v
          have h2 := hU (v - J[w].d)
          rw [hua, hwt] at *
          have e : v - J[w].d - J[u].d = v - (J[w].d + J[u].d) := by omega
          rw [e] at h2; omega
        · simp at hc
      · simp at hc
    · simp at hc
  | r3 xi S arms r =>
    simp only [concl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hr
        split at hc
        · rename_i hcd
          obtain ⟨hm, hA, hu, hcc, ha⟩ := hcd
          cases hc
          obtain ⟨hS, hbb, hw⟩ := holds_w x (hJ r hr) hu hcc
          rw [ha] at hS hw
          obtain ⟨hB, hX⟩ := armsOK_sound x hOK hp hJ ⟨xi, h⟩ hm S arms none hA
          refine ⟨h, hbb, fun u => ?_⟩
          have hMn : Mn x u xi = x.M u ⟨xi, h⟩ := Mn_fin x u ⟨xi, h⟩
          dsimp only
          rw [hMn]
          rcases Nat.eq_zero_or_pos u with hu0 | hu1
          · subst hu0; rw [x.M_zero]; exact Nat.zero_le _
          rw [x.M_merge ⟨xi, h⟩ hm u hu1]
          have a1 := (x.wF ⟨xi, h⟩).le_late u
          have hdm : ∀ i : Fin (net.ar ⟨xi, h⟩), dminA net b J ⟨xi, h⟩ S arms ≤ armDl net b J ⟨xi, h⟩ S arms i :=
            fun i => (hB i (by simp) 0).2
          have hle : ∀ i : Fin (net.ar ⟨xi, h⟩), x.P ⟨xi, h⟩ i (x.F ⟨xi, h⟩ u) ≤
              filt (sel (labA arms i.val).1) (labA arms i.val).2
                (Mn x (u - b.loF ⟨xi, h⟩ - dminA net b J ⟨xi, h⟩ S arms) S) := by
            intro i
            have hb1 := (hB i (by simp) (x.F ⟨xi, h⟩ u)).1
            have := hdm i
            exact Nat.le_trans hb1 (filt_mono _ _ (Mn_mono x S (by omega)))
          have hs := fsum_mono _ _ _ hle
          have hc := fsum_filt_le (net.ar ⟨xi, h⟩) (fun i => labA arms i.val) hX
            (Mn x (u - b.loF ⟨xi, h⟩ - dminA net b J ⟨xi, h⟩ S arms) S)
          have h4 := hw (u - b.loF ⟨xi, h⟩ - dminA net b J ⟨xi, h⟩ S arms)
          have e : u - b.loF ⟨xi, h⟩ - dminA net b J ⟨xi, h⟩ S arms - J[r].d =
              u - (b.loF ⟨xi, h⟩ + dminA net b J ⟨xi, h⟩ S arms + J[r].d) := by omega
          rw [e] at h4
          try dsimp only at hc
          omega
        · simp at hc
      · simp at hc
    · simp at hc
  | sub xi S ab arms w1 w2 =>
    simp only [concl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hab
        split at hc
        · rename_i h1
          split at hc
          · rename_i h2
            split at hc
            · rename_i hcd
              obtain ⟨hm, hA, hu1, hc1, ha1, hb1, hu2, hc2, ha2⟩ := hcd
              cases hc
              obtain ⟨hS, _, hw1⟩ := holds_w x (hJ w1 h1) hu1 hc1
              obtain ⟨_, hbb, hw2⟩ := holds_w x (hJ w2 h2) hu2 hc2
              rw [ha1, hb1] at hw1; rw [ha1] at hS
              rw [ha2] at hw2
              obtain ⟨hB, hX⟩ := armsOK_sound x hOK hp hJ ⟨xi, h⟩ hm S arms (some ab) hA
              refine ⟨hS, hbb, fun u => ?_⟩
              have hw := hw1 u
              have e2 : u - (J[w1].d + b.loF ⟨xi, h⟩ + b.loP ⟨xi, h⟩ ⟨ab, hab⟩ + J[w2].d) =
                  u - J[w1].d - b.loF ⟨xi, h⟩ - b.loP ⟨xi, h⟩ ⟨ab, hab⟩ - J[w2].d := by omega
              show filt (sel (labA arms ab).1) (labA arms ab).2 (Mn x u S) ≤ Mn x (u - (J[w1].d + b.loF ⟨xi, h⟩ +
                b.loP ⟨xi, h⟩ ⟨ab, hab⟩ + J[w2].d)) J[w2].bb + (J[w1].t + J[w2].t)
              rw [e2]
              have hflt := filt_le (sel (labA arms ab).1) (labA arms ab).2 (Mn x u S)
              rcases Nat.eq_zero_or_pos (u - J[w1].d) with hv0 | hv1
              · rw [hv0, Mn_zero] at hw; omega
              have hMn : Mn x (u - J[w1].d) xi = x.M (u - J[w1].d) ⟨xi, h⟩ := Mn_fin x _ ⟨xi, h⟩
              rw [hMn, x.M_merge ⟨xi, h⟩ hm _ hv1] at hw
              have a1 := (x.wF ⟨xi, h⟩).le_late (u - J[w1].d)
              generalize hsd : x.F ⟨xi, h⟩ (u - J[w1].d) = s at hw a1
              generalize hmd : Mn x u S = m at hw hflt ⊢
              -- the other arms are below their branch counts of `m`
              have hrest : fsum (net.ar ⟨xi, h⟩) (fun i => if i = ⟨ab, hab⟩ then 0 else x.P ⟨xi, h⟩ i s) ≤
                  fsum (net.ar ⟨xi, h⟩) (fun i => if i = ⟨ab, hab⟩ then 0 else
                    filt (sel (labA arms i.val).1) (labA arms i.val).2 m) := by
                apply fsum_mono; intro i
                by_cases hi : i = ⟨ab, hab⟩
                · simp [hi]
                · simp only [hi, ite_false]
                  have hne : some ab ≠ some i.val := by
                    intro e; apply hi; apply Fin.ext; exact (Option.some.inj e).symm
                  obtain ⟨hb, _⟩ := hB i hne s
                  have hmo := Mn_mono x S (show s - armDl net b J ⟨xi, h⟩ S arms i ≤ u by omega)
                  rw [hmd] at hmo
                  exact Nat.le_trans hb (filt_mono _ _ hmo)
              have hsp := fsum_split _ (fun i => x.P ⟨xi, h⟩ i s) ⟨ab, hab⟩
              have hspl := fsum_split _ (fun i => filt (sel (labA arms i.val).1) (labA arms i.val).2 m) ⟨ab, hab⟩
              have hcons := fsum_filt_le (net.ar ⟨xi, h⟩) (fun i => labA arms i.val) hX m
              -- the target arm's pin
              obtain ⟨_, _, hkg, hoffa⟩ := (hOK ⟨xi, h⟩ ⟨ab, hab⟩).2.2.2.1 hm
              have hpA := x.P_le hOK ⟨xi, h⟩ ⟨ab, hab⟩ hkg s
              have h3 := x.M_mono (u - J[w1].d - b.loF ⟨xi, h⟩ - b.loP ⟨xi, h⟩ ⟨ab, hab⟩) (net.src ⟨xi, h⟩ ⟨ab, hab⟩)
                (s - b.loP ⟨xi, h⟩ ⟨ab, hab⟩) (by omega)
              have h4 := hw2 (u - J[w1].d - b.loF ⟨xi, h⟩ - b.loP ⟨xi, h⟩ ⟨ab, hab⟩)
              rw [Mn_fin] at h4
              try dsimp only at hsp hspl hcons
              omega
            · simp at hc
          · simp at hc
        · simp at hc
      · simp at hc
    · simp at hc

theorem runFrom_sound : ∀ (l : List Ln) {J J' : Array Jd}, AllH x J → runFrom net b parts J l = some J' → AllH x J'
  | [], J, J', hJ, h => by simp only [runFrom, Option.some.injEq] at h; subst h; exact hJ
  | ln :: l, J, J', hJ, h => by
      simp only [runFrom] at h
      split at h
      · rename_i j hj
        exact runFrom_sound l (allH_push x hJ (concl_sound x hOK hp hJ ln hj)) h
      · simp at h

/-- **`runLog_sound`**: every line of an accepted log holds, for every behaviour
(under `Net4.OK7` and SelPart). -/
theorem runLog_sound {log : List Ln} {J : Array Jd} (h : runLog net b parts log = some J) : AllH x J :=
  runFrom_sound x hOK hp log (J := #[]) (fun i hi => absurd hi (by simp)) h

end

/-! ## 4. Item certificates (STRICT margins) -/

section
variable {N : Nat} (net : Net4 N) (b : Bands4 net) (parts : List (List Nat))

/-- A stage pin's Back certificate: log line `i` is a walk from the pin's source
(in its label when filtered) back to the stage, (pin + walk) at most one token,
STRICTLY slower than the stage's slowest own feedback. -/
def BackOK7 (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (i : Nat) : Prop :=
  ∃ hi : i < J.size, J[i].u = false ∧ J[i].a = (net.src j p).val ∧ J[i].bb = j.val ∧
    J[i].c = (if net.pk j p = PK.filt then some (net.grp j p, net.br j p) else none) ∧
    J[i].t + net.off j p ≤ 1 ∧ b.hiQ j < b.loP j p + J[i].d

instance (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (i : Nat) : Decidable (BackOK7 net b J j p i) := by
  unfold BackOK7; exact inferInstance

def backOK7 (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (i : Nat) : Bool := decide (BackOK7 net b J j p i)

/-- A delay line's certificate: log line `i` is a closed walk of its source with
at most one token, STRICTLY slower than every hop window. -/
def LineOK7 (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (i : Nat) : Prop :=
  ∃ hi : i < J.size, J[i].u = false ∧ J[i].c = none ∧ J[i].a = (net.src j p).val ∧ J[i].bb = (net.src j p).val ∧
    J[i].t ≤ 1 ∧ ∀ k : Fin (net.nc j p - 1), b.dw j p k.val < J[i].d

instance (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (i : Nat) : Decidable (LineOK7 net b J j p i) := by
  unfold LineOK7; exact inferInstance

def lineOK7 (J : Array Jd) (j : Fin N) (p : Fin (net.ar j)) (i : Nat) : Bool := decide (LineOK7 net b J j p i)

/-- A merge's exclusivity certificate: at most one arm; or every arm bounded by a
label of one source `S`, labels pairwise exclusive, and log line `w` a walk
`S → xm` with at most one token. -/
def ExclOK7 (J : Array Jd) (xm : Fin N) (S : Nat) (arms : List Arm) (w : Nat) : Prop :=
  net.ar xm ≤ 1 ∨ (ArmsOK net b parts J xm S arms none ∧
    ∃ hw : w < J.size, J[w].u = false ∧ J[w].c = none ∧ J[w].a = S ∧ J[w].bb = xm.val ∧ J[w].t ≤ 1)

instance (J : Array Jd) (xm : Fin N) (S : Nat) (arms : List Arm) (w : Nat) :
    Decidable (ExclOK7 net b parts J xm S arms w) := by
  unfold ExclOK7; exact inferInstance

def exclOK7 (J : Array Jd) (xm : Fin N) (S : Nat) (arms : List Arm) (w : Nat) : Bool :=
  decide (ExclOK7 net b parts J xm S arms w)

end

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)
  (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts)

include hOK in
theorem backOK7_sound {J : Array Jd} (hJ : AllH x J) (j : Fin N) (p : Fin (net.ar j)) (hk : net.pk j p ≠ PK.guard)
    (i : Nat) (h : backOK7 net b J j p i = true) (s : Nat) : x.P j p s ≤ x.M (x.Q j s) j + 1 := by
  obtain ⟨hi, hu, ha, hbb, hc, ht, hq⟩ := of_decide_eq_true h
  have a4 := (x.wQ j).early_le s
  have hmq := x.M_mono (x.Q j s) j (s - b.loP j p - J[i].d) (by omega)
  by_cases hf : net.pk j p = PK.filt
  · rw [if_pos hf] at hc
    obtain ⟨_, _, hw⟩ := holds_wc x (hJ i hi) hu hc
    have h0 := x.P_filt_le j p hf s
    have h1 := hw (s - b.loP j p)
    rw [ha, hbb, Mn_fin, Mn_fin] at h1
    have e : s - b.loP j p - J[i].d = s - b.loP j p - J[i].d := rfl
    omega
  · rw [if_neg hf] at hc
    obtain ⟨_, _, hw⟩ := holds_w x (hJ i hi) hu hc
    have h0 := x.P_le hOK j p hk s
    have h1 := hw (s - b.loP j p)
    rw [ha, hbb, Mn_fin, Mn_fin] at h1
    omega

theorem lineOK7_sound {J : Array Jd} (hJ : AllH x J) (j : Fin N) (p : Fin (net.ar j)) (i : Nat)
    (h : lineOK7 net b J j p i = true) (s : Nat) : ContigF (net.nc j p) (x.cm j p s) := by
  obtain ⟨hi, hu, hc, ha, hbb, ht, hdw⟩ := of_decide_eq_true h
  obtain ⟨_, _, hw⟩ := holds_w x (hJ i hi) hu hc
  rw [ha, hbb] at hw
  have hev : OneEvent (fun t => x.M t (net.src j p)) J[i].d := by
    intro u; have := hw (u + J[i].d); rw [Nat.add_sub_cancel, Mn_fin, Mn_fin] at this; simp only; omega
  have hmono : MonoC (fun t => x.M t (net.src j p)) := fun a c h => x.M_mono _ _ _ h
  apply contigF_chain _ _ (net.nc_pos j p)
  intro k hk
  have hsk := x.hskew j p k ⟨k.val + 1, hk⟩ rfl s
  have hd := hdw ⟨k.val, by omega⟩
  exact close_of_window (fun t => x.M t (net.src j p)) _ hmono hev (x.G j p k s) (x.G j p ⟨k.val + 1, hk⟩ s)
    (by simp only at hd; omega) (by simp only at hd; omega)

include hOK hp in
theorem exclOK7_sound {J : Array Jd} (hJ : AllH x J) (xm : Fin N) (hm : net.mg xm = true) (S : Nat)
    (arms : List Arm) (w : Nat) (h : exclOK7 net b parts J xm S arms w = true) (s : Nat) :
    fodd (net.ar xm) (fun p => x.P xm p s) ≤ 1 := by
  rcases of_decide_eq_true h with hle | ⟨hA, hw, hu, hc, ha, hbb, ht⟩
  · have := fodd_le (net.ar xm) (fun p => x.P xm p s); omega
  obtain ⟨hS, _, hW⟩ := holds_w x (hJ w hw) hu hc
  rw [ha, hbb] at hW
  simp only [Mn_fin] at hW
  obtain ⟨hB, hX⟩ := armsOK_sound x hOK hp hJ xm hm S arms none hA
  let dm := dminA net b J xm S arms
  let L := J[w].d
  let σ : Nat → Nat := fun t => if 1 ≤ t - dm - L then x.F xm (t - dm - L) else 0
  have hσ : ∀ t, 0 < t → σ t < t := by
    intro t ht; simp only [σ]; split
    · have := x.F_lt xm (t - dm - L) (by omega); omega
    · exact ht
  refine merge_exclN (net.ar xm) (fun i => labA arms i.val) hX (fun i t => x.P xm i t)
    (fun t => Mn x (t - dm) S) σ hσ (fun i a c hac => x.P_mono xm i hac) ?_ ?_
    (fun i => x.P_zero_merge hOK xm hm i) s
  · intro i t
    obtain ⟨hb1, hd⟩ := hB i (by simp) t
    exact Nat.le_trans hb1 (filt_mono _ _ (Mn_mono x S (by omega)))
  · intro t _
    have h1 := hW (t - dm)
    simp only [σ]
    split
    · rename_i hv
      rw [x.M_merge xm hm _ hv] at h1
      have e : t - dm - J[w].d = t - dm - L := rfl
      omega
    · rename_i hv
      have : t - dm - J[w].d = 0 := by simp only [L] at hv; omega
      rw [this, x.M_zero] at h1
      omega

end

/-! ## 5. The verdict -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

/-- **`verdict7`**: `Beh7.safe` from an accepted log. `cp`, `cxm`, `cl` mark the
stage pins, merges and line pins the checker certified (with the log lines /
exclusivity data `back`, `xS xa xw`, `line`); every other item carries its
count-level obligation (`rB`, `rX`, `rL`). Under OK7, SelPart, SelOK and GuardOK
every node is its reset value flipped `M t j` times at every time. -/
theorem verdict7 (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {log : List Ln} {J : Array Jd}
    (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (rB : ∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → x.P j p s ≤ x.M (x.Q j s) j + 1)
    (rX : ∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => x.P m p s) ≤ 1)
    (rL : ∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (x.cm j p s))
    (hsel : x.SelOK) (hguard : x.GuardOK) : ∀ t (j : Fin N), x.c j t = ph (net.v j) (x.M t j) := by
  have hA := runLog_sound x hOK hp hJ
  refine x.safe hOK hsel ?_ ?_ ?_ hguard
  · intro j p s hk
    cases hc : cl j p
    · exact rL j p s hk hc
    · exact lineOK7_sound x hA j p _ (hcl j p hc) s
  · intro j p s hm hk
    cases hc : cp j p
    · exact rB j p s hm hk hc
    · exact backOK7_sound x hOK hA j p hk _ (hcp j p hc) s
  · intro m s hm
    cases hc : cxm m
    · exact rX m s hm hc
    · exact exclOK7_sound x hOK hp hA m hm _ _ _ (hcx m hc) s

end

end Formal.Core.XAudit.Events7
