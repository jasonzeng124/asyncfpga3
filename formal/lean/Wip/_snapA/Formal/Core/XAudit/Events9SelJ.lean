import Formal.Core.XAudit.Events9SelL

/-!
# Formal.Core.XAudit.Events9SelJ — a junction-anchored acknowledge lag, derived causally

Probe E9SelRun (shard A). Notes: `formal/notes/A-e9selrun.md` §3.

E8SelC's split hold rows anchor the select's hold at a JUNCTION wire `w` of the copy path
(`full = top ++ bot`, `w` the top of `bot`) and assume H_ACK_LAG_w with the lag `plo π` of ONE
path π from the acknowledge to `w`. E8Causal (`sibling_lag_neg`) showed that this lag does not
follow from causality when a token can close the acknowledge through a SIBLING arm that does
not pass `w`. E8Causal's `selL` derives the lag from the log only at the SOURCE (lag
`dW + 1 − phi bot`), which loses the spread `phi bot − plo bot` of the shared stretch.

This file derives the lag from the JUNCTION, with the minimum over all arms. Fix a source `S`
and a monotone warp `gB` (in the design: `gB = tau bot`, the warp of the shared lower part).
A **junction judgement** (`Jd` with `bb` ignored) is
* walk: `M u a ≤ M (gB (u − d)) S + t` ("`a` trails the junction by `d`"), or
* U-bound with label `(g, β)`: `M u a ≤ filt (sel g) β (M (gB (u − d)) S)`.
Rules of the junction log (`JLn`, conclusions `jconcl`, each proved sound in `jconcl_sound`):
* `jrefl`: `S` trails the junction by 0, only if `gB` is the identity-or-later (`bot = []`);
* `jpin n p e`: a real stage `n` whose (non-guarded, offset-0) pin `p` reads `S` with every copy
  through the junction (`FacP`: `G n p i s ≤ gB (s − e)`) trails it by `loF n + e`;
* `juT n p e`: the same for a filtered pin, as a U-bound in the pin's label;
* `jwalk w r` / `juW w r`: a walk line `w` of the ACCEPTED main log (`a → X`) followed by a
  junction judgement of `X`;
* `jr3 xm arms`: a merge whose arms carry pairwise exclusive labels, each arm either a filtered
  pin of `xm` itself through the junction (lag `e`) or a junction U-bound of the arm's source
  (lag `loP + d`): the merge trails the junction by `loF + MIN over arms`. This is the rule
  `sibling_lag_neg` asks for: a token routed to the sibling branch is bounded by the SIBLING
  arm's own (shorter) lag, and the row uses the minimum.

`facOK` (decidable) checks `FacP` on the parsed netlist: every copy path of the pin ENDS with
the list `bot`, and its upper part has `plo ≥ e + 1` (`fac_of_ok`). So for a copy whose read is
cut at the junction, `top` at its HIGH end and every arm's unshared stretch at its LOW end enter
the margin: the "min over arms plus the spread of the unshared stretch".

**`design_verdict9_selJ`**: `Events9SelL.design_verdict9_selTP` with H_REQ_CNT from checked
`ReqLineT` lines (as `selT`) and H_ACK_CNT from a checked junction row per copy: the junction
log of `(src, bot)` runs (`runJ`), and its line `jw` is a token-free walk judgement of the ack
leaf `na` with `Dl ≤ d + plo κa + 1`. Select-side trace hypotheses left: C's H_BUNDLE,
H_SEL_SETUP, H_SEL_O.

NOT covered: as `Events9SelL`. The junction is a list equality of path suffixes: two copies
share `bot` only if their certificate paths end with the SAME gate inputs (then their warps are
the same function, `tau hsat bot`).
-/

namespace Formal.Core.XAudit.Events9SelJ

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events3 (filt filt_mono)
open Formal.Core.XAudit.Events4 (filt_le)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9
open Formal.Core.XAudit.Events8Bridge
open Formal.Core.XAudit.Events9Sel
open Formal.Core.XAudit.Events9SelC
open Formal.Core.XAudit.Events9SelHold
open Formal.Core.XAudit.Events9SelSplit
open Formal.Core.XAudit.Events9Prefix
open Formal.Core.XAudit.Events9PrefixSel
open Formal.Core.XAudit.Events9SelL

/-! ## 1. Pin bounds against an arbitrary copy bound -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)

theorem P_le_of (j : Fin N) (p : Fin (net.ar j)) (hk : net.pk j p ≠ PK.guard) (s B : Nat)
    (hcm : ∀ i, x.cm j p s i ≤ B) : x.P j p s ≤ B + net.off j p := by
  have hn := net.nc_pos j p
  have hmax := fmax_le _ _ hn _ hcm
  have hmm : fmin _ (x.cm j p s) ≤ fmax _ (x.cm j p s) := by
    obtain ⟨i, hi⟩ := fmin_mem _ (x.cm j p s) hn; rw [hi]; exact le_fmax _ _ i
  unfold Beh7.P Beh7.pc
  cases hpk : net.pk j p with
  | guard => exact absurd hpk hk
  | plain => simp only; omega
  | filt => simp only; have := filt_le (sel (net.grp j p)) (net.br j p) (fmax _ (x.cm j p s)); omega
  | multi =>
    simp only
    cases net.op j p
    · simp only [Bool.false_eq_true, ite_false]; unfold orCnt; omega
    · simp only [ite_true]; unfold andCnt; omega

theorem P_filt_le_of (j : Fin N) (p : Fin (net.ar j)) (hk : net.pk j p = PK.filt) (s B : Nat)
    (hcm : ∀ i, x.cm j p s i ≤ B) :
    x.P j p s ≤ filt (sel (net.grp j p)) (net.br j p) B + net.off j p := by
  have hmax := fmax_le _ _ (net.nc_pos j p) _ hcm
  unfold Beh7.P Beh7.pc
  simp only [hk]
  have := filt_mono (sel (net.grp j p)) (net.br j p) hmax
  omega

end

/-! ## 2. Junction judgements and their log -/

/-- A merge arm of a junction `jr3` line: its label, and either `dir` (a filtered pin of the
merge itself, through the junction with lag `e`) or `ref`, the junction line of a U-bound of
the arm's source. -/
structure JArm where
  g : Nat
  b : Bool
  dir : Bool
  e : Nat
  ref : Nat
  deriving Repr, Inhabited

/-- A junction log line. -/
inductive JLn where
  | jrefl
  | jpin (n p e : Nat)
  | juT (n p e : Nat)
  | jwalk (w r : Nat)
  | juW (w r : Nat)
  | jr3 (xm : Nat) (arms : List JArm)
  deriving Repr, Inhabited

def labJ (arms : List JArm) (i : Nat) : Lab := ((arms.getD i default).g, (arms.getD i default).b)

section
variable {N : Nat} (net : Net4 N) (b : Bands4 net) (parts : List (List Nat)) (J : Array Jd)
  (S : Nat) (fc : Nat → Nat → Nat → Bool) (idok : Bool)

/-- The lag of arm `i` of merge `xm` beyond the junction, or `none`. -/
def armJ (JJ : Array Jd) (xm : Fin N) (i : Fin (net.ar xm)) (a : JArm) : Option Nat :=
  if a.dir then
    if net.pk xm i = PK.filt ∧ net.grp xm i = a.g ∧ net.br xm i = a.b ∧ (net.src xm i).val = S ∧
        net.off xm i = 0 ∧ fc xm.val i.val a.e = true
    then some a.e else none
  else if hr : a.ref < JJ.size then
    if JJ[a.ref].u = true ∧ JJ[a.ref].c = some (a.g, a.b) ∧ JJ[a.ref].a = (net.src xm i).val
    then some (b.loP xm i + JJ[a.ref].d) else none
  else none

def armJl (JJ : Array Jd) (xm : Fin N) (arms : List JArm) (i : Fin (net.ar xm)) : Nat :=
  (armJ net b S fc JJ xm i (arms.getD i.val default)).getD 0

def ArmsJ (JJ : Array Jd) (xm : Fin N) (arms : List JArm) : Prop :=
  arms.length = net.ar xm ∧
  (∀ i : Fin (net.ar xm), (armJ net b S fc JJ xm i (arms.getD i.val default)).isSome = true) ∧
  (∀ i i' : Fin (net.ar xm), i ≠ i' → lx parts (labJ arms i.val) (labJ arms i'.val) = true)

instance (JJ : Array Jd) (xm : Fin N) (arms : List JArm) : Decidable (ArmsJ net b parts S fc JJ xm arms) := by
  unfold ArmsJ; exact inferInstance

def dminJ (JJ : Array Jd) (xm : Fin N) (arms : List JArm) : Nat :=
  fminL ((List.finRange (net.ar xm)).map (armJl net b S fc JJ xm arms))

/-- **The conclusion of a junction log line** (`bb` is `S` throughout and unused). -/
def jconcl (JJ : Array Jd) : JLn → Option Jd
  | .jrefl => if idok = true ∧ S < N then some ⟨false, S, none, S, 0, 0⟩ else none
  | .jpin n p e =>
    if h : n < N then if hp : p < net.ar ⟨n, h⟩ then
      if net.mg ⟨n, h⟩ = false ∧ net.pk ⟨n, h⟩ ⟨p, hp⟩ ≠ PK.guard ∧ net.off ⟨n, h⟩ ⟨p, hp⟩ = 0 ∧
          (net.src ⟨n, h⟩ ⟨p, hp⟩).val = S ∧ fc n p e = true
      then some ⟨false, n, none, S, b.loF ⟨n, h⟩ + e, 0⟩ else none
    else none else none
  | .juT n p e =>
    if h : n < N then if hp : p < net.ar ⟨n, h⟩ then
      if net.mg ⟨n, h⟩ = false ∧ net.pk ⟨n, h⟩ ⟨p, hp⟩ = PK.filt ∧ net.off ⟨n, h⟩ ⟨p, hp⟩ = 0 ∧
          (net.src ⟨n, h⟩ ⟨p, hp⟩).val = S ∧ fc n p e = true
      then some ⟨true, n, some (net.grp ⟨n, h⟩ ⟨p, hp⟩, net.br ⟨n, h⟩ ⟨p, hp⟩), S, b.loF ⟨n, h⟩ + e, 0⟩ else none
    else none else none
  | .jwalk w r =>
    if hw : w < J.size then if hr : r < JJ.size then
      if J[w].u = false ∧ J[w].c = none ∧ JJ[r].u = false ∧ JJ[r].c = none ∧ J[w].bb = JJ[r].a
      then some ⟨false, J[w].a, none, S, J[w].d + JJ[r].d, J[w].t + JJ[r].t⟩ else none
    else none else none
  | .juW w r =>
    if hw : w < J.size then if hr : r < JJ.size then
      if J[w].u = false ∧ J[w].c = none ∧ J[w].t = 0 ∧ JJ[r].u = true ∧ JJ[r].c.isSome ∧ J[w].bb = JJ[r].a
      then some ⟨true, J[w].a, JJ[r].c, S, J[w].d + JJ[r].d, 0⟩ else none
    else none else none
  | .jr3 xm arms =>
    if h : xm < N then
      if net.mg ⟨xm, h⟩ = true ∧ ArmsJ net b parts S fc JJ ⟨xm, h⟩ arms
      then some ⟨false, xm, none, S, b.loF ⟨xm, h⟩ + dminJ net b S fc JJ ⟨xm, h⟩ arms, 0⟩ else none
    else none

def runJFrom (JJ : Array Jd) : List JLn → Option (Array Jd)
  | [] => some JJ
  | ln :: l => match jconcl net b parts J S fc idok JJ ln with
    | some j => runJFrom (JJ.push j) l
    | none => none

/-- Run a junction log: `some JJ` iff every line is accepted. -/
def runJ (l : List JLn) : Option (Array Jd) := runJFrom net b parts J S fc idok #[] l

end

/-! ## 3. Semantics and soundness -/

section
variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool} (x : Beh7 net b sel)
  (S : Nat) (gB : Nat → Nat)

def HoldsJC : Bool → Option (Nat × Bool) → Nat → Nat → Nat → Prop
  | false, none, a, d, t => ∀ u, Mn x u a ≤ Mn x (gB (u - d)) S + t
  | false, some _, _, _, _ => False
  | true, some (g, β), a, d, _ => ∀ u, Mn x u a ≤ filt (sel g) β (Mn x (gB (u - d)) S)
  | true, none, _, _, _ => False

/-- What a junction judgement means. -/
def HoldsJ (j : Jd) : Prop := j.a < N ∧ HoldsJC x S gB j.u j.c j.a j.d j.t

def AllJ (JJ : Array Jd) : Prop := ∀ i (h : i < JJ.size), HoldsJ x S gB JJ[i]

/-- The copies of pin `p` of node `n` read `S` through the junction, `e` beyond it. -/
def FacP (n p e : Nat) : Prop :=
  ∀ (h : n < N) (hp : p < net.ar ⟨n, h⟩) (i : Fin (net.nc ⟨n, h⟩ ⟨p, hp⟩)) s,
    x.G ⟨n, h⟩ ⟨p, hp⟩ i s ≤ gB (s - e)

variable {S gB} (hgB : Mono gB) {fc : Nat → Nat → Nat → Bool} (hfc : ∀ n p e, fc n p e = true → FacP x gB n p e)
  {idok : Bool} (hid : idok = true → ∀ v, v ≤ gB v)
  (hOK : net.OK7) {parts : List (List Nat)} (hp : SelPart sel parts) {J : Array Jd} (hA : AllH x J)
include hgB hfc hid hOK hp hA

theorem cm_le_fac {n : Fin N} {p : Fin (net.ar n)} {e : Nat} (hf : fc n.val p.val e = true) (s : Nat)
    (i : Fin (net.nc n p)) (hs : (net.src n p).val = S) :
    x.cm n p s i ≤ Mn x (gB (s - e)) S := by
  unfold Beh7.cm
  rw [← hs, Mn_fin]
  exact x.M_mono _ _ _ (hfc _ _ _ hf n.isLt p.isLt i s)

theorem armJ_sound {JJ : Array Jd} (hJJ : AllJ x S gB JJ) (xm : Fin N) (hm : net.mg xm = true)
    (i : Fin (net.ar xm)) (a : JArm) (dl : Nat) (h : armJ net b S fc JJ xm i a = some dl) :
    ∀ s, x.P xm i s ≤ filt (sel a.g) a.b (Mn x (gB (s - dl)) S) := by
  intro s
  unfold armJ at h
  split at h
  · split at h
    · rename_i hc
      obtain ⟨hk, hg, hb, hs, ho, hf⟩ := hc
      cases h
      have := P_filt_le_of x xm i hk s _ (fun c => cm_le_fac x hgB hfc hid hOK hp hA hf s c hs)
      rw [hg, hb, ho] at this; omega
    · simp at h
  · split at h
    · rename_i hr
      split at h
      · rename_i hc
        obtain ⟨hu, hcc, ha⟩ := hc
        cases h
        obtain ⟨_, hU⟩ := hJJ _ hr
        rw [hu, hcc] at hU
        have h1 := x.P_merge_le hOK xm hm i s
        have h2 := hU (s - b.loP xm i)
        rw [ha, Mn_fin] at h2
        have e : s - b.loP xm i - JJ[a.ref].d = s - (b.loP xm i + JJ[a.ref].d) := by omega
        rw [e] at h2; omega
      · simp at h
    · simp at h

/-- **Soundness of one junction line.** -/
theorem jconcl_sound {JJ : Array Jd} (hJJ : AllJ x S gB JJ) (ln : JLn) {j : Jd}
    (hc : jconcl net b parts J S fc idok JJ ln = some j) : HoldsJ x S gB j := by
  cases ln with
  | jrefl =>
    simp only [jconcl] at hc
    split at hc
    · rename_i hcd
      cases hc
      refine ⟨hcd.2, fun u => ?_⟩
      have := Mn_mono x S (hid hcd.1 u)
      simpa using this
    · simp at hc
  | jpin n p e =>
    simp only [jconcl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hp'
        split at hc
        · rename_i hcd
          obtain ⟨hm, hk, ho, hs, hf⟩ := hcd
          cases hc
          refine ⟨h, fun u => ?_⟩
          show Mn x u n ≤ Mn x (gB (u - (b.loF ⟨n, h⟩ + e))) S + 0
          rw [show n = (⟨n, h⟩ : Fin N).val from rfl, Mn_fin]
          have h1 := x.M_le_pin ⟨n, h⟩ hm ⟨p, hp'⟩ u
          have h2 := P_le_of x ⟨n, h⟩ ⟨p, hp'⟩ hk (x.F ⟨n, h⟩ u) _
            (fun c => cm_le_fac x hgB hfc hid hOK hp hA (n := ⟨n, h⟩) (p := ⟨p, hp'⟩) hf _ c hs)
          have a1 := (x.wF ⟨n, h⟩).le_late u
          have h3 := Mn_mono x S (hgB (x.F ⟨n, h⟩ u - e) (u - (b.loF ⟨n, h⟩ + e)) (by omega))
          omega
        · simp at hc
      · simp at hc
    · simp at hc
  | juT n p e =>
    simp only [jconcl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hp'
        split at hc
        · rename_i hcd
          obtain ⟨hm, hk, ho, hs, hf⟩ := hcd
          cases hc
          refine ⟨h, fun u => ?_⟩
          show Mn x u n ≤ filt (sel (net.grp ⟨n, h⟩ ⟨p, hp'⟩)) (net.br ⟨n, h⟩ ⟨p, hp'⟩)
            (Mn x (gB (u - (b.loF ⟨n, h⟩ + e))) S)
          rw [show n = (⟨n, h⟩ : Fin N).val from rfl, Mn_fin]
          have h1 := x.M_le_pin ⟨n, h⟩ hm ⟨p, hp'⟩ u
          have h2 := P_filt_le_of x ⟨n, h⟩ ⟨p, hp'⟩ hk (x.F ⟨n, h⟩ u) _
            (fun c => cm_le_fac x hgB hfc hid hOK hp hA (n := ⟨n, h⟩) (p := ⟨p, hp'⟩) hf _ c hs)
          have a1 := (x.wF ⟨n, h⟩).le_late u
          have h3 := filt_mono (sel (net.grp ⟨n, h⟩ ⟨p, hp'⟩)) (net.br ⟨n, h⟩ ⟨p, hp'⟩)
            (Mn_mono x S (hgB (x.F ⟨n, h⟩ u - e) (u - (b.loF ⟨n, h⟩ + e)) (by omega)))
          omega
        · simp at hc
      · simp at hc
    · simp at hc
  | jwalk w r =>
    simp only [jconcl] at hc
    split at hc
    · rename_i hw
      split at hc
      · rename_i hr
        split at hc
        · rename_i hcd
          obtain ⟨hu, hcc, hu2, hc2, hab⟩ := hcd
          cases hc
          obtain ⟨ha, _, hW⟩ := holds_w x (hA w hw) hu hcc
          obtain ⟨_, hR⟩ := hJJ r hr
          rw [hu2, hc2] at hR
          refine ⟨ha, fun u => ?_⟩
          show Mn x u J[w].a ≤ Mn x (gB (u - (J[w].d + JJ[r].d))) S + (J[w].t + JJ[r].t)
          have h1 := hW u
          have h2 := hR (u - J[w].d)
          rw [← hab] at h2
          have e : u - J[w].d - JJ[r].d = u - (J[w].d + JJ[r].d) := by omega
          rw [e] at h2; omega
        · simp at hc
      · simp at hc
    · simp at hc
  | juW w r =>
    simp only [jconcl] at hc
    split at hc
    · rename_i hw
      split at hc
      · rename_i hr
        split at hc
        · rename_i hcd
          obtain ⟨hu, hcc, ht, hu2, hs2, hab⟩ := hcd
          cases hc
          obtain ⟨⟨g, β⟩, hcg⟩ := Option.isSome_iff_exists.mp hs2
          obtain ⟨ha, _, hW⟩ := holds_w x (hA w hw) hu hcc
          obtain ⟨_, hR⟩ := hJJ r hr
          rw [hu2, hcg] at hR
          refine ⟨ha, ?_⟩
          show HoldsJC x S gB true JJ[r].c J[w].a (J[w].d + JJ[r].d) 0
          rw [hcg]
          intro u
          have h1 := hW u
          have h2 := hR (u - J[w].d)
          rw [← hab] at h2
          have e : u - J[w].d - JJ[r].d = u - (J[w].d + JJ[r].d) := by omega
          rw [e] at h2; rw [ht] at h1; omega
        · simp at hc
      · simp at hc
    · simp at hc
  | jr3 xi arms =>
    simp only [jconcl] at hc
    split at hc
    · rename_i h
      split at hc
      · rename_i hcd
        obtain ⟨hm, hL, hAr, hX⟩ := hcd
        cases hc
        refine ⟨h, fun u => ?_⟩
        show Mn x u xi ≤ Mn x (gB (u - (b.loF ⟨xi, h⟩ + dminJ net b S fc JJ ⟨xi, h⟩ arms))) S + 0
        rw [show xi = (⟨xi, h⟩ : Fin N).val from rfl, Mn_fin]
        rcases Nat.eq_zero_or_pos u with hu0 | hu1
        · subst hu0; rw [x.M_zero]; exact Nat.zero_le _
        rw [x.M_merge ⟨xi, h⟩ hm u hu1]
        have a1 := (x.wF ⟨xi, h⟩).le_late u
        generalize hm0 : Mn x (gB (u - (b.loF ⟨xi, h⟩ + dminJ net b S fc JJ ⟨xi, h⟩ arms))) S = m0
        have hle : ∀ i : Fin (net.ar ⟨xi, h⟩), x.P ⟨xi, h⟩ i (x.F ⟨xi, h⟩ u) ≤
            filt (sel (labJ arms i.val).1) (labJ arms i.val).2 m0 := by
          intro i
          obtain ⟨dl, hdl⟩ := Option.isSome_iff_exists.mp (hAr i)
          have hb1 := armJ_sound x hgB hfc hid hOK hp hA hJJ ⟨xi, h⟩ hm i _ dl hdl (x.F ⟨xi, h⟩ u)
          have hdm : dminJ net b S fc JJ ⟨xi, h⟩ arms ≤ dl := by
            have := fminL_le _ (armJl net b S fc JJ ⟨xi, h⟩ arms i)
              (List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩)
            unfold armJl at this; rw [hdl] at this; exact this
          rw [← hm0]
          exact Nat.le_trans hb1 (filt_mono _ _ (Mn_mono x S (hgB _ _ (by omega))))
        have hs := fsum_mono _ _ _ hle
        have hc := fsum_filt_le (net.ar ⟨xi, h⟩) (fun i => labJ arms i.val)
          (fun i i' hne => lx_sound hp (hX i i' hne)) m0
        try dsimp only at hc
        omega
      · simp at hc
    · simp at hc

theorem allJ_push {JJ : Array Jd} {j : Jd} (hJ : AllJ x S gB JJ) (hj : HoldsJ x S gB j) :
    AllJ x S gB (JJ.push j) := by
  intro i hi
  rw [Array.getElem_push]
  split
  · exact hJ i _
  · exact hj

theorem runJFrom_sound : ∀ (l : List JLn) {JJ JJ' : Array Jd}, AllJ x S gB JJ →
    runJFrom net b parts J S fc idok JJ l = some JJ' → AllJ x S gB JJ'
  | [], JJ, JJ', hJ, h => by simp only [runJFrom, Option.some.injEq] at h; subst h; exact hJ
  | ln :: l, JJ, JJ', hJ, h => by
      simp only [runJFrom] at h
      split at h
      · rename_i j hj
        exact runJFrom_sound l (allJ_push x hJ (jconcl_sound x hgB hfc hid hOK hp hA hJ ln hj)) h
      · simp at h

/-- **`runJ_sound`**: every line of an accepted junction log holds, for every behaviour, every
monotone `gB` through which the checked pins' copies read `S`. -/
theorem runJ_sound {l : List JLn} {JJ : Array Jd} (h : runJ net b parts J S fc idok l = some JJ) :
    AllJ x S gB JJ :=
  runJFrom_sound x hgB hfc hid hOK hp hA l (fun i hi => absurd hi (by simp)) h

end

/-! ## 4. The junction check on the parsed netlist -/

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

/-- **`facOK`** (decidable): node `n` is real and every copy path of its pin `p` ends with the
list `bot` (the junction's lower part), with an upper part of `plo ≥ e + 1`. -/
def facOK (bot : Path) (n p e : Nat) : Bool :=
  if h : n < N then if hp : p < net.ar ⟨n, h⟩ then
    decide ((rn ⟨n, h⟩).virt = false) && (List.finRange (net.nc ⟨n, h⟩ ⟨p, hp⟩)).all fun i =>
      let f := full net rn ⟨n, h⟩ ⟨p, hp⟩ i.val
      decide (bot.length < f.length) && decide (f.drop (f.length - bot.length) = bot) &&
        decide (e + 1 ≤ plo d (f.take (f.length - bot.length)))
  else false else false

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {sel : Nat → Nat → Bool}

theorem fac_of_ok (hsat : SatPin d plG x) (hr : Recog6 d net b rn rank rw fuel) (bh : Beh7 net b sel)
    (hG : ∀ j, (rn j).virt = false → ∀ p i s, bh.G j p i s = tau hsat (full net rn j p i.val) (s + 1))
    (bot : Path) (hbot : pathOK d bot = true) :
    ∀ n p e, facOK d net rn bot n p e = true → FacP bh (tau hsat bot) n p e := by
  intro n p e h hn hp i s
  simp only [facOK, dif_pos hn, dif_pos hp, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hv, hall⟩ := h
  have hi := hall i (List.mem_finRange i)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hi
  obtain ⟨⟨_, hdrop⟩, hplo⟩ := hi
  have hnr := hr.2 ⟨n, hn⟩ hv
  have hok := (full_ok hr.1 ⟨n, hn⟩ hnr ⟨p, hp⟩ i).1
  generalize hf : full net rn ⟨n, hn⟩ ⟨p, hp⟩ i.val = f at hdrop hplo hok
  generalize hc : f.length - bot.length = c at hdrop hplo
  have htop : pathOK d (f.take c) = true := by
    unfold pathOK at hok ⊢
    exact List.all_eq_true.mpr fun e' he => List.all_eq_true.mp hok e' (List.mem_of_mem_take he)
  rw [hG ⟨n, hn⟩ hv ⟨p, hp⟩ i s, hf, ← List.take_append_drop c f, tau_append, hdrop]
  have wT := tau_warp hsat _ htop
  have := wT.le_late (s + 1)
  exact (tau_warp hsat _ hbot).mono _ _ (by omega)

end

/-! ## 5. The verdict with junction-anchored ack lags -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **The junction row of one copy and literal** (decidable): the junction log `jl` of source
`src` and lower part `bot` runs, and its line `jw` is a token-free walk judgement of the ack leaf
`na` whose lag `dj` covers `Dl`: `Dl ≤ dj + plo κa + 1`. -/
def jrowOK (parts : List (List Nat)) (J : Array Jd) (src : Nat) (bot : Path) (jl : List JLn) (jw na plk Dl : Nat) : Bool :=
  match runJ net b parts J src (facOK d net rn bot) (decide (bot = [])) jl with
  | some JJ => if h : jw < JJ.size then
      decide (JJ[jw].u = false) && decide (JJ[jw].c = none) && decide (JJ[jw].a = na) && decide (JJ[jw].t = 0) &&
        decide (Dl ≤ JJ[jw].d + plk + 1)
    else false
  | none => false

/-- **`design_verdict9_selJ`: the select verdict with junction-anchored, causally derived ack
lags.** As `Events9SelL.design_verdict9_selT`, but the lag `Dl` of each copy and literal is
certified by a junction row (`jrowOK`) at the copy's own cut instead of a source-anchored
`AckLineT`: the junction log of `(src, botP cut)` (rules `jrefl`, `jpin`, `juT`, `jwalk`, `juW`,
`jr3` with the minimum over arms) derives `M u na ≤ M (tau bot (u − dj)) src`, which gives
H_ACK_CNT with `Dl ≤ dj + plo κa + 1`. Select-side trace hypotheses left: C's H_BUNDLE,
H_SEL_SETUP, H_SEL_O (per request leaf). -/
theorem design_verdict9_selJ (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (m : (j : Fin N) → Fin (net.ar j) → Nat → SelEnt) (cut : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (Dl : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (ta tq : (j : Fin N) → Fin (net.ar j) → Nat → AT) (na : (j : Fin N) → Fin (net.ar j) → Nat → Fin N)
    (κa : (j : Fin N) → Fin (net.ar j) → Nat → Path)
    (wq : (j : Fin N) → Fin (net.ar j) → Nat → List Nat)
    (jl : (j : Fin N) → Fin (net.ar j) → Nat → List JLn) (jw : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true ∧
      treeOK (d := d) (net := net) (rn := rn) (m j p sb.1) (ta j p sb.1) (tq j p sb.1) (na j p sb.1) (κa j p sb.1) = true ∧
      reqOK d J (na j p sb.1).val (κa j p sb.1) (AT.leaves (tq j p sb.1)) (wq j p sb.1) = true)
    (hrow : ∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)), (rn j).virt = false → net.pk j p = PK.filt →
      sb ∈ selLits net rn j p →
      holdBandS d net rn j p (m j p sb.1) i.val (cut j p i.val) (Dl j p i.val sb.1) = true ∧
      jrowOK d net b rn parts J (net.src j p).val (botP d net rn j p i.val (cut j p i.val)) (jl j p i.val)
        (jw j p i.val sb.1) (na j p sb.1).val (plo d (κa j p sb.1)) (Dl j p i.val sb.1) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts →
        (∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
          bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
          bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2)) →
        ∀ (R : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
          (O : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat),
        (∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          Formal.Net.Ops.Held ((m j p sb.1).ch x)) →
        (∀ j p (sb : Nat × Bool) k u, (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          bh.M u (net.src j p) = 2 * k + 1 → ∀ l ∈ AT.leaves (tq j p sb.1),
          2 * k + 1 ≤ Mn bh (tau hsat l.2 (O j p sb.1 k)) l.1) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k, (rn j).virt = false → net.pk j p = PK.filt →
          sb ∈ selLits net rn j p →
          O j p sb.1 k + (gt d (m j p sb.1).rg).hi + selHi d net rn j p ≤ R j p k + b.loC j p i) →
        (∀ j p u k, (rn j).virt = false → net.pk j p = PK.filt →
          bh.M u (net.src j p) = 2 * k + 1 → R j p k ≤ u) →
        (∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
          sel (net.grp j p) k = selFn (selLits net rn j p)
            (fun i => x (d.wire (m j p i).dw) (O j p i k))) →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        bh.SelOK ∧ ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh', hc', hgc', hG, H⟩ := design_verdict9_selTP hr hOK hJ back line xS xw xa hl gd cp cxm cl cg
    hcp hcx hcl hcg m cut Dl ta tq na κa (fun j p sb hv hk hs => ⟨(hm j p sb hv hk hs).1, (hm j p sb hv hk hs).2.1⟩)
    (fun j p sb i hv hk hs => (hrow j p sb i hv hk hs).1) hsat h0 h1 hT hrst harb sel
  refine ⟨bh', hc', hgc', fun hp hvirt R O hheld hO hsetup hwin hsel rB rX rL rG => ?_⟩
  have hA := runLog_sound bh' hOK hp hJ
  refine H hp hvirt R O hheld hO ?_ ?_ hsetup hwin hsel rB rX rL rG
  · intro j p sb v hv hk hs l hl
    obtain ⟨_, hTr, hq⟩ := hm j p sb hv hk hs
    obtain ⟨_, _, _, hκp, _, hlq⟩ := treeOK_spec hTr
    obtain ⟨w, hw⟩ := reqOK_mem d _ _ hq l hl
    exact reqCnt_of_lineT bh' hA hw (tau_warp hsat _ (hlq l hl).2) (tau_warp hsat _ hκp) (Nat.le_refl _) v
  · intro j p sb i k r σ hv hk hs hu hσ
    obtain ⟨_, hTr, _⟩ := hm j p sb hv hk hs
    obtain ⟨_, _, _, hκp, _, _⟩ := treeOK_spec hTr
    have hn := hr.2 j hv
    have hok := (full_ok hr.1 j hn p i).1
    have hbot : pathOK d (botP d net rn j p i.val (cut j p i.val)) = true := by
      unfold botP; unfold pathOK at hok ⊢
      exact List.all_eq_true.mpr fun e he => List.all_eq_true.mp hok e (List.mem_of_mem_drop he)
    have hjr := (hrow j p sb i hv hk hs).2
    unfold jrowOK at hjr
    split at hjr
    · rename_i JJ hrun
      split at hjr
      · rename_i hjw
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hjr
        obtain ⟨⟨⟨⟨hu', hc''⟩, ha'⟩, ht'⟩, hD⟩ := hjr
        have wB := tau_warp hsat _ hbot
        have hall := runJ_sound bh' (S := (net.src j p).val) wB.mono
          (fac_of_ok hsat hr bh' hG _ hbot)
          (fun hid v => by
            have e := of_decide_eq_true hid
            rw [e]; exact Nat.le_refl _)
          hOK hp hA hrun
        obtain ⟨_, hH⟩ := hall jw hjw
        rw [hu', hc''] at hH
        have h1 := hH (tau hsat (κa j p sb.1) σ)
        rw [ha', ht', Mn_fin, Mn_fin] at h1
        have wκ := tau_warp hsat _ hκp
        have h2 := wκ.le_late σ
        have h3 := bh'.M_mono _ _ _ (wB.mono (tau hsat (κa j p sb.1) σ - JJ[jw].d) r (by omega))
        omega
      · simp at hjr
    · simp at hjr

end

end Formal.Core.XAudit.Events9SelJ
