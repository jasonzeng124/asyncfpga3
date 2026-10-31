import Formal.Core.XAudit.Events9ParBeh
import Formal.Core.XAudit.Events9ParRst

/-!
# Formal.Core.XAudit.Events9ArbNet — the corrected arbiter core over the parsed netlist

Probe E9ArbNet (shard A). See `formal/notes/A-e9arbnet.md`.

`Events9Arb.core_of_settle` and `Events9ParRst.core_of_en_rst` are CELL-level statements: four
abstract signals `r1 r2 a q` read through abstract warps. `Events9ParBeh.design_verdict9par`
assumes, over the parsed design `d` and its certificate (`Net4`, `Bands4`, `RNode`), the
hypotheses `HARB7'` (every virtual node has an `ND7` behaviour, the grant / `R0` wires carry the
virtual signals) and `HRst` (the readers of one arbiter share one reset). This file links the two.

* `ArbD` (data, from the certificate generator, untrusted): per arbiter the six virtual nodes
  (`ctl`, two grants, two shadows, `R0`), the four LUT gates of `bd_arbiter`'s core in `d`
  (`ugrant` O5 / O6, `ustate` O5 / O6), the LUT input index of every read, the route path below
  each LUT input down to the net it reads, and per request the net wire `w` and how it is built
  from the request's source node (`RPin`: a buffer / inverter / AND / OR tree, or a steer).
* **`ArbOK`** (decidable): the four gates have the `bd_arbiter` functions on the given inputs
  (`InitSpec`, evaluated over the INITs: `g1 = r1·q`, `g2 = r2·¬q`, `R0 = r1·q + r2·¬q`,
  `q = rst + (A0 ? q : C(r1, ¬r2))`), every route path is a checked chain to its net (`chkT`), the
  request nets are what the virtual pins say (`ReqOK`, as `Events6.PinR`), the virtual nodes have
  the corrected-core shape and EXACTLY the bands `Events9Arb.CoreOf` computes from the per-pin
  paths of `d` (`plo` / `phi`, `kOf`, `loCtl`, `rdG`, `rdS`), the grant / `R0` nodes carry the
  real output wires, and the band side conditions of `core_of_settle` hold.
* **`arb_core`**: SatPin on `d` + `ArbOK` + the per-arbiter TRACE conditions `ArbCond` (outputs
  low on `[0, T0 + 2]`, the settle bound `hstall` with `H`, and `RdOK` = B1 / B2 / C for the four
  readers, all stated on the wires of `d` and the per-pin warps of the SatPin witness) give the
  cell-level corrected core with the common reader reset (`CoreOfR`).
* **`arb_nd7_*`**: a `CoreOfR` at an `ArbOK` arbiter gives `ND7` node behaviours of its six
  virtual nodes over `ccOf rn x cv` (with `cv` = the core's ctl and shadows, the real wires
  elsewhere), the readers with the common reset.
* **`harb_of_arbs`**: if every virtual node of the certificate belongs to exactly one `ArbOK`
  arbiter (checked: an owner map), every node of a reset class is one of their readers, the
  certificate has `FixShape`, and every arbiter satisfies `ArbCond`, then there is `cv` with
  `HARB7'` and `HRst`. **`design_verdict9arbnet`**: `design_verdict9par` with `HARB7'` and `HRst`
  replaced by these checks and the per-arbiter trace conditions.

NOT covered here: the trace conditions themselves (`ArbCond`: hstall, B1/B2/C, the quiet start) —
they are hypotheses; and the settle bound `H` exists only for uncontested phases (a near tie has
no bound, `Core/Delay/InvolutionLoop*`, `Events8Arb.ct_g2_osc`), so every use is conditional on
an uncontested schedule. The conditions are stated for the per-pin warps of the (classically
chosen) SatPin witness; any discharge that holds for every warp in the bands covers it.
-/

namespace Formal.Core.XAudit.Events9ArbNet

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8Arb
open Formal.Core.XAudit.Events9Arb
open Formal.Core.LutList (o5B o6B)
open Formal.Cells.ArbBinary (ARB_ST GRANT)

/-! ## 1. Small lemmas -/

theorem cel_reidx2 {n : Nat} (hn : n = 2) (f : Nat → Bool) (q : Bool) :
    cel (fun p : Fin n => f p.val) q = cel (fun p : Fin 2 => f p.val) q := by
  subst hn; rfl

theorem cel_reidx1 {n : Nat} (hn : n = 1) (c q : Bool) :
    cel (fun _ : Fin n => c) q = cel (fun _ : Fin 1 => c) q := by
  subst hn; rfl

theorem fany_reidx2 {n : Nat} (hn : n = 2) (f : Nat → Bool) :
    fany n (fun p : Fin n => f p.val) = (f 0 || f 1) := by
  subst hn; simp [fany]

theorem fany_const {n : Nat} (hn : 0 < n) (c : Bool) : fany n (fun _ : Fin n => c) = c := by
  match n, hn with
  | k + 1, _ =>
    simp only [fany]
    cases c
    · simp only [Bool.false_or]
      induction k with
      | zero => rfl
      | succ m ih => simp only [fany, Bool.false_or]; exact ih (Nat.succ_pos _)
    · rfl

theorem shiftW1 : Warp 1 1 (fun t : Nat => t - 1) :=
  ⟨fun a b hab => by omega, fun t => by omega, fun t => by omega⟩

theorem beq_not (a b : Bool) : ((!a) == !b) = (a == b) := by cases a <;> cases b <;> rfl

/-- Two warps in bands `[lo1, hi1]`, `[lo2, hi2]` read within `hi2 − lo1` of each other. -/
theorem skew_of_bands {lo1 hi1 lo2 hi2 w : Nat} {f g : Nat → Nat} (hf : Warp lo1 hi1 f)
    (hg : Warp lo2 hi2 g) (hw : hi2 - lo1 ≤ w) (s : Nat) : f s ≤ g s + w := by
  have := hf.le_late s; have := hg.early_le s; omega

/-- The pin function of `Beh4` / `ND7` (`hpin`), with the copies' values `c` and the select test `sb`. -/
def pinF (pk : PK) (inv op : Bool) (nc : Nat) (c : Fin nc → Bool) (sb : Bool) : Bool :=
  inv ^^ match pk with
    | PK.multi => if op then fall nc c else fany nc c
    | PK.guard => if op then fall nc c else fany nc c
    | PK.filt => fany nc (fun i => c i && sb)
    | PK.plain => fany nc c

/-! ## 2. A request net built from its source node -/

/-- The request of one branch: the net wire `w` the readers read, and how it is built from the
request's source node (`RPin` with `ip`/`fold` unused: tree `paths` from `w` down to the source's
output wire, or a steer gate `sg` with the chain `top` from `w` to its output and `bot` from its
control input to the source). -/
structure ReqD where
  w : Nat
  rp : RPin
  deriving Repr, Inhabited

section
variable {N : Nat} (d : Design) (rn : Fin N → RNode) (fuel : Nat)

/-- **`ReqOK`** (decidable): the request net `R.w` is the pin function (kind `pk`, inversion `inv`,
operator `op`, `nc` copies, branch `br`) of the source node `s`, as `Events6.PinR` checks a real
pin (with the pin wire `R.w` instead of a LUT input). -/
def ReqOK (s : Fin N) (pk : PK) (inv op : Bool) (nc : Nat) (br : Bool) (R : ReqD) : Prop :=
  ((rn s).virt = true → (rn s).hasW = true) ∧ pk ≠ PK.guard ∧ R.rp.copies.length = nc ∧
  (∀ π ∈ R.rp.copies, pathOK d π = true) ∧ R.rp.fold = [] ∧
  (R.rp.st = false →
    chkT d (rn s).ow fuel op R.w R.rp.paths = some inv ∧ pk ≠ PK.filt ∧ (pk = PK.plain → nc = 1)) ∧
  (R.rp.st = true →
    pk = PK.filt ∧ inv = false ∧ nc = 1 ∧ R.rp.sg < d.gates.length ∧ R.rp.sci < (gt d R.rp.sg).k ∧
    (∀ sb ∈ R.rp.ssel, sb.1 < (gt d R.rp.sg).k) ∧
    InitSpec (gt d R.rp.sg) (steerSpec R.rp) ∧
    chkT d (gt d R.rp.sg).out fuel true R.w [R.rp.top] = some false ∧
    chkT d (rn s).ow fuel true ((gt d R.rp.sg).ins.getD R.rp.sci 0) [R.rp.bot] = some false ∧
    br = brOf R.rp.ssel)

instance (s : Fin N) (pk : PK) (inv op : Bool) (nc : Nat) (br : Bool) (R : ReqD) :
    Decidable (ReqOK d rn fuel s pk inv op nc br R) := by
  unfold ReqOK; exact inferInstance

end

section
variable {N : Nat} {d : Design} {net : Net4 N} {rn : Fin N → RNode} {fuel : Nat}
  {x : Fin d.n → Sig} (hsat : SatPin d plG x) {cv : Fin N → Sig}

/-- The select a steered request net carries at time `u` (`Events6.svOf` with the pin wire `R.w`). -/
noncomputable def svR (R : ReqD) (u : Nat) : Bool :=
  if R.rp.ssel.length = 1 then vals hsat R.rp.sg (R.rp.ssel.headD (0, false)).1 (tau hsat R.rp.top u)
  else foldM (fun i => vals hsat R.rp.sg i (tau hsat R.rp.top u)) R.rp.ssel

variable (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  (hW : ∀ s, (rn s).virt = true → (rn s).hasW = true → ∀ t, x (d.wire (rn s).ow) t = cv s t)
include h0 h1 hW

/-- **The request net, read from its source** (as `Events7.ndReal7.hpin` for a real pin): at
every time `u`, the request wire is the pin function of the source node's signal read at the
composed warps of the copies (and, for a steer, the select the steer gate reads). -/
theorem req_val {s : Fin N} {pk : PK} {inv op : Bool} {nc : Nat} {br : Bool} {R : ReqD}
    (hR : ReqOK d rn fuel s pk inv op nc br R) (u : Nat) :
    x (d.wire R.w) u = pinF pk inv op nc (fun i => ccOf rn x cv s (tau hsat (R.rp.copies.getD i.val []) u))
      (svR hsat R u == br) := by
  obtain ⟨hsw, hng, hlen, _hpaths, _hfold, hnst, hst⟩ := hR
  have hsrc := src_wire (rn := rn) (cv := cv) hW s hsw
  cases hs : R.rp.st
  · obtain ⟨hchk, hnf, hpl⟩ := hnst hs
    have hc : R.rp.copies = R.rp.paths := by simp [RPin.copies, hs]
    have ev := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hchk u
    simp only [hsrc] at ev
    rw [ev, hc]
    rw [hc] at hlen
    cases hpk : pk with
    | guard => exact absurd hpk hng
    | filt => exact absurd hpk hnf
    | multi =>
      simp only [pinF]
      rw [fall_list (fun π => ccOf rn x cv s (tau hsat π u)) [] _ _ hlen,
        fany_list (fun π => ccOf rn x cv s (tau hsat π u)) [] _ _ hlen]
      unfold specL; cases op <;> rfl
    | plain =>
      simp only [pinF]
      have h1' := hpl hpk
      rw [fany_list (fun π => ccOf rn x cv s (tau hsat π u)) [] _ _ hlen]
      unfold specL; split
      · rw [all_eq_any_one _ _ (by rw [hlen, h1'])]
      · rfl
  · obtain ⟨hpk, hi, hnc1, hsg, hsci, hssel, hspec, hct, hcb, hbr⟩ := hst hs
    have hc : R.rp.copies = [R.rp.top ++ (R.rp.sg, R.rp.sci) :: R.rp.bot] := by
      simp [RPin.copies, hs]
    subst hpk; subst hi
    simp only [pinF, Bool.false_xor]
    have ev1 := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hct u
    simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at ev1
    rw [ev1]
    generalize hu' : tau hsat R.rp.top u = u'
    rw [gate_spec hsat h0 h1 hsg hspec u']
    simp only [steerSpec]
    rw [if_pos hsci]
    have ev2 := chkT_sound hsat h0 h1 _ fuel _ _ _ _ hcb (wf hsat R.rp.sg R.rp.sci u')
    simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at ev2
    rw [ev2, hsrc]
    have hfl := fany_list (fun π => ccOf rn x cv s (tau hsat π u) && (svR hsat R u == br)) [] _ _ hlen
    try simp only at hfl ⊢
    rw [hfl, hc]
    simp only [List.any_cons, List.any_nil, Bool.or_false]
    rw [tau_append]
    simp only [tau]
    rw [hu']
    congr 1
    unfold svR; rw [hbr, hu']
    have hsb := sv_br (fun i => vals hsat R.rp.sg i u') R.rp.ssel
    try simp only at hsb
    rw [hsb]
    unfold foldM vals
    apply Bool.eq_iff_iff.mpr; rw [List.all_eq_true, List.all_eq_true]
    constructor
    · intro H sb hsb; have := H sb hsb; simp only [if_pos (hssel sb hsb)] at this ⊢; exact this
    · intro H sb hsb; have := H sb hsb; simp only [if_pos (hssel sb hsb)] at this ⊢; exact this

end

/-! ## 3. One arbiter in the parsed design -/

/-- **Arbiter data** (from the certificate generator; every field is checked by `ArbOK`).
Virtual nodes `jc` (ctl), `jg1 jg2` (grants), `js1 js2` (shadows), `jR` (R0), the real node `jA`
driving A0. Gates of `d`: `gG1` = ugrant O5 (`g1`), `gG2` = ugrant O6 (`g2`), `gR` = ustate O5
(`R0`), `gQ` = ustate O6 (`q`). `iXY` = the LUT input index of a read, `pXY` the route path below
that input down to the net it reads (the request nets `rq1.w`, `rq2.w`, the `q` wire, A0's wire,
the reset wire). -/
structure ArbD (N : Nat) where
  jc : Fin N
  jg1 : Fin N
  jg2 : Fin N
  js1 : Fin N
  js2 : Fin N
  jR : Fin N
  jA : Fin N
  gG1 : Nat
  gG2 : Nat
  gR : Nat
  gQ : Nat
  i1g1 : Nat
  iqg1 : Nat
  i2g2 : Nat
  iqg2 : Nat
  i1R : Nat
  i2R : Nat
  iqR : Nat
  p1g1 : Path
  pqg1 : Path
  p2g2 : Path
  pqg2 : Path
  p1R : Path
  p2R : Path
  pqR : Path
  i1Q : Nat
  i2Q : Nat
  iqQ : Nat
  irQ : Nat
  iA : Nat
  p1Q : Path
  p2Q : Path
  pqQ : Path
  prQ : Path
  pA : Path
  rq1 : ReqD
  rq2 : ReqD

section
variable {N : Nat} (d : Design) (a : ArbD N)

/-- Full read paths (LUT input first, then the route down to the net). -/
def P1g1 : Path := (a.gG1, a.i1g1) :: a.p1g1
def Pqg1 : Path := (a.gG1, a.iqg1) :: a.pqg1
def P2g2 : Path := (a.gG2, a.i2g2) :: a.p2g2
def Pqg2 : Path := (a.gG2, a.iqg2) :: a.pqg2
def P1R : Path := (a.gR, a.i1R) :: a.p1R
def P2R : Path := (a.gR, a.i2R) :: a.p2R
def PqR : Path := (a.gR, a.iqR) :: a.pqR
def PA : Path := (a.gQ, a.iA) :: a.pA

/-- The per-pin band of a read path. -/
def bd (P : Path) : Nat × Nat := (plo d P, phi d P)

/-- **The cell-level per-pin bands** of this arbiter in `d` (`Events8Arb.ArbBands`; indices as
`ArbPin`: `I0 = r1, I1 = r2, I2 = q, I4 = A0`; unused entries `(1,1)`). -/
def bandsOf : ArbBands where
  st := fun i => if i.val = 4 then bd d (PA a) else (1, 1)
  r0 := fun i => if i.val = 0 then bd d (P1R a) else if i.val = 1 then bd d (P2R a) else
    if i.val = 2 then bd d (PqR a) else (1, 1)
  g1 := fun i => if i.val = 0 then bd d (P1g1 a) else if i.val = 2 then bd d (Pqg1 a) else (1, 1)
  g2 := fun i => if i.val = 1 then bd d (P2g2 a) else if i.val = 2 then bd d (Pqg2 a) else (1, 1)

/-- The `q` wire: ustate O6's output. -/
def qW : Nat := (gt d a.gQ).out

end

/-- One read: gate `gi` input `i` is the net `w` through the route path `p` (decidable). -/
def RdP (d : Design) (fuel gi i : Nat) (p : Path) (w : Nat) : Prop :=
  gi < d.gates.length ∧ i < (gt d gi).k ∧ pathOK d ((gi, i) :: p) = true ∧
  chkT d w fuel true ((gt d gi).ins.getD i 0) [p] = some false

instance (d : Design) (fuel gi i : Nat) (p : Path) (w : Nat) : Decidable (RdP d fuel gi i p w) := by
  unfold RdP; exact inferInstance

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include h0 h1

theorem rdP_val {fuel gi i w : Nat} {p : Path} (h : RdP d fuel gi i p w) (t : Nat) :
    (if i < (gt d gi).k then x (d.wire ((gt d gi).ins.getD i 0)) (wf hsat gi i t) else false) =
      x (d.wire w) (tau hsat ((gi, i) :: p) t) := by
  obtain ⟨_, hi, _, hc⟩ := h
  rw [if_pos hi]
  have ev := chkT_sound hsat h0 h1 _ _ _ _ _ _ hc (wf hsat gi i t)
  simp only [Bool.false_xor, specL, ite_true, List.all_cons, List.all_nil, Bool.and_true] at ev
  rw [ev]; rfl

end

/-! ### The checks on one arbiter -/

section
variable {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (fuel rw : Nat)

def pin0 (j : Fin N) : Fin (net.ar j) := ⟨0, net.ar_pos j⟩

/-- **A reader node** of the corrected core (grant or shadow) on the request `R` of source `s`:
shape (virtual, stage, reset 0, two pins, no bubbles, `F = Q = (1,1)`), pin 0 = the request
(source `s`, `ReqOK`, copy bands = request band `[lr, hr]` plus each copy's path, the copy
window), pin 1 = the filtered ctl pin (source `jc`, branch `brc`, band `[lc, hc]`). -/
def RdNodeOK (j jc s : Fin N) (brc : Bool) (lr hr lc hc : Nat) (R : ReqD) : Prop :=
  (rn j).virt = true ∧ net.mg j = false ∧ net.v j = false ∧ net.ar j = 2 ∧
  b.loF j = 1 ∧ b.hiF j = 1 ∧ b.loQ j = 1 ∧ b.hiQ j = 1 ∧ 1 ≤ lr ∧ 1 ≤ lc ∧
  ∀ p : Fin (net.ar j), net.neg j p = false ∧
    (p.val = 0 → net.src j p = s ∧
      ReqOK d rn fuel s (net.pk j p) (net.inv j p) (net.op j p) (net.nc j p) (net.br j p) R ∧
      (∀ i : Fin (net.nc j p), b.loC j p i = plo d (R.rp.copies.getD i.val []) + lr ∧
        b.hiC j p i = phi d (R.rp.copies.getD i.val []) + hr) ∧
      (∀ i i' : Fin (net.nc j p), i'.val = i.val + 1 →
        b.hiC j p i' - b.loC j p i ≤ b.dw j p i.val ∧ b.hiC j p i - b.loC j p i' ≤ b.dw j p i.val)) ∧
    (p.val = 1 → net.src j p = jc ∧ net.pk j p = PK.filt ∧ net.inv j p = false ∧ net.nc j p = 1 ∧
      net.br j p = brc ∧ ∀ i : Fin (net.nc j p), b.loC j p i = lc ∧ b.hiC j p i = hc)

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance (j jc s : Fin N) (brc : Bool) (lr hr lc hc : Nat) (R : ReqD) :
    Decidable (RdNodeOK d net b rn fuel j jc s brc lr hr lc hc R) := by
  unfold RdNodeOK; exact inferInstance

/-- **ctl**: virtual, stage, reset 0, one plain inverted pin from `jA` (real), band `[lo, 10^12]`. -/
def CtlOK (jc jA : Fin N) (lo : Nat) : Prop :=
  (rn jc).virt = true ∧ (rn jc).hasW = false ∧ net.mg jc = false ∧ net.v jc = false ∧ net.ar jc = 1 ∧
  b.loF jc = 1 ∧ b.hiF jc = 1 ∧ b.loQ jc = 1 ∧ b.hiQ jc = 1 ∧ (rn jA).virt = false ∧ 1 ≤ lo ∧
  ∀ p : Fin (net.ar jc), net.src jc p = jA ∧ net.pk jc p = PK.plain ∧ net.inv jc p = true ∧
    net.neg jc p = false ∧ net.nc jc p = 1 ∧ ∀ i : Fin (net.nc jc p), b.loC jc p i = lo ∧ b.hiC jc p i = 10 ^ 12

instance (jc jA : Fin N) (lo : Nat) : Decidable (CtlOK net b rn jc jA lo) := by
  unfold CtlOK; exact inferInstance

/-- **R0**: virtual merge with the real wire `ow`, two plain pins from the shadows, all bands `(1,1)`. -/
def MgOK (jR js1 js2 : Fin N) (ow : Nat) : Prop :=
  (rn jR).virt = true ∧ (rn jR).hasW = true ∧ (rn jR).ow = ow ∧ net.mg jR = true ∧ net.v jR = false ∧
  net.ar jR = 2 ∧ b.loF jR = 1 ∧ b.hiF jR = 1 ∧ b.loQ jR = 1 ∧ b.hiQ jR = 1 ∧
  ∀ p : Fin (net.ar jR), net.inv jR p = false ∧ net.neg jR p = false ∧ net.pk jR p = PK.plain ∧
    net.nc jR p = 1 ∧ (p.val = 0 → net.src jR p = js1) ∧ (p.val = 1 → net.src jR p = js2) ∧
    ∀ i : Fin (net.nc jR p), b.loC jR p i = 1 ∧ b.hiC jR p i = 1

instance (jR js1 js2 : Fin N) (ow : Nat) : Decidable (MgOK net b rn jR js1 js2 ow) := by
  unfold MgOK; exact inferInstance

/-- **`ArbOK`** (decidable): the arbiter `a` is a `bd_arbiter` core of `d` whose virtual nodes are
the corrected core with the bands `CoreOf (bandsOf d a)`. -/
def ArbOK (a : ArbD N) : Prop :=
  let B := bandsOf d a
  let K := kOf B
  -- the four LUTs and their reads (bd_arbiter's functions, evaluated on the INITs)
  RdP d fuel a.gG1 a.i1g1 a.p1g1 a.rq1.w ∧ RdP d fuel a.gG1 a.iqg1 a.pqg1 (qW d a) ∧
  InitSpec (gt d a.gG1) (fun v => v a.i1g1 && v a.iqg1) ∧
  RdP d fuel a.gG2 a.i2g2 a.p2g2 a.rq2.w ∧ RdP d fuel a.gG2 a.iqg2 a.pqg2 (qW d a) ∧
  InitSpec (gt d a.gG2) (fun v => v a.i2g2 && !v a.iqg2) ∧
  RdP d fuel a.gR a.i1R a.p1R a.rq1.w ∧ RdP d fuel a.gR a.i2R a.p2R a.rq2.w ∧
  RdP d fuel a.gR a.iqR a.pqR (qW d a) ∧
  InitSpec (gt d a.gR) (fun v => (v a.i1R && v a.iqR) || (v a.i2R && !v a.iqR)) ∧
  a.gQ < d.gates.length ∧
  RdP d fuel a.gQ a.i1Q a.p1Q a.rq1.w ∧ RdP d fuel a.gQ a.i2Q a.p2Q a.rq2.w ∧
  RdP d fuel a.gQ a.iqQ a.pqQ (qW d a) ∧ RdP d fuel a.gQ a.irQ a.prQ rw ∧
  RdP d fuel a.gQ a.iA a.pA (rn a.jA).ow ∧
  InitSpec (gt d a.gQ) (fun v => v a.irQ || (if v a.iA then v a.iqQ else
    ((v a.i1Q && !v a.i2Q) || (v a.iqQ && !(!v a.i1Q && v a.i2Q))))) ∧
  -- the virtual nodes: corrected-core shape and bands
  [a.jc, a.jg1, a.jg2, a.js1, a.js2, a.jR].Nodup ∧
  CtlOK net b rn a.jc a.jA (loCtl B) ∧
  RdNodeOK d net b rn fuel a.jg1 a.jc (net.src a.jg1 (pin0 net a.jg1)) false
    (rdG (B.g1 0) (B.g1 2) K).loR (rdG (B.g1 0) (B.g1 2) K).hiR (rdG (B.g1 0) (B.g1 2) K).loC
    (rdG (B.g1 0) (B.g1 2) K).hiC a.rq1 ∧
  RdNodeOK d net b rn fuel a.jg2 a.jc (net.src a.jg2 (pin0 net a.jg2)) true
    (rdG (B.g2 1) (B.g2 2) K).loR (rdG (B.g2 1) (B.g2 2) K).hiR (rdG (B.g2 1) (B.g2 2) K).loC
    (rdG (B.g2 1) (B.g2 2) K).hiC a.rq2 ∧
  RdNodeOK d net b rn fuel a.js1 a.jc (net.src a.jg1 (pin0 net a.jg1)) false
    (rdS (B.r0 0) (B.r0 2) K).loR (rdS (B.r0 0) (B.r0 2) K).hiR (rdS (B.r0 0) (B.r0 2) K).loC
    (rdS (B.r0 0) (B.r0 2) K).hiC a.rq1 ∧
  RdNodeOK d net b rn fuel a.js2 a.jc (net.src a.jg2 (pin0 net a.jg2)) true
    (rdS (B.r0 1) (B.r0 2) K).loR (rdS (B.r0 1) (B.r0 2) K).hiR (rdS (B.r0 1) (B.r0 2) K).loC
    (rdS (B.r0 1) (B.r0 2) K).hiC a.rq2 ∧
  (rn a.jg1).hasW = true ∧ (rn a.jg1).ow = (gt d a.gG1).out ∧
  (rn a.jg2).hasW = true ∧ (rn a.jg2).ow = (gt d a.gG2).out ∧
  (rn a.js1).hasW = false ∧ (rn a.js2).hasW = false ∧
  MgOK net b rn a.jR a.js1 a.js2 (gt d a.gR).out ∧
  -- band side conditions of core_of_settle
  1 ≤ (B.g1 0).1 ∧ 1 ≤ (B.g2 1).1 ∧ 3 ≤ (B.r0 0).1 ∧ 3 ≤ (B.r0 1).1 ∧ 2 ≤ K ∧
  K + 2 ≤ (B.g1 2).1 ∧ K + 2 ≤ (B.g2 2).1 ∧ K + 4 ≤ (B.r0 2).1

set_option synthInstance.maxSize 8192 in
set_option synthInstance.maxHeartbeats 800000 in
instance (a : ArbD N) : Decidable (ArbOK d net b rn fuel rw a) := by
  unfold ArbOK; exact inferInstance

end

/-! ### The cell-level signals and warps of an arbiter, and its trace conditions -/

section
variable {N : Nat} {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x) (rn : Fin N → RNode)
  (a : ArbD N)

/-- The per-pin reads of `R0` (ustate O5), `g1`, `g2` (ugrant O5 / O6) as `core_of_settle` takes
them: the composed warps of the full read paths (unused indices: a 1-step shift). -/
noncomputable def frOf : Fin 5 → Nat → Nat := fun i =>
  if i.val = 0 then tau hsat (P1R a) else if i.val = 1 then tau hsat (P2R a) else
  if i.val = 2 then tau hsat (PqR a) else fun t => t - 1
noncomputable def f1Of : Fin 3 → Nat → Nat := fun i =>
  if i.val = 0 then tau hsat (P1g1 a) else if i.val = 2 then tau hsat (Pqg1 a) else fun t => t - 1
noncomputable def f2Of : Fin 3 → Nat → Nat := fun i =>
  if i.val = 1 then tau hsat (P2g2 a) else if i.val = 2 then tau hsat (Pqg2 a) else fun t => t - 1
/-- ustate O6's read of A0. -/
noncomputable def f4Of : Nat → Nat := tau hsat (PA a)

/-- The arbiter's signals on the wires of `d`. -/
def r1S : Sig := x (d.wire a.rq1.w)
def r2S : Sig := x (d.wire a.rq2.w)
def qS : Sig := x (d.wire (qW d a))
def aS : Sig := x (d.wire (rn a.jA).ow)
def g1S : Sig := x (d.wire (gt d a.gG1).out)
def g2S : Sig := x (d.wire (gt d a.gG2).out)
def R0S : Sig := x (d.wire (gt d a.gR).out)

/-- **The trace conditions of one arbiter** (hypotheses; NOT checked): the outputs are low on the
quiet start `[0, T0 + 2]`; the settle bound (`hstall`, every ustate time within `H` of an ok time:
A0 read high, or `q` settled for the rest of the A0-low phase); and `RdOK` (B1 = RT1 / RT1b,
B2 = rise only from settled reads, C = request falls read only at unsettled times) for the four
readers, all against ustate O6's read of A0. -/
structure ArbCond (T0 H : Nat) : Prop where
  low : ∀ t, t ≤ T0 + 2 → g1S (x := x) a t = false ∧ g2S (x := x) a t = false ∧ R0S (x := x) a t = false
  t1 : ((bandsOf d a).g1 2).1 ≤ T0
  t2 : ((bandsOf d a).g2 2).1 ≤ T0
  t3 : ((bandsOf d a).r0 2).1 ≤ T0 + 2
  stall : ∀ v, ∃ v', v' ≤ v ∧ v ≤ v' + H ∧
    (v' = 0 ∨ Ok (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a) (v' + 1 - kOf (bandsOf d a)))
  hi : H + kOf (bandsOf d a) + ((bandsOf d a).st 4).2 ≤ 10 ^ 12
  e1 : RdOK (Settled (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a)) (r1S (x := x) a) (qS (x := x) a)
    (g1S (x := x) a) (f1Of hsat a 0) (f1Of hsat a 2) T0
  e2 : RdOK (Settled (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a)) (r2S (x := x) a)
    (fun u => !qS (x := x) a u) (g2S (x := x) a) (f2Of hsat a 1) (f2Of hsat a 2) T0
  e3 : RdOK (Settled (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a)) (r1S (x := x) a) (qS (x := x) a)
    (fun t => r1S (x := x) a (frOf hsat a 0 (t + 2)) && qS (x := x) a (frOf hsat a 2 (t + 2)))
    (fun t => frOf hsat a 0 (t + 2)) (fun t => frOf hsat a 2 (t + 2)) T0
  e4 : RdOK (Settled (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a)) (r2S (x := x) a)
    (fun u => !qS (x := x) a u)
    (fun t => r2S (x := x) a (frOf hsat a 1 (t + 2)) && !qS (x := x) a (frOf hsat a 2 (t + 2)))
    (fun t => frOf hsat a 1 (t + 2)) (fun t => frOf hsat a 2 (t + 2)) T0

end

/-! ### `arb_core`: the arbiter of `d` is a behaviour of the corrected core -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {fuel rw : Nat}
  {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include h0 h1

/-- **`arb_core`**: under the per-pin semantics of `d`, an `ArbOK` arbiter satisfying its trace
conditions is a behaviour of the corrected core `CoreOf (bandsOf d a)`, with the common reader
reset `decide (u < T0)` (`CoreOfR`), on the wires of `d`. -/
theorem arb_core {a : ArbD N} (hA : ArbOK d net b rn fuel rw a) {T0 H : Nat}
    (hc : ArbCond hsat rn a T0 H) :
    CoreOfR (bandsOf d a) (fun u => decide (u < T0)) (r1S (x := x) a) (r2S (x := x) a)
      (aS (x := x) rn a) (R0S (x := x) a) (g1S (x := x) a) (g2S (x := x) a) := by
  obtain ⟨r11, r1q, s1, r22, r2q, s2, rR1, rR2, rRq, sR, _hgQ, _, _, _, _, rQA, _, _, _, _, _, _, _,
    _, _, _, _, _, _, _, hb1, hb2, hb3, hb4, hK2, hq1, hq2, hq3⟩ := hA
  -- warps
  have wP : ∀ {gi i w : Nat} {p : Path}, RdP d fuel gi i p w → Warp (plo d ((gi, i) :: p)) (phi d ((gi, i) :: p))
      (tau hsat ((gi, i) :: p)) := fun h => tau_warp hsat _ h.2.2.1
  have hfr : Rd 5 (bandsOf d a).r0 (frOf hsat a) := by
    intro i
    simp only [bandsOf, frOf, bd]
    by_cases e0 : i.val = 0
    · simp only [e0, ite_true]; exact wP rR1
    · by_cases e1 : i.val = 1
      · simp only [e1, ite_true]; exact wP rR2
      · by_cases e2 : i.val = 2
        · simp only [e2, ite_true]; exact wP rRq
        · simp only [e0, e1, e2, ite_false]; exact shiftW1
  have hf1 : Rd 3 (bandsOf d a).g1 (f1Of hsat a) := by
    intro i
    simp only [bandsOf, f1Of, bd]
    by_cases e0 : i.val = 0
    · simp only [e0, ite_true]; exact wP r11
    · by_cases e2 : i.val = 2
      · simp only [e2, ite_true]; exact wP r1q
      · simp only [e0, e2, ite_false]; exact shiftW1
  have hf2 : Rd 3 (bandsOf d a).g2 (f2Of hsat a) := by
    intro i
    simp only [bandsOf, f2Of, bd]
    by_cases e1 : i.val = 1
    · simp only [e1, ite_true]; exact wP r22
    · by_cases e2 : i.val = 2
      · simp only [e2, ite_true]; exact wP r2q
      · simp only [e1, e2, ite_false]; exact shiftW1
  have hf4 : Warp ((bandsOf d a).st 4).1 ((bandsOf d a).st 4).2 (f4Of hsat a) := by
    simp only [bandsOf, bd]; exact wP rQA
  -- the gate equations
  have hR0 : ∀ t, R0S (x := x) a t = o5B ARB_ST [r1S (x := x) a (frOf hsat a 0 t), r2S (x := x) a (frOf hsat a 1 t),
      qS (x := x) a (frOf hsat a 2 t), (fun _ => false) (frOf hsat a 3 t), aS (x := x) rn a (frOf hsat a 4 t), true] := by
    intro t
    rw [r0_eq]
    unfold R0S
    rw [gate_spec hsat h0 h1 rR1.1 sR t]
    simp only
    rw [rdP_val hsat h0 h1 rR1 t, rdP_val hsat h0 h1 rR2 t, rdP_val hsat h0 h1 rRq t]
    rfl
  have hg1 : ∀ t, g1S (x := x) a t = o5B GRANT [r1S (x := x) a (f1Of hsat a 0 t), r2S (x := x) a (f1Of hsat a 1 t),
      qS (x := x) a (f1Of hsat a 2 t), false, false, true] := by
    intro t
    rw [g1_eq]
    unfold g1S
    rw [gate_spec hsat h0 h1 r11.1 s1 t]
    simp only
    rw [rdP_val hsat h0 h1 r11 t, rdP_val hsat h0 h1 r1q t]
    rfl
  have hg2 : ∀ t, g2S (x := x) a t = o6B GRANT [r1S (x := x) a (f2Of hsat a 0 t), r2S (x := x) a (f2Of hsat a 1 t),
      qS (x := x) a (f2Of hsat a 2 t), false, false, true] := by
    intro t
    rw [g2_eq]
    unfold g2S
    rw [gate_spec hsat h0 h1 r22.1 s2 t]
    simp only
    rw [rdP_val hsat h0 h1 r22 t, rdP_val hsat h0 h1 r2q t]
    rfl
  -- the canonical ctl, and core_of_en_rst
  have hcv := ctlc_vctl (a := aS (x := x) rn a) (q := qS (x := x) a) hf4 hK2 hc.stall hc.hi
  have hc' : VCtl (loCtl (bandsOf d a)) (10 ^ 12) (aS (x := x) rn a)
      (ctlc (aS (x := x) rn a) (qS (x := x) a) (f4Of hsat a) (kOf (bandsOf d a))) := by
    simp only [loCtl]; exact hcv
  have hb1' : ∀ u : Bool, u = (u == true) := fun u => by cases u <;> rfl
  have hb2' : ∀ u : Bool, (!u) = (u == false) := fun u => by cases u <;> rfl
  have E1 := enOK_of_rd (br := true) hK2 (fun u => hb1' (qS (x := x) a u)) hc.e1
  have E2 := enOK_of_rd (br := false) hK2 (fun u => hb2' (qS (x := x) a u)) hc.e2
  have E3 := enOK_of_rd (br := true) hK2 (fun u => hb1' (qS (x := x) a u)) hc.e3
  have E4 := enOK_of_rd (br := false) hK2 (fun u => hb2' (qS (x := x) a u)) hc.e4
  exact core_of_en_rst (rs := fun _ => false) (a := aS (x := x) rn a) (q := qS (x := x) a)
    (bandsOf d a) (frOf hsat a) (f1Of hsat a) (f2Of hsat a) hfr hf1 hf2 hR0 hg1 hg2 T0
    hc.low hb1 hb2 hb3 hb4 hq1 hq2 hq3 hc.t1 hc.t2 hc.t3 hc' E1 E2 E3 E4

end

/-! ## 4. Node behaviours (`ND7`) of the six virtual nodes -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {fuel : Nat}
  {x : Fin d.n → Sig} (hsat : SatPin d plG x) {cv : Fin N → Sig}
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
  (hW : ∀ s, (rn s).virt = true → (rn s).hasW = true → ∀ t, x (d.wire (rn s).ow) t = cv s t)


theorem ccOf_virt {j : Fin N} (h : (rn j).virt = true) (t : Nat) : ccOf rn x cv j t = cv j t := by
  unfold ccOf; rw [if_pos h]

include hsat h0 h1 hW

/-- **A reader node**: a `VRdR` (the corrected core's grant / shadow, reset `ρ`) on the request
wire `R.w`, at a node passing `RdNodeOK` with the ctl branch `!br`, is an `ND7` behaviour with
reset `ρ` (the select of the ctl pin is the negated core select: the certificate's labels). -/
theorem nd7_rd {j jc s : Fin N} {R : ReqD} {lr hr lc hc : Nat} {br : Bool} {ρ ctl y : Sig}
    (hn : RdNodeOK d net b rn fuel j jc s (!br) lr hr lc hc R)
    (hcj : ∀ t, cv j t = y t) (hcc : ∀ t, cv jc t = ctl t) (hvc : (rn jc).virt = true)
    (hv : VRdR lr hr lc hc br ρ (x (d.wire R.w)) ctl y) :
    Nonempty {nd : ND7 net b (ccOf rn x cv) j // nd.r = ρ} := by
  obtain ⟨hvj, hmg, hv0, har, hF1, hF2, hQ1, hQ2, hlr, hlc, hp⟩ := hn
  obtain ⟨F, GR, GC, Q, sv, wF, wGR, wGC, wQ, hr0, hra, heq⟩ := hv
  have hpv : ∀ p : Fin (net.ar j), p.val = 0 ∨ p.val = 1 := fun p => by have := p.isLt; omega
  have hwG : ∀ (p : Fin (net.ar j)) (i : Fin (net.nc j p)), Warp (b.loC j p i) (b.hiC j p i)
      (fun u => if p.val = 0 then tau hsat (R.rp.copies.getD i.val []) (GR u) else GC u) := by
    intro p i
    rcases hpv p with e | e
    · obtain ⟨_, h0', -⟩ := hp p
      obtain ⟨_, ⟨_, _, _, hpaths, _⟩, hb, _⟩ := h0' e
      simp only [e, ite_true]
      rw [(hb i).1, (hb i).2]
      have hmem : R.rp.copies.getD i.val [] ∈ R.rp.copies ∨ R.rp.copies.getD i.val [] = [] := by
        rw [List.getD_eq_getElem?_getD]
        cases hh : R.rp.copies[i.val]? with
        | none => right; rfl
        | some π => left; exact List.mem_of_getElem? hh
      have hok : pathOK d (R.rp.copies.getD i.val []) = true := by
        rcases hmem with hm | hm
        · exact hpaths _ hm
        · rw [hm]; rfl
      exact warp_comp (tau_warp hsat _ hok) wGR
    · obtain ⟨_, -, h1'⟩ := hp p
      obtain ⟨_, _, _, _, _, hb⟩ := h1' e
      have e0 : p.val ≠ 0 := by omega
      simp only [e0, ite_false]
      rw [(hb i).1, (hb i).2]; exact wGC
  refine ⟨⟨{
    pin := fun p u => if p.val = 0 then x (d.wire R.w) (GR u) else (ctl (GC u) && ((!sv u) == !br))
    q := fun u => ccOf rn x cv j (Q u)
    r := ρ
    sv := fun p u => if p.val = 0 then svR hsat R (GR u) else !sv u
    F := F
    G := fun p i u => if p.val = 0 then tau hsat (R.rp.copies.getD i.val []) (GR u) else GC u
    Q := Q
    wF := by rw [hF1, hF2]; exact wF
    wG := ?_
    wQ := by rw [hQ1, hQ2]; exact wQ
    loF1 := by rw [hF1]; exact Nat.le_refl 1
    loC1 := ?_
    loQ1 := by rw [hQ1]; exact Nat.le_refl 1
    hc := ?_
    hpin := ?_
    hq := fun t => rfl
    r0 := hr0
    ranti := hra
    hskew := ?_ }, rfl⟩⟩
  · exact hwG
  · -- loC1
    intro p i
    rcases hpv p with e | e
    · obtain ⟨_, h0', -⟩ := hp p
      obtain ⟨_, _, hb, _⟩ := h0' e
      rw [(hb i).1]; omega
    · obtain ⟨_, -, h1'⟩ := hp p
      obtain ⟨_, _, _, _, _, hb⟩ := h1' e
      rw [(hb i).1]; exact hlc
  · -- hc
    intro t
    rw [ccOf_virt (cv := cv) hvj, hcj t, heq t, hmg]
    simp only [Bool.false_eq_true, ite_false, hv0]
    split
    · rfl
    · rw [ccOf_virt (cv := cv) hvj, hcj]
      have hneg : ∀ p : Fin (net.ar j), net.neg j p = false := fun p => (hp p).1
      have hfun : (fun p : Fin (net.ar j) => (if p.val = 0 then x (d.wire R.w) (GR (F t)) else
          (ctl (GC (F t)) && ((!sv (F t)) == !br))) ^^ net.neg j p) =
          (fun p : Fin (net.ar j) => (fun k : Nat => if k = 0 then x (d.wire R.w) (GR (F t)) else
          (ctl (GC (F t)) && (sv (F t) == br))) p.val) := by
        funext p; rw [hneg p, beq_not]; simp
      rw [hfun]
      exact (cel_reidx2 har (fun k : Nat => if k = 0 then x (d.wire R.w) (GR (F t)) else
        (ctl (GC (F t)) && (sv (F t) == br))) _).symm
  · -- hpin
    intro p t
    rcases hpv p with e | e
    · obtain ⟨_, h0', -⟩ := hp p
      obtain ⟨hs, hR, _, _⟩ := h0' e
      simp only [e, ite_true]
      rw [req_val hsat h0 h1 hW hR (GR t), hs]
      cases net.pk j p <;> rfl
    · obtain ⟨_, -, h1'⟩ := hp p
      obtain ⟨hs, hpk, hinv, hnc, hbr, _⟩ := h1' e
      have e0 : p.val ≠ 0 := by omega
      simp only [e0, ite_false, hpk, hinv, Bool.false_xor, hs, hbr]
      rw [ccOf_virt (cv := cv) hvc, hcc]
      exact (fany_const (by rw [hnc]; exact Nat.zero_lt_one) _).symm
  · -- hskew
    intro p i i' hii s'
    rcases hpv p with e | e
    · obtain ⟨_, h0', -⟩ := hp p
      obtain ⟨_, _, _, hdw⟩ := h0' e
      obtain ⟨d1, d2⟩ := hdw i i' hii
      exact ⟨skew_of_bands (hwG p i) (hwG p i') d1 s', skew_of_bands (hwG p i') (hwG p i) d2 s'⟩
    · obtain ⟨_, -, h1'⟩ := hp p
      obtain ⟨_, _, _, hnc, _, _⟩ := h1' e
      have := i'.isLt; have := i.isLt; rw [hnc] at *; omega


/-- **ctl**: a `VCtl` of the A0 source wire at a node passing `CtlOK` is an `ND7` behaviour. -/
theorem nd7_ctl {jc jA : Fin N} {lo : Nat} {ctl : Sig} (hn : CtlOK net b rn jc jA lo)
    (hcc : ∀ t, cv jc t = ctl t) (hv : VCtl lo (10 ^ 12) (x (d.wire (rn jA).ow)) ctl) :
    Nonempty (ND7 net b (ccOf rn x cv) jc) := by
  obtain ⟨hvj, _, hmg, hv0, har, hF1, hF2, hQ1, hQ2, hAr, hlo, hp⟩ := hn
  obtain ⟨F, G, Q, r, wF, wG, wQ, hr0, hra, heq⟩ := hv
  refine ⟨{
    pin := fun _ u => !(x (d.wire (rn jA).ow) (G u))
    q := fun u => ccOf rn x cv jc (Q u)
    r := r
    sv := fun _ _ => false
    F := F
    G := fun _ _ => G
    Q := Q
    wF := by rw [hF1, hF2]; exact wF
    wG := fun p i => by rw [((hp p).2.2.2.2.2 i).1, ((hp p).2.2.2.2.2 i).2]; exact wG
    wQ := by rw [hQ1, hQ2]; exact wQ
    loF1 := by rw [hF1]; exact Nat.le_refl 1
    loC1 := fun p i => by rw [((hp p).2.2.2.2.2 i).1]; exact hlo
    loQ1 := by rw [hQ1]; exact Nat.le_refl 1
    hc := ?_
    hpin := ?_
    hq := fun t => rfl
    r0 := hr0
    ranti := hra
    hskew := ?_ }⟩
  · intro t
    rw [ccOf_virt (cv := cv) hvj, hcc t, heq t, hmg]
    simp only [Bool.false_eq_true, ite_false, hv0]
    split
    · rfl
    · rw [ccOf_virt (cv := cv) hvj, hcc]
      have hneg : ∀ p : Fin (net.ar jc), net.neg jc p = false := fun p => (hp p).2.2.2.1
      have hfun : (fun p : Fin (net.ar jc) => (!(x (d.wire (rn jA).ow) (G (F t)))) ^^ net.neg jc p) =
          (fun _ : Fin (net.ar jc) => !(x (d.wire (rn jA).ow) (G (F t)))) := by
        funext p; rw [hneg p]; simp
      rw [hfun]
      exact (cel_reidx1 har _ _).symm
  · intro p t
    obtain ⟨hs, hpk, hinv, _, hnc, _⟩ := hp p
    simp only [hpk, hinv, hs]
    have hcA : ∀ u, ccOf rn x cv jA u = x (d.wire (rn jA).ow) u := fun u => by
      unfold ccOf; rw [hAr]; rfl
    simp only [hcA]
    rw [fany_const (by rw [hnc]; exact Nat.zero_lt_one)]
    simp
  · intro p i i' hii _
    have := i'.isLt; have := i.isLt; rw [(hp p).2.2.2.2.1] at *; omega

/-- **R0**: a `(1,1)` merge of the two shadow signals at a node passing `MgOK` is an `ND7` behaviour. -/
theorem nd7_mg {jR js1 js2 : Fin N} {ow : Nat} {s1 s2 : Sig} (hn : MgOK net b rn jR js1 js2 ow)
    (h1v : (rn js1).virt = true) (h2v : (rn js2).virt = true)
    (hc1 : ∀ t, cv js1 t = s1 t) (hc2 : ∀ t, cv js2 t = s2 t) (hcR : ∀ t, cv jR t = x (d.wire ow) t)
    (hv : VMerge 1 1 1 1 1 1 s1 s2 (x (d.wire ow))) :
    Nonempty (ND7 net b (ccOf rn x cv) jR) := by
  obtain ⟨hvj, _, _, hmg, _, har, hF1, hF2, hQ1, hQ2, hp⟩ := hn
  obtain ⟨F, G1, G2, wF, w1, w2, heq⟩ := hv
  have hpv : ∀ p : Fin (net.ar jR), p.val = 0 ∨ p.val = 1 := fun p => by have := p.isLt; omega
  refine ⟨{
    pin := fun p u => if p.val = 0 then s1 (G1 u) else s2 (G2 u)
    q := fun u => ccOf rn x cv jR (u - 1)
    r := fun _ => true
    sv := fun _ _ => false
    F := F
    G := fun p _ u => if p.val = 0 then G1 u else G2 u
    Q := fun u => u - 1
    wF := by rw [hF1, hF2]; exact wF
    wG := ?_
    wQ := by rw [hQ1, hQ2]; exact shiftW1
    loF1 := by rw [hF1]; exact Nat.le_refl 1
    loC1 := fun p i => by rw [((hp p).2.2.2.2.2.2 i).1]; exact Nat.le_refl 1
    loQ1 := by rw [hQ1]; exact Nat.le_refl 1
    hc := ?_
    hpin := ?_
    hq := fun t => rfl
    r0 := rfl
    ranti := fun _ _ _ _ => rfl
    hskew := ?_ }⟩
  · intro p i
    rw [((hp p).2.2.2.2.2.2 i).1, ((hp p).2.2.2.2.2.2 i).2]
    rcases hpv p with e | e
    · simp only [e, ite_true]; exact w1
    · have e0 : p.val ≠ 0 := by omega
      simp only [e0, ite_false]; exact w2
  · intro t
    rw [ccOf_virt (cv := cv) hvj, hcR t, heq t, hmg]
    simp only [ite_true]
    exact (fany_reidx2 har (fun k : Nat => if k = 0 then s1 (G1 (F t)) else s2 (G2 (F t)))).symm
  · intro p t
    obtain ⟨hinv, _, hpk, hnc, hs1, hs2, _⟩ := hp p
    simp only [hpk, hinv, Bool.false_xor]
    rcases hpv p with e | e
    · simp only [e, ite_true, hs1 e]
      rw [ccOf_virt (cv := cv) h1v, hc1]
      exact (fany_const (by rw [hnc]; exact Nat.zero_lt_one) _).symm
    · have e0 : p.val ≠ 0 := by omega
      simp only [e0, ite_false, hs2 e]
      rw [ccOf_virt (cv := cv) h2v, hc2]
      exact (fany_const (by rw [hnc]; exact Nat.zero_lt_one) _).symm
  · intro p i i' hii _
    have := i'.isLt; have := i.isLt; rw [(hp p).2.2.2.1] at *; omega

end


/-! ## 5. All arbiters: `HARB7'` and `HRst` -/

/-- The six virtual nodes of an arbiter. -/
def ArbD.nodes {N : Nat} (a : ArbD N) : List (Fin N) := [a.jc, a.jg1, a.jg2, a.js1, a.js2, a.jR]

/-- **The owner map** (decidable): `own j = some k` iff `j` is one of arbiter `k`'s six virtual
nodes (so the arbiters' node sets are disjoint), and every virtual node has an owner. -/
def OwnOK {N K : Nat} (rn : Fin N → RNode) (as : Fin K → ArbD N) (own : Fin N → Option (Fin K)) : Prop :=
  (∀ j k, own j = some k ↔ j ∈ (as k).nodes) ∧ ∀ j, (rn j).virt = true → own j ≠ none

instance {N K : Nat} (rn : Fin N → RNode) (as : Fin K → ArbD N) (own : Fin N → Option (Fin K)) :
    Decidable (OwnOK rn as own) := by
  unfold OwnOK; exact inferInstance

/-- **The reset classes are readers** (decidable): every node with `rs j ≠ 0` is a grant or a
shadow of some arbiter. -/
def RsOK {N K : Nat} (as : Fin K → ArbD N) (rs : Nat → Nat) : Prop :=
  ∀ j : Fin N, rs j.val ≠ 0 → ∃ k, j = (as k).jg1 ∨ j = (as k).jg2 ∨ j = (as k).js1 ∨ j = (as k).js2

instance {N K : Nat} (as : Fin K → ArbD N) (rs : Nat → Nat) : Decidable (RsOK as rs) := by
  unfold RsOK; exact inferInstance

/-- The virtual signals: an arbiter's ctl and shadows from the core, the real wires elsewhere. -/
def cvOf {N K : Nat} {d : Design} (x : Fin d.n → Sig) (rn : Fin N → RNode) (as : Fin K → ArbD N)
    (own : Fin N → Option (Fin K)) (ctlK s1K s2K : Fin K → Sig) (j : Fin N) : Sig :=
  match own j with
  | some k => if j = (as k).jc then ctlK k else if j = (as k).js1 then s1K k else
      if j = (as k).js2 then s2K k else x (d.wire (rn j).ow)
  | none => x (d.wire (rn j).ow)

section
variable {N K : Nat} {d : Design} {x : Fin d.n → Sig} {rn : Fin N → RNode} {as : Fin K → ArbD N}
  {own : Fin N → Option (Fin K)} {ctlK s1K s2K : Fin K → Sig}

theorem cvOf_jc {k : Fin K} (h : own (as k).jc = some k) :
    cvOf x rn as own ctlK s1K s2K (as k).jc = ctlK k := by
  unfold cvOf; rw [h]; simp

theorem cvOf_js1 {k : Fin K} (h : own (as k).js1 = some k) (h1 : (as k).js1 ≠ (as k).jc) :
    cvOf x rn as own ctlK s1K s2K (as k).js1 = s1K k := by
  unfold cvOf; rw [h]; simp [h1]

theorem cvOf_js2 {k : Fin K} (h : own (as k).js2 = some k) (h1 : (as k).js2 ≠ (as k).jc)
    (h2 : (as k).js2 ≠ (as k).js1) :
    cvOf x rn as own ctlK s1K s2K (as k).js2 = s2K k := by
  unfold cvOf; rw [h]; simp [h1, h2]

theorem cvOf_wire {j : Fin N} {k : Fin K} (h : own j = some k) (h1 : j ≠ (as k).jc) (h2 : j ≠ (as k).js1)
    (h3 : j ≠ (as k).js2) : cvOf x rn as own ctlK s1K s2K j = x (d.wire (rn j).ow) := by
  unfold cvOf; rw [h]; simp [h1, h2, h3]

end

section
variable {N K : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {fuel rw : Nat}
  {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)

include hsat h0 h1 in
/-- **`harb_of_arbs`**: if every virtual node of the certificate belongs to exactly one arbiter
(`OwnOK`), every arbiter passes `ArbOK` and satisfies its trace conditions `ArbCond` (one quiet
start `T0`, settle bounds `H k`), the certificate has the corrected shape (`FixShape`) and its
reset classes are readers (`RsOK`), then there are virtual signals `cv` with `HARB7'` and `HRst`
(all readers reset by `decide (u < T0)`). -/
theorem harb_of_arbs (as : Fin K → ArbD N) (own : Fin N → Option (Fin K)) (rs : Nat → Nat)
    (hA : ∀ k, ArbOK d net b rn fuel rw (as k)) (hown : OwnOK rn as own) (hrs : RsOK as rs)
    (hfs : Events9Arb.FixShape net b rn)
    (T0 : Nat) (H : Fin K → Nat) (hc : ∀ k, ArbCond hsat rn (as k) T0 (H k)) :
    ∃ cv, Events9Arb.HARB7' net b rn x cv ∧ Events9Par.HRst net b rn x cv rs := by
  have hcore := fun k => arb_core hsat h0 h1 (hA k) (hc k)
  -- the core's ctl and shadows, per arbiter
  let ctlK : Fin K → Sig := fun k => Classical.choose (hcore k)
  let s1K : Fin K → Sig := fun k => Classical.choose (Classical.choose_spec (hcore k))
  let s2K : Fin K → Sig := fun k => Classical.choose (Classical.choose_spec (Classical.choose_spec (hcore k)))
  have hspec : ∀ k, VCtl (loCtl (bandsOf d (as k))) (10 ^ 12) (aS (x := x) rn (as k)) (ctlK k) ∧
      VRdR (rdG ((bandsOf d (as k)).g1 0) ((bandsOf d (as k)).g1 2) (kOf (bandsOf d (as k)))).loR
        (rdG ((bandsOf d (as k)).g1 0) ((bandsOf d (as k)).g1 2) (kOf (bandsOf d (as k)))).hiR
        (rdG ((bandsOf d (as k)).g1 0) ((bandsOf d (as k)).g1 2) (kOf (bandsOf d (as k)))).loC
        (rdG ((bandsOf d (as k)).g1 0) ((bandsOf d (as k)).g1 2) (kOf (bandsOf d (as k)))).hiC true
        (fun u => decide (u < T0)) (r1S (x := x) (as k)) (ctlK k) (g1S (x := x) (as k)) ∧
      VRdR (rdG ((bandsOf d (as k)).g2 1) ((bandsOf d (as k)).g2 2) (kOf (bandsOf d (as k)))).loR
        (rdG ((bandsOf d (as k)).g2 1) ((bandsOf d (as k)).g2 2) (kOf (bandsOf d (as k)))).hiR
        (rdG ((bandsOf d (as k)).g2 1) ((bandsOf d (as k)).g2 2) (kOf (bandsOf d (as k)))).loC
        (rdG ((bandsOf d (as k)).g2 1) ((bandsOf d (as k)).g2 2) (kOf (bandsOf d (as k)))).hiC false
        (fun u => decide (u < T0)) (r2S (x := x) (as k)) (ctlK k) (g2S (x := x) (as k)) ∧
      VRdR (rdS ((bandsOf d (as k)).r0 0) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).loR
        (rdS ((bandsOf d (as k)).r0 0) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).hiR
        (rdS ((bandsOf d (as k)).r0 0) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).loC
        (rdS ((bandsOf d (as k)).r0 0) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).hiC true
        (fun u => decide (u < T0)) (r1S (x := x) (as k)) (ctlK k) (s1K k) ∧
      VRdR (rdS ((bandsOf d (as k)).r0 1) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).loR
        (rdS ((bandsOf d (as k)).r0 1) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).hiR
        (rdS ((bandsOf d (as k)).r0 1) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).loC
        (rdS ((bandsOf d (as k)).r0 1) ((bandsOf d (as k)).r0 2) (kOf (bandsOf d (as k)))).hiC false
        (fun u => decide (u < T0)) (r2S (x := x) (as k)) (ctlK k) (s2K k) ∧
      VMerge 1 1 1 1 1 1 (s1K k) (s2K k) (R0S (x := x) (as k)) :=
    fun k => Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (hcore k)))
  let cv := cvOf x rn as own ctlK s1K s2K
  -- facts per arbiter
  have hmem : ∀ k j, j ∈ (as k).nodes → own j = some k := fun k j h => ((hown.1 j k).2 h)
  have hnd : ∀ k, [(as k).jc, (as k).jg1, (as k).jg2, (as k).js1, (as k).js2, (as k).jR].Nodup :=
    fun k => (hA k).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hW : ∀ s, (rn s).virt = true → (rn s).hasW = true → ∀ t, x (d.wire (rn s).ow) t = cv s t := by
    intro s hv hw t
    obtain ⟨k, hk⟩ : ∃ k, own s = some k := by
      cases h : own s with
      | none => exact absurd h (hown.2 s hv)
      | some k => exact ⟨k, rfl⟩
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hctl, _, _, _, _, _, _, _, _, hs1, hs2, _⟩ := hA k
    have n1 : s ≠ (as k).jc := fun e => by rw [e, hctl.2.1] at hw; exact absurd hw (by decide)
    have n2 : s ≠ (as k).js1 := fun e => by rw [e, hs1] at hw; exact absurd hw (by decide)
    have n3 : s ≠ (as k).js2 := fun e => by rw [e, hs2] at hw; exact absurd hw (by decide)
    show _ = cvOf x rn as own ctlK s1K s2K s t
    rw [cvOf_wire hk n1 n2 n3]
  -- the node behaviours of arbiter k's nodes
  have hND : ∀ k, (Nonempty (ND7 net b (ccOf rn x cv) (as k).jc)) ∧
      Nonempty {nd : ND7 net b (ccOf rn x cv) (as k).jg1 // nd.r = fun u => decide (u < T0)} ∧
      Nonempty {nd : ND7 net b (ccOf rn x cv) (as k).jg2 // nd.r = fun u => decide (u < T0)} ∧
      Nonempty {nd : ND7 net b (ccOf rn x cv) (as k).js1 // nd.r = fun u => decide (u < T0)} ∧
      Nonempty {nd : ND7 net b (ccOf rn x cv) (as k).js2 // nd.r = fun u => decide (u < T0)} ∧
      Nonempty (ND7 net b (ccOf rn x cv) (as k).jR) := by
    intro k
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hnd', hctl, hg1, hg2, hs1, hs2, hw1, hw1o,
      hw2, hw2o, hs1w, hs2w, hmg, _⟩ := hA k
    obtain ⟨sc, sg1, sg2, ss1, ss2, sm⟩ := hspec k
    have hnd'' := hnd'
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hnd''
    obtain ⟨⟨c1, c2, c3, c4, c5⟩, ⟨g1a, g1b, g1c, g1d⟩, ⟨g2a, g2b, g2c⟩, ⟨s1a, s1b⟩, s2a, _⟩ := hnd''
    have m : ∀ j, j ∈ (as k).nodes → own j = some k := hmem k
    have ojc := m (as k).jc (by simp [ArbD.nodes])
    have ojg1 := m (as k).jg1 (by simp [ArbD.nodes])
    have ojg2 := m (as k).jg2 (by simp [ArbD.nodes])
    have ojs1 := m (as k).js1 (by simp [ArbD.nodes])
    have ojs2 := m (as k).js2 (by simp [ArbD.nodes])
    have ojR := m (as k).jR (by simp [ArbD.nodes])
    have ecc : ∀ t, cv (as k).jc t = ctlK k t := fun t => by
      show cvOf x rn as own ctlK s1K s2K _ t = _; rw [cvOf_jc ojc]
    have ecg1 : ∀ t, cv (as k).jg1 t = g1S (x := x) (as k) t := fun t => by
      show cvOf x rn as own ctlK s1K s2K _ t = _
      rw [cvOf_wire ojg1 (Ne.symm c1) g1b g1c]; unfold g1S; rw [hw1o]
    have ecg2 : ∀ t, cv (as k).jg2 t = g2S (x := x) (as k) t := fun t => by
      show cvOf x rn as own ctlK s1K s2K _ t = _
      rw [cvOf_wire ojg2 (Ne.symm c2) g2a g2b]; unfold g2S; rw [hw2o]
    have ecs1 : ∀ t, cv (as k).js1 t = s1K k t := fun t => by
      show cvOf x rn as own ctlK s1K s2K _ t = _; rw [cvOf_js1 ojs1 (Ne.symm c3)]
    have ecs2 : ∀ t, cv (as k).js2 t = s2K k t := fun t => by
      show cvOf x rn as own ctlK s1K s2K _ t = _; rw [cvOf_js2 ojs2 (Ne.symm c4) (Ne.symm s1a)]
    have ecR : ∀ t, cv (as k).jR t = x (d.wire (gt d (as k).gR).out) t := fun t => by
      show cvOf x rn as own ctlK s1K s2K _ t = _
      rw [cvOf_wire ojR (Ne.symm c5) (Ne.symm s1b) (Ne.symm s2a)]; rw [hmg.2.2.1]
    have hvc : (rn (as k).jc).virt = true := hctl.1
    refine ⟨nd7_ctl hsat h0 h1 hW hctl ecc sc, nd7_rd hsat h0 h1 hW hg1 ecg1 ecc hvc sg1,
      nd7_rd hsat h0 h1 hW hg2 ecg2 ecc hvc sg2, nd7_rd hsat h0 h1 hW hs1 ecs1 ecc hvc ss1,
      nd7_rd hsat h0 h1 hW hs2 ecs2 ecc hvc ss2,
      nd7_mg hsat h0 h1 hW hmg hs1.1 hs2.1 ecs1 ecs2 ecR sm⟩
  refine ⟨cv, ⟨⟨?_, ?_, ?_⟩, hfs⟩, ⟨fun _ u => decide (u < T0), ?_⟩⟩
  · intro j hv
    obtain ⟨k, hk⟩ : ∃ k, own j = some k := by
      cases h : own j with
      | none => exact absurd h (hown.2 j hv)
      | some k => exact ⟨k, rfl⟩
    have hj := (hown.1 j k).1 hk
    simp only [ArbD.nodes, List.mem_cons, List.not_mem_nil, or_false] at hj
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hND k
    rcases hj with e | e | e | e | e | e <;> subst e
    · exact n1
    · obtain ⟨nd⟩ := n2; exact ⟨nd.val⟩
    · obtain ⟨nd⟩ := n3; exact ⟨nd.val⟩
    · obtain ⟨nd⟩ := n4; exact ⟨nd.val⟩
    · obtain ⟨nd⟩ := n5; exact ⟨nd.val⟩
    · exact n6
  · intro j hv hw t; exact hW j hv hw t
  · intro j hv hm
    obtain ⟨k, hk⟩ : ∃ k, own j = some k := by
      cases h : own j with
      | none => exact absurd h (hown.2 j hv)
      | some k => exact ⟨k, rfl⟩
    have hj := (hown.1 j k).1 hk
    simp only [ArbD.nodes, List.mem_cons, List.not_mem_nil, or_false] at hj
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hctl, hg1, hg2, hs1, hs2, _, _,
      _, _, _, _, hmg, _⟩ := hA k
    rcases hj with e | e | e | e | e | e <;> subst e
    · rw [hctl.2.2.1] at hm; exact absurd hm (by decide)
    · rw [hg1.2.1] at hm; exact absurd hm (by decide)
    · rw [hg2.2.1] at hm; exact absurd hm (by decide)
    · rw [hs1.2.1] at hm; exact absurd hm (by decide)
    · rw [hs2.2.1] at hm; exact absurd hm (by decide)
    · rw [← hW _ hv hmg.2.1 0, hmg.2.2.1]
      exact ((hc k).low 0 (Nat.zero_le _)).2.2
  · intro j hj
    obtain ⟨k, e | e | e | e⟩ := hrs j hj <;> subst e
    · exact (hND k).2.1
    · exact (hND k).2.2.1
    · exact (hND k).2.2.2.1
    · exact (hND k).2.2.2.2.1

end


/-! ## 6. The design verdict with the arbiter link checked -/

section
open Formal.Core.XAudit.Events8 Formal.Core.XAudit.Events9 Formal.Core.XAudit.Events9Par
variable {N K : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig}

/-- **`design_verdict9arbnet`**: `Events9Par.design_verdict9par` with its two arbiter hypotheses
`HARB7'` and `HRst` replaced by CHECKED data (`ArbOK` per arbiter, `OwnOK`, `RsOK`, `FixShape`)
and the per-arbiter trace conditions `ArbCond` (quiet start `T0`, settle bounds `H k`, B1/B2/C on
the four readers). Same conclusion, for SOME virtual signals `cv` (the corrected core's ctl and
shadows, built from the real traces). -/
theorem design_verdict9arbnet (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {rs : Nat → Nat} {log : List LnP} {J : Array Jd}
    (hJ : runLogP net b rs parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (as : Fin K → ArbD N) (own : Fin N → Option (Fin K))
    (hA : ∀ k, ArbOK d net b rn fuel rw (as k)) (hown : OwnOK rn as own) (hrs : RsOK as rs)
    (hfs : Events9Arb.FixShape net b rn)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T))
    (T0 : Nat) (H : Fin K → Nat) (hc : ∀ k, ArbCond hsat rn (as k) T0 (H k))
    (sel : Nat → Nat → Bool) :
    ∃ cv : Fin N → Sig, ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts → bh.SelOK →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = ph (net.v j) (bh.M t j)) := by
  obtain ⟨cv, harb, hR⟩ := harb_of_arbs hsat h0 h1 as own rs hA hown hrs hfs T0 H hc
  exact ⟨cv, design_verdict9par hr hOK hJ back line xS xw xa hl gd cp cxm cl cg hcp hcx hcl hcg
    hsat h0 h1 hT hrst harb hR sel⟩

end

end Formal.Core.XAudit.Events9ArbNet
