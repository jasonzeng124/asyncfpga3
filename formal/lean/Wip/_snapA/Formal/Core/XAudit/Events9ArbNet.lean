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
  b.loF j = 1 ∧ b.hiF j = 1 ∧ b.loQ j = 1 ∧ b.hiQ j = 1 ∧
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
  b.loF jc = 1 ∧ b.hiF jc = 1 ∧ b.loQ jc = 1 ∧ b.hiQ jc = 1 ∧ (rn jA).virt = false ∧
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

theorem shiftW1 : Warp 1 1 (fun t : Nat => t - 1) :=
  ⟨fun a b hab => by omega, fun t => by omega, fun t => by omega⟩

/-- **`arb_core`**: under the per-pin semantics of `d`, an `ArbOK` arbiter satisfying its trace
conditions is a behaviour of the corrected core `CoreOf (bandsOf d a)`, with the common reader
reset `decide (u < T0)` (`CoreOfR`), on the wires of `d`. -/
theorem arb_core {a : ArbD N} (hA : ArbOK d net b rn fuel rw a) {T0 H : Nat}
    (hc : ArbCond hsat rn a T0 H) :
    CoreOfR (bandsOf d a) (fun u => decide (u < T0)) (r1S (x := x) a) (r2S (x := x) a)
      (aS (x := x) rn a) (R0S (x := x) a) (g1S (x := x) a) (g2S (x := x) a) := by
  obtain ⟨r11, r1q, s1, r22, r2q, s2, rR1, rR2, rRq, sR, hgQ, _, _, _, _, rQA, _, _, _, _, _, _,
    _, _, _, _, _, _, hb1, hb2, hb3, hb4, hK2, hq1, hq2, hq3⟩ := hA
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
  exact core_of_en_rst (bandsOf d a) (frOf hsat a) (f1Of hsat a) (f2Of hsat a) hfr hf1 hf2 hR0 hg1 hg2 T0
    hc.low hb1 hb2 hb3 hb4 hq1 hq2 hq3 hc.t1 hc.t2 hc.t3 hc'
    (enOK_of_rd hK2 (fun u => hb1' _) hc.e1) (enOK_of_rd hK2 (fun u => hb2' _) hc.e2)
    (enOK_of_rd hK2 (fun u => hb1' _) hc.e3) (enOK_of_rd hK2 (fun u => hb2' _) hc.e4)

end

end Formal.Core.XAudit.Events9ArbNet
