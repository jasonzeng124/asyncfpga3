import Formal.Core.XAudit.Events6Gate
import Formal.Core.XAudit.Events6Cert

/-!
# Formal.Core.XAudit.Events6Design — W-E4n: every per-pin behaviour of the parsed netlist is a `Beh4`

Probe A-events6. See `formal/notes/A-events6.md`.

**The recognition** `Recog6 d net b rn rank rw fuel` (decidable) relates the parsed
design `d` to an `Events5.Net4` and its `Bands4`, through per-node data `RNode`
(the LUT of a stage or merge, its feedback and reset paths, and per pin: the LUT
input it enters, a folded select pattern, and either the paths of a
buffer/inverter/AND/OR tree down to the source's output wire or a steer gate
with the chains above and below it). It checks, by evaluation over the INITs:
the stage LUT is `rst ? v : C(lit_1 .. lit_n, q)` with the folded steer
literals; a merge LUT is the OR of its pins; every pin tree (`chkT`); every
steer gate; and that the bands of the `Net4` are the bands of these paths
under the per-pin semantics (`loF = hiF = 1`, the LUT pin's own band moved into
each copy, `dw` = `pairW`).

**H_ARB** (`HARB`) is the hypothesis that the arbiter cores behave as the virtual
mux core (A-events4 §1): every VIRTUAL node (the arbiter's `ctl`, grants, `R0`)
has a node behaviour `ND` in its bands, and the grant / `R0` output wires carry
it. It is a hypothesis, not checked: the arbiter has no SI and can be metastable.

**`design_beh4`**: every per-pin behaviour (`SatPin d plG x`, no H_ATOMIC_LUT) of a
recognised design, with constant wires, reset high until `T`, and H_ARB, is a
`Beh4` whose node `j` is the wire of `j`'s LUT (real nodes) or the virtual
signal (H_ARB). Each node samples its pins one step after the LUT's pin warps
(`F t = t - 1`); the per-pin warps move into the copies (`G`), the feedback (`Q`)
and the reset. `gc` (the guarded counts) is a free monotone argument.
-/

namespace Formal.Core.XAudit.Events6

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5

/-! ## Recognition data -/

/-- One pin of a real node. -/
structure RPin where
  /-- the LUT input this pin enters -/
  ip : Nat
  /-- folded steer: `(LUT input, value)` select literals ANDed into this pin's literal -/
  fold : List (Nat × Bool) := []
  /-- steer kind: a separate steer gate `sg` (control input `sci`, selects `ssel`) -/
  st : Bool := false
  /-- tree kind: one path per copy, from the pin wire down to the source's output wire -/
  paths : List Path := []
  top : Path := []
  sg : Nat := 0
  sci : Nat := 0
  ssel : List (Nat × Bool) := []
  bot : Path := []
  deriving Repr, Inhabited

def RPin.copies (r : RPin) : List Path := if r.st then [r.top ++ (r.sg, r.sci) :: r.bot] else r.paths

/-- One node: real (a LUT) or virtual (H_ARB). -/
structure RNode where
  virt : Bool
  /-- output wire (virtual: meaningful when `hasW`) -/
  ow : Nat
  hasW : Bool := true
  lut : Nat := 0
  qi : Nat := 0
  ri : Nat := 0
  qp : Path := []
  rp : Path := []
  pins : List RPin := []
  deriving Repr, Inhabited

def foldM (v : Nat → Bool) (l : List (Nat × Bool)) : Bool := l.all fun sb => v sb.1 == sb.2

/-- The branch of a filtered pin: the select value for a 1-bit pattern, `true`
(= "the pattern matches") otherwise. -/
def brOf (l : List (Nat × Bool)) : Bool := match l with
  | [(_, b)] => b
  | _ => true

section
variable {N : Nat} (d : Design) (net : Net4 N) (rn : Fin N → RNode)

def rpin (j : Fin N) (p : Fin (net.ar j)) : RPin := (rn j).pins.getD p.val default

def pinW (j : Fin N) (p : Fin (net.ar j)) : Nat := (gt d (rn j).lut).ins.getD (rpin net rn j p).ip 0

def full (j : Fin N) (p : Fin (net.ar j)) (i : Nat) : Path :=
  ((rn j).lut, (rpin net rn j p).ip) :: (rpin net rn j p).copies.getD i []

def stageSpec (j : Fin N) (v : Nat → Bool) : Bool :=
  if v (rn j).ri then net.v j else
    cel (fun p : Fin (net.ar j) => (v (rpin net rn j p).ip ^^ net.neg j p) && foldM v (rpin net rn j p).fold) (v (rn j).qi)

def mergeSpec (j : Fin N) (v : Nat → Bool) : Bool := fany (net.ar j) (fun p => v (rpin net rn j p).ip)

def steerSpec (r : RPin) (v : Nat → Bool) : Bool := v r.sci && foldM v r.ssel

end

/-- Checks on one pin of a real node (decidable). -/
def PinR {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (fuel : Nat)
    (j : Fin N) (p : Fin (net.ar j)) : Prop :=
  (rpin net rn j p).ip < (gt d (rn j).lut).k ∧
  ((rn (net.src j p)).virt = true → (rn (net.src j p)).hasW = true) ∧
  (rpin net rn j p).copies.length = net.nc j p ∧
  (∀ π ∈ (rpin net rn j p).copies, pathOK d π = true ∧ π ≠ []) ∧
  (∀ i : Fin (net.nc j p), b.loC j p i = plo d (full net rn j p i) - 1 ∧ b.hiC j p i = phi d (full net rn j p i) - 1) ∧
  (∀ i : Fin (net.nc j p), i.val + 1 < net.nc j p →
    b.dw j p i.val = pairW d (full net rn j p i.val) (full net rn j p (i.val + 1))) ∧
  ((rpin net rn j p).st = true →
    net.pk j p = PK.filt ∧ (rpin net rn j p).fold = [] ∧ (rpin net rn j p).sg < d.gates.length ∧
    (rpin net rn j p).sci < (gt d (rpin net rn j p).sg).k ∧
    (∀ sb ∈ (rpin net rn j p).ssel, sb.1 < (gt d (rpin net rn j p).sg).k) ∧
    InitSpec (gt d (rpin net rn j p).sg) (steerSpec (rpin net rn j p)) ∧
    chkT d (gt d (rpin net rn j p).sg).out fuel true (pinW d net rn j p) [(rpin net rn j p).top] = some false ∧
    chkT d (rn (net.src j p)).ow fuel true
      ((gt d (rpin net rn j p).sg).ins.getD (rpin net rn j p).sci 0) [(rpin net rn j p).bot] = some false ∧
    net.br j p = brOf (rpin net rn j p).ssel) ∧
  ((rpin net rn j p).st = false →
    chkT d (rn (net.src j p)).ow fuel (net.op j p) (pinW d net rn j p) (rpin net rn j p).paths = some (net.inv j p) ∧
    (∀ sb ∈ (rpin net rn j p).fold, sb.1 < (gt d (rn j).lut).k) ∧
    ((rpin net rn j p).fold ≠ [] → net.pk j p = PK.filt ∧ net.neg j p = false ∧
      net.br j p = brOf (rpin net rn j p).fold ∧ net.mg j = false) ∧
    ((rpin net rn j p).fold = [] → net.pk j p ≠ PK.filt))

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
instance {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (fuel : Nat)
    (j : Fin N) (p : Fin (net.ar j)) : Decidable (PinR d net b rn fuel j p) := by
  unfold PinR; exact inferInstance

/-- Checks on one real node (decidable). -/
def NodeR {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (rank : Fin N → Nat)
    (rw fuel : Nat) (j : Fin N) : Prop :=
  (rn j).lut < d.gates.length ∧ (rn j).ow = (gt d (rn j).lut).out ∧ b.loF j = 1 ∧ b.hiF j = 1 ∧
  (net.mg j = false →
    InitSpec (gt d (rn j).lut) (stageSpec net rn j) ∧
    (rn j).qi < (gt d (rn j).lut).k ∧ (rn j).ri < (gt d (rn j).lut).k ∧
    chkT d (gt d (rn j).lut).out fuel true ((gt d (rn j).lut).ins.getD (rn j).qi 0) [(rn j).qp] = some false ∧
    pathOK d (rn j).qp = true ∧ (rn j).qp ≠ [] ∧
    chkT d rw fuel true ((gt d (rn j).lut).ins.getD (rn j).ri 0) [(rn j).rp] = some false ∧
    pathOK d (rn j).rp = true ∧
    b.loQ j = plo d (((rn j).lut, (rn j).qi) :: (rn j).qp) - 1 ∧
    b.hiQ j = phi d (((rn j).lut, (rn j).qi) :: (rn j).qp) - 1) ∧
  (net.mg j = true →
    InitSpec (gt d (rn j).lut) (mergeSpec net rn j) ∧ b.loQ j = 1 ∧ b.hiQ j = 1 ∧
    ∀ p : Fin (net.ar j), (rn (net.src j p)).virt = false → net.mg (net.src j p) = true →
      rank (net.src j p) < rank j) ∧
  ∀ p : Fin (net.ar j), PinR d net b rn fuel j p

instance {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (rank : Fin N → Nat)
    (rw fuel : Nat) (j : Fin N) : Decidable (NodeR d net b rn rank rw fuel j) := by
  unfold NodeR; exact inferInstance

/-- **The recognition** (decidable): every real node passes `NodeR`. -/
def Recog6 {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (rank : Fin N → Nat)
    (rw fuel : Nat) : Prop :=
  d.WF ∧ ∀ j : Fin N, (rn j).virt = false → NodeR d net b rn rank rw fuel j

instance {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (rank : Fin N → Nat)
    (rw fuel : Nat) : Decidable (Recog6 d net b rn rank rw fuel) := by
  unfold Recog6; exact inferInstance

/-! ## Node behaviours and the assembly of a `Beh4` -/

/-- The per-node part of a `Beh4` (every field of `Beh4` that belongs to one
node), for a given family `cc` of node signals. -/
structure ND {N : Nat} (net : Net4 N) (b : Bands4 net) (cc : Fin N → Sig) (j : Fin N) where
  pin : Fin (net.ar j) → Sig
  q : Sig
  r : Sig
  sv : Fin (net.ar j) → Sig
  F : Nat → Nat
  G : (p : Fin (net.ar j)) → Fin (net.nc j p) → Nat → Nat
  Q : Nat → Nat
  wF : Warp (b.loF j) (b.hiF j) F
  wG : ∀ p i, Warp (b.loC j p i) (b.hiC j p i) (G p i)
  wQ : Warp (b.loQ j) (b.hiQ j) Q
  loF1 : 1 ≤ b.loF j
  loC1 : ∀ p i, 1 ≤ b.loC j p i
  loQ1 : 1 ≤ b.loQ j
  hc : ∀ t, cc j t =
    if net.mg j then fany (net.ar j) (fun p => pin p (F t))
    else if r (F t) then net.v j else cel (fun p => pin p (F t) ^^ net.neg j p) (q (F t))
  hpin : ∀ p t, pin p t = (net.inv j p ^^
    match net.pk j p with
    | PK.multi => if net.op j p then fall (net.nc j p) (fun i => cc (net.src j p) (G p i t))
                  else fany (net.nc j p) (fun i => cc (net.src j p) (G p i t))
    | PK.filt => fany (net.nc j p) (fun i => cc (net.src j p) (G p i t) && (sv p t == net.br j p))
    | _ => fany (net.nc j p) (fun i => cc (net.src j p) (G p i t)))
  hq : ∀ t, q t = cc j (Q t)
  r0 : r 0 = true
  ranti : ∀ a c, a ≤ c → r c = true → r a = true
  hskew : ∀ p (i i' : Fin (net.nc j p)), i'.val = i.val + 1 → ∀ s,
    G p i s ≤ G p i' s + b.dw j p i.val ∧ G p i' s ≤ G p i s + b.dw j p i.val

/-- A `Beh4` from node behaviours. -/
noncomputable def ofND {N : Nat} {net : Net4 N} {b : Bands4 net} (sel : Nat → Nat → Bool) (cc : Fin N → Sig)
    (nd : ∀ j, ND net b cc j) (gc : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (gcmono : ∀ j p a s, a ≤ s → gc j p a ≤ gc j p s)
    (mg0 : ∀ j, net.mg j = true → cc j 0 = false) : Beh4 net b sel where
  c := cc
  pin := fun j => (nd j).pin
  q := fun j => (nd j).q
  r := fun j => (nd j).r
  sv := fun j => (nd j).sv
  gc := gc
  F := fun j => (nd j).F
  G := fun j => (nd j).G
  Q := fun j => (nd j).Q
  wF := fun j => (nd j).wF
  wG := fun j => (nd j).wG
  wQ := fun j => (nd j).wQ
  loF1 := fun j => (nd j).loF1
  loC1 := fun j => (nd j).loC1
  loQ1 := fun j => (nd j).loQ1
  hc := fun j => (nd j).hc
  hpin := fun j => (nd j).hpin
  hq := fun j => (nd j).hq
  r0 := fun j => (nd j).r0
  ranti := fun j => (nd j).ranti
  hskew := fun j => (nd j).hskew
  mg0 := mg0
  gcmono := gcmono

/-- The node signals: a real node is the wire of its LUT, a virtual node the
H_ARB signal. -/
def ccOf {N : Nat} {d : Design} (rn : Fin N → RNode) (x : Fin d.n → Sig) (cv : Fin N → Sig) (j : Fin N) : Sig :=
  if (rn j).virt then cv j else x (d.wire (rn j).ow)

/-- **H_ARB** (hypothesis): the virtual nodes behave as the virtual mux core in
their bands; the grant and `R0` wires carry the virtual signals; `R0` is low
at time 0. -/
def HARB {N : Nat} {d : Design} (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode) (x : Fin d.n → Sig)
    (cv : Fin N → Sig) : Prop :=
  (∀ j, (rn j).virt = true → Nonempty (ND net b (ccOf rn x cv) j)) ∧
  (∀ j, (rn j).virt = true → (rn j).hasW = true → ∀ t, x (d.wire (rn j).ow) t = cv j t) ∧
  (∀ j, (rn j).virt = true → net.mg j = true → cv j 0 = false)

end Formal.Core.XAudit.Events6
