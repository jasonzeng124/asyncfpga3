import Formal.Net.CapstoneNetDef

/-!
# Probe C-8y2: the circuit-safety pipeline, parametric in the kernel

gcd_hw (C-8m/8q/8r/8s, `Capstone*`) and ipow (C-8y, `IpowCap*`, a text copy of the gcd chain
with ~45 substituted constants) carry the same 3000-line proof twice. Here the proof is written
ONCE, over an arbitrary kernel, and gcd_hw and ipow become instances (`KernelCapGcd`,
`KernelCapIpow`).

A kernel is two type classes:

* `KD` (data): bdc's token graph (`rules`, `spine`: C-8i's importer `dfimport`); the C
  reference as the token run's initial/final stores and the spec value (`init`, `final`,
  `spec`, the input domain `dom`, the ports `chOut`/`chEnd`, the number `nIn` of environment
  channels with `start` = channel `nIn - 1`, and the source values `srcVal`); the circuit
  network with bdc's link placement (`ops`, `tab`, `prodT`, `consT`, `out0`, `start`:
  `capnet.py net`); and the walk certificate (`spL`, `spN`, `grpL` .. `recs`, the arbiter
  cascade constants `cq1` .. `cl2`: `capnet.py spine`/`walktab`).
* `KP` (proof obligations, all `Prop`): every one is either a decidable check on the data
  (discharged per kernel by `decide`, or by the existing per-kernel theorem of the same
  statement), or one of four facts about the C reference: the token-level theorem `good_run`
  (from `init a b` some run reaches `final (spec a b)`, for `dom a b`), the shape of
  `init`/`final` (`init_*`, `final_*`), and `init_inv` (one spine token).

The kernel-dependent definitions the obligations mention (`OpChk`, `SpOK`, the walk checker
`cOK`, ...) are here, copied from the gcd files with gcd's constants replaced by the class's
fields: channel ids 3/250 by `chEnd`/`chOut`, `3 ≤ g` by `nIn ≤ g`, the start source index 2 by
`nIn - 1`, gcd's cascade 13/27/246/251/249/154/155 by `cq1`/`cq2`/`cq3`/`cres`/`cidx`/`cl1`/`cl2`.
The one structural generalisation: an operator `.src z which d` with `which + 1 < nIn` is a data
argument (descriptor `.hist which d`), `which = nIn - 1` is start (`.zero`); gcd and ipow have
`nIn = 3`, collatz `nIn = 2`.
-/

namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk

/-- The data of a kernel: token graph, C reference (as stores), network, walk certificate. -/
class KD where
  /-- bdc's token graph (C-8i importer) and its control spine. -/
  rules : List Rule
  spine : List Nat
  /-- The C reference: initial store from the arguments, final store from the result. -/
  init : Nat → Nat → Store Nat Nat
  final : Nat → Store Nat Nat
  /-- The C function's value, and the inputs on which the token theorem holds. -/
  spec : Nat → Nat → Nat
  dom : Nat → Nat → Prop
  /-- Ports: the result channel, the end channel, the number of environment channels
  (`0 .. nIn - 2` data arguments, `nIn - 1` start). -/
  chOut : Nat
  chEnd : Nat
  nIn : Nat
  /-- The value source `which` offers (the arguments; 0 for start). -/
  srcVal : Nat → Nat → Nat → Nat
  /-- The circuit network (capnet net: bdc's graph + bdc's link placement). -/
  NC : Nat
  NO : Nat
  ops : List (K NC)
  tab : Tab
  prodT : List (Fin NO)
  consT : List (Fin NO)
  out0 : Fin NC
  out0d : Nat
  start : Fin NC
  /-- The walk certificate (capnet spine / walktab). -/
  spL : List Bool
  spN : List Nat
  grpL : List Nat
  rhoL : List Nat
  adjL : List Bool
  alL : List (List Nat)
  lcL : List Nat
  recs : List (Nat × Nat × Nat × Bool × List Nat)
  acc : Fin NC
  /-- The 3-input arbiter cascade (inputs `cq1 cq2 cq3`, result `cres`, index `cidx`, the
  rules of inputs 1/2 `cl1 cl2`). A kernel without one maps them onto a 2-input
  control_merge (C-8y). -/
  cq1 : Nat
  cq2 : Nat
  cq3 : Nat
  cres : Nat
  cidx : Nat
  cl1 : Nat
  cl2 : Nat

open KD

section defs
variable [KD]

abbrev G : Nat → Node Nat Nat := graph rules

def sideOK : Rule → Bool
  | .mux s ds _ _ => decide ds.Nodup && !(ds.contains s)
  | .branch _ _ t f => t != f
  | _ => true

def produced (c : Nat) : Bool := rules.any fun r => r.outsL.contains c
def consumed (c : Nat) : Bool := rules.any fun r => r.insL.contains c

def NoEnd (g : Nat) : Prop := g ≠ chEnd ∧ g ≠ chOut

variable {n : Nat}

/-- Justification `j` produces token channel `gm` from circuit inputs `ins` (Nat ids). -/
def JOK (T : Tab) (ins : List Nat) (gm : Nat) : J → Prop
  | .direct p d => p < ins.length ∧ T.d (ins.getD p 0) = .hist gm d ∧ NoEnd gm
  | .fold l1 p g1 d e1 => p < ins.length ∧ rules[l1]? = some (.comp [g1] gm e1) ∧
      T.d (ins.getD p 0) = .hist g1 d ∧ NoEnd g1 ∧ NoEnd gm ∧ nIn ≤ gm
  | .const l1 g1 e1 => rules[l1]? = some (.comp [g1] gm e1) ∧ evf e1 = true ∧ NoEnd gm ∧ nIn ≤ gm

instance (T : Tab) (ins : List Nat) (gm : Nat) (j : J) : Decidable (JOK T ins gm j) := by
  cases j <;> unfold JOK NoEnd <;> infer_instance

def FoldOK (T : Tab) (t f : Nat) (fd : E) (sw : SW) : Option (Nat × Nat × Nat × Nat) → Prop
  | none => fd = .var 0 ∧ T.d t = .hist sw.gt sw.dt ∧ T.d f = .hist sw.gf sw.df
  | some (lt, lf, gt', gf') => rules[lt]? = some (.comp [sw.gt] gt' fd) ∧
      rules[lf]? = some (.comp [sw.gf] gf' fd) ∧
      NoEnd sw.gt ∧ NoEnd sw.gf ∧ nIn ≤ gt' ∧ nIn ≤ gf' ∧ T.d t = .hist gt' sw.dt ∧
      T.d f = .hist gf' sw.df

instance (T : Tab) (t f : Nat) (fd : E) (sw : SW) (o : Option (Nat × Nat × Nat × Nat)) :
    Decidable (FoldOK T t f fd sw o) := by
  rcases o with _ | ⟨lt, lf, gt', gf'⟩ <;> unfold FoldOK NoEnd <;> infer_instance

/-- The per-operator checker (C-8m's, kernel-parametric). -/
def OpChk (T : Tab) : K n → Prop
  | .forkG i os => ∀ o ∈ os, T.d o.val = .copy i.val
  | .forkH i os l h d hs => rules[l]? = some (.fork h hs) ∧ T.d i.val = .hist h d ∧ NoEnd h ∧
      ∀ p ∈ os, T.d p.1.val = .hist p.2 d ∧ p.2 ∈ hs ∧ nIn ≤ p.2
  | .join ins o e js jw => rules[jw.l]? = some (.comp jw.gins jw.go e) ∧
      T.d o.val = .hist jw.go jw.dO ∧
      nIn ≤ jw.go ∧ js.length = jw.gins.length ∧ jw.gins ≠ [] ∧
      (∀ m < js.length, JOK T (ins.map Fin.val) (jw.gins.getD m 0) (js.getD m (.direct 0 0))) ∧
      jw.dO = e.eval (js.map J.dflt)
  | .bjoin ins o ec ed => T.d o.val = .bj ec ed (ins.map Fin.val) ∧ ins ≠ []
  | .steerC _ t f => T.d t.val = .zero ∧ T.d f.val = .zero
  | .steerD j t f fd sw =>
      rules[sw.l]? = some (.branch sw.gc sw.gd sw.gt sw.gf) ∧ NoEnd sw.gc ∧ NoEnd sw.gd ∧
      nIn ≤ sw.gt ∧ nIn ≤ sw.gf ∧ T.d j.val = .bj sw.jc.σ sw.jd.σ sw.jins ∧ sw.jins ≠ [] ∧
      JOK T sw.jins sw.gc sw.jc ∧ JOK T sw.jins sw.gd sw.jd ∧
      (if (sw.jc.dflt % 2 == 1) then sw.dt else sw.df) = fd.eval [sw.jd.dflt] ∧
      FoldOK T t.val f.val fd sw sw.fold
  | .mux c x y z mw =>
      rules[mw.l]? = some (.mux mw.gs [mw.gx, mw.gy] mw.gz 1) ∧ T.d x.val = .hist mw.gx mw.dx ∧
      T.d y.val = .hist mw.gy mw.dy ∧ T.d z.val = .hist mw.gz mw.dz ∧ NoEnd mw.gs ∧ NoEnd mw.gx ∧
      NoEnd mw.gy ∧ nIn ≤ mw.gz ∧ NoEnd mw.gi ∧ nIn ≤ mw.gs ∧
      chase T 32 c.val = mw.zc ∧ T.d mw.zc = .cmz mw.xa mw.ya mw.w ∧ T.w mw.w = .lab2 mw.gi ∧
      (mw.gs = mw.gi ∨ (rules[mw.lf]? = some (.fork mw.gi mw.hs) ∧ mw.gs ∈ mw.hs)) ∧ mw.dz = mw.dx
  | .muxn c x0 x1 x2 z nw =>
      rules[nw.l]? = some (.mux nw.gs [nw.g0, nw.g1, nw.g2] nw.gz 2) ∧
      T.d x0.val = .hist nw.g0 nw.d0 ∧
      T.d x1.val = .hist nw.g1 nw.d1 ∧ T.d x2.val = .hist nw.g2 nw.d2 ∧ T.d z.val = .hist nw.gz nw.dz ∧
      NoEnd nw.gs ∧ NoEnd nw.g0 ∧ NoEnd nw.g1 ∧ NoEnd nw.g2 ∧ nIn ≤ nw.gz ∧
      chase T 32 c.val = nw.zc ∧ T.d nw.zc = .cmz nw.acc nw.in2 nw.w2 ∧
      T.d nw.acc = .cmz nw.in0 nw.in1 nw.w1 ∧ T.w nw.w2 = .hi3 nw.gs ∧ T.w nw.w1 = .lo3 nw.gs ∧
      nw.dz = nw.d0
  | .amerge x y z w => T.d z.val = .cmz x.val y.val w ∧ x ≠ z ∧ y ≠ z
  | .link i o => T.d o.val = T.d i.val ∨ T.d o.val = .copy i.val
  | .src z which d => (which + 1 < nIn ∧ T.d z.val = .hist which d) ∨
      (which = nIn - 1 ∧ T.d z.val = .zero)
  | .sink _ => True

instance (T : Tab) (k : K n) : Decidable (OpChk T k) := by
  cases k <;> unfold OpChk <;> (try unfold NoEnd) <;> infer_instance

/-! ## The network -/

def opAt (o : Fin NO) : K NC := ops.getD o.val (K.sink 0)
def prodOf (c : Fin NC) : Fin NO := prodT.getD c.val 0
def consOf (c : Fin NC) : Fin NO := consT.getD c.val 0

def sp (c : Fin NC) : Bool := spL.getD c.val false

/-- Shape of the spine at one operator (C-8r). -/
def SpOK : K NC → Bool
  | .forkG i os => if sp i then (os.filter sp).length == 1 else os.all (fun o => !sp o)
  | .forkH _ os _ _ _ _ => os.all (fun p => !sp p.1)
  | .join _ o _ _ _ => !sp o
  | .bjoin ins o _ _ => !sp o || (match ins with | [c, d] => !sp c && sp d | _ => false)
  | .steerC j t f => sp t == sp j && sp f == sp j && t != f
  | .steerD _ t f _ _ => !sp t && !sp f
  | .mux _ _ _ z _ => !sp z
  | .muxn _ _ _ _ z _ => !sp z
  | .amerge x y z _ => sp x && sp y && sp z && x != y
  | .link i o => sp i == sp o
  | .src z which _ => sp z == (which == nIn - 1) && (which != nIn - 1 || z == start)
  | .sink _ => true

def bn (b : Bool) : Nat := if b then 1 else 0

/-! ## The walk checker (C-8s) -/

def grp (c : Fin NC) : Nat := grpL.getD c.val 0
def rho (c : Fin NC) : Nat := rhoL.getD c.val 0
def adj (c : Fin NC) : Bool := adjL.getD c.val true
def al (c : Fin NC) : List Nat := alL.getD c.val []
def lc (c : Fin NC) : Nat := lcL.getD c.val 0

def gr (c : Fin NC) : Nat × Nat := (grp c, rho c)

/-- The group-position indicator of channel (g, r, a) relative to the walk's current channel. -/
def Bo (cur : Option (Nat × Nat)) (g r : Nat) (a : Bool) : Nat :=
  match cur with
  | none => 0
  | some (gc, rc) => bn (a && g == gc && decide (r ≤ rc))

def dcount (dg : Option Nat) (l : List Nat) : Nat :=
  match dg with | some h => l.count h | none => 0

def transR (c : Nat × Nat) (o : Option (Nat × Nat)) (on : Option Nat) (dg : Option Nat) :
    Nat × Nat × Nat × Bool × List Nat → Bool
  | (d, g, r, a, l) => Bo (some c) g r a + bn (on == some d) ==
      dcount dg l + Bo o g r a

def transOK (c : Fin NC) (o : Option (Fin NC)) (dg : Option Nat) : Bool :=
  recs.all (transR (gr c) (o.map gr) (o.map Fin.val) dg)

def condOK (c : Fin NC) (gc : Nat) : Bool :=
  match tab.d c.val with
  | .bj ec ed [cc, _] => ec == .var 0 && ed == .lit 0 &&
      (match tab.d cc with | .hist h _ => h == gc | _ => false)
  | _ => false

def stayOK (c o : Fin NC) : Bool := sp o && grp o == grp c && o != acc && transOK c (some o) none

def forkR (c o : Fin NC) : Bool :=
  o != acc && grp o != grp c &&
  match rules[lc c]? with
  | some (.fork i hs) => i == grp c && hs.filter (fun h => spine.contains h) == [grp o]
  | some (.cm i res idx _) => i == grp c && res == grp o && !(spine.contains idx) && res != idx
  | _ => false

def steerR (c t f : Fin NC) : Bool :=
  match rules[lc c]? with
  | some (.branch gc gd gt gf) => adj c && gd == grp c && grp t == gt && grp f == gf && gt != gf &&
      !(spine.contains gc) && gc != chEnd && gc != chOut && condOK c gc && t != acc && f != acc &&
      grp t != grp c && grp f != grp c
  | _ => false

def amR (c y z : Fin NC) (w : Nat) : Bool :=
  sp z && grp z != grp c &&
  match rules[lc c]? with
  | some (.cm i res idx kk) => i == grp c && res == grp z && !(spine.contains idx) && res != idx &&
      decide (nIn ≤ idx) && decide (nIn ≤ res) && idx != chOut &&
      (z != acc || (res == cres && idx == cidx && kk % 4 != 2)) &&
      (match tab.w w with
       | .lab2 gi => gi == idx && al z == [res] && kk == bn (c == y)
       | .lo3 gi => gi == cidx && idx == cidx && al z == [cq1, cq2] && kk == bn (c == y)
       | .hi3 gi => gi == idx && al z == [res] && c == y && kk == 2)
  | _ => false

def accOK (c x y z : Fin NC) (w : Nat) : Bool :=
  c == acc && c == x && x != y && al z == [cres] && tab.w w == .hi3 cidx &&
    Bo (some (gr c)) (grp z) (rho z) (adj z) == 0

def sinkR (c : Fin NC) : Bool := rules[lc c]? == some (.sink (grp c))

/-- The step out of spine channel `c`. -/
def cOK (c : Fin NC) : Bool :=
  match opAt (consOf c) with
  | .link _ o => stayOK c o
  | .bjoin _ o _ _ => stayOK c o
  | .forkG _ os => match os.find? sp with
    | some o => stayOK c o || (transOK c (some o) (some (grp c)) && forkR c o)
    | none => false
  | .steerC _ t f => sp t && transOK c (some t) (some (grp c)) &&
      transOK c (some f) (some (grp c)) && steerR c t f
  | .amerge x y z w => (stayOK c z && accOK c x y z w) ||
      (transOK c (some z) (some (grp c)) && amR c y z w)
  | .sink _ => transOK c none (some (grp c)) && sinkR c
  | _ => false

def cOKn (n : Nat) : Bool := if h : n < NC then cOK ⟨n, h⟩ else false

/-- Producers of a control_merge's result or index channel are that control_merge's rules. -/
def cmPairOK (r : Rule) : Bool :=
  match r with
  | .cm _ res idx _ => res != idx && decide (nIn ≤ res) && decide (nIn ≤ idx) &&
      rules.all (fun r2 => !(r2.outsL.contains res || r2.outsL.contains idx) ||
        (match r2 with | .cm _ res2 idx2 _ => res2 == res && idx2 == idx | _ => false))
  | _ => true

/-- The labels of the cascade's control_merge (index channel `cidx`). -/
def labOK (r : Rule) : Bool :=
  match r with
  | .cm i _ idx kk => idx != cidx || ((i, kk) == (cq1, 0) || (i, kk) == (cq2, 1) || (i, kk) == (cq3, 2))
  | _ => true

end defs

/-- The proof obligations of a kernel. Each is a decidable check on `KD`'s data, except the
facts about the C reference (`good_run`, `init_*`, `final_*`) and `closedG` (the one-token
spine invariant is closed under firing, C-8i's `closedG`). -/
class KP [KD] : Prop where
  -- token graph
  spine_nodup : spine.Nodup
  ins_ok : checkIns rules = true
  outs_ok : checkOuts spine rules = true
  side_ok : rules.all sideOK = true
  closedG : Closed (step G) (GcdHw.Inv spine)
  -- the C reference, as stores, and the token-level theorem
  init_inv : ∀ a b, GcdHw.Inv spine (init a b)
  init_empty : ∀ a b c, nIn ≤ c → init a b c = []
  init_src : ∀ a b w, w + 1 < nIn → init a b w = [srcVal a b w]
  init_start : ∀ a b, init a b (nIn - 1) = [0]
  src_start : ∀ a b, srcVal a b (nIn - 1) = 0
  final_out : ∀ r, final r chOut = [r]
  final_empty : ∀ r c, c ≠ chEnd → c ≠ chOut → final r c = []
  good_run : ∀ a b, dom a b → ∃ n, Run (step G) (init a b) n (final (spec a b))
  -- ports
  env_np : ∀ w, w < nIn → produced w = false
  out_nc : consumed chOut = false
  out_ge : nIn ≤ chOut
  -- the network
  ops_ok : ∀ o, OpChk tab (opAt o)
  rank_ok : RankOK tab
  nf_pos : 0 < tab.nf
  prod_out : ∀ (o : Fin NO) (c : Fin NC), c ∈ (opAt o).outsC → prodOf c = o
  cons_in : ∀ (o : Fin NO) (c : Fin NC), c ∈ (opAt o).insC → consOf c = o
  prod_mem : ∀ c : Fin NC, c ∈ (opAt (prodOf c)).outsC
  cons_mem : ∀ c : Fin NC, c ∈ (opAt (consOf c)).insC
  out0_desc : tab.d out0.val = .hist chOut out0d
  -- the control spine
  spok : ∀ o, SpOK (opAt o) = true
  noloop : ∀ c, prodOf c ≠ consOf c
  sp_start : sp start = true
  prod_start : opAt (prodOf start) = .src start (nIn - 1) 0
  -- the walk certificate
  spN_chk : (List.range NC).all (fun n => spL.getD n false == spN.contains n) = true
  recs_chk : recs == spN.map (fun n => (n, grpL.getD n 0, rhoL.getD n 0, adjL.getD n true,
    alL.getD n []))
  cOK_chk : spN.all cOKn = true
  recs_glob : recs.all (fun r => spine.contains r.2.1 && r.2.2.2.2.all spine.contains &&
    (!r.2.2.2.1 || r.2.2.2.2 == [r.2.1])) = true
  init_chk : recs.all (fun r => bn (r.1 == start.val) ==
    Bo (some (nIn - 1, rhoL.getD start.val 0)) r.2.1 r.2.2.1 r.2.2.2.1) = true
  grp_start : grp start = nIn - 1
  spine_noend : spine.all (fun g => g != chEnd && g != chOut) = true
  cmPair_chk : rules.all cmPairOK = true
  lab_chk : rules.all labOK = true
  r154 : rules[cl1]? = some (.cm cq1 cres cidx 0)
  r155 : rules[cl2]? = some (.cm cq2 cres cidx 1)
  cq12 : cq1 ≠ cq2
  cq31 : cq3 ≠ cq1
  cq32 : cq3 ≠ cq2
  cq1_sp : cq1 ∈ spine
  cq2_sp : cq2 ∈ spine
  idx_ge : nIn ≤ cidx
  start_acc : start ≠ acc

end Formal.Net.KCap
