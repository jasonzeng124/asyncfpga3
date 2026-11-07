import Formal.Net.CapstoneSafeHist
import Formal.Net.CapstoneSafePer
import Formal.Net.CapstoneCM
import Formal.Net.CapstoneSrc
import Formal.Net.OpsGcd
import Formal.Net.OpsLink
import Formal.Net.OpsMuxNOp

/-!
# Probe C-8m: circuit networks over bdc's gcd_hw graph, and their stream solution

A circuit network is a list of operators `K n` over channels `Fin n`, each one a cell kind
of the Ops framework (fork, join, steer, mux, 3-way mux, arbiter-merge stage, link, source,
sink). `Cell` is the gate-model hypothesis of an operator, `Eqn` its token equation,
`cell_op` the Ops operator theorem for it (all proved in 8f/8j/8l; here only dispatched).

The stream solution (O2) is described per circuit channel by a descriptor `D`:
* `hist h d`: the channel carries GcdHw channel `h`'s one-invocation history, repeated
  forever (`perL`), `d` if that history is empty;
* `copy c`, `zero`, `cmz x y w`, `bj ec ed ins`: ghost values (control channels, arbiter
  outputs, the branch-internal joined channel), defined by the operator's own equation.

`refF` evaluates descriptors (by a rank, checked); `ref_*` unfold it. Each operator carries
witnesses naming the GcdHw rule it implements; `OpChk` (decidable) checks them against
`GcdHw.Gcd.rules` and the descriptors, and `eqn_sound` proves the operator's token equation
for the solution from the run invariants of `CapstoneSafeHist`.
-/

namespace Formal.Net.CapNet
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.GcdHw Formal.Net.CapSafe

abbrev R : List Rule := GcdHw.Gcd.rules

/-! ## Join-input justifications -/

/-- How a GcdHw comp input is obtained from the circuit join's inputs:
* `direct p d`: circuit input `p` carries it (default `d`);
* `fold l1 p g1 d e1`: it is the output of the zero-delay comp `l1 = comp [g1] _ e1`
  (trunci), whose input `g1` circuit input `p` carries (default `d`);
* `const l1 g1 e1`: it is the output of the zero-delay comp `l1 = comp [g1] _ e1` with a
  closed `e1` (a control-triggered constant). -/
inductive J
  | direct (p d : Nat)
  | fold (l1 p g1 d : Nat) (e1 : E)
  | const (l1 g1 : Nat) (e1 : E)
  deriving DecidableEq, Repr

def J.σ : J → E
  | .direct p _ => .var p
  | .fold _ p _ _ e1 => e1.subst [.var p]
  | .const _ _ e1 => e1

def J.dflt : J → Nat
  | .direct _ d => d
  | .fold _ _ _ d e1 => e1.eval [d]
  | .const _ _ e1 => e1.eval []

def evf : E → Bool
  | .var _ => false
  | .lit _ => true
  | .un _ _ a => evf a
  | .bin _ _ a b => evf a && evf b
  | .sel s a b => evf s && evf a && evf b

theorem evf_eval : ∀ (e : E) (env : List Nat), evf e = true → e.eval env = e.eval []
  | .var _, _, h => by simp [evf] at h
  | .lit _, _, _ => rfl
  | .un o w a, env, h => by simp only [E.eval]; rw [evf_eval a env h]
  | .bin o w a b, env, h => by
    simp only [evf, Bool.and_eq_true] at h
    simp only [E.eval]; rw [evf_eval a env h.1, evf_eval b env h.2]
  | .sel s a b, env, h => by
    simp only [evf, Bool.and_eq_true] at h
    simp only [E.eval]; rw [evf_eval s env h.1.1, evf_eval a env h.1.2, evf_eval b env h.2]

/-! ## Descriptors and the solution -/

inductive D
  | hist (h d : Nat)
  | copy (c : Nat)
  | zero
  | cmz (x y w : Nat)
  | bj (ec ed : E) (ins : List Nat)
  deriving DecidableEq, Repr

/-- The arbiter-stage oracles: the token run's control_merge labels, read from the history
of the control_merge's index channel `gi`. `lab2`: a 2-input merge (label 1 = input 1);
`hi3`/`lo3`: stage 2 / stage 1 of the 3-input cascade (label 2 / label 1 among labels ≠ 2). -/
inductive W
  | lab2 (gi : Nat)
  | hi3 (gi : Nat)
  | lo3 (gi : Nat)
  deriving DecidableEq, Repr

def W.om (H : Nat → List Nat) : W → Nat → Bool
  | .lab2 gi, k => perL (H gi) 0 k % 2 == 1
  | .hi3 gi, k => perL (H gi) 0 k % 4 == 2
  | .lo3 gi, k => perL ((H gi).filter (fun v => v % 4 != 2)) 0 k % 4 == 1

structure Tab where
  desc : List D
  om : List W
  rank : List Nat
  nf : Nat

def Tab.d (T : Tab) (c : Nat) : D := T.desc.getD c .zero
def Tab.w (T : Tab) (w : Nat) : W := T.om.getD w (.lab2 0)
def Tab.rk (T : Tab) (c : Nat) : Nat := T.rank.getD c 0

def refF (T : Tab) (H : Nat → List Nat) : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | f + 1, c, k => match T.d c with
    | .hist h d => perL (H h) d k
    | .copy c' => refF T H f c' k
    | .zero => 0
    | .cmz x y w =>
      2 * (if (T.w w).om H k then refF T H f y (cnt ((T.w w).om H) k)
           else refF T H f x (cnt (fun i => !(T.w w).om H i) k)) + Mux.b2n ((T.w w).om H k)
    | .bj ec ed ins =>
      2 * ed.eval (ins.map fun c => refF T H f c k) + ec.eval (ins.map fun c => refF T H f c k) % 2

def D.deps : D → List Nat
  | .copy c => [c]
  | .cmz x y _ => [x, y]
  | .bj _ _ ins => ins
  | _ => []

/-- The descriptor graph is ranked (so `refF` is defined by its equations). -/
def RankOK (T : Tab) : Prop :=
  ∀ c, (T.d c).deps ≠ [] → T.rk c + 1 < T.nf ∧ ∀ c' ∈ (T.d c).deps, T.rk c' < T.rk c

theorem refF_congr (T : Tab) (H : Nat → List Nat) (c : Nat) (f1 f2 : Nat)
    (h : ∀ c' ∈ (T.d c).deps, ∀ k, refF T H f1 c' k = refF T H f2 c' k) :
    ∀ k, refF T H (f1 + 1) c k = refF T H (f2 + 1) c k := by
  intro k
  simp only [refF]
  cases hd : T.d c with
  | hist h d => rfl
  | copy c' => exact h c' (by simp [hd, D.deps]) k
  | zero => rfl
  | cmz x y w =>
    simp only
    rw [h x (by simp [hd, D.deps]), h y (by simp [hd, D.deps])]
  | bj ec ed ins =>
    simp only
    have : ins.map (fun c => refF T H f1 c k) = ins.map (fun c => refF T H f2 c k) :=
      List.map_congr_left (fun c' hc' => h c' (by simp [hd, D.deps, hc']) k)
    rw [this]

theorem refF_stable (T : Tab) (H : Nat → List Nat) (hR : RankOK T) :
    ∀ r c, T.rk c ≤ r → ∀ f k, refF T H (f + r + 1) c k = refF T H (r + 1) c k := by
  intro r
  induction r using Nat.strongRecOn with
  | _ r ih =>
    intro c hc f
    apply refF_congr
    intro c' hc' k
    have hne : (T.d c).deps ≠ [] := List.ne_nil_of_mem hc'
    have hlt := (hR c hne).2 c' hc'
    have hr : T.rk c' < r := by omega
    -- both sides equal refF (rk c' + 1) c'
    have e1 := ih (T.rk c') hr c' (Nat.le_refl _) (f + r - T.rk c' - 1) k
    have e2 := ih (T.rk c') hr c' (Nat.le_refl _) (r - T.rk c' - 1) k
    rw [show f + r - T.rk c' - 1 + T.rk c' + 1 = f + r by omega] at e1
    rw [show r - T.rk c' - 1 + T.rk c' + 1 = r by omega] at e2
    rw [e1, e2]

/-- The solution on circuit channel `c`. -/
def refT (T : Tab) (H : Nat → List Nat) (c k : Nat) : Nat := refF T H T.nf c k

theorem refF_nf (T : Tab) (H : Nat → List Nat) (hR : RankOK T) {c c' : Nat}
    (hd : (T.d c).deps ≠ []) (hc' : c' ∈ (T.d c).deps) (k : Nat) :
    refF T H (T.nf - 1) c' k = refT T H c' k := by
  have h1 := hR c hd
  have h2 := h1.2 c' hc'
  have e1 := refF_stable T H hR (T.rk c') c' (Nat.le_refl _) (T.nf - 2 - T.rk c') k
  have e2 := refF_stable T H hR (T.rk c') c' (Nat.le_refl _) (T.nf - 1 - T.rk c') k
  rw [show T.nf - 2 - T.rk c' + T.rk c' + 1 = T.nf - 1 by omega] at e1
  rw [show T.nf - 1 - T.rk c' + T.rk c' + 1 = T.nf by omega] at e2
  unfold refT; rw [e1, e2]

theorem refT_unfold (T : Tab) (H : Nat → List Nat) (hR : RankOK T) {c : Nat} (hd : (T.d c).deps ≠ [])
    (k : Nat) : refT T H c k = refF T H (T.nf - 1 + 1) c k := by
  have := (hR c hd).1
  unfold refT; rw [show T.nf - 1 + 1 = T.nf by omega]

theorem ref_hist (T : Tab) (H : Nat → List Nat) {c h d : Nat} (hd : T.d c = .hist h d) (hnf : 0 < T.nf)
    (k : Nat) : refT T H c k = perL (H h) d k := by
  unfold refT; rw [show T.nf = T.nf - 1 + 1 by omega]; simp only [refF, hd]

theorem ref_zero (T : Tab) (H : Nat → List Nat) {c : Nat} (hd : T.d c = .zero) (hnf : 0 < T.nf)
    (k : Nat) : refT T H c k = 0 := by
  unfold refT; rw [show T.nf = T.nf - 1 + 1 by omega]; simp only [refF, hd]

theorem ref_copy (T : Tab) (H : Nat → List Nat) (hR : RankOK T) {c c' : Nat} (hd : T.d c = .copy c')
    (k : Nat) : refT T H c k = refT T H c' k := by
  have hne : (T.d c).deps ≠ [] := by simp [hd, D.deps]
  rw [refT_unfold T H hR hne]; simp only [refF, hd]
  exact refF_nf T H hR hne (by simp [hd, D.deps]) k

theorem ref_cmz (T : Tab) (H : Nat → List Nat) (hR : RankOK T) {c x y w : Nat} (hd : T.d c = .cmz x y w)
    (k : Nat) : refT T H c k =
      2 * (if (T.w w).om H k then refT T H y (cnt ((T.w w).om H) k)
           else refT T H x (cnt (fun i => !(T.w w).om H i) k)) + Mux.b2n ((T.w w).om H k) := by
  have hne : (T.d c).deps ≠ [] := by simp [hd, D.deps]
  rw [refT_unfold T H hR hne]; simp only [refF, hd]
  rw [refF_nf T H hR hne (c' := x) (by simp [hd, D.deps]), refF_nf T H hR hne (c' := y) (by simp [hd, D.deps])]

theorem ref_bj (T : Tab) (H : Nat → List Nat) (hR : RankOK T) {c : Nat} {ec ed : E} {ins : List Nat}
    (hd : T.d c = .bj ec ed ins) (hne : ins ≠ []) (k : Nat) : refT T H c k =
      2 * ed.eval (ins.map fun c => refT T H c k) + ec.eval (ins.map fun c => refT T H c k) % 2 := by
  have hne' : (T.d c).deps ≠ [] := by simp [hd, D.deps, hne]
  rw [refT_unfold T H hR hne']; simp only [refF, hd]
  have : ins.map (fun c => refF T H (T.nf - 1) c k) = ins.map (fun c => refT T H c k) :=
    List.map_congr_left (fun c' hc' => refF_nf T H hR hne' (by simp [hd, D.deps, hc']) k)
  rw [this]

/-- Following `copy` descriptors. -/
def chase (T : Tab) : Nat → Nat → Nat
  | 0, c => c
  | f + 1, c => match T.d c with
    | .copy c' => chase T f c'
    | _ => c

theorem ref_chase (T : Tab) (H : Nat → List Nat) (hR : RankOK T) :
    ∀ f c k, refT T H c k = refT T H (chase T f c) k := by
  intro f
  induction f with
  | zero => intro c k; rfl
  | succ f ih =>
    intro c k
    simp only [chase]
    cases hd : T.d c with
    | copy c' => rw [ref_copy T H hR hd, ih]
    | _ => rfl

/-! ## The histories of a complete run -/

def Hh (a b : Nat) (y : TS) (c : Nat) : List Nat := GcdHw.Gcd.init a b c ++ y.pr c

theorem Hh_pr {a b : Nat} {y : TS} {c : Nat} (h : 3 ≤ c) : Hh a b y c = y.pr c := by
  simp [Hh, init_empty a b c h]

theorem Hh_cn {a b : Nat} {y : TS} (hy : Good a b y) {c : Nat} (h3 : c ≠ 3) (h250 : c ≠ 250) :
    Hh a b y c = y.cn c := by
  have := hy.fifo c
  rw [hy.fin, final_empty _ c h3 h250, List.append_nil] at this
  exact this

def NoEnd (g : Nat) : Prop := g ≠ 3 ∧ g ≠ 250

/-! ## Operators -/

def sel2 (v : Nat) : Bool := v % 2 == 1
def selD (v : Nat) : Nat := if v % 2 = 1 then 2 else v / 2 % 2
def jg (e : E) (js : List J) : List Nat → Nat := fun vs => (e.subst (js.map J.σ)).eval vs
def bg (ec ed : E) : List Nat → Nat := fun vs => 2 * ed.eval vs + ec.eval vs % 2
def srcV (a b which : Nat) : Nat := if which = 0 then a else if which = 1 then b else 0

/-- Checker witnesses (they do not enter the gate models or the equations). -/
structure JW where
  l : Nat
  gins : List Nat
  go : Nat
  dO : Nat
  deriving Repr

structure SW where
  l : Nat
  gc : Nat
  gd : Nat
  gt : Nat
  gf : Nat
  jc : J
  jd : J
  jins : List Nat
  fold : Option (Nat × Nat × Nat × Nat)
  dt : Nat
  df : Nat
  deriving Repr

structure MW where
  l : Nat
  gs : Nat
  gx : Nat
  gy : Nat
  gz : Nat
  dx : Nat
  dy : Nat
  dz : Nat
  zc : Nat
  xa : Nat
  ya : Nat
  w : Nat
  gi : Nat
  lf : Nat
  hs : List Nat
  deriving Repr

structure NW where
  l : Nat
  gs : Nat
  g0 : Nat
  g1 : Nat
  g2 : Nat
  gz : Nat
  d0 : Nat
  d1 : Nat
  d2 : Nat
  dz : Nat
  zc : Nat
  acc : Nat
  in2 : Nat
  in0 : Nat
  in1 : Nat
  w2 : Nat
  w1 : Nat
  deriving Repr

/-- The operators. `e` of `join` and `fd` of `steerD` are the data functions (checked
against the rules); the `*W` fields are checker witnesses. -/
inductive K (n : Nat)
  | forkG (i : Fin n) (os : List (Fin n))
  | forkH (i : Fin n) (os : List (Fin n × Nat)) (l h d : Nat) (hs : List Nat)
  | join (ins : List (Fin n)) (o : Fin n) (e : E) (js : List J) (jw : JW)
  | bjoin (ins : List (Fin n)) (o : Fin n) (ec ed : E)
  | steerC (j t f : Fin n)
  | steerD (j t f : Fin n) (fd : E) (sw : SW)
  | mux (c x y z : Fin n) (mw : MW)
  | muxn (c x0 x1 x2 z : Fin n) (nw : NW)
  | amerge (x y z : Fin n) (w : Nat)
  | link (i o : Fin n)
  | src (z : Fin n) (which d : Nat)
  | sink (i : Fin n)
  deriving Repr

variable {n : Nat}

def cx3 (x0 x1 x2 : Fin n) : Nat → Fin n
  | 0 => x0
  | 1 => x1
  | _ => x2

def K.insC : K n → List (Fin n)
  | .forkG i _ => [i]
  | .forkH i _ _ _ _ _ => [i]
  | .join ins _ _ _ _ => ins
  | .bjoin ins _ _ _ => ins
  | .steerC j _ _ => [j]
  | .steerD j _ _ _ _ => [j]
  | .mux c x y _ _ => [c, x, y]
  | .muxn c x0 x1 x2 _ _ => [c, x0, x1, x2]
  | .amerge x y _ _ => [x, y]
  | .link i _ => [i]
  | .src _ _ _ => []
  | .sink i => [i]

def K.outsC : K n → List (Fin n)
  | .forkG _ os => os
  | .forkH _ os _ _ _ _ => os.map Prod.fst
  | .join _ o _ _ _ => [o]
  | .bjoin _ o _ _ => [o]
  | .steerC _ t f => [t, f]
  | .steerD _ t f _ _ => [t, f]
  | .mux _ _ _ z _ => [z]
  | .muxn _ _ _ _ z _ => [z]
  | .amerge _ _ z _ => [z]
  | .link _ o => [o]
  | .src z _ _ => [z]
  | .sink _ => []

/-- The gate-model hypothesis of each operator (8f/8j/8l cell models). -/
def Cell (ch : Fin n → Chan) (sv : Nat → Nat) : K n → Prop
  | .forkG i os => Fork.Fork (ch i) (os.map ch)
  | .forkH i os _ _ _ _ => Fork.Fork (ch i) ((os.map Prod.fst).map ch)
  | .join ins o e js _ => Join.Join (jg e js) (ins.map ch) (ch o)
  | .bjoin ins o ec ed => Join.Join (bg ec ed) (ins.map ch) (ch o)
  | .steerC j t f => Steer.Steer sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then t else f))
  | .steerD j t f fd _ =>
      Steer.Steer sel2 (fun v => fd.eval [v / 2]) (ch j) (fun b => ch (bif b then t else f))
  | .mux c x y z _ => ∃ j0 j1, Mux.Mux sel2 (ch x) (ch y) (ch c) (ch z) j0 j1
  | .muxn c x0 x1 x2 z _ =>
      ∃ j, MuxN.MuxN selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j
  | .amerge x y z _ => ∃ g1 g2, CM.AMerge (ch x) (ch y) (ch z) g1 g2
  | .link i o => ∃ c, Link.Link (ch i) (ch o) c
  | .src z which _ => Capstone.Src (ch z) (sv which)
  | .sink i => Ops.Gcd.Sink (ch i)

/-- H_CM_FORCED, per arbiter stage: the circuit's winner of every offered output token is
the oracle `om w` (the token run's label). -/
def Forced (ch : Fin n → Chan) (om : Nat → Nat → Bool) : K n → Prop
  | .amerge _ _ z w => ∀ k r, OffAt (ch z) k r → CM.winner (ch z) k = om w k
  | _ => True

/-- The token equations. -/
def Eqn (ch : Fin n → Chan) (om : Nat → Nat → Bool) (sv : Nat → Nat) : K n → (Fin n → Nat → Nat) → Prop
  | .forkG i os => Fork.forkEq i os
  | .forkH i os _ _ _ _ => Fork.forkEq i (os.map Prod.fst)
  | .join ins o e js _ => Join.joinEq (jg e js) ins o
  | .bjoin ins o ec ed => Join.joinEq (bg ec ed) ins o
  | .steerC j t f => Steer.steerEq sel2 (fun _ => 0) j (fun b => bif b then t else f)
  | .steerD j t f fd _ =>
      Steer.steerEq sel2 (fun v => fd.eval [v / 2]) j (fun b => bif b then t else f)
  | .mux c x y z _ => Mux.muxEq sel2 c x y z
  | .muxn c x0 x1 x2 z _ => MuxN.muxnEq selD c (cx3 x0 x1 x2) z
  | .amerge x y z w => Capstone.amergeOff (ch z) (om w) x y z
  | .link i o => Link.linkEq i o
  | .src z which _ => Capstone.srcEq z (sv which)
  | .sink _ => fun _ => True

/-- Distinctness side conditions of the arbiter stages. -/
def Dist : K n → Prop
  | .amerge x y z _ => x ≠ z ∧ y ≠ z
  | _ => True

/-- **Every operator is an Ops operator** (dispatch to 8f/8j/8l's theorems). -/
theorem cell_op (ch : Fin n → Chan) (om : Nat → Nat → Bool) (sv : Nat → Nat) (k : K n)
    (hc : Cell ch sv k) (hf : Forced ch om k) (hd : Dist k) :
    OpProto ch k.insC k.outsC ∧ OpData ch k.insC k.outsC (Eqn ch om sv k) := by
  cases k with
  | forkG i os => exact Fork.fork_op ch i os hc
  | forkH i os l h d hs => exact Fork.fork_op ch i (os.map Prod.fst) hc
  | join ins o e js _ => exact Join.join_op ch ins o hc
  | bjoin ins o ec ed => exact Join.join_op ch ins o hc
  | steerC j t f => exact Steer.steer_op ch j (fun b => bif b then t else f) hc
  | steerD j t f fd _ => exact Steer.steer_op ch j (fun b => bif b then t else f) hc
  | mux c x y z _ =>
    obtain ⟨j0, j1, M⟩ := hc; exact Mux.mux_op ch c x y z j0 j1 M
  | muxn c x0 x1 x2 z _ =>
    obtain ⟨j, M⟩ := hc; exact MuxN.muxn_op ch c (cx3 x0 x1 x2) z j M
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc
    exact Capstone.amerge_op_forced ch x y z g1 g2 M hd.1 hd.2 (om w) hf
  | link i o => obtain ⟨c, L⟩ := hc; exact Link.link_op ch i o c L
  | src z which _ => exact Capstone.src_op ch z (sv which) hc
  | sink i => exact Ops.Gcd.sink_op ch i hc

/-! ## The checker -/

/-- Justification `j` produces GcdHw channel `gm` from circuit inputs `ins` (Nat ids). -/
def JOK (T : Tab) (ins : List Nat) (gm : Nat) : J → Prop
  | .direct p d => p < ins.length ∧ T.d (ins.getD p 0) = .hist gm d ∧ NoEnd gm
  | .fold l1 p g1 d e1 => p < ins.length ∧ R[l1]? = some (.comp [g1] gm e1) ∧
      T.d (ins.getD p 0) = .hist g1 d ∧ NoEnd g1 ∧ NoEnd gm ∧ 3 ≤ gm
  | .const l1 g1 e1 => R[l1]? = some (.comp [g1] gm e1) ∧ evf e1 = true ∧ NoEnd gm ∧ 3 ≤ gm

instance (T : Tab) (ins : List Nat) (gm : Nat) (j : J) : Decidable (JOK T ins gm j) := by
  cases j <;> unfold JOK NoEnd <;> infer_instance

def FoldOK (T : Tab) (t f : Nat) (fd : E) (sw : SW) : Option (Nat × Nat × Nat × Nat) → Prop
  | none => fd = .var 0 ∧ T.d t = .hist sw.gt sw.dt ∧ T.d f = .hist sw.gf sw.df
  | some (lt, lf, gt', gf') => R[lt]? = some (.comp [sw.gt] gt' fd) ∧ R[lf]? = some (.comp [sw.gf] gf' fd) ∧
      NoEnd sw.gt ∧ NoEnd sw.gf ∧ 3 ≤ gt' ∧ 3 ≤ gf' ∧ T.d t = .hist gt' sw.dt ∧ T.d f = .hist gf' sw.df

instance (T : Tab) (t f : Nat) (fd : E) (sw : SW) (o : Option (Nat × Nat × Nat × Nat)) :
    Decidable (FoldOK T t f fd sw o) := by
  rcases o with _ | ⟨lt, lf, gt', gf'⟩ <;> unfold FoldOK NoEnd <;> infer_instance

def OpChk (T : Tab) : K n → Prop
  | .forkG i os => ∀ o ∈ os, T.d o.val = .copy i.val
  | .forkH i os l h d hs => R[l]? = some (.fork h hs) ∧ T.d i.val = .hist h d ∧ NoEnd h ∧
      ∀ p ∈ os, T.d p.1.val = .hist p.2 d ∧ p.2 ∈ hs ∧ 3 ≤ p.2
  | .join ins o e js jw => R[jw.l]? = some (.comp jw.gins jw.go e) ∧ T.d o.val = .hist jw.go jw.dO ∧
      3 ≤ jw.go ∧ js.length = jw.gins.length ∧ jw.gins ≠ [] ∧
      (∀ m < js.length, JOK T (ins.map Fin.val) (jw.gins.getD m 0) (js.getD m (.direct 0 0))) ∧
      jw.dO = e.eval (js.map J.dflt)
  | .bjoin ins o ec ed => T.d o.val = .bj ec ed (ins.map Fin.val) ∧ ins ≠ []
  | .steerC _ t f => T.d t.val = .zero ∧ T.d f.val = .zero
  | .steerD j t f fd sw =>
      R[sw.l]? = some (.branch sw.gc sw.gd sw.gt sw.gf) ∧ NoEnd sw.gc ∧ NoEnd sw.gd ∧ 3 ≤ sw.gt ∧
      3 ≤ sw.gf ∧ T.d j.val = .bj sw.jc.σ sw.jd.σ sw.jins ∧ sw.jins ≠ [] ∧
      JOK T sw.jins sw.gc sw.jc ∧ JOK T sw.jins sw.gd sw.jd ∧
      (if (sw.jc.dflt % 2 == 1) then sw.dt else sw.df) = fd.eval [sw.jd.dflt] ∧
      FoldOK T t.val f.val fd sw sw.fold
  | .mux c x y z mw =>
      R[mw.l]? = some (.mux mw.gs [mw.gx, mw.gy] mw.gz 1) ∧ T.d x.val = .hist mw.gx mw.dx ∧
      T.d y.val = .hist mw.gy mw.dy ∧ T.d z.val = .hist mw.gz mw.dz ∧ NoEnd mw.gs ∧ NoEnd mw.gx ∧
      NoEnd mw.gy ∧ 3 ≤ mw.gz ∧ NoEnd mw.gi ∧ 3 ≤ mw.gs ∧
      chase T 32 c.val = mw.zc ∧ T.d mw.zc = .cmz mw.xa mw.ya mw.w ∧ T.w mw.w = .lab2 mw.gi ∧
      (mw.gs = mw.gi ∨ (R[mw.lf]? = some (.fork mw.gi mw.hs) ∧ mw.gs ∈ mw.hs)) ∧ mw.dz = mw.dx
  | .muxn c x0 x1 x2 z nw =>
      R[nw.l]? = some (.mux nw.gs [nw.g0, nw.g1, nw.g2] nw.gz 2) ∧ T.d x0.val = .hist nw.g0 nw.d0 ∧
      T.d x1.val = .hist nw.g1 nw.d1 ∧ T.d x2.val = .hist nw.g2 nw.d2 ∧ T.d z.val = .hist nw.gz nw.dz ∧
      NoEnd nw.gs ∧ NoEnd nw.g0 ∧ NoEnd nw.g1 ∧ NoEnd nw.g2 ∧ 3 ≤ nw.gz ∧
      chase T 32 c.val = nw.zc ∧ T.d nw.zc = .cmz nw.acc nw.in2 nw.w2 ∧
      T.d nw.acc = .cmz nw.in0 nw.in1 nw.w1 ∧ T.w nw.w2 = .hi3 nw.gs ∧ T.w nw.w1 = .lo3 nw.gs ∧
      nw.dz = nw.d0
  | .amerge x y z w => T.d z.val = .cmz x.val y.val w ∧ x ≠ z ∧ y ≠ z
  | .link i o => T.d o.val = T.d i.val ∨ T.d o.val = .copy i.val
  | .src z which d => (which = 0 ∧ T.d z.val = .hist 0 d) ∨ (which = 1 ∧ T.d z.val = .hist 1 d) ∨
      (which = 2 ∧ T.d z.val = .zero)
  | .sink _ => True

instance (T : Tab) (k : K n) : Decidable (OpChk T k) := by
  cases k <;> unfold OpChk <;> (try unfold NoEnd) <;> infer_instance

end Formal.Net.CapNet
