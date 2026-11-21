import Formal.Net.IpowCapSafeHist
import Formal.Net.CapstoneNetDef
import Formal.Net.CapstoneSafePer

/-!
# INSTANTIATED for ipow_ps by formal/tools/capnet/instantiate.py -- DO NOT EDIT

Source: `Formal/Net/CapstoneNetDef.lean` (the gcd_hw proof), rewritten by the substitution table in
instantiate.py (namespace, the kernel's graph module, out/end channels 57/4, the spec
`IpowHw.ipowSpec a b` in place of `Nat.gcd a b`, theorem prefix `ipow_hw_`). Everything else is the gcd text;
its comments below still speak of gcd_hw where they describe the shared argument.

Only the kernel-dependent slice of CapstoneNetDef is copied: `R`, the run histories `Hh`,
`NoEnd`, and the checker `JOK`/`FoldOK`/`OpChk`. The operator kinds `K`, the gate models
`Cell`, the equations `Eqn`, `Forced`, `cell_op` and the solution `refT` are gcd's own
(imported from `Formal.Net.CapstoneNetDef`, namespace `Formal.Net.CapNet`).
-/

namespace Formal.Net.IpowCap
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.GcdHw
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)

abbrev R : List Rule := IpowHw.rules


def Hh (a b : Nat) (y : TS) (c : Nat) : List Nat := IpowHw.init a b c ++ y.pr c

theorem Hh_pr {a b : Nat} {y : TS} {c : Nat} (h : 3 ≤ c) : Hh a b y c = y.pr c := by
  simp [Hh, init_empty a b c h]

theorem Hh_cn {a b : Nat} {y : TS} (hy : Good a b y) {c : Nat} (h3 : c ≠ 4) (h250 : c ≠ 57) :
    Hh a b y c = y.cn c := by
  have := hy.fifo c
  rw [hy.fin, final_empty _ c h3 h250, List.append_nil] at this
  exact this

def NoEnd (g : Nat) : Prop := g ≠ 4 ∧ g ≠ 57

/-! ## The checker -/

variable {n : Nat}

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

end Formal.Net.IpowCap
