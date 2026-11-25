import Formal.Net.IpowCapCut

/-!
# INSTANTIATED for ipow_ps by formal/tools/capnet/instantiate.py -- DO NOT EDIT

Source: `Formal/Net/CapstoneWalkTab.lean` (the gcd_hw proof), rewritten by the substitution table in
instantiate.py (namespace, the kernel's graph module, out/end channels 57/4, the spec
`IpowHw.ipowSpec a b` in place of `Nat.gcd a b`, theorem prefix `ipow_hw_`). Everything else is the gcd text;
its comments below still speak of gcd_hw where they describe the shared argument.

H_WALK proof (C-8s). gcd's 3-input cascade (acc251 over control_merge12, rules 154/155) has no
counterpart in this kernel: its constants are mapped to the 2-input control_merge of rules
19/20 (cm 22|41 -> 39, index 40), for which every cascade fact stated here is true
(kernel-checked), and `acc` to channel 0, which is not a spine channel, so the walk never
takes the cascade branches. The tables (`spN` .. `recs`) are `capnet.py walktab`'s.
-/

namespace Formal.Net.IpowCap
open Formal.Net Formal.Net.GcdHw Formal.Net.IpowHw
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CapSafe (cntL perL cntL_zero cntL_cons_succ cnt_take cnt_add cnt_periodic perL_ne perL_mod len_pos cnt_per filter_rank filter_len sel tst sel_rank sel_len)

set_option maxRecDepth 100000

def spN : List Nat := [2, 5, 28, 29, 63, 65, 66, 67, 68, 85, 90, 94, 98, 99, 100]

def grpL : List Nat := [0, 0, 2, 0, 0, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 39, 0, 41, 41, 41, 41, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 55, 0, 0, 0, 0, 58, 0, 0, 0, 5, 0, 0, 0, 39, 39, 58]

def rhoL : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 2, 0, 0]

def adjL : List Bool := [true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true, true]

def alL : List (List Nat) := [[0], [0], [2], [0], [0], [5], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [22], [23], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [39], [0], [41], [41], [41], [41], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [0], [55], [0], [0], [0], [0], [58], [0], [0], [0], [5], [0], [0], [0], [39], [39], [58]]

def lcL : List Nat := [0, 0, 0, 0, 0, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 35, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 0, 20, 20, 20, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 36, 0, 0, 0, 0, 37, 0, 0, 0, 12, 0, 0, 0, 33, 33, 37]

def recs : List (Nat × Nat × Nat × Bool × List Nat) := [(2, 2, 0, true, [2]), (5, 5, 0, true, [5]), (28, 22, 0, true, [22]), (29, 23, 0, true, [23]), (63, 39, 1, true, [39]), (65, 41, 0, true, [41]), (66, 41, 1, true, [41]), (67, 41, 2, true, [41]), (68, 41, 3, true, [41]), (85, 55, 0, true, [55]), (90, 58, 1, true, [58]), (94, 5, 1, true, [5]), (98, 39, 2, true, [39]), (99, 39, 0, true, [39]), (100, 58, 0, true, [58])]


def grp (c : Fin NC) : Nat := grpL.getD c.val 0
def rho (c : Fin NC) : Nat := rhoL.getD c.val 0
def adj (c : Fin NC) : Bool := adjL.getD c.val true
def al (c : Fin NC) : List Nat := alL.getD c.val []
def lc (c : Fin NC) : Nat := lcL.getD c.val 0
def acc : Fin NC := 0

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
      !(spine.contains gc) && gc != 4 && gc != 57 && condOK c gc && t != acc && f != acc &&
      grp t != grp c && grp f != grp c
  | _ => false

def amR (c y z : Fin NC) (w : Nat) : Bool :=
  sp z && grp z != grp c &&
  match rules[lc c]? with
  | some (.cm i res idx kk) => i == grp c && res == grp z && !(spine.contains idx) && res != idx &&
      decide (3 ≤ idx) && decide (3 ≤ res) && idx != 57 &&
      (z != acc || (res == 39 && idx == 40 && kk % 4 != 2)) &&
      (match tab.w w with
       | .lab2 gi => gi == idx && al z == [res] && kk == bn (c == y)
       | .lo3 gi => gi == 40 && idx == 40 && al z == [22, 41] && kk == bn (c == y)
       | .hi3 gi => gi == idx && al z == [res] && c == y && kk == 2)
  | _ => false

def accOK (c x y z : Fin NC) (w : Nat) : Bool :=
  c == acc && c == x && x != y && al z == [39] && tab.w w == .hi3 40 &&
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

/-! ## Kernel checks -/

theorem spN_chk : (List.range NC).all (fun n => spL.getD n false == spN.contains n) = true := by
  decide +kernel

theorem recs_chk : recs == spN.map (fun n => (n, grpL.getD n 0, rhoL.getD n 0, adjL.getD n true,
    alL.getD n [])) := by decide +kernel

theorem cOK_chk : spN.all cOKn = true := by decide +kernel

theorem recs_glob : recs.all (fun r => spine.contains r.2.1 && r.2.2.2.2.all spine.contains &&
    (!r.2.2.2.1 || r.2.2.2.2 == [r.2.1])) = true := by decide +kernel

theorem init_chk : recs.all (fun r => bn (r.1 == 2) == Bo (some (2, rhoL.getD 2 0)) r.2.1 r.2.2.1 r.2.2.2.1)
    = true := by decide +kernel

theorem grp_start : grp start = 2 := by decide

theorem spine_noend : spine.all (fun g => g != 4 && g != 57) = true := by decide

/-- Producers of a control_merge's result or index channel are that control_merge's rules. -/
def cmPairOK (r : Rule) : Bool :=
  match r with
  | .cm _ res idx _ => res != idx && decide (3 ≤ res) && decide (3 ≤ idx) &&
      rules.all (fun r2 => !(r2.outsL.contains res || r2.outsL.contains idx) ||
        (match r2 with | .cm _ res2 idx2 _ => res2 == res && idx2 == idx | _ => false))
  | _ => true

theorem cmPair_chk : rules.all cmPairOK = true := by decide +kernel

/-- The labels of control_merge12 (index channel 249). -/
def lab249OK (r : Rule) : Bool :=
  match r with
  | .cm i _ idx kk => idx != 40 || ((i, kk) == (22, 0) || (i, kk) == (41, 1) || (i, kk) == (246, 2))
  | _ => true

theorem lab249_chk : rules.all lab249OK = true := by decide +kernel

theorem r154 : rules[19]? = some (.cm 22 39 40 0) := by decide
theorem r155 : rules[20]? = some (.cm 41 39 40 1) := by decide

end Formal.Net.IpowCap
