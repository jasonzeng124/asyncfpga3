import Formal.Timing.WinArray

/-!
# Kernel-friendly single-pass windows: in-arc buckets + a cons table (probe C-10d)

`WinArray.winTable` is the right algorithm for compiled code (`#eval`: in-place
`Array.set`, O(arcs)), but the KERNEL reduces lazily: after k updates an entry
read walks k unevaluated `List.set` layers, and kernel `decide` on 300 arcs took
17 s / 2.1 GB, on 900 arcs it was killed (notes/C-10d-routed.md).

Here the netlist is given as **in-arc buckets** `B : List (List Arc)` (entry `v`
= the arcs into node `v`; the netlist is `ofBuckets B`, arcs = `B.flatten`), and
the windows are computed in one pass over the nodes, consing each new window
onto a list (`tabB`).  Every arc is read once; a source lookup walks already
evaluated cons cells, O(n).  Kernel `decide`: 3000 arcs / 2001 nodes in ~8 s.

* `winB_eq`   : `(ofBuckets B).WF → winB B v = win (ofBuckets B) v`  (every `B`:
  if the buckets are mislabelled, `bucketsOK` fails and `winB` falls back to `win`)
* `checkB_eq` : the same for the check; `checkB_sound`: 10a's `check_sound`.
-/

namespace Formal.Timing
open Formal.Net

/-- A netlist given by its in-arc buckets. -/
def ofBuckets (B : List (List Arc)) : Netlist := ⟨B.flatten⟩

/-- Bucket `i` (counted from `k`) holds only arcs into node `k + i`. -/
def bucketsFrom : List (List Arc) → Nat → Bool
  | [], _ => true
  | b :: bs, k => b.all (fun a => a.dst == k) && bucketsFrom bs (k + 1)

def bucketsOK (B : List (List Arc)) : Bool := bucketsFrom B 0

/-- Window of an earlier node `x < k`, from the reversed table `R` (head = node `k-1`). -/
def rget (R : List (Option Win)) (k x : Nat) : Option Win := R.getD (k - 1 - x) none

/-- One pass over the buckets; `R` is the reversed table of nodes `0 .. k-1`. -/
def tabB : List (List Arc) → Nat → List (Option Win) → List (Option Win)
  | [], _, R => R
  | b :: bs, k, R =>
    let w := if k = 0 then some (0, 0) else collect (fun x => if x < k then rget R k x else none) k b
    tabB bs (k + 1) (w :: R)

def winBfast (B : List (List Arc)) (v : Nat) : Option Win :=
  let R := tabB B 0 []
  if v < R.length then rget R R.length v else if v = 0 then some (0, 0) else none

def winB (B : List (List Arc)) (v : Nat) : Option Win :=
  if bucketsOK B then winBfast B v else win (ofBuckets B) v

def checkB (B : List (List Arc)) (req : Nat) (data : List Nat) (setup : Nat) : Bool :=
  if bucketsOK B then
    let R := tabB B 0 []
    checkWith (fun v => if v < R.length then rget R R.length v else if v = 0 then some (0, 0) else none)
      req data setup
  else check (ofBuckets B) req data setup

def slackB (B : List (List Arc)) (req : Nat) (data : List Nat) (setup : Nat) : Option Int :=
  if bucketsOK B then
    let R := tabB B 0 []
    slackWith (fun v => if v < R.length then rget R R.length v else if v = 0 then some (0, 0) else none)
      req data setup
  else slack (ofBuckets B) req data setup

/-! ## `collect` over a flattened bucket list -/

theorem omerge_assoc (x y z : Option Win) : omerge (omerge x y) z = omerge x (omerge y z) := by
  rcases x with _ | ⟨x1, x2⟩ <;> rcases y with _ | ⟨y1, y2⟩ <;> rcases z with _ | ⟨z1, z2⟩ <;>
    simp only [omerge, Option.some.injEq, Prod.mk.injEq] <;> omega

theorem omerge_none_left (c : Option Win) : omerge none c = c := rfl

theorem collect_append (L : Nat → Option Win) (v : Nat) :
    ∀ p q : List Arc, collect L v (p ++ q) = omerge (collect L v q) (collect L v p)
  | [], q => by simp only [List.nil_append]; exact (omerge_none _).symm
  | a :: p, q => by
    rw [List.cons_append, collect_cons, collect_append L v p q, collect_cons, omerge_assoc]

theorem collect_nil_of (L : Nat → Option Win) (v : Nat) (l : List Arc) (h : ∀ a ∈ l, a.dst ≠ v) :
    collect L v l = none := by
  have := collect_append_none L v l [] h
  rw [List.append_nil] at this; exact this

theorem bucketsFrom_head {b : List Arc} {bs : List (List Arc)} {k : Nat}
    (h : bucketsFrom (b :: bs) k = true) : ∀ a ∈ b, a.dst = k := by
  simp only [bucketsFrom, Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact h.1

theorem bucketsFrom_tail {b : List Arc} {bs : List (List Arc)} {k : Nat}
    (h : bucketsFrom (b :: bs) k = true) : bucketsFrom bs (k + 1) = true := by
  simp only [bucketsFrom, Bool.and_eq_true] at h
  exact h.2

theorem collect_flatten (L : Nat → Option Win) (v : Nat) :
    ∀ (B : List (List Arc)) (k : Nat), bucketsFrom B k = true →
      collect L v B.flatten = if k ≤ v then collect L v (B.getD (v - k) []) else none
  | [], k, _ => by
    simp only [List.flatten_nil, List.getD_eq_getElem?_getD, List.getElem?_nil, Option.getD_none]
    split <;> rfl
  | b :: bs, k, h => by
    rw [List.flatten_cons, collect_append, collect_flatten L v bs (k + 1) (bucketsFrom_tail h)]
    have hb := bucketsFrom_head h
    by_cases hv : v = k
    · subst hv
      simp only [Nat.le_refl, if_true, Nat.sub_self, List.getD_cons_zero]
      rw [if_neg (by omega), omerge_none_left]
    · rw [collect_nil_of L v b (fun a ha => by rw [hb a ha]; exact Ne.symm hv), omerge_none]
      by_cases hk : k + 1 ≤ v
      · rw [if_pos hk, if_pos (by omega)]
        have : v - k = (v - (k + 1)) + 1 := by omega
        rw [this, List.getD_cons_succ]
      · rw [if_neg hk, if_neg (by omega)]

/-! ## The pass computes `win` -/

theorem tabB_length : ∀ (bs : List (List Arc)) (k : Nat) (R : List (Option Win)),
    (tabB bs k R).length = R.length + bs.length
  | [], _, R => by simp [tabB]
  | b :: bs, k, R => by
    simp only [tabB]; rw [tabB_length bs (k + 1)]; simp only [List.length_cons]; omega

theorem tabB_inv (B : List (List Arc)) (hwf : (ofBuckets B).WF) (hok : bucketsOK B = true) :
    ∀ (bs : List (List Arc)) (k : Nat) (R : List (Option Win)),
      B.drop k = bs → R.length = k → (∀ x, x < k → rget R k x = win (ofBuckets B) x) →
      ∀ x, x < k + bs.length → rget (tabB bs k R) (k + bs.length) x = win (ofBuckets B) x
  | [], k, R, _, _, hR => by simpa [tabB] using hR
  | b :: bs, k, R, hd, hl, hR => by
    have hkb : B.getD k [] = b := by
      rw [List.getD_eq_getElem?_getD, ← List.head?_drop, hd]; rfl
    have hd' : B.drop (k + 1) = bs := by rw [← List.drop_drop, hd]; rfl
    have hw : (if k = 0 then some (0, 0) else
        collect (fun x => if x < k then rget R k x else none) k b) = win (ofBuckets B) k := by
      by_cases hk : k = 0
      · subst hk; rfl
      · rw [if_neg hk, win_eq _ hwf hk]
        show _ = collect (win (ofBuckets B)) k B.flatten
        rw [collect_flatten _ _ B 0 hok, if_pos (Nat.zero_le _), Nat.sub_zero, hkb]
        apply collect_congr
        intro a ha hda
        have hmem : a ∈ (ofBuckets B).arcs := by
          show a ∈ B.flatten
          rw [List.mem_flatten]
          refine ⟨b, ?_, ha⟩
          rw [← hkb, List.getD_eq_getElem?_getD]
          have hkl : k < B.length := by
            apply Classical.byContradiction; intro hn
            have : B.drop k = [] := List.drop_eq_nil_of_le (by omega)
            rw [hd] at this; cases this
          rw [List.getElem?_eq_getElem hkl]; exact List.getElem_mem hkl
        have := (hwf a hmem).1
        rw [if_pos (by omega)]
        exact hR a.src (by omega)
    intro x hx
    have e : k + (b :: bs).length = k + 1 + bs.length := by simp only [List.length_cons]; omega
    rw [e]
    show rget (tabB bs (k + 1) ((if k = 0 then some (0, 0) else
      collect (fun x => if x < k then rget R k x else none) k b) :: R)) (k + 1 + bs.length) x = _
    rw [hw]
    exact tabB_inv B hwf hok bs (k + 1) _ hd' (by simp only [List.length_cons, hl]) (by
      intro y hy
      by_cases hyk : y = k
      · subst hyk; simp only [rget, Nat.add_sub_cancel, Nat.sub_self, List.getD_cons_zero]
      · have : k + 1 - 1 - y = (k - 1 - y) + 1 := by omega
        simp only [rget, this, List.getD_cons_succ]
        exact hR y (by omega)) x (by omega)

theorem winBfast_eq (B : List (List Arc)) (hwf : (ofBuckets B).WF) (hok : bucketsOK B = true) (v : Nat) :
    winBfast B v = win (ofBuckets B) v := by
  have hlen : (tabB B 0 []).length = B.length := by rw [tabB_length]; simp
  unfold winBfast
  simp only [hlen]
  by_cases hv : v < B.length
  · rw [if_pos hv]
    have := tabB_inv B hwf hok B 0 [] rfl rfl (fun x hx => absurd hx (Nat.not_lt_zero _)) v (by omega)
    simpa using this
  · rw [if_neg hv]
    by_cases h0 : v = 0
    · subst h0; rw [if_pos rfl]; rfl
    · rw [if_neg h0, win_eq _ hwf h0]
      show none = collect (win (ofBuckets B)) v B.flatten
      rw [collect_flatten _ _ B 0 hok, if_pos (Nat.zero_le _), Nat.sub_zero,
        List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
      rfl

theorem winB_eq (B : List (List Arc)) (hwf : (ofBuckets B).WF) (v : Nat) :
    winB B v = win (ofBuckets B) v := by
  unfold winB
  split
  · next hok => exact winBfast_eq B hwf hok v
  · rfl

theorem winBfast_fun (B : List (List Arc)) (hwf : (ofBuckets B).WF) (hok : bucketsOK B = true) :
    (fun v => if v < (tabB B 0 []).length then rget (tabB B 0 []) (tabB B 0 []).length v
      else if v = 0 then some (0, 0) else none) = win (ofBuckets B) :=
  funext (winBfast_eq B hwf hok)

theorem checkB_eq (B : List (List Arc)) (hwf : (ofBuckets B).WF) (req : Nat) (data : List Nat)
    (setup : Nat) : checkB B req data setup = check (ofBuckets B) req data setup := by
  unfold checkB
  split
  · next hok => simp only []; rw [winBfast_fun B hwf hok]; rfl
  · rfl

theorem slackB_eq (B : List (List Arc)) (hwf : (ofBuckets B).WF) (req : Nat) (data : List Nat)
    (setup : Nat) : slackB B req data setup = slack (ofBuckets B) req data setup := by
  unfold slackB
  split
  · next hok => simp only []; rw [winBfast_fun B hwf hok]; rfl
  · rfl

theorem checkB_sound {B : List (List Arc)} (hwf : (ofBuckets B).WF) {req : Nat} {data : List Nat}
    {setup : Nat} (hc : checkB B req data setup = true) {sig : Nat → Trace}
    (r : Run (ofBuckets B) sig) : ∀ d ∈ data, ∀ s t, changes (sig d) s → changes (sig req) t →
      s + setup ≤ t :=
  check_sound hwf (checkB_eq B hwf req data setup ▸ hc) r

theorem changes_in_winB {B : List (List Arc)} (hwf : (ofBuckets B).WF) {sig : Nat → Trace}
    (r : Run (ofBuckets B) sig) : ∀ v t, changes (sig v) t →
      ∃ e l, winB B v = some (e, l) ∧ e ≤ t ∧ t ≤ l := by
  intro v t h
  rw [winB_eq B hwf]
  exact changes_in_window hwf r v t h

/-! ## Many relative-timing instances in one `decide` -/

/-- One relative-timing instance: in-arc buckets, request nodes, data node, and
the data part `P` (for exactness via 10a's `Separated`). -/
abbrev RTEntry := List (List Arc) × List Nat × Nat × List Nat

/-- Every request node of the entry switches no earlier than the data node (setup 0). -/
def rtOne (e : RTEntry) : Bool := e.2.1.all fun r => checkB e.1 r [e.2.2.1] 0

def wfOne (e : RTEntry) : Bool := decide (ofBuckets e.1).WF

/-- The side conditions of `check_exact_disjoint`, decidably. -/
def sepOne (e : RTEntry) : Bool :=
  decide (Separated (ofBuckets e.1) (fun v => e.2.2.2.contains v)) && e.2.2.2.contains e.2.2.1 &&
    e.2.1.all (fun r => !e.2.2.2.contains r && (winB e.1 r).isSome)

theorem rtOne_sound (e : RTEntry) (hwf : wfOne e = true) (h : rtOne e = true) {sig : Nat → Trace}
    (run : Run (ofBuckets e.1) sig) :
    ∀ r ∈ e.2.1, ∀ s t, changes (sig e.2.2.1) s → changes (sig r) t → s ≤ t := by
  intro r hr s t hs ht
  have hw : (ofBuckets e.1).WF := of_decide_eq_true hwf
  have hc : checkB e.1 r [e.2.2.1] 0 = true := List.all_eq_true.1 h r hr
  have := checkB_sound hw hc run e.2.2.1 List.mem_cons_self s t hs ht
  omega

theorem rtOne_exact (e : RTEntry) (hwf : wfOne e = true) (hs : sepOne e = true) (h : rtOne e = false) :
    ∃ r ∈ e.2.1, ∃ sig, Nonempty (FixedRun (ofBuckets e.1) sig) ∧
      ∃ s t, changes (sig e.2.2.1) s ∧ changes (sig r) t ∧ t < s := by
  have hw : (ofBuckets e.1).WF := of_decide_eq_true hwf
  simp only [sepOne, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at hs
  obtain ⟨⟨hsep, hd⟩, hreq⟩ := hs
  have hsep' := of_decide_eq_true hsep
  have : ∃ r ∈ e.2.1, checkB e.1 r [e.2.2.1] 0 = false := by
    apply Classical.byContradiction; intro hn
    apply Bool.false_ne_true; rw [← h, rtOne, List.all_eq_true]
    intro r hr
    cases hc : checkB e.1 r [e.2.2.1] 0
    · exact absurd ⟨r, hr, hc⟩ hn
    · rfl
  obtain ⟨r, hr, hc⟩ := this
  obtain ⟨h1, h2⟩ := hreq r hr
  rw [checkB_eq e.1 hw] at hc
  rw [winB_eq e.1 hw] at h2
  obtain ⟨d, hdm, sig, hrun, s, t, hs', ht', hlt⟩ :=
    check_exact_disjoint hw hsep' h1 (fun d hd' => by
      rw [List.mem_singleton] at hd'; rw [hd']; exact hd) h2 hc
  rw [List.mem_singleton] at hdm
  subst hdm
  exact ⟨r, hr, sig, hrun, s, t, hs', ht', by omega⟩

end Formal.Timing
