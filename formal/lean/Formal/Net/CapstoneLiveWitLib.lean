import Formal.Net.CapstoneWitnessLib
import Formal.Net.CapstoneLiveNd

/-!
# Probe C-8z2 (1): kernel checkers for the liveness hypotheses on an event-list run

`gcd_hw_live_final` (8z) has, besides 8t's H_CELLS / H_BUNDLE / H_START_ONCE, four hypotheses
about the run's timing and progress: H_BOUNDED_DELAY' `H` (every gate's `BndG H`, except
`start`'s LUT), H_ARB_UNCONTESTED_BOUNDED `H` (`ArbUnc`), H_START_ENV `H` (`StartEnv`) and
H_NO_DEADLOCK'. This file makes all four checkable by the kernel on a run given as 8t's event
lists (`CD`), with `H = 1`.

* **Gates as data.** `gatesE k` lists the gates of an operator kind as syntax (`GE`: an output
  signal and two Boolean excitation expressions, toward true and toward false, over the signal
  atoms `Sg`). `gates_eq` proves `gatesK p k ++ grantsK p k = (gatesE k).map (toG p)`: the
  syntax denotes exactly 8u's gate list, in the same order. So nothing about the gates is
  re-modelled here.
* **Step property.** `spChk` checks, for one gate, "excited toward `v` at `t` ⇒ output `v` at
  `t + 1`" at the change points of its inputs and output only (`pw_of`); `spChk_sound` lifts it
  to every `t`. With `H = 1` that is `BndG 1` (`bnd_of_step`) and, for the grants, `ArbUnc 1`.
* **No deadlock.** `ndOne` checks one certificate entry `(p, j, v)`: at tick `t`, gate `j` of
  operator `p` (not `start`'s producer) is excited toward `v` and does not show `v`. A list of
  entries for `t = 0, 1, ..., F` refutes `Quiet2` at every tick up to `F` (`nd_of`).
-/

namespace Formal.Net.CapNet.LiveWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Wit
open Formal.Cells.LinkHandshake (ctlB ctlB_eq)

/-! ## Gate syntax -/

/-- Signal atoms. `it k` is internal node `k` of the operator the gate belongs to. -/
inductive Sg
  | rq (c : Fin NC)
  | ak (c : Fin NC)
  | it (k : Nat)
  | s2 (c : Fin NC)
  | sD (c : Fin NC) (k : Nat)
  deriving Repr

/-- Boolean expressions over the atoms. -/
inductive BE
  | s (x : Sg)
  | n (e : BE)
  | a (e f : BE)
  | o (e f : BE)
  | allT (l : List Sg)
  | allF (l : List Sg)
  deriving Repr

/-- A gate: output atom, excitation toward true, excitation toward false. -/
structure GE where
  out : Sg
  eT : BE
  eF : BE
  deriving Repr

def evS (p : Fin NO) : Sg → GS → Bool
  | .rq c, s => s.rq c
  | .ak c, s => s.ak c
  | .it k, s => s.it p k
  | .s2 c, s => sel2 (s.dt c)
  | .sD c k, s => selD (s.dt c) == k

def evE (p : Fin NO) : BE → GS → Bool
  | .s x, s => evS p x s
  | .n e, s => !evE p e s
  | .a e f, s => evE p e s && evE p f s
  | .o e f, s => evE p e s || evE p f s
  | .allT l, s => l.all (fun x => evS p x s)
  | .allF l, s => l.all (fun x => !evS p x s)

def toG (p : Fin NO) (g : GE) : Gate :=
  ⟨evS p g.out, fun v s => evE p (bif v then g.eT else g.eF) s = true⟩

/-- A wire/LUT gate `out := e`. -/
def wireE (o : Sg) (e : BE) : GE := ⟨o, e, .n e⟩
/-- A C-element-like gate: all of `es` agree on `v`. -/
def cel2E (o : Sg) (e f : BE) : GE := ⟨o, .a e f, .a (.n e) (.n f)⟩

def gatesE : K NC → List GE
  | .forkG i os => os.map (fun c => wireE (.rq c) (.s (.rq i))) ++
      [⟨.ak i, .allT (os.map .ak), .allF (os.map .ak)⟩]
  | .forkH i os _ _ _ _ => (os.map Prod.fst).map (fun c => wireE (.rq c) (.s (.rq i))) ++
      [⟨.ak i, .allT ((os.map Prod.fst).map .ak), .allF ((os.map Prod.fst).map .ak)⟩]
  | .join ins o _ _ _ => ⟨.rq o, .allT (ins.map .rq), .allF (ins.map .rq)⟩ ::
      ins.map (fun c => wireE (.ak c) (.s (.ak o)))
  | .bjoin ins o _ _ => ⟨.rq o, .allT (ins.map .rq), .allF (ins.map .rq)⟩ ::
      ins.map (fun c => wireE (.ak c) (.s (.ak o)))
  | .steerC j t f => [wireE (.rq t) (.a (.s (.rq j)) (.s (.s2 j))),
      wireE (.rq f) (.a (.s (.rq j)) (.n (.s (.s2 j)))),
      wireE (.ak j) (.o (.s (.ak t)) (.s (.ak f)))]
  | .steerD j t f _ _ => [wireE (.rq t) (.a (.s (.rq j)) (.s (.s2 j))),
      wireE (.rq f) (.a (.s (.rq j)) (.n (.s (.s2 j)))),
      wireE (.ak j) (.o (.s (.ak t)) (.s (.ak f)))]
  | .mux c x y z _ =>
      [cel2E (.it 0) (.s (.rq x)) (.a (.s (.rq c)) (.n (.s (.s2 c)))),
       cel2E (.it 1) (.s (.rq y)) (.a (.s (.rq c)) (.s (.s2 c))),
       wireE (.rq z) (.o (.s (.it 0)) (.s (.it 1))),
       cel2E (.ak x) (.s (.it 0)) (.s (.ak z)),
       cel2E (.ak y) (.s (.it 1)) (.s (.ak z)),
       wireE (.ak c) (.s (.ak z))]
  | .muxn c x0 x1 x2 z _ =>
      (List.range 3).map (fun k => cel2E (.it k) (.s (.rq (cx3 x0 x1 x2 k))) (.a (.s (.rq c)) (.s (.sD c k)))) ++
      [wireE (.rq z) (.o (.o (.s (.it 0)) (.s (.it 1))) (.s (.it 2)))] ++
      (List.range 3).map (fun k => cel2E (.ak (cx3 x0 x1 x2 k)) (.s (.it k)) (.s (.ak z))) ++
      [wireE (.ak c) (.s (.ak z))]
  | .amerge x y z _ =>
      [⟨.rq z, .a (.o (.s (.it 0)) (.s (.it 1))) (.a (.n (.s (.ak x))) (.n (.s (.ak y)))),
          .n (.o (.s (.it 0)) (.s (.it 1)))⟩,
       cel2E (.ak x) (.s (.it 0)) (.s (.ak z)),
       cel2E (.ak y) (.s (.it 1)) (.s (.ak z))] ++
      [⟨.it 0, .a (.a (.s (.rq x)) (.n (.s (.it 1)))) (.n (.s (.ak z))), .n (.s (.rq x))⟩,
       ⟨.it 1, .a (.a (.s (.rq y)) (.n (.s (.it 0)))) (.n (.s (.ak z))), .n (.s (.rq y))⟩]
  | .link i o => [wireE (.it 0) (.o (.a (.s (.rq i)) (.n (.s (.ak o))))
        (.a (.s (.it 0)) (.o (.s (.rq i)) (.n (.s (.ak o)))))),
      wireE (.ak i) (.s (.it 0)), wireE (.rq o) (.s (.it 0))]
  | .src z _ _ => [wireE (.rq z) (.n (.s (.ak z)))]
  | .sink i => [wireE (.ak i) (.s (.rq i))]

/-! ## The syntax denotes 8u's gates -/

theorem toG_eq (p : Fin NO) (g : GE) (G : Gate) (ho : ∀ s, evS p g.out s = G.out s)
    (hT : ∀ s, evE p g.eT s = true ↔ G.exc true s) (hF : ∀ s, evE p g.eF s = true ↔ G.exc false s) :
    toG p g = G := by
  obtain ⟨o, e⟩ := G
  simp only [toG, Gate.mk.injEq]
  refine ⟨funext ho, ?_⟩
  funext v s
  cases v
  · exact propext (hF s)
  · exact propext (hT s)

theorem toG_wire (p : Fin NO) (o : Sg) (e : BE) (o' e' : GS → Bool) (ho : ∀ s, evS p o s = o' s)
    (he : ∀ s, evE p e s = e' s) : toG p (wireE o e) = gw o' e' := by
  apply toG_eq
  · exact ho
  · intro s; simp only [wireE, gw, he]
  · intro s; simp only [wireE, gw, evE, he]; cases e' s <;> simp

theorem toG_cel2 (p : Fin NO) (o : Sg) (e f : BE) (o' e' f' : GS → Bool) (ho : ∀ s, evS p o s = o' s)
    (he : ∀ s, evE p e s = e' s) (hf : ∀ s, evE p f s = f' s) :
    toG p (cel2E o e f) = ⟨o', fun v s => e' s = v ∧ f' s = v⟩ := by
  apply toG_eq
  · exact ho
  · intro s; simp only [cel2E, evE, he, hf]; cases e' s <;> cases f' s <;> simp
  · intro s; simp only [cel2E, evE, he, hf]; cases e' s <;> cases f' s <;> simp

theorem toG_all (p : Fin NO) (o : Sg) (l : List Sg) (o' : GS → Bool) (f : Fin NC → Sg) (f' : GS → Fin NC → Bool)
    (cs : List (Fin NC)) (hl : l = cs.map f) (ho : ∀ s, evS p o s = o' s) (hf : ∀ s c, evS p (f c) s = f' s c) :
    toG p ⟨o, .allT l, .allF l⟩ = ⟨o', fun v s => ∀ c ∈ cs, f' s c = v⟩ := by
  subst hl
  apply toG_eq
  · exact ho
  · intro s; simp [evE, hf]
  · intro s; simp [evE, hf]

theorem map_toG_wire (p : Fin NO) {α : Type} (cs : List α) (o : α → Sg) (e : α → BE)
    (o' : α → GS → Bool) (e' : α → GS → Bool) (ho : ∀ c s, evS p (o c) s = o' c s)
    (he : ∀ c s, evE p (e c) s = e' c s) :
    (cs.map (fun c => wireE (o c) (e c))).map (toG p) = cs.map (fun c => gw (o' c) (e' c)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro c _
  exact toG_wire p _ _ _ _ (ho c) (he c)

/-- **The gate syntax is 8u's gate list**, in order, arbiter grants included. -/
theorem gates_eq (p : Fin NO) (k : K NC) : gatesK p k ++ grantsK p k = (gatesE k).map (toG p) := by
  cases k with
  | forkG i os =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_append, List.map_cons, List.map_nil]
    rw [map_toG_wire p os (fun c => .rq c) (fun _ => .s (.rq i)) (fun c s => s.rq c) (fun _ s => s.rq i)
      (fun _ _ => rfl) (fun _ _ => rfl)]
    rw [toG_all p (.ak i) _ (fun s => s.ak i) Sg.ak (fun s c => s.ak c) os rfl (fun _ => rfl) (fun _ _ => rfl)]
  | forkH i os l h d hs =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_append, List.map_cons, List.map_nil]
    rw [map_toG_wire p (os.map Prod.fst) (fun c => .rq c) (fun _ => .s (.rq i)) (fun c s => s.rq c)
      (fun _ s => s.rq i) (fun _ _ => rfl) (fun _ _ => rfl)]
    rw [toG_all p (.ak i) _ (fun s => s.ak i) Sg.ak (fun s c => s.ak c) (os.map Prod.fst) rfl (fun _ => rfl)
      (fun _ _ => rfl)]
  | join ins o e js jw =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons]
    rw [map_toG_wire p ins (fun c => .ak c) (fun _ => .s (.ak o)) (fun c s => s.ak c) (fun _ s => s.ak o)
      (fun _ _ => rfl) (fun _ _ => rfl)]
    rw [toG_all p (.rq o) _ (fun s => s.rq o) Sg.rq (fun s c => s.rq c) ins rfl (fun _ => rfl) (fun _ _ => rfl)]
  | bjoin ins o ec ed =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons]
    rw [map_toG_wire p ins (fun c => .ak c) (fun _ => .s (.ak o)) (fun c s => s.ak c) (fun _ s => s.ak o)
      (fun _ _ => rfl) (fun _ _ => rfl)]
    rw [toG_all p (.rq o) _ (fun s => s.rq o) Sg.rq (fun s c => s.rq c) ins rfl (fun _ => rfl) (fun _ _ => rfl)]
  | steerC j t f =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons, List.map_nil]
    rw [toG_wire p _ _ (fun s => s.rq t) (fun s => s.rq j && (sel2 (s.dt j) == true)) (fun _ => rfl)
      (fun s => by simp [evE, evS]),
      toG_wire p _ _ (fun s => s.rq f) (fun s => s.rq j && (sel2 (s.dt j) == false)) (fun _ => rfl)
      (fun s => by simp [evE, evS]),
      toG_wire p _ _ (fun s => s.ak j) (fun s => s.ak t || s.ak f) (fun _ => rfl) (fun _ => rfl)]
  | steerD j t f fd sw =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons, List.map_nil]
    rw [toG_wire p _ _ (fun s => s.rq t) (fun s => s.rq j && (sel2 (s.dt j) == true)) (fun _ => rfl)
      (fun s => by simp [evE, evS]),
      toG_wire p _ _ (fun s => s.rq f) (fun s => s.rq j && (sel2 (s.dt j) == false)) (fun _ => rfl)
      (fun s => by simp [evE, evS]),
      toG_wire p _ _ (fun s => s.ak j) (fun s => s.ak t || s.ak f) (fun _ => rfl) (fun _ => rfl)]
  | mux c x y z mw =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons, List.map_nil]
    rw [toG_cel2 p _ _ _ (fun s => s.it p 0) (fun s => s.rq x) (fun s => s.rq c && !sel2 (s.dt c))
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
      toG_cel2 p _ _ _ (fun s => s.it p 1) (fun s => s.rq y) (fun s => s.rq c && sel2 (s.dt c))
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
      toG_wire p _ _ (fun s => s.rq z) (fun s => s.it p 0 || s.it p 1) (fun _ => rfl) (fun _ => rfl),
      toG_cel2 p _ _ _ (fun s => s.ak x) (fun s => s.it p 0) (fun s => s.ak z)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
      toG_cel2 p _ _ _ (fun s => s.ak y) (fun s => s.it p 1) (fun s => s.ak z)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
      toG_wire p _ _ (fun s => s.ak c) (fun s => s.ak z) (fun _ => rfl) (fun _ => rfl)]
  | muxn c x0 x1 x2 z nw =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_append, List.map_cons, List.map_nil]
    have e1 : ((List.range 3).map (fun k => cel2E (.it k) (.s (.rq (cx3 x0 x1 x2 k)))
        (.a (.s (.rq c)) (.s (.sD c k))))).map (toG p) =
        (List.range 3).map (fun k => (⟨fun s => s.it p k,
          fun v s => s.rq (cx3 x0 x1 x2 k) = v ∧ (s.rq c && (selD (s.dt c) == k)) = v⟩ : Gate)) := by
      rw [List.map_map]; apply List.map_congr_left; intro k _
      exact toG_cel2 p _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    have e2 : ((List.range 3).map (fun k => cel2E (.ak (cx3 x0 x1 x2 k)) (.s (.it k)) (.s (.ak z)))).map (toG p) =
        (List.range 3).map (fun k => (⟨fun s => s.ak (cx3 x0 x1 x2 k),
          fun v s => s.it p k = v ∧ s.ak z = v⟩ : Gate)) := by
      rw [List.map_map]; apply List.map_congr_left; intro k _
      exact toG_cel2 p _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    rw [e1, e2, toG_wire p _ _ (fun s => s.rq z) (fun s => s.it p 0 || s.it p 1 || s.it p 2) (fun _ => rfl)
        (fun _ => rfl),
      toG_wire p _ _ (fun s => s.ak c) (fun s => s.ak z) (fun _ => rfl) (fun _ => rfl)]
  | amerge x y z w =>
    simp only [gatesK, grantsK, gatesE, List.map_append, List.map_cons, List.map_nil]
    rw [toG_cel2 p _ _ _ (fun s => s.ak x) (fun s => s.it p 0) (fun s => s.ak z)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl),
      toG_cel2 p _ _ _ (fun s => s.ak y) (fun s => s.it p 1) (fun s => s.ak z)
        (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
    have h1 : toG p ⟨.rq z, .a (.o (.s (.it 0)) (.s (.it 1))) (.a (.n (.s (.ak x))) (.n (.s (.ak y)))),
        .n (.o (.s (.it 0)) (.s (.it 1)))⟩ = ⟨fun s => s.rq z, fun v s => (s.it p 0 || s.it p 1) = v ∧
          (v = true → s.ak x = false ∧ s.ak y = false)⟩ := by
      apply toG_eq
      · intro s; rfl
      · intro s; simp only [evE, evS]
        cases s.it p 0 <;> cases s.it p 1 <;> cases s.ak x <;> cases s.ak y <;> simp
      · intro s; simp only [evE, evS]
        cases s.it p 0 <;> cases s.it p 1 <;> simp
    have h2 : toG p ⟨.it 0, .a (.a (.s (.rq x)) (.n (.s (.it 1)))) (.n (.s (.ak z))), .n (.s (.rq x))⟩ =
        ⟨fun s => s.it p 0, fun v s => (v = true → (s.rq x && !s.it p 1 && !s.ak z) = true) ∧
          (v = false → s.rq x = false)⟩ := by
      apply toG_eq
      · intro s; rfl
      · intro s; simp only [evE, evS]; simp
      · intro s; simp only [evE, evS]; simp
    have h3 : toG p ⟨.it 1, .a (.a (.s (.rq y)) (.n (.s (.it 0)))) (.n (.s (.ak z))), .n (.s (.rq y))⟩ =
        ⟨fun s => s.it p 1, fun v s => (v = true → (s.rq y && !s.it p 0 && !s.ak z) = true) ∧
          (v = false → s.rq y = false)⟩ := by
      apply toG_eq
      · intro s; rfl
      · intro s; simp only [evE, evS]; simp
      · intro s; simp only [evE, evS]; simp
    rw [h1, h2, h3]
  | link i o =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons, List.map_nil]
    rw [toG_wire p _ _ (fun s => s.it p 0) (fun s => ctlB (s.rq i) (s.ak o) (s.it p 0) false) (fun _ => rfl)
        (fun s => by simp only [evE, evS, ctlB_eq]),
      toG_wire p _ _ (fun s => s.ak i) (fun s => s.it p 0) (fun _ => rfl) (fun _ => rfl),
      toG_wire p _ _ (fun s => s.rq o) (fun s => s.it p 0) (fun _ => rfl) (fun _ => rfl)]
  | src z which d =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons, List.map_nil]
    rw [toG_wire p _ _ (fun s => s.rq z) (fun s => !s.ak z) (fun _ => rfl) (fun _ => rfl)]
  | sink i =>
    simp only [gatesK, grantsK, gatesE, List.append_nil, List.map_cons, List.map_nil]
    rw [toG_wire p _ _ (fun s => s.ak i) (fun s => s.rq i) (fun _ => rfl) (fun _ => rfl)]

theorem mem_gatesE {p : Fin NO} {k : K NC} {g : Gate} (h : g ∈ gatesK p k ++ grantsK p k) :
    ∃ ge ∈ gatesE k, g = toG p ge := by
  rw [gates_eq] at h
  obtain ⟨ge, hge, rfl⟩ := List.mem_map.mp h
  exact ⟨ge, hge, rfl⟩

/-! ## The run and fast evaluation on event lists -/

section run
variable (cd : Fin NC → CD)

/-- The producer's output channel (where 8t's data keeps its internal traces). -/
def outK : K NC → Fin NC
  | .mux _ _ _ z _ => z
  | .muxn _ _ _ _ z _ => z
  | .amerge _ _ z _ => z
  | .link _ o => o
  | _ => 0

/-- The internal traces of the run. -/
def itrW : Itr := fun p k => bv ((cd (outK (opAt p))).aux k)

def evF (oc : Fin NC) : Sg → Nat → Bool
  | .rq c, t => bv (cd c).rq t
  | .ak c, t => bv (cd c).ak t
  | .it k, t => bv ((cd oc).aux k) t
  | .s2 c, t => sel2 (nv (cd c).d0 (cd c).dt t)
  | .sD c k, t => selD (nv (cd c).d0 (cd c).dt t) == k

def evEF (oc : Fin NC) : BE → Nat → Bool
  | .s x, t => evF cd oc x t
  | .n e, t => !evEF oc e t
  | .a e f, t => evEF oc e t && evEF oc f t
  | .o e f, t => evEF oc e t || evEF oc f t
  | .allT l, t => l.all (fun x => evF cd oc x t)
  | .allF l, t => l.all (fun x => !evF cd oc x t)

/-- Change points of an atom. -/
def cps (oc : Fin NC) : Sg → List Nat
  | .rq c => (cd c).rq
  | .ak c => (cd c).ak
  | .it k => (cd oc).aux k
  | .s2 c => (cd c).dts
  | .sD c _ => (cd c).dts

def cpsE (oc : Fin NC) : BE → List Nat
  | .s x => cps cd oc x
  | .n e => cpsE oc e
  | .a e f => cpsE oc e ++ cpsE oc f
  | .o e f => cpsE oc e ++ cpsE oc f
  | .allT l => l.flatMap (cps cd oc)
  | .allF l => l.flatMap (cps cd oc)

end run

variable {cd : Fin NC → CD}

theorem evS_gs (p : Fin NO) (x : Sg) (t : Nat) :
    evS p x (gsAt (wch cd) (itrW cd) t) = evF cd (outK (opAt p)) x t := by
  cases x <;> rfl

theorem evE_gs (p : Fin NO) : ∀ (e : BE) (t : Nat),
    evE p e (gsAt (wch cd) (itrW cd) t) = evEF cd (outK (opAt p)) e t
  | .s x, t => evS_gs p x t
  | .n e, t => by simp only [evE, evEF, evE_gs p e t]
  | .a e f, t => by simp only [evE, evEF, evE_gs p e t, evE_gs p f t]
  | .o e f, t => by simp only [evE, evEF, evE_gs p e t, evE_gs p f t]
  | .allT l, t => by simp only [evE, evEF, evS_gs]
  | .allF l, t => by simp only [evE, evEF, evS_gs]

theorem evF_st {oc : Fin NC} {x : Sg} {t : Nat} (h : t ∉ cps cd oc x) :
    evF cd oc x (t + 1) = evF cd oc x t := by
  cases x with
  | rq c => exact bv_st h
  | ak c => exact bv_st h
  | it k => exact bv_st h
  | s2 c => simp only [evF]; rw [nv_st h]
  | sD c k => simp only [evF]; rw [nv_st h]

theorem all_st {oc : Fin NC} {l : List Sg} {t : Nat} (h : t ∉ l.flatMap (cps cd oc)) (f : Bool → Bool) :
    l.all (fun x => f (evF cd oc x (t + 1))) = l.all (fun x => f (evF cd oc x t)) := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.flatMap_cons, List.mem_append, not_or] at h
    simp only [List.all_cons, evF_st h.1, ih h.2]

theorem evEF_st {oc : Fin NC} : ∀ {e : BE} {t : Nat}, t ∉ cpsE cd oc e →
    evEF cd oc e (t + 1) = evEF cd oc e t
  | .s x, t, h => evF_st h
  | .n e, t, h => by simp only [evEF, evEF_st (e := e) h]
  | .a e f, t, h => by
    obtain ⟨h1, h2⟩ := nm h; simp only [evEF, evEF_st h1, evEF_st h2]
  | .o e f, t, h => by
    obtain ⟨h1, h2⟩ := nm h; simp only [evEF, evEF_st h1, evEF_st h2]
  | .allT l, t, h => all_st h id
  | .allF l, t, h => all_st h (fun b => !b)

/-! ## The step property -/

/-- One gate at one tick: excited toward `v` ⇒ shows `v` one tick later. -/
def Qg (cd : Fin NC → CD) (oc : Fin NC) (g : GE) (t : Nat) : Bool :=
  (!evEF cd oc g.eT t || evF cd oc g.out (t + 1)) && (!evEF cd oc g.eF t || !evF cd oc g.out (t + 1))

def spChk (cd : Fin NC → CD) (oc : Fin NC) (g : GE) : Bool :=
  pwChk (cpsE cd oc g.eT ++ cpsE cd oc g.eF ++ (cps cd oc g.out).map (· - 1)) (Qg cd oc g)

theorem spChk_sound {oc : Fin NC} {g : GE} (h : spChk cd oc g = true) : ∀ t, Qg cd oc g t = true := by
  apply pw_of h
  intro t ht
  obtain ⟨h12, h3⟩ := nm ht
  obtain ⟨h1, h2⟩ := nm h12
  have h4 : t + 1 ∉ cps cd oc g.out := fun hm => h3 (List.mem_map.mpr ⟨t + 1, hm, rfl⟩)
  simp only [Qg, evEF_st h1, evEF_st h2, evF_st h4]

/-- Step property of a gate of the global-state semantics. -/
def Step (S : Nat → GS) (g : Gate) : Prop := ∀ v t, g.exc v (S t) → g.out (S (t + 1)) = v

theorem step_of {p : Fin NO} {ge : GE} (h : spChk cd (outK (opAt p)) ge = true) :
    Step (gsAt (wch cd) (itrW cd)) (toG p ge) := by
  intro v t he
  have hq := spChk_sound h t
  simp only [toG] at he ⊢
  rw [evE_gs] at he
  rw [evS_gs]
  simp only [Qg, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hq
  cases v
  · simp only [Bool.cond_false] at he
    rcases hq.2 with h' | h'
    · rw [he] at h'; cases h'
    · exact h'
  · simp only [Bool.cond_true] at he
    rcases hq.1 with h' | h'
    · rw [he] at h'; cases h'
    · exact h'

theorem bnd_of_step {S : Nat → GS} {g : Gate} (h : Step S g) : BndG 1 S g := by
  intro v t hw
  exact ⟨t + 1, by omega, by omega, h v t (hw t (Nat.le_refl _) (by omega))⟩

/-- Per-operator check: every gate of the operator has the step property. -/
def opStep (cd : Fin NC → CD) (p : Fin NO) : Bool :=
  (gatesE (opAt p)).all (spChk cd (outK (opAt p)))

theorem step_all {p : Fin NO} (h : opStep cd p = true) :
    ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p), Step (gsAt (wch cd) (itrW cd)) g := by
  intro g hg
  obtain ⟨ge, hge, rfl⟩ := mem_gatesE hg
  exact step_of (List.all_eq_true.mp h ge hge)

/-- Per-operator checks over the operator range `[lo, hi)`, `start`'s producer excepted. -/
def stepR (cd : Fin NC → CD) (lo hi : Nat) : Bool :=
  (List.range' lo (hi - lo)).all (fun i => if h : i < NO then (i == (prodOf start).val) || opStep cd ⟨i, h⟩
    else true)

theorem stepR_get {lo hi : Nat} (h : stepR cd lo hi = true) (p : Fin NO) (h1 : lo ≤ p.val) (h2 : p.val < hi)
    (hp : p ≠ prodOf start) : opStep cd p = true := by
  have hm : p.val ∈ List.range' lo (hi - lo) := List.mem_range'_1.mpr ⟨h1, by omega⟩
  have := List.all_eq_true.mp h p.val hm
  simp only [p.isLt, dite_true, Bool.or_eq_true, beq_iff_eq] at this
  rcases this with e | e
  · exact absurd (Fin.ext e) hp
  · exact e

/-- H_BOUNDED_DELAY' with `H = 1`, from the per-operator checks. -/
theorem bnd_all (h : ∀ p : Fin NO, p ≠ prodOf start → opStep cd p = true) :
    ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG 1 (gsAt (wch cd) (itrW cd)) g :=
  fun p hp g hg => bnd_of_step (step_all (h p hp) g (List.mem_append_left _ hg))

/-- H_ARB_UNCONTESTED_BOUNDED with `H = 1` (even the full law), from the grants' checks. -/
theorem arb_all (h : ∀ p : Fin NO, p ≠ prodOf start → opStep cd p = true)
    (hs : ∀ x u z w, opAt (prodOf start) ≠ .amerge x u z w) :
    ∀ p x u z w, opAt p = .amerge x u z w →
      ArbUnc 1 (wch cd x) (wch cd u) (wch cd z) (itrW cd p 0) (itrW cd p 1) := by
  intro p x u z w hp
  have hne : p ≠ prodOf start := fun e => hs x u z w (e ▸ hp)
  have hst := step_all (h p hne)
  rw [hp] at hst
  have g1 := hst _ (List.mem_append_right _ (List.mem_cons_self ..))
  have g2 := hst _ (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t hw
    have := hw t (Nat.le_refl _) (by omega)
    refine ⟨t + 1, by omega, by omega, g1 true t ⟨fun _ => ?_, fun h => by cases h⟩⟩
    exact this.1
  · intro t hw
    have := hw t (Nat.le_refl _) (by omega)
    refine ⟨t + 1, by omega, by omega, g2 true t ⟨fun _ => ?_, fun h => by cases h⟩⟩
    exact this.1
  · intro t hw
    have := hw t (Nat.le_refl _) (by omega)
    exact ⟨t + 1, by omega, by omega, g1 false t ⟨fun h => (by cases h), fun _ => this⟩⟩
  · intro t hw
    have := hw t (Nat.le_refl _) (by omega)
    exact ⟨t + 1, by omega, by omega, g2 false t ⟨fun h => (by cases h), fun _ => this⟩⟩

/-! ## No deadlock before a given tick -/

/-- One certificate entry at tick `t`: operator `p`'s gate `j` is excited toward `v` and does
not show `v`; `p` is not `start`'s producer. -/
def ndOne (cd : Fin NC → CD) (t : Nat) (e : Nat × Nat × Bool) : Bool :=
  if h : e.1 < NO then
    let p : Fin NO := ⟨e.1, h⟩
    let k := opAt p
    let g := (gatesE k).getD e.2.1 ⟨.it 0, .s (.it 0), .s (.it 0)⟩
    (e.1 != (prodOf start).val) && decide (e.2.1 < (gatesE k).length) &&
      evEF cd (outK k) (bif e.2.2 then g.eT else g.eF) t && (evF cd (outK k) g.out t != e.2.2)
  else false

def ndChk (cd : Fin NC → CD) : Nat → List (Nat × Nat × Bool) → Bool
  | _, [] => true
  | t, e :: es => ndOne cd t e && ndChk cd (t + 1) es

theorem ndChk_get : ∀ (es : List (Nat × Nat × Bool)) (t0 : Nat), ndChk cd t0 es = true →
    ∀ i (h : i < es.length), ndOne cd (t0 + i) es[i] = true
  | [], _, _, i, h => absurd h (by simp)
  | e :: es, t0, hc, i, h => by
    simp only [ndChk, Bool.and_eq_true] at hc
    cases i with
    | zero => simpa using hc.1
    | succ i =>
      have := ndChk_get es (t0 + 1) hc.2 i (by simpa using h)
      rw [show t0 + (i + 1) = t0 + 1 + i by omega]; simpa using this

theorem not_quiet_of {t : Nat} {e : Nat × Nat × Bool} (h : ndOne cd t e = true) :
    ¬ Live.Nd.Quiet2 (gsAt (wch cd) (itrW cd) t) := by
  intro hq
  unfold ndOne at h
  split at h
  · rename_i hp
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hst, hj⟩, hex⟩, hout⟩ := h
    have hmem : (gatesE (opAt ⟨e.1, hp⟩)).getD e.2.1 ⟨.it 0, .s (.it 0), .s (.it 0)⟩ ∈
        gatesE (opAt ⟨e.1, hp⟩) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem hj
    have hg : toG ⟨e.1, hp⟩ ((gatesE (opAt ⟨e.1, hp⟩)).getD e.2.1 ⟨.it 0, .s (.it 0), .s (.it 0)⟩) ∈
        gatesK ⟨e.1, hp⟩ (opAt ⟨e.1, hp⟩) ++ grantsK ⟨e.1, hp⟩ (opAt ⟨e.1, hp⟩) := by
      rw [gates_eq]; exact List.mem_map.mpr ⟨_, hmem, rfl⟩
    have hne : (⟨e.1, hp⟩ : Fin NO) ≠ prodOf start := fun h' => hst (by rw [← h'])
    have := hq ⟨e.1, hp⟩ hne _ hg e.2.2 (by simp only [toG]; rw [evE_gs]; exact hex)
    simp only [toG] at this
    rw [evS_gs] at this
    exact hout this
  · cases h

/-- **H_NO_DEADLOCK' from a certificate.** If the certificate covers ticks `0 .. F` and the
out0 acknowledge falls at `F`, no tick before the first out0 close is quiescent. -/
theorem nd_of (cert : List (Nat × Nat × Bool)) (hc : ndChk cd 0 cert = true) (F : Nat)
    (hF : fallB (wch cd out0).ack F = true) (hlen : cert.length = F + 1) :
    ∀ t, cnt (fallB (wch cd out0).ack) t = 0 →
      ¬ (Live.Nd.Quiet2 (gsAt (wch cd) (itrW cd) t) ∧
        (cnt (riseB (wch cd start).req) t = 0 → (wch cd start).ack t = false →
          (wch cd start).req t = true)) := by
  intro t ht hq
  have htF : t ≤ F := by
    apply Classical.byContradiction
    intro hn
    have h1 := cnt_mono (fallB (wch cd out0).ack) (show F + 1 ≤ t by omega)
    have h2 : cnt (fallB (wch cd out0).ack) (F + 1) ≥ 1 := by simp [cnt, hF]
    omega
  have := ndChk_get cert 0 hc t (by omega)
  rw [Nat.zero_add] at this
  exact not_quiet_of this hq.1

/-! ## Start: one offer at tick 0, and H_START_ENV -/

theorem start_env {L : List Nat} (hL : (cd start).rq = 0 :: L) (hf : ∀ e ∈ L, 1 ≤ e) :
    Live.Nd.StartEnv 1 (wch cd start) := by
  have hr1 : (wch cd start).req 1 = true := by
    show bv (cd start).rq 1 = true
    rw [hL]
    have : cntLt L 1 = 0 := by
      clear hL
      induction L with
      | nil => rfl
      | cons e L ih =>
        simp only [cntLt]
        have := hf e (List.mem_cons_self ..)
        rw [ih (fun e' h' => hf e' (List.mem_cons_of_mem _ h'))]
        simp; omega
    simp [bv, cntLt, this]
  have hr0 : (wch cd start).req 0 = false := bv_zero _
  intro t hw
  cases t with
  | zero => exact ⟨1, by omega, by omega, hr1⟩
  | succ t =>
    have h := (hw (t + 1) (Nat.le_refl _) (by omega)).1
    have h1 := cnt_mono (riseB (wch cd start).req) (show 1 ≤ t + 1 by omega)
    have h2 : cnt (riseB (wch cd start).req) 1 = 1 := by simp [cnt, riseB, hr0, hr1]
    omega

/-! ## One-toggle requests, and an out0 that never closes -/

/-- A request whose toggle list is `[r]` rises at most once. -/
theorem once_of1 {L : List Nat} {r : Nat} (hL : L = [r]) :
    ∀ t, Handshake.cnt (riseB (bv L)) t ≤ 1 := by
  apply cnt_le_one (t1 := r)
  intro e he
  have hmv : bv L (e + 1) ≠ bv L e := by
    simp only [riseB, Bool.and_eq_true, Bool.not_eq_true'] at he; rw [he.1, he.2]; decide
  have hm := mem_of_ne hmv
  subst hL
  simpa using hm

theorem bv_one {e u : Nat} (h : e < u) : bv [e] u = true := by
  simp [bv, cntLt, h]

theorem never_close (h : (cd out0).ak = []) : ∀ t, cnt (fallB (wch cd out0).ack) t = 0 := by
  have hb : ∀ u, (wch cd out0).ack u = false := fun u => by
    show bv (cd out0).ak u = false
    rw [h]; rfl
  intro t
  induction t with
  | zero => rfl
  | succ t ih => simp [cnt, fallB, hb, ih]

theorem bv_two {r f u : Nat} (h : r < f) : bv [r, f] u = (decide (r < u) && !decide (f < u)) := by
  unfold bv cntLt cntLt cntLt
  by_cases h1 : r < u <;> by_cases h2 : f < u <;> simp [h1, h2] <;> omega

/-- The release half of `start`'s LUT, for a request toggled at `r` and `f` and an
acknowledge toggled at `a` and `g`, with the request released right after the acknowledge. -/
theorem start_rel {r f a g : Nat} (hr : (cd start).rq = [r, f]) (ha : (cd start).ak = [a, g])
    (hrf : r < f) (hag : a < g) (hfa : f ≤ a + 1) :
    ∀ t, Win 1 t (fun u => (wch cd start).req u = true ∧ (wch cd start).ack u = true) →
      Ev 1 t (fun u => (wch cd start).req u = false) := by
  intro t hw
  have h1 := hw t (Nat.le_refl _) (by omega)
  have h2 := hw (t + 1) (by omega) (Nat.le_refl _)
  simp only [wch, CD.ch, hr, ha, bv_two hrf, bv_two hag, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq, decide_eq_false_iff_not] at h1 h2
  omega

/-! ## H_CELLS with the internal traces explicit -/

theorem cellI_of (sv : Nat → Nat) (p : Fin NO) (h : kChk cd sv (opAt p) = true) :
    CellI (wch cd) sv (itrW cd) p (opAt p) := by
  have hI : ∀ k, itrW cd p k = bv ((cd (outK (opAt p))).aux k) := fun _ => rfl
  generalize hk : opAt p = k at h hI ⊢
  cases k with
  | mux c x y z mw =>
    show Mux.Mux sel2 _ _ _ _ (itrW cd p 0) (itrW cd p 1)
    rw [hI 0, hI 1]; exact mux_sound h
  | muxn c x0 x1 x2 z nw =>
    show MuxN.MuxN selD _ _ _ (itrW cd p)
    have : itrW cd p = fun k => bv ((cd z).aux k) := funext hI
    rw [this]; exact muxn_sound h
  | amerge x y z w =>
    show CM.AMerge _ _ _ (itrW cd p 0) (itrW cd p 1)
    rw [hI 0, hI 1]; exact am_sound h
  | link i o =>
    show Link.Link _ _ (itrW cd p 0)
    rw [hI 0]; exact link_sound h
  | forkG i os => exact kChk_sound sv _ h
  | forkH i os l hh d hs => exact kChk_sound sv _ h
  | join ins o e js jw => exact kChk_sound sv _ h
  | bjoin ins o ec ed => exact kChk_sound sv _ h
  | steerC j t f => exact kChk_sound sv _ h
  | steerD j t f fd sw => exact kChk_sound sv _ h
  | src z which d => exact kChk_sound sv _ h
  | sink i => exact kChk_sound sv _ h

end Formal.Net.CapNet.LiveWit
