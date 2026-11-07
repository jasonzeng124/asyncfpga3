import Formal.Net.CapstoneLiveRank
import Formal.Net.CapstoneLiveArb

/-!
# Probe C-8u (4): gcd_hw circuit liveness, reduced to two named network obligations

This file states circuit-level liveness for the concrete 465-channel gcd_hw network of 8m and
proves it from the ranking theorem (`CapstoneLiveRank.rank_live`), the arbiter result
(`CapstoneLiveArb.gcd_hw_arb_settle`) and 8r's safety theorem. **It is a reduction, not a full
liveness proof**: two network-wide obligations stay hypotheses (H_NO_DEADLOCK and
H_FIRING_BOUND), see "What is open" below.

## The run and the bounded-delay hypothesis

A circuit run is `ch` (request, acknowledge and bus traces of every channel) together with
`itr`, the internal gate traces of every operator (`itr p k`: the mux joins `j0, j1`, the
3-way mux joins `j 0..2`, the arbiter grants `g1, g2`, the link controller node `c`). `CellI`
is 8m's `Cell` with these internal traces made explicit (`cellI_cell`).

The global state at `t` is `gsAt ch itr t` (every req, ack, bus and internal bit). Every gate
of every operator is listed (`gatesK`, `grantsK`) as an output plus an excitation toward each
value, both read from the global state. The excitations are the guards of the 8f/8j/8l SI
models (the C-element "all inputs agree", the steer LUT, the link LUT `ctlB`, ...).

* **H_BOUNDED_DELAY `H`** (`BndG`, every non-arbitrating gate): if a gate is excited toward
  `v` on a whole window `[t, t + H]`, its output shows `v` somewhere in the window. This is
  the upper (settle) half of the inertial channel of C-8d/8n with `hi ≤ H`, for every LUT,
  C-element, delay line and route that the SI models lump into one gate.
* **H_ARB_UNCONTESTED_BOUNDED `H`** (`ArbUnc`, the 9 arbiter stages): the same for the grants,
  but only when the other request is low. No bound is assumed for a contested arbiter.

## The theorem

`gcd_hw_live`: under H_CELLS, H_BUNDLE, H_START_ONCE, H_WALK (8r), H_BOUNDED_DELAY `H`,
H_ARB_UNCONTESTED_BOUNDED `H`, H_NO_DEADLOCK and H_FIRING_BOUND `N`, the circuit closes its
first `out0` token at some step `e < (N + 1) * (H + 1)`, and the value latched is
`Nat.gcd a b`.

The arbiters enter through `gcd_hw_arb_settle`: since no stage is ever contested (8q/8r),
H_ARB_UNCONTESTED_BOUNDED gives the full bounded law, so a frozen state is fully quiescent
(`frozen_quiet`), arbiters included. Without that step a frozen state could hide a contested
arbiter that is excited but may wait forever (`CapstoneLiveArb.stall_*`).

## What is open (not proved here; each is a hypothesis of `gcd_hw_live`)

* **H_NO_DEADLOCK**: before the first `out0` close, some gate is excited (`¬ Quiet`). This is
  the global progress fact (the circuit simulates the live token run: T1 + T5 + capacity).
* **H_FIRING_BOUND `N`**: before the first `out0` close, at most `N` ticks change the state.
  `CapstoneLiveSpine.gcd_hw_spine_offers_bounded` bounds the 67 spine channels by the walk
  length `L`; the data channels, the free-running `a`/`b`/literal sources and the internal
  nodes are not bounded in Lean.
* Consistency of H_BOUNDED_DELAY with H_CELLS on gcd_hw (a run meeting both, beyond the
  all-gates toy of `CapstoneLiveRank.timed_rank_unit`) is not exhibited.
-/

namespace Formal.Net.CapNet.Live
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe (Good)
open Formal.Cells.LinkHandshake (ctlB)

/-- Internal gate traces of every operator. -/
abbrev Itr := Fin NO → Nat → Trace

/-- The global circuit state at one tick. -/
structure GS where
  rq : Fin NC → Bool
  ak : Fin NC → Bool
  dt : Fin NC → Nat
  it : Fin NO → Nat → Bool

def gsAt (ch : Fin NC → Chan) (itr : Itr) (t : Nat) : GS :=
  ⟨fun c => (ch c).req t, fun c => (ch c).ack t, fun c => (ch c).dat t, fun p k => itr p k t⟩

/-- A gate: its output, and its excitation toward each value, read from the global state. -/
structure Gate where
  out : GS → Bool
  exc : Bool → GS → Prop

/-- A wire/buffer gate: `o` follows `e`. -/
def gw (o e : GS → Bool) : Gate := ⟨o, fun v s => e s = v⟩

/-- The non-arbitrating gates of operator `p`. -/
def gatesK (p : Fin NO) : K NC → List Gate
  | .forkG i os => os.map (fun c => gw (fun s => s.rq c) (fun s => s.rq i)) ++
      [⟨fun s => s.ak i, fun v s => ∀ c ∈ os, s.ak c = v⟩]
  | .forkH i os _ _ _ _ => (os.map Prod.fst).map (fun c => gw (fun s => s.rq c) (fun s => s.rq i)) ++
      [⟨fun s => s.ak i, fun v s => ∀ c ∈ os.map Prod.fst, s.ak c = v⟩]
  | .join ins o _ _ _ => ⟨fun s => s.rq o, fun v s => ∀ c ∈ ins, s.rq c = v⟩ ::
      ins.map (fun c => gw (fun s => s.ak c) (fun s => s.ak o))
  | .bjoin ins o _ _ => ⟨fun s => s.rq o, fun v s => ∀ c ∈ ins, s.rq c = v⟩ ::
      ins.map (fun c => gw (fun s => s.ak c) (fun s => s.ak o))
  | .steerC j t f => [gw (fun s => s.rq t) (fun s => s.rq j && (sel2 (s.dt j) == true)),
      gw (fun s => s.rq f) (fun s => s.rq j && (sel2 (s.dt j) == false)),
      gw (fun s => s.ak j) (fun s => s.ak t || s.ak f)]
  | .steerD j t f _ _ => [gw (fun s => s.rq t) (fun s => s.rq j && (sel2 (s.dt j) == true)),
      gw (fun s => s.rq f) (fun s => s.rq j && (sel2 (s.dt j) == false)),
      gw (fun s => s.ak j) (fun s => s.ak t || s.ak f)]
  | .mux c x y z _ =>
      [⟨fun s => s.it p 0, fun v s => s.rq x = v ∧ (s.rq c && !sel2 (s.dt c)) = v⟩,
       ⟨fun s => s.it p 1, fun v s => s.rq y = v ∧ (s.rq c && sel2 (s.dt c)) = v⟩,
       gw (fun s => s.rq z) (fun s => s.it p 0 || s.it p 1),
       ⟨fun s => s.ak x, fun v s => s.it p 0 = v ∧ s.ak z = v⟩,
       ⟨fun s => s.ak y, fun v s => s.it p 1 = v ∧ s.ak z = v⟩,
       gw (fun s => s.ak c) (fun s => s.ak z)]
  | .muxn c x0 x1 x2 z _ =>
      (List.range 3).map (fun k => (⟨fun s => s.it p k,
        fun v s => s.rq (cx3 x0 x1 x2 k) = v ∧ (s.rq c && (selD (s.dt c) == k)) = v⟩ : Gate)) ++
      [gw (fun s => s.rq z) (fun s => s.it p 0 || s.it p 1 || s.it p 2)] ++
      (List.range 3).map (fun k => (⟨fun s => s.ak (cx3 x0 x1 x2 k),
        fun v s => s.it p k = v ∧ s.ak z = v⟩ : Gate)) ++
      [gw (fun s => s.ak c) (fun s => s.ak z)]
  | .amerge x y z _ =>
      [⟨fun s => s.rq z, fun v s => (s.it p 0 || s.it p 1) = v ∧
          (v = true → s.ak x = false ∧ s.ak y = false)⟩,
       ⟨fun s => s.ak x, fun v s => s.it p 0 = v ∧ s.ak z = v⟩,
       ⟨fun s => s.ak y, fun v s => s.it p 1 = v ∧ s.ak z = v⟩]
  | .link i o => [gw (fun s => s.it p 0) (fun s => ctlB (s.rq i) (s.ak o) (s.it p 0) false),
      gw (fun s => s.ak i) (fun s => s.it p 0), gw (fun s => s.rq o) (fun s => s.it p 0)]
  | .src z _ _ => [gw (fun s => s.rq z) (fun s => !s.ak z)]
  | .sink i => [gw (fun s => s.ak i) (fun s => s.rq i)]

/-- The arbiter grants of operator `p` (rise guard: own request, other grant low, `A0` low;
fall guard: own request low). -/
def grantsK (p : Fin NO) : K NC → List Gate
  | .amerge x y z _ =>
      [⟨fun s => s.it p 0, fun v s => (v = true → (s.rq x && !s.it p 1 && !s.ak z) = true) ∧
          (v = false → s.rq x = false)⟩,
       ⟨fun s => s.it p 1, fun v s => (v = true → (s.rq y && !s.it p 0 && !s.ak z) = true) ∧
          (v = false → s.rq y = false)⟩]
  | _ => []

/-- H_BOUNDED_DELAY `H` for one gate. -/
def BndG (H : Nat) (S : Nat → GS) (g : Gate) : Prop :=
  ∀ v t, Win H t (fun u => g.exc v (S u)) → Ev H t (fun u => g.out (S u) = v)

/-- Quiescent: no gate (arbiter grants included) is excited. -/
def Quiet (s : GS) : Prop :=
  ∀ p : Fin NO, ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p), ∀ v, g.exc v s → g.out s = v

/-- 8m's gate models with the internal traces explicit. -/
def CellI (ch : Fin NC → Chan) (sv : Nat → Nat) (itr : Itr) (p : Fin NO) : K NC → Prop
  | .mux c x y z _ => Mux.Mux sel2 (ch x) (ch y) (ch c) (ch z) (itr p 0) (itr p 1)
  | .muxn c x0 x1 x2 z _ => MuxN.MuxN selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) (itr p)
  | .amerge x y z _ => CM.AMerge (ch x) (ch y) (ch z) (itr p 0) (itr p 1)
  | .link i o => Link.Link (ch i) (ch o) (itr p 0)
  | .forkG i os => Cell ch sv (.forkG i os)
  | .forkH i os l h d hs => Cell ch sv (.forkH i os l h d hs)
  | .join ins o e js jw => Cell ch sv (.join ins o e js jw)
  | .bjoin ins o ec ed => Cell ch sv (.bjoin ins o ec ed)
  | .steerC j t f => Cell ch sv (.steerC j t f)
  | .steerD j t f fd sw => Cell ch sv (.steerD j t f fd sw)
  | .src z which d => Cell ch sv (.src z which d)
  | .sink i => Cell ch sv (.sink i)

theorem cellI_cell {ch : Fin NC → Chan} {sv : Nat → Nat} {itr : Itr} {p : Fin NO} :
    ∀ k : K NC, CellI ch sv itr p k → Cell ch sv k
  | .mux _ _ _ _ _, h => ⟨_, _, h⟩
  | .muxn _ _ _ _ _ _, h => ⟨_, h⟩
  | .amerge _ _ _ _, h => ⟨_, _, h⟩
  | .link _ _, h => ⟨_, h⟩
  | .forkG _ _, h => h
  | .forkH _ _ _ _ _ _, h => h
  | .join _ _ _ _ _, h => h
  | .bjoin _ _ _ _, h => h
  | .steerC _ _ _, h => h
  | .steerD _ _ _ _ _, h => h
  | .src _ _ _, h => h
  | .sink _, h => h

/-- The arbiter grants obey `BndG` under the full bounded law. -/
theorem grants_bnd {ch : Fin NC → Chan} {itr : Itr} {H : Nat} {p : Fin NO} {x y z : Fin NC} {w : Nat}
    (hS : ArbSettle H (ch x) (ch y) (ch z) (itr p 0) (itr p 1)) :
    ∀ g ∈ grantsK p (.amerge x y z w), BndG H (gsAt ch itr) g := by
  intro g hg v t hw
  simp only [grantsK, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · cases v
    · exact hS.fall1 t (fun u h1 h2 => (hw u h1 h2).2 rfl)
    · exact hS.rise1 t (fun u h1 h2 => (hw u h1 h2).1 rfl)
  · cases v
    · exact hS.fall2 t (fun u h1 h2 => (hw u h1 h2).2 rfl)
    · exact hS.rise2 t (fun u h1 h2 => (hw u h1 h2).1 rfl)

/-- A gate obeying `BndG` is not excited in a state frozen for `H + 1` ticks. -/
theorem bnd_frozen {H : Nat} {S : Nat → GS} {g : Gate} (hb : BndG H S g) {t : Nat}
    (hfz : ∀ u, t ≤ u → u ≤ t + H → S u = S t) : ∀ v, g.exc v (S t) → g.out (S t) = v := by
  intro v he
  obtain ⟨u, h1, h2, ho⟩ := hb v t (fun u h1 h2 => by show g.exc v (S u); rw [hfz u h1 h2]; exact he)
  rw [hfz u h1 h2] at ho; exact ho

/-- **H_FROZEN_QUIET for gcd_hw.** Under H_BOUNDED_DELAY and the full arbiter law at every
stage, a state frozen for `H + 1` ticks is quiescent. -/
theorem frozen_quiet {ch : Fin NC → Chan} {itr : Itr} {H : Nat}
    (hB : ∀ p, ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (hA : ∀ p x u z w, opAt p = .amerge x u z w → ArbSettle H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    {t : Nat} (hfz : ∀ u, t ≤ u → u ≤ t + H → gsAt ch itr u = gsAt ch itr t) :
    Quiet (gsAt ch itr t) := by
  intro p g hg
  rcases List.mem_append.mp hg with hg | hg
  · exact bnd_frozen (hB p g hg) hfz
  · cases hk : opAt p with
    | amerge x u z w =>
      rw [hk] at hg
      exact bnd_frozen (grants_bnd (hA p x u z w hk) g hg) hfz
    | _ => rw [hk] at hg; simp [grantsK] at hg

/-- The first event of a counted trace. -/
theorem first_ev (f : Nat → Bool) : ∀ t, 1 ≤ cnt f t → ∃ e, e < t ∧ f e = true ∧ cnt f e = 0 := by
  intro t
  induction t with
  | zero => intro h; simp [cnt] at h
  | succ t ih =>
    intro h
    by_cases h0 : 1 ≤ cnt f t
    · obtain ⟨e, a, b, c⟩ := ih h0
      exact ⟨e, by omega, b, c⟩
    · cases hf : f t
      · simp [cnt, hf] at h; omega
      · exact ⟨t, by omega, hf, by omega⟩

/-- Change marker of the global state. -/
noncomputable def chG (ch : Fin NC → Chan) (itr : Itr) (u : Nat) : Bool :=
  @decide (gsAt ch itr (u + 1) ≠ gsAt ch itr u) (Classical.propDecidable _)

theorem chG_false {ch : Fin NC → Chan} {itr : Itr} {u : Nat} (h : chG ch itr u = false) :
    gsAt ch itr (u + 1) = gsAt ch itr u := by
  unfold chG at h
  apply Classical.byContradiction
  intro hne
  have := @decide_eq_true _ (Classical.propDecidable _) hne
  rw [this] at h; cases h

/-- **gcd_hw circuit liveness, reduced.** Under the safety hypotheses of 8r, bounded gate
delays `H` (arbiters: only when uncontested), H_NO_DEADLOCK and H_FIRING_BOUND `N`, the
circuit closes its first `out0` token within `(N + 1) * (H + 1)` ticks, carrying
`Nat.gcd a b`. -/
theorem gcd_hw_live (a b H N : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (y : CapSafe.TS) (hy : Good a b y) (H_WALK : WalkOK (σY a b y) (omOf a b y))
    (H_BOUNDED_DELAY : ∀ p, ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (H_ARB_UNCONTESTED_BOUNDED : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbUnc H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    (H_NO_DEADLOCK : ∀ t, cnt (fallB (ch out0).ack) t = 0 → ¬ Quiet (gsAt ch itr t))
    (H_FIRING_BOUND : ∀ T, cnt (fallB (ch out0).ack) T = 0 → cnt (chG ch itr) T ≤ N) :
    ∃ e, e < (N + 1) * (H + 1) ∧ TokAt (ch out0) 0 e ∧ (ch out0).dat e = Nat.gcd a b := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hA : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbSettle H (ch x) (ch u) (ch z) (itr p 0) (itr p 1) := by
    intro p x u z w hp
    have M := H_CELLS p
    rw [hp] at M
    exact gcd_hw_arb_settle a b H ch hC H_BUNDLE H_START_ONCE y hy H_WALK p x u z w hp _ _ M
      (H_ARB_UNCONTESTED_BOUNDED p x u z w hp)
  obtain ⟨t, ht, hP⟩ := rank_live (gsAt ch itr) Quiet (fun t => cnt (fallB (ch out0).ack) t ≠ 0)
    (chG ch itr) H N (fun _ h => chG_false h)
    (fun _ hfz => frozen_quiet H_BOUNDED_DELAY hA hfz)
    (fun t hp => H_NO_DEADLOCK t (by omega))
    (fun T hT => H_FIRING_BOUND T (by have := hT T (Nat.le_refl _); omega))
  obtain ⟨e, he, hf, hc0⟩ := first_ev (fallB (ch out0).ack) t (by omega)
  have hsafe := (gcd_hw_circuit_safe'' a b ch hC H_BUNDLE H_START_ONCE ⟨y, hy, H_WALK⟩).1
  exact ⟨e, by omega, ⟨hf, hc0⟩, hsafe 0 e ⟨hf, hc0⟩⟩

end Formal.Net.CapNet.Live
