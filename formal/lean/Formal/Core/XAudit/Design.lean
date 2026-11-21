import Formal.Core.XSim

/-!
# Formal.Core.XAudit.Design — a flattened netlist as an `XSim` network, and the timed verdicts

Probe A-xaudit (Phase 2 item A). See `formal/notes/A-xaudit.md`.

The executable `xaudit` (`Formal/Core/XAudit/Main.lean`) parses a yosys
`write_json` netlist (trusted code) into a `Design`: a number of wires and a
list of `GSpec` gates, each an INIT number, a pin list, an output wire and a
delay band `[lo, hi]` in time steps. Every LUT output is one gate; every
connection from a net to a LUT pin is a separate routed wire with its own
buffer gate (`Lut 1`, INIT `0b10`) and its own band (per-arc delays).

This file, which the executable calls, is proved:

* `toLGate_rel`, `sat_build_iff`: the `XSim` circuit built from a `Design` is
  exactly "each output wire is the transport-delayed (band `[lo,hi]`) value of
  INIT bit number `addr(pin values)`", gate by gate. This is the lemma that
  connects the parsed netlist to the `Circuit` that `XSim.sound_circuit` is
  about. What it does not cover is the parse (JSON → `Design`), which is
  trusted code.
* `audit_sound`, `audit_binary`: the rows that the executable computes
  (`audit d u T`, i.e. `XSim.hist` itself) cover every behaviour.
* `noX_sound` (the meaning of "no X reported at node `w`"): if the column of
  `w` has no `X` on `[t1, t2]`, then in EVERY behaviour (every delay of every
  gate and route inside its band, as monotone warps; any power-up state) the
  waveform of `w` on `[t1, t2]` is the same, namely the printed one. So `w`
  cannot glitch there, under any delays in the band.
* `settled_forever`: if the inputs are constant from `T` on and the last
  `H ≥ max hi` rows are equal, the binary values of row `T` hold for all
  later time.
-/

namespace Formal.Core.XAudit

open Formal.Core K3
open Formal.Core.XSim
open Formal.Core.TraceDiscrete (Sig)

/-- One gate of the flattened design, as parsed (raw indices). -/
structure GSpec where
  /-- `cell/pin` or `cell/O6` etc., for the report. -/
  name : String
  k : Nat
  /-- INIT as a number: bit `a` is the output at address `a` (`I0` = LSB). -/
  init : Nat
  /-- wire index of pin `I0 .. I(k-1)`. -/
  ins : List Nat
  out : Nat
  lo : Nat
  hi : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A design: wires `0 .. m` (so `m + 1` wires) and gates. -/
structure Design where
  m : Nat
  gates : List GSpec
  deriving Repr

/-- Number of wires. -/
abbrev Design.n (d : Design) : Nat := d.m + 1

/-- Wire with index `i` (taken modulo `n`; `WF` makes it exact). -/
def Design.wire (d : Design) (i : Nat) : Fin d.n := ⟨i % d.n, Nat.mod_lt _ (Nat.succ_pos _)⟩

theorem Design.wire_val (d : Design) {i : Nat} (h : i < d.n) : (d.wire i).val = i :=
  Nat.mod_eq_of_lt h

/-- The LUT of a gate: INIT reduced to `2^k` bits. -/
def GSpec.lut (g : GSpec) : Lut g.k := ⟨BitVec.ofNat (2 ^ g.k) g.init⟩

/-- The `XSim` gate of a parsed gate. -/
def GSpec.toLGate (d : Design) (g : GSpec) : LGate d.n :=
  { k := g.k, lut := g.lut, ins := fun p => d.wire (g.ins.getD p.val 0), out := d.wire g.out,
    lo := g.lo, hi := g.hi }

/-- The `XSim` network of a design. -/
def build (d : Design) : List (LGate d.n) := d.gates.map (GSpec.toLGate d)

/-- Well-formedness of a gate (checked by the executable, `Design.wfB`). -/
def GSpec.WF (d : Design) (g : GSpec) : Prop :=
  g.ins.length = g.k ∧ (∀ i ∈ g.ins, i < d.n) ∧ g.out < d.n ∧ 1 ≤ g.lo ∧ g.lo ≤ g.hi ∧
    g.init < 2 ^ 2 ^ g.k

instance (d : Design) (g : GSpec) : Decidable (g.WF d) := by
  unfold GSpec.WF; exact inferInstance

def Design.WF (d : Design) : Prop := ∀ g ∈ d.gates, g.WF d

instance (d : Design) : Decidable d.WF := by unfold Design.WF; exact inferInstance

/-- The Boolean check the executable runs. -/
def Design.wfB (d : Design) : Bool := decide d.WF

/-! ## The built circuit is the parsed netlist -/

theorem GSpec.lut_entry (g : GSpec) (a : Nat) (ha : a < 2 ^ g.k) :
    g.lut.entry a = g.init.testBit a := by
  simp only [GSpec.lut, Lut.entry, BitVec.getLsbD_ofNat, ha, decide_true, Bool.true_and]

/-- Pin `p` of a well-formed gate is connected to wire `g.ins[p]`. -/
theorem toLGate_ins (d : Design) (g : GSpec) (hg : g.WF d) (p : Fin g.k) :
    ((g.toLGate d).ins p).val = g.ins[p.val]'(by rw [hg.1]; exact p.isLt) := by
  have hp : p.val < g.ins.length := by rw [hg.1]; exact p.isLt
  simp only [GSpec.toLGate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp,
    Option.getD_some]
  exact d.wire_val (hg.2.1 _ (List.getElem_mem hp))

theorem toLGate_out (d : Design) (g : GSpec) (hg : g.WF d) : ((g.toLGate d).out).val = g.out :=
  d.wire_val hg.2.2.1

/-- **The gate relation of a parsed gate.** The output wire is the transport
delay (band `[lo, hi]`) of INIT bit number `addr(values of the pin wires)`. -/
theorem toLGate_rel (d : Design) (g : GSpec) (x : Fin d.n → Sig) :
    (g.toLGate d).rel x ↔ TraceDiscrete.Transport g.lo g.hi
      (fun t => g.init.testBit (addr (fun p : Fin g.k => x (d.wire (g.ins.getD p.val 0)) t)))
      (x (d.wire g.out)) := by
  have e : (g.toLGate d).exc x =
      (fun t => g.init.testBit (addr (fun p : Fin g.k => x (d.wire (g.ins.getD p.val 0)) t))) := by
    funext t
    exact g.lut_entry _ (addr_lt _)
  simp only [LGate.rel]
  rw [e]; rfl

/-- **The circuit of a design** (`Circuit.Sat`) is the conjunction of the gate
relations of the parsed gates. -/
theorem sat_build_iff (d : Design) (x : Fin d.n → Sig) :
    Circuit.Sat (toCircuit (build d)) x ↔ ∀ g ∈ d.gates, (g.toLGate d).rel x := by
  simp only [Circuit.Sat, toCircuit, build, List.map_map, List.mem_map, Function.comp]
  constructor
  · intro h g hg; exact h _ ⟨g, hg, rfl⟩
  · rintro h _ ⟨g, hg, rfl⟩; exact h g hg

theorem build_lo (d : Design) (hwf : d.WF) : ∀ G ∈ build d, 1 ≤ G.lo := by
  intro G hG
  simp only [build, List.mem_map] at hG
  obtain ⟨g, hg, rfl⟩ := hG
  exact (hwf g hg).2.2.2.1

theorem build_lohi (d : Design) (hwf : d.WF) : ∀ G ∈ build d, G.lo ≤ G.hi := by
  intro G hG
  simp only [build, List.mem_map] at hG
  obtain ⟨g, hg, rfl⟩ := hG
  exact (hwf g hg).2.2.2.2.1

/-! ## The timed audit -/

/-- Power-up: every driven wire unknown. -/
def a0X {n : Nat} : Fin n → K3 := fun _ => X

/-- **What the executable computes**: the `XSim` history `[row T, ..., row 0]`
of the built network under abstract inputs `u`, from an all-`X` power-up. -/
def audit (d : Design) (u : Fin d.n → Nat → K3) (T : Nat) : List (List K3) :=
  hist (build d) u a0X T

/-- Value of wire `w` at step `s` read from a history computed to `T`. -/
def valAt (H : List (List K3)) (T s w : Nat) : K3 := (H.getD (T - s) []).getD w X

theorem valAt_audit (d : Design) (u : Fin d.n → Nat → K3) (T s : Nat) (hs : s ≤ T) (w : Fin d.n) :
    valAt (audit d u T) T s w.val = val (build d) u a0X s w := by
  simp only [valAt, audit, val, hist_getD _ _ _ T s hs]

/-- The concrete inputs agree with the abstract stimulus `u` on every primary
input (undriven wire). -/
def InputsCovered (d : Design) (u : Fin d.n → Nat → K3) (x : Fin d.n → Sig) : Prop :=
  ∀ w, Undriven (build d) w → ∀ t, u w t ⊑ ofBool (x w t)

/-- **Soundness of the audit.** For every behaviour `x` of the parsed netlist
(every gate and route delay inside its band, any power-up state) whose inputs
follow the stimulus, every value printed by the audit covers `x`. -/
theorem audit_sound (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (hin : InputsCovered d u x) :
    ∀ s, s ≤ T → ∀ w : Fin d.n, valAt (audit d u T) T s w.val ⊑ ofBool (x w s) := by
  intro s hs w
  rw [valAt_audit d u T s hs w]
  exact sound_circuit (build d) u a0X (build_lo d hwf) x hsat hin (fun _ _ => X_le _) s w

/-- A binary printed value is the value in every behaviour. -/
theorem audit_binary (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (hin : InputsCovered d u x) (s : Nat) (hs : s ≤ T) (w : Fin d.n) (v : Bool)
    (hv : valAt (audit d u T) T s w.val = ofBool v) : x w s = v :=
  defined_eq (audit_sound d hwf u T x hsat hin s hs w) hv

/-- The Boolean "no X on `w` in `[t1, t2]`" check that the report prints. -/
def noX (H : List (List K3)) (T w t1 t2 : Nat) : Bool :=
  (List.range' t1 (t2 + 1 - t1)).all (fun s => valAt H T s w != X)

/-- **Meaning of "no X reported at node `w` on `[t1, t2]`".** Every behaviour
of the parsed netlist whose inputs follow the stimulus has, at every step of
`[t1, t2]`, the value `pick` of the printed one: the waveform of `w` there is
one fixed binary waveform, the same for every delay assignment in the bands
and every power-up state. In particular `w` cannot glitch in `[t1, t2]` beyond
the transitions the printed waveform shows. -/
theorem noX_sound (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (w : Fin d.n) (t1 t2 : Nat) (ht2 : t2 ≤ T) (h : noX (audit d u T) T w.val t1 t2 = true)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (hin : InputsCovered d u x) :
    ∀ s, t1 ≤ s → s ≤ t2 → x w s = pick (valAt (audit d u T) T s w.val) := by
  intro s h1 h2
  simp only [noX, List.all_eq_true, List.mem_range'_1, bne_iff_ne, ne_eq] at h
  have hX := h s ⟨h1, by omega⟩
  obtain ⟨v, hv⟩ := ne_X_iff.mp hX
  rw [audit_binary d hwf u T x hsat hin s (by omega) w v hv, hv]
  cases v <;> rfl

/-- Corollary: two behaviours agree on `w` throughout an X-free window. -/
theorem noX_deterministic (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (w : Fin d.n) (t1 t2 : Nat) (ht2 : t2 ≤ T) (h : noX (audit d u T) T w.val t1 t2 = true)
    (x y : Fin d.n → Sig) (hx : Circuit.Sat (toCircuit (build d)) x)
    (hy : Circuit.Sat (toCircuit (build d)) y) (hix : InputsCovered d u x)
    (hiy : InputsCovered d u y) : ∀ s, t1 ≤ s → s ≤ t2 → x w s = y w s := by
  intro s h1 h2
  rw [noX_sound d hwf u T w t1 t2 ht2 h x hx hix s h1 h2,
    noX_sound d hwf u T w t1 t2 ht2 h y hy hiy s h1 h2]

/-- The rows `T - H .. T` of the history are equal (checked by the executable). -/
def rowsFixed (H : List (List K3)) (T Hd : Nat) : Bool :=
  (List.range' (T - Hd) (Hd + 1)).all (fun s => H.getD (T - s) [] == H.getD 0 [])

/-- Max `hi` of a design. -/
def Design.maxHi (d : Design) : Nat := d.gates.foldl (fun a g => max a g.hi) 0

theorem foldl_max_ge (l : List GSpec) (a : Nat) : a ≤ l.foldl (fun a g => max a g.hi) a := by
  induction l generalizing a with
  | nil => exact Nat.le_refl _
  | cons g l ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

theorem foldl_max_mem (l : List GSpec) (a : Nat) : ∀ g ∈ l, g.hi ≤ l.foldl (fun a g => max a g.hi) a := by
  induction l generalizing a with
  | nil => intro g hg; cases hg
  | cons g' l ih =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · exact Nat.le_trans (Nat.le_max_right _ _) (foldl_max_ge l _)
      · exact ih _ g hg

theorem build_hi (d : Design) : ∀ G ∈ build d, G.hi ≤ d.maxHi := by
  intro G hG
  simp only [build, List.mem_map] at hG
  obtain ⟨g, hg, rfl⟩ := hG
  exact foldl_max_mem d.gates 0 g hg

/-- **Settled.** If the stimulus is constant from `T ≥ 1` on and the last
`maxHi + 1` rows are equal (`rowsFixed`), then every binary value of row `T`
holds in every behaviour for ALL later time. -/
theorem settled_forever (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat) (hT : 1 ≤ T)
    (hu : ∀ w, Undriven (build d) w → ∀ t, T ≤ t → u w t = u w T)
    (hfix : rowsFixed (audit d u T) T d.maxHi = true)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (hin : InputsCovered d u x) (w : Fin d.n) (v : Bool)
    (hv : valAt (audit d u T) T T w.val = ofBool v) : ∀ t, T ≤ t → x w t = v := by
  intro t ht
  have hr : ∀ s, T - d.maxHi ≤ s → s ≤ T → arow (build d) u a0X s = arow (build d) u a0X T := by
    intro s h1 h2
    simp only [rowsFixed, List.all_eq_true, List.mem_range'_1, beq_iff_eq] at hfix
    have := hfix s ⟨h1, by omega⟩
    simp only [audit] at this
    rw [hist_getD _ _ _ T s h2] at this
    rw [this]
    have h0 := hist_getD (build d) u a0X T T (Nat.le_refl _)
    simp only [Nat.sub_self] at h0
    exact h0
  have hs := val_stationary (build d) u a0X d.maxHi T hT (build_lo d hwf) (build_lohi d hwf)
    (build_hi d) hu hr t w ht
  have hc := sound_circuit (build d) u a0X (build_lo d hwf) x hsat hin (fun _ _ => X_le _) t w
  rw [hs, ← valAt_audit d u T T (Nat.le_refl _) w, hv] at hc
  exact defined_eq hc rfl

end Formal.Core.XAudit

namespace Formal.Core.XAudit

open Formal.Core K3

/-- A stimulus: initial value of each listed input wire (others `X`), and
events `(step, wire, value)` in time order; the value of an input at step `t`
is that of its last event at or before `t`. A value may be `X` (unknown
input: covers both levels and any glitch). -/
structure Stim where
  init : List (Nat × K3)
  events : List (Nat × Nat × K3)
  deriving Repr

def Stim.initOf (st : Stim) (w : Nat) : K3 :=
  st.init.foldl (fun acc p => if p.1 == w then p.2 else acc) X

/-- The abstract input signal of a stimulus. -/
def Stim.u (st : Stim) {n : Nat} (w : Fin n) (t : Nat) : K3 :=
  st.events.foldl (fun acc e => if e.2.1 == w.val && e.1 ≤ t then e.2.2 else acc) (st.initOf w.val)

/-- Last event time (inputs are constant from there on). -/
def Stim.last (st : Stim) : Nat := st.events.foldl (fun a e => max a e.1) 0

theorem Stim.foldl_const {evs : List (Nat × Nat × K3)} (w t T : Nat) (hT : ∀ e ∈ evs, e.1 ≤ T) (ht : T ≤ t) (acc : K3) :
    evs.foldl (fun acc (e : Nat × Nat × K3) => if e.2.1 == w && e.1 ≤ t then e.2.2 else acc) acc =
    evs.foldl (fun acc (e : Nat × Nat × K3) => if e.2.1 == w && e.1 ≤ T then e.2.2 else acc) acc := by
  induction evs generalizing acc with
  | nil => rfl
  | cons e l ih =>
      simp only [List.foldl_cons]
      have he := hT e (List.mem_cons_self ..)
      have : (e.1 ≤ t) = (e.1 ≤ T) := propext ⟨fun _ => he, fun h => Nat.le_trans h ht⟩
      simp only [this]
      exact ih (fun e' h' => hT e' (List.mem_cons_of_mem _ h')) _

theorem Stim.last_ge (st : Stim) : ∀ e ∈ st.events, e.1 ≤ st.last := by
  have key : ∀ (l : List (Nat × Nat × K3)) (a : Nat),
      a ≤ l.foldl (fun a e => max a e.1) a ∧ ∀ e ∈ l, e.1 ≤ l.foldl (fun a e => max a e.1) a := by
    intro l
    induction l with
    | nil => intro a; exact ⟨Nat.le_refl _, fun e h => by cases h⟩
    | cons e l ih =>
        intro a
        obtain ⟨h1, h2⟩ := ih (max a e.1)
        refine ⟨Nat.le_trans (Nat.le_max_left _ _) h1, fun e' he' => ?_⟩
        rcases List.mem_cons.mp he' with rfl | he'
        · exact Nat.le_trans (Nat.le_max_right _ _) h1
        · exact h2 e' he'
  exact (key st.events 0).2

/-- The stimulus is constant after its last event. -/
theorem Stim.u_const (st : Stim) {n : Nat} (w : Fin n) (T t : Nat) (hT : st.last ≤ T) (ht : T ≤ t) :
    st.u w t = st.u w T := by
  unfold Stim.u
  exact Stim.foldl_const w.val t T (fun e he => Nat.le_trans (st.last_ge e he) hT) ht _

end Formal.Core.XAudit
