import Formal.Core.XAudit.Events2Design
import Formal.Core.XAudit.Events2Strict

/-!
# Formal.Core.XAudit.Events2PinDesign — the per-pin netlist semantics and its link to `BehP`

Shard A, probe events2pin (the open item 1 of `Wip/Contradictions.lean`). Notes:
`formal/notes/A-events2pin.md`.

`Events2Design.design_beh2` turns every behaviour of the parsed netlist into an
`Events2.Beh`, whose LUTs read all their pins at ONE instant (H_ATOMIC_LUT:
`Design.toLGate_rel`, one warp per gate). This file drops that assumption at the
netlist level:

* `PinRel d pl g x`: gate `g` reads its input index `i` through ITS OWN monotone
  warp `f i`, in the band `pl g i` (a per-pin band table: the pin-to-output arc
  of that physical LUT pin, site-pin delay included). This is the pure per-pin
  delay form of the LUT mux tree (B's H_PIN_FIFO); it exhibits function hazards.
* `SatPin d pl x`: every gate of the design satisfies `PinRel`.
  `sat_pin_of_sat`: the old (atomic) behaviours are among them whenever each pin
  band contains its gate's band, so the per-pin semantics only adds behaviours.
* `OneOK`: 1-input gates (routes, buffers, inverters) keep their own band; for
  them the per-pin and the atomic relation coincide (`rel_of_pin1`).
* **`design_behP`**: every `SatPin` behaviour of a recognised design (`Recog2`,
  the same decidable recognition as `Events2Design`) is a `BehP` with the pin
  bands `sm.pins pl` (pin `p` of stage `j` = index `p`, own feedback = index
  `ar j`, reset = index `ar j + 1`, the `bd_ce.v` layout).
* **`design_safe_pin`**: with `BackPin` on those bands every C-element output is
  `ph v (M t j)` at every time, in every per-pin behaviour (`BehP.safe`); no
  H_ATOMIC_LUT anywhere. Also the per-window bound `cycle_le_pin` (at most `wTok w`
  events in every window of `wLoP w` steps, for every closed walk `w`).
* `env_pin`, `close`, `EnvOK`: the environment gates of `xevents2`, as per-pin
  gates (1-input, so nothing changes for them).
-/

namespace Formal.Core.XAudit.Events2Pin

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig Transport Warp)
open Formal.Core.XAudit.Events (ph IsBuf)
open Formal.Core.XAudit.Events2
open Formal.Core.XAudit.Events2Strict

/-! ## The per-pin semantics of a gate -/

/-- A per-pin band table: the band (in steps) of input index `i` of gate `g`. -/
abbrev PinTab := GSpec → Nat → Nat × Nat

/-- **Per-pin gate relation.** The output at `t` is the INIT bit at the address
formed by reading input index `i` at `f i t`, each `f i` a monotone warp in the
band `pl g i`. -/
def PinRel (d : Design) (pl : PinTab) (g : GSpec) (x : Fin d.n → Sig) : Prop :=
  ∃ f : Nat → Nat → Nat, (∀ i, i < g.k → Warp (pl g i).1 (pl g i).2 (f i)) ∧
    ∀ t, x (d.wire g.out) t =
      g.init.testBit (addr (fun p : Fin g.k => x (d.wire (g.ins.getD p.val 0)) (f p.val t)))

/-- **The per-pin netlist semantics**: every gate satisfies `PinRel`. -/
def SatPin (d : Design) (pl : PinTab) (x : Fin d.n → Sig) : Prop :=
  ∀ g ∈ d.gates, PinRel d pl g x

/-- 1-input gates keep their own band (decidable). -/
def OneOK (d : Design) (pl : PinTab) : Prop :=
  ∀ g ∈ d.gates, g.k = 1 → pl g 0 = (g.lo, g.hi)

instance (d : Design) (pl : PinTab) : Decidable (OneOK d pl) := by
  unfold OneOK; exact inferInstance

/-- Every per-pin band is a band (`lo ≤ hi`); checked by the executable so that
`PinRel` is never vacuous for want of a warp (`shift` is a warp in any band). -/
def BandsOK (d : Design) (pl : PinTab) : Prop :=
  ∀ g ∈ d.gates, ∀ i, i < g.k → (pl g i).1 ≤ (pl g i).2

instance (d : Design) (pl : PinTab) : Decidable (BandsOK d pl) := by
  unfold BandsOK; exact inferInstance

theorem shift_warp (lo hi : Nat) (h : lo ≤ hi) : Warp lo hi (fun t => t - lo) :=
  ⟨fun a b hab => by omega, fun t => by omega, fun t => by omega⟩

/-- For a 1-input gate with its own band the per-pin relation is the gate
relation. -/
theorem rel_of_pin1 (d : Design) (pl : PinTab) (g : GSpec) (x : Fin d.n → Sig) (hk : g.k = 1)
    (hpl : pl g 0 = (g.lo, g.hi)) (h : PinRel d pl g x) : (g.toLGate d).rel x := by
  rw [toLGate_rel]
  obtain ⟨f, hw, he⟩ := h
  have w0 := hw 0 (by omega)
  rw [hpl] at w0
  refine ⟨f 0, w0, fun t => ?_⟩
  rw [he t]
  show g.init.testBit (addr _) = g.init.testBit (addr _)
  congr 2
  funext p
  have : p.val = 0 := by have := p.isLt; omega
  rw [this]

/-- An atomic gate behaviour is a per-pin one when every pin band contains the
gate's band (all pins read through the gate's one warp). -/
theorem pin_of_rel (d : Design) (pl : PinTab) (g : GSpec) (x : Fin d.n → Sig)
    (hb : ∀ i, i < g.k → (pl g i).1 ≤ g.lo ∧ g.hi ≤ (pl g i).2)
    (h : (g.toLGate d).rel x) : PinRel d pl g x := by
  rw [toLGate_rel] at h
  obtain ⟨f, hw, he⟩ := h
  refine ⟨fun _ => f, fun i hi => ⟨hw.mono, fun t => ?_, fun t => ?_⟩, fun t => he t⟩
  · show f t ≤ _; have := hw.le_late t; have := (hb i hi).1; omega
  · show _ ≤ f t; have := hw.early_le t; have := (hb i hi).2; omega

/-- **The per-pin semantics contains the atomic one** (when the pin bands
contain the gate bands): `SatPin` only adds behaviours. -/
theorem sat_pin_of_sat (d : Design) (pl : PinTab) (x : Fin d.n → Sig)
    (hb : ∀ g ∈ d.gates, ∀ i, i < g.k → (pl g i).1 ≤ g.lo ∧ g.hi ≤ (pl g i).2)
    (hsat : Circuit.Sat (toCircuit (build d)) x) : SatPin d pl x := by
  have hs := (sat_build_iff d x).mp hsat
  exact fun g hg => pin_of_rel d pl g x (hb g hg) (hs g hg)

/-! ## Chains of 1-input gates under the per-pin semantics -/

/-- `Events2.chain_warp` needing the gate relation of 1-input gates only. -/
theorem chain_warp1 (d : Design) (x : Fin d.n → Sig)
    (hs : ∀ g ∈ d.gates, g.k = 1 → (g.toLGate d).rel x) :
    ∀ (gs : List GSpec) (a b : Nat), chainOK d gs a b = true →
      ∃ f, Warp (cLo gs) (cHi gs) f ∧ ∀ t, x (d.wire b) t = (cInv gs ^^ x (d.wire a) (f t))
  | [], a, b, h => by
      simp only [chainOK, beq_iff_eq] at h; subst h
      exact ⟨id, ⟨fun _ _ h => h, fun t => by simp [cLo], fun t => by simp [cHi]⟩,
        fun t => by simp [cInv]⟩
  | g :: gs, a, b, h => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h
      obtain ⟨⟨⟨⟨hg, hk⟩, hi⟩, hins⟩, hrest⟩ := h
      obtain ⟨f1, w1, e1⟩ := gate1_transport d g a hk hi hins x (hs g hg hk)
      obtain ⟨f2, w2, e2⟩ := chain_warp1 d x hs gs g.out b hrest
      refine ⟨fun t => f1 (f2 t), ⟨fun a b h => w1.mono _ _ (w2.mono _ _ h), fun t => ?_, fun t => ?_⟩,
        fun t => ?_⟩
      · have := w1.le_late (f2 t); have := w2.le_late t; simp only [cLo]; omega
      · have := w1.early_le (f2 t); have := w2.early_le t; simp only [cHi]; omega
      · rw [e2, e1]; simp only [cInv]
        generalize (g.init == 1) = u; generalize cInv gs = w
        generalize x (d.wire a) (f1 (f2 t)) = y
        cases u <;> cases w <;> cases y <;> rfl

/-! ## The stage LUT read per pin -/

/-- **A recognised C-element LUT under the per-pin semantics**: its output is
the settled C-element function of input pin `p` read at `f p t`, the feedback
read at `f (ar j) t` and the reset read at `f (ar j + 1) t`. -/
theorem lut_transport_pin {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net) (pl : PinTab)
    (hr : Recog2 d net sm) (j : Fin N) (x : Fin d.n → Sig) (h0 : ∀ t, x (d.wire 0) t = false)
    (h : PinRel d pl (sm.lut j) x) :
    ∃ f : Nat → Nat → Nat, (∀ i, i < 6 → Warp (pl (sm.lut j) i).1 (pl (sm.lut j) i).2 (f i)) ∧
      ∀ t, x (d.wire (sm.lut j).out) t =
        net.lutF j (fun p => x (d.wire (sm.pw j p)) (f p.val t))
          (x (d.wire (sm.fbG j).out) (f (net.ar j) t))
          (x (d.wire (sm.rG j).out) (f (net.ar j + 1) t)) := by
  obtain ⟨_, hk, har, hinit, hins, _⟩ := hr.2 j
  obtain ⟨f, hf, he⟩ := h
  refine ⟨f, fun i hi => hf i (by rw [hk]; exact hi), fun t => ?_⟩
  rw [he t]
  have hbit : ∀ i, (addr (fun p : Fin (sm.lut j).k =>
      x (d.wire ((sm.lut j).ins.getD p.val 0)) (f p.val t))).testBit i
      = if i < 6 then x (d.wire ((sm.lut j).ins.getD i 0)) (f i t) else false := by
    intro i
    rw [testBit_addr]
    by_cases hi : i < (sm.lut j).k
    · rw [dif_pos hi, if_pos (by omega)]
    · rw [dif_neg hi, if_neg (by omega)]
  generalize ea : addr (fun p : Fin (sm.lut j).k =>
      x (d.wire ((sm.lut j).ins.getD p.val 0)) (f p.val t)) = a at hbit
  have ha : a < 64 := by
    rw [← ea]
    have := addr_lt (fun p : Fin (sm.lut j).k => x (d.wire ((sm.lut j).ins.getD p.val 0)) (f p.val t))
    have h64 : 2 ^ (sm.lut j).k = 64 := by rw [hk]
    rw [h64] at this; exact this
  rw [hins] at hbit
  have hhi : ∀ i, i < 6 → net.ar j + 2 ≤ i → a.testBit i = false := by
    intro i h6 hi; rw [hbit, if_pos h6, layout_hi _ _ _ _ hi, h0]
  rw [hinit a ha hhi]
  unfold spec CNet.lutF
  have hr' : a.testBit (net.ar j + 1) = x (d.wire (sm.rG j).out) (f (net.ar j + 1) t) := by
    rw [hbit, if_pos (by omega), layout_r]
  have hq' : a.testBit (net.ar j) = x (d.wire (sm.fbG j).out) (f (net.ar j) t) := by
    rw [hbit, if_pos (by omega), layout_q]
  have hp' : ∀ p : Fin (net.ar j), a.testBit p.val = x (d.wire (sm.pw j p)) (f p.val t) := by
    intro p; rw [hbit, if_pos (by omega), layout_pin]
  rw [hr', hq']
  simp only [hp']

/-! ## Stage pin bands and the netlist link -/

/-- The per-pin bands of the stages, read off the table at the `bd_ce.v`
layout: pin `p` is index `p`, the own feedback index `ar j`, the reset
index `ar j + 1`. -/
def pinsOf {N : Nat} {net : CNet N} (sm : SMap2 net) (pl : PinTab) : PinBands net :=
  ⟨fun j p => (pl (sm.lut j) p.val).1, fun j p => (pl (sm.lut j) p.val).2,
   fun j => (pl (sm.lut j) (net.ar j)).1, fun j => (pl (sm.lut j) (net.ar j)).2,
   fun j => (pl (sm.lut j) (net.ar j + 1)).1, fun j => (pl (sm.lut j) (net.ar j + 1)).2⟩

/-- Input and feedback pin arcs take at least one step (decidable). -/
def PinOK {N : Nat} {net : CNet N} (sm : SMap2 net) (pl : PinTab) : Prop :=
  ∀ j, (∀ p : Fin (net.ar j), 1 ≤ (pl (sm.lut j) p.val).1) ∧ 1 ≤ (pl (sm.lut j) (net.ar j)).1

instance {N : Nat} {net : CNet N} (sm : SMap2 net) (pl : PinTab) : Decidable (PinOK sm pl) := by
  unfold PinOK; exact inferInstance

/-- **Every per-pin behaviour of a recognised design is a `BehP`.** -/
theorem design_behP {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net) (pl : PinTab)
    (hr : Recog2 d net sm) (h1 : OneOK d pl) (hp : PinOK sm pl)
    (x : Fin d.n → Sig) (hsat : SatPin d pl x)
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ bh : BehP net sm.bands (pinsOf sm pl), ∀ j t, bh.c j t = x (d.wire (sm.lut j).out) t := by
  have hs1 : ∀ g ∈ d.gates, g.k = 1 → (g.toLGate d).rel x :=
    fun g hg hk => rel_of_pin1 d pl g x hk (h1 g hg hk) (hsat g hg)
  have hwf := hr.1
  have lo1 : ∀ g ∈ d.gates, 1 ≤ g.lo := fun g hg => (hwf g hg).2.2.2.1
  have har : ∀ j, net.ar j ≤ 4 := fun j => (hr.2 j).2.2.1
  have tF := fun j => lut_transport_pin d net sm pl hr j x h0 (hsat _ (hr.2 j).1)
  have tG : ∀ j p, ∃ f, Warp (cLo (sm.chain j p)) (cHi (sm.chain j p)) f ∧ ∀ t,
      x (d.wire (sm.pw j p)) t = (net.inv j p ^^ x (d.wire (sm.lut (net.src j p)).out) (f t)) := by
    intro j p
    obtain ⟨f, w, e⟩ := chain_warp1 d x hs1 _ _ _ ((hr.2 j).2.2.2.2.2.1 p).1
    exact ⟨f, w, fun t => by rw [e t, ((hr.2 j).2.2.2.2.2.1 p).2.2]⟩
  have tQ : ∀ j, ∃ f, Warp (sm.fbG j).lo (sm.fbG j).hi f ∧ ∀ t,
      x (d.wire (sm.fbG j).out) t = x (d.wire (sm.lut j).out) (f t) := fun j =>
    Events.buf_transport d _ _ (hr.2 j).2.2.2.2.2.2.1 x
      (hs1 _ (hr.2 j).2.2.2.2.2.2.1.1 (hr.2 j).2.2.2.2.2.2.1.2.1)
  have tR : ∀ j, ∃ f, Warp (sm.rG j).lo (sm.rG j).hi f ∧ ∀ t,
      x (d.wire (sm.rG j).out) t = x (d.wire sm.rst) (f t) := fun j =>
    Events.buf_transport d _ _ (hr.2 j).2.2.2.2.2.2.2 x
      (hs1 _ (hr.2 j).2.2.2.2.2.2.2.1 (hr.2 j).2.2.2.2.2.2.2.2.1)
  refine ⟨{
    c := fun j => x (d.wire (sm.lut j).out)
    pin := fun j p => x (d.wire (sm.pw j p))
    q := fun j => x (d.wire (sm.fbG j).out)
    r := fun j => x (d.wire (sm.rG j).out)
    Fp := fun j p => Classical.choose (tF j) p.val
    Fq := fun j => Classical.choose (tF j) (net.ar j)
    Fr := fun j => Classical.choose (tF j) (net.ar j + 1)
    G := fun j p => Classical.choose (tG j p)
    Q := fun j => Classical.choose (tQ j)
    wFp := fun j p => (Classical.choose_spec (tF j)).1 p.val (by have := p.isLt; have := har j; omega)
    wFq := fun j => (Classical.choose_spec (tF j)).1 (net.ar j) (by have := har j; omega)
    wFr := fun j => (Classical.choose_spec (tF j)).1 (net.ar j + 1) (by have := har j; omega)
    wG := fun j p => (Classical.choose_spec (tG j p)).1
    wQ := fun j => (Classical.choose_spec (tQ j)).1
    loP1 := fun j p => (hp j).1 p
    loPq1 := fun j => (hp j).2
    loG1 := fun j p => cLo_pos d hwf _ _ _ ((hr.2 j).2.2.2.2.2.1 p).1 ((hr.2 j).2.2.2.2.2.1 p).2.1
    loQ1 := fun j => lo1 _ (hr.2 j).2.2.2.2.2.2.1.1
    hc := fun j t => (Classical.choose_spec (tF j)).2 t
    hpin := fun j p t => (Classical.choose_spec (tG j p)).2 t
    hq := fun j t => (Classical.choose_spec (tQ j)).2 t
    r0 := fun j => by
      show x (d.wire (sm.rG j).out) 0 = true
      rw [(Classical.choose_spec (tR j)).2 0, hrst]
      have := (Classical.choose_spec (tR j)).1.le_late 0
      simp only [decide_eq_true_eq]; omega
    ranti := fun j a b hab hb => by
      show x (d.wire (sm.rG j).out) a = true
      have hb' : x (d.wire (sm.rG j).out) b = true := hb
      rw [(Classical.choose_spec (tR j)).2, hrst] at hb' ⊢
      simp only [decide_eq_true_eq] at hb' ⊢
      have := (Classical.choose_spec (tR j)).1.mono a b hab; omega }, fun j t => rfl⟩

/-- **Per-window bound, per pin**: around any closed walk through `j`, at most
`wTok w` events of `j` in every window of `wLoP w` steps (the per-pin form of
`Events2Time`'s `cycle_le`; immediate from `BehP.walk_le`). -/
theorem cycle_le_pin {N : Nat} {net : CNet N} {b : Bands net} {pb : PinBands net}
    (x : BehP net b pb) (w : List (Arc net)) (j : Fin N) (hw : walkOK net j j w = true) (t : Nat) :
    x.M (t + wLoP b pb w) j ≤ x.M t j + wTok net w := by
  have := x.walk_le w j j hw (t + wLoP b pb w)
  rwa [Nat.add_sub_cancel] at this

/-- **Soundness on the parsed design, per pin.** Under `BackPin` on the stage
pin bands, every C-element output of every per-pin behaviour is its reset
value flipped `M t j` times, with `M` monotone. -/
theorem design_safe_pin {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net) (pl : PinTab)
    (hr : Recog2 d net sm) (h1 : OneOK d pl) (hp : PinOK sm pl)
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : BackPin sm.bands (pinsOf sm pl) back)
    (x : Fin d.n → Sig) (hsat : SatPin d pl x)
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ M : Nat → Fin N → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧
      (∀ t j, x (d.wire (sm.lut j).out) t = ph (net.v j) (M t j)) ∧
      (∀ (w : List (Arc net)) (j : Fin N), walkOK net j j w = true →
        ∀ t, M (t + wLoP sm.bands (pinsOf sm pl) w) j ≤ M t j + wTok net w) := by
  obtain ⟨bh, hc⟩ := design_behP d net sm pl hr h1 hp x hsat h0 T hT hrst
  exact ⟨bh.M, fun j a b h => bh.M_mono b j a h, fun t j => by rw [← hc]; exact bh.safe hB t j,
    fun w j hw t => cycle_le_pin bh w j hw t⟩

/-! ## The environment (as in `xevents2`) -/

/-- The design closed by its environment gates. Same wires. -/
def close (d : Design) (env : List GSpec) : Design := ⟨d.m, d.gates ++ env⟩

/-- An environment gate is a 1-input buffer (`INIT 2`) or inverter (`INIT 1`). -/
def EnvOK (g : GSpec) : Prop := g.k = 1 ∧ (g.init = 1 ∨ g.init = 2) ∧ g.ins.length = 1

instance (g : GSpec) : Decidable (EnvOK g) := by unfold EnvOK; exact inferInstance

/-- The environment hypothesis on one port is its gate's relation
(`Events2Main.env_rel`, restated here: an executable module cannot be imported). -/
theorem env_rel (d : Design) (g : GSpec) (hg : EnvOK g) (x : Fin d.n → Sig) (lo hi : Nat)
    (hlo : g.lo ≤ lo) (hhi : hi ≤ g.hi)
    (h : Transport lo hi (fun t => (g.init == 1) ^^ x (d.wire (g.ins.getD 0 0)) t)
      (x (d.wire g.out))) :
    (g.toLGate d).rel x := by
  refine (toLGate_rel d g x).mpr ?_
  have h' := TraceDiscrete.transport_mono hlo hhi h
  obtain ⟨name, k, init, ins, out, glo, ghi⟩ := g
  obtain ⟨hk, hi', hl⟩ := hg
  simp only at hk hi' hl h' ⊢
  subst hk
  obtain ⟨a, rfl⟩ : ∃ a, ins = [a] := by
    match ins, hl with
    | [a], _ => exact ⟨a, rfl⟩
  have e : (fun t => init.testBit (addr (fun p : Fin 1 => x (d.wire ([a].getD p.val 0)) t))) =
      (fun t => (init == 1) ^^ x (d.wire a) t) := by
    funext t
    show init.testBit ((x (d.wire a) t).toNat + 2 * 0) = _
    rcases hi' with rfl | rfl <;> cases x (d.wire a) t <;> rfl
  rw [e]; exact h'

/-- … and so its per-pin relation (a 1-input gate keeps its own band). -/
theorem env_pin (d : Design) (pl : PinTab) (g : GSpec) (hg : EnvOK g) (hpl : pl g 0 = (g.lo, g.hi))
    (x : Fin d.n → Sig) (lo hi : Nat) (hlo : g.lo ≤ lo) (hhi : hi ≤ g.hi)
    (h : Transport lo hi (fun t => (g.init == 1) ^^ x (d.wire (g.ins.getD 0 0)) t)
      (x (d.wire g.out))) : PinRel d pl g x :=
  pin_of_rel d pl g x (fun i hi => by
    have : i = 0 := by have := hg.1; omega
    subst this; rw [hpl]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩) (env_rel d g hg x lo hi hlo hhi h)

theorem sat_pin_close (d : Design) (env : List GSpec) (pl : PinTab) (x : Fin d.n → Sig)
    (hsat : SatPin d pl x) (henv : ∀ g ∈ env, PinRel (close d env) pl g x) :
    SatPin (close d env) pl x := by
  intro g hg
  simp only [close, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hsat g hg
  · exact henv g hg

end Formal.Core.XAudit.Events2Pin
