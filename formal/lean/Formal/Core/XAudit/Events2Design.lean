import Formal.Core.XAudit.EventsDesign
import Formal.Core.XAudit.Events2Time
import Formal.Core.LutCells

/-!
# Formal.Core.XAudit.Events2Design — the generalised counter domain on a parsed `xaudit` design

Probe A-events2. Connects `Events2.Beh.safe` (and the rate bounds of
`Events2Time`) to the netlist as `xaudit` parses it.

* **E4, cells.** A stage's LUT is any LUT6 whose INIT, under the layout
  `[pin_0 .. pin_{n-1}, q, rst, 0 ..]`, is the C-element of the bubbled pins
  with reset value `v` (`InitOK`, decided over the 64 addresses). The real
  INITs of `bd_c2`, `bd_c2_set`, `bd_c2n`, `bd_c2n_set`, `bd_c3`, `bd_c4`
  from `Formal.Core.LutCells` (generated from `cells/rtl/bd_ce.v`) pass, with
  their pin lists (`cells_ok`); a wrong INIT does not (`cells_neg`).
* **E1, chains.** A pin may be reached through any chain of 1-input gates
  (routed arcs, `bd_delay` LUT1 buffers, inverters): `chainOK`, composed into
  one transport channel with the summed band and the parity of the inverters
  (`chain_warp`).
* **E2, environment.** The environment is a list of extra 1-input gates (an
  eager sender is an inverter from the stage whose acknowledge it reads to
  the request port; an eager receiver a buffer from the request it
  acknowledges to the acknowledge port), stated as HYPOTHESES on the input
  ports' waveforms (`pipe3_safe`'s `henv`). Each is a transport channel in a
  stated band, i.e. a handshake partner that answers each event of its
  partner stage, no sooner than `lo` and no later than `hi` after it.

`design_beh2`: every `Circuit.Sat` behaviour of a recognised design is a
`Beh`; `design_safe2`: with `Back` every C-element output wire is
`ph v (M t j)` at every time. `Pipe3` instantiates it on the `xaudit
--emit-lean` literal of `designs/pipe3.json` (slow-corner bands).
-/

namespace Formal.Core.XAudit.Events2

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig Transport Warp)
open Formal.Core.XAudit.Events (ph IsBuf)

/-! ## LUT addresses -/

theorem testBit_add_two_mul (b : Bool) (m i : Nat) :
    (b.toNat + 2 * m).testBit i = if i = 0 then b else m.testBit (i - 1) := by
  cases i with
  | zero => cases b <;> simp [Nat.testBit_zero] <;> omega
  | succ i =>
    simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, Nat.testBit_succ]
    congr 1; cases b <;> simp <;> omega

theorem testBit_addr : ∀ {k : Nat} (f : Fin k → Bool) (i : Nat),
    (addr f).testBit i = if h : i < k then f ⟨i, h⟩ else false
  | 0, f, i => by simp [addr]
  | k + 1, f, i => by
      show ((f 0).toNat + 2 * addr (vtail f)).testBit i = _
      rw [testBit_add_two_mul, testBit_addr]
      cases i with
      | zero => simp
      | succ i =>
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel]
        by_cases h : i < k
        · rw [dif_pos h, dif_pos (by omega)]; rfl
        · rw [dif_neg h, dif_neg (by omega)]

/-! ## C-element INITs (E4) -/

/-- What address `a` of a C-element LUT must hold, pins at `I0 .. I(n-1)`,
feedback at `In`, reset at `I(n+1)`. -/
def spec (n : Nat) (v : Bool) (neg : Fin n → Bool) (a : Nat) : Bool :=
  if a.testBit (n + 1) then v else cel (fun p : Fin n => a.testBit p.val ^^ neg p) (a.testBit n)

/-- **InitOK** (decidable): on every address whose unused pins are 0, the
INIT is the C-element with reset value `v`. -/
def InitOK (n : Nat) (v : Bool) (neg : Fin n → Bool) (init : Nat) : Prop :=
  ∀ a, a < 64 → (∀ i, i < 6 → n + 2 ≤ i → a.testBit i = false) → init.testBit a = spec n v neg a

instance (n : Nat) (v : Bool) (neg : Fin n → Bool) (init : Nat) : Decidable (InitOK n v neg init) := by
  unfold InitOK; exact inferInstance

/-- The LUT pin layout of every `bd_ce.v` cell. -/
def layout {n : Nat} (pw : Fin n → Nat) (qw rw : Nat) : List Nat :=
  List.ofFn pw ++ [qw, rw] ++ List.replicate (4 - n) 0

theorem layout_pin {n : Nat} (pw : Fin n → Nat) (qw rw : Nat) (i : Fin n) :
    (layout pw qw rw).getD i.val 0 = pw i := by
  simp [layout, List.getD_eq_getElem?_getD, List.getElem?_append_left, i.isLt]

theorem layout_q {n : Nat} (pw : Fin n → Nat) (qw rw : Nat) :
    (layout pw qw rw).getD n 0 = qw := by
  simp [layout, List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left]

theorem layout_r {n : Nat} (pw : Fin n → Nat) (qw rw : Nat) :
    (layout pw qw rw).getD (n + 1) 0 = rw := by
  simp [layout, List.getD_eq_getElem?_getD, List.getElem?_append_right, List.getElem?_append_left]

theorem layout_hi {n : Nat} (pw : Fin n → Nat) (qw rw : Nat) (i : Nat) (h : n + 2 ≤ i) :
    (layout pw qw rw).getD i 0 = 0 := by
  simp only [layout, List.getD_eq_getElem?_getD, List.append_assoc]
  rw [List.getElem?_append_right (by simp; omega), List.getElem?_append_right (by simp; omega)]
  simp only [List.length_ofFn, List.length_cons, List.length_nil, List.getElem?_replicate]
  split <;> rfl

/-- The cells of `cells/rtl/bd_ce.v`, as `(arity, reset value, bubbles)`. -/
def negC2n : Fin 2 → Bool := fun p => p.val == 1

theorem cells_ok :
    InitOK 2 false (fun _ => false) LutCells.bd_c2_u.init ∧
    InitOK 2 true (fun _ => false) LutCells.bd_c2_set_u.init ∧
    InitOK 2 false negC2n LutCells.bd_c2n_u.init ∧
    InitOK 2 true negC2n LutCells.bd_c2n_set_u.init ∧
    InitOK 3 false (fun _ => false) LutCells.bd_c3_u.init ∧
    InitOK 4 false (fun _ => false) LutCells.bd_c4_u.init := by decide +kernel

/-- The pin lists of the same cells are the layout (`fb .O` = feedback,
`rst` next, tied 0 above). -/
theorem cells_pins :
    LutCells.bd_c2_u.pins = [.sig "a", .sig "b", .fb .O, .sig "rst", .c0, .c0] ∧
    LutCells.bd_c2_set_u.pins = [.sig "a", .sig "b", .fb .O, .sig "rst", .c0, .c0] ∧
    LutCells.bd_c2n_u.pins = [.sig "a", .sig "b", .fb .O, .sig "rst", .c0, .c0] ∧
    LutCells.bd_c2n_set_u.pins = [.sig "a", .sig "b", .fb .O, .sig "rst", .c0, .c0] ∧
    LutCells.bd_c3_u.pins = [.sig "a", .sig "b", .sig "c", .fb .O, .sig "rst", .c0] ∧
    LutCells.bd_c4_u.pins = [.sig "a", .sig "b", .sig "c", .sig "d", .fb .O, .sig "rst"] := by
  decide

/-- NEGATIVE CONTROL: the check can fail. `bd_c3`'s INIT is not a 2-input
C-element, `bd_c2`'s is not `bd_c2n`, and `bd_c4`'s with a bubble is not
`bd_c4`. -/
theorem cells_neg :
    ¬ InitOK 2 false (fun _ => false) LutCells.bd_c3_u.init ∧
    ¬ InitOK 2 false negC2n LutCells.bd_c2_u.init ∧
    ¬ InitOK 4 false (fun p => p.val == 3) LutCells.bd_c4_u.init ∧
    ¬ InitOK 3 true (fun _ => false) LutCells.bd_c3_u.init := by decide +kernel

/-! ## Chains of 1-input gates (E1) -/

/-- A chain of buffers (`INIT 2`) and inverters (`INIT 1`) of the design from
wire `a` to wire `b`. -/
def chainOK (d : Design) : List GSpec → Nat → Nat → Bool
  | [], a, b => a == b
  | g :: gs, a, b => decide (g ∈ d.gates) && g.k == 1 && (g.init == 2 || g.init == 1) &&
      g.ins == [a] && chainOK d gs g.out b

def cInv : List GSpec → Bool
  | [] => false
  | g :: gs => (g.init == 1) ^^ cInv gs

def cLo : List GSpec → Nat
  | [] => 0
  | g :: gs => g.lo + cLo gs

def cHi : List GSpec → Nat
  | [] => 0
  | g :: gs => g.hi + cHi gs

theorem gate1_transport (d : Design) (g : GSpec) (a : Nat) (hk : g.k = 1)
    (hi : g.init = 2 ∨ g.init = 1) (hins : g.ins = [a]) (x : Fin d.n → Sig)
    (h : (g.toLGate d).rel x) :
    ∃ f, Warp g.lo g.hi f ∧ ∀ t, x (d.wire g.out) t = ((g.init == 1) ^^ x (d.wire a) (f t)) := by
  rw [toLGate_rel] at h
  obtain ⟨name, k, init, ins, out, lo, hi'⟩ := g
  simp only at hk hi hins h ⊢
  subst hk; subst hins
  obtain ⟨f, hf, he⟩ := h
  refine ⟨f, hf, fun t => ?_⟩
  rw [he t]
  show init.testBit ((x (d.wire a) (f t)).toNat + 2 * 0) = _
  generalize x (d.wire a) (f t) = y
  rcases hi with rfl | rfl <;> cases y <;> rfl

theorem chain_warp (d : Design) (x : Fin d.n → Sig) (hs : ∀ g ∈ d.gates, (g.toLGate d).rel x) :
    ∀ (gs : List GSpec) (a b : Nat), chainOK d gs a b = true →
      ∃ f, Warp (cLo gs) (cHi gs) f ∧ ∀ t, x (d.wire b) t = (cInv gs ^^ x (d.wire a) (f t))
  | [], a, b, h => by
      simp only [chainOK, beq_iff_eq] at h; subst h
      exact ⟨id, ⟨fun _ _ h => h, fun t => by simp [cLo], fun t => by simp [cHi]⟩,
        fun t => by simp [cInv]⟩
  | g :: gs, a, b, h => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Bool.or_eq_true] at h
      obtain ⟨⟨⟨⟨hg, hk⟩, hi⟩, hins⟩, hrest⟩ := h
      obtain ⟨f1, w1, e1⟩ := gate1_transport d g a hk hi hins x (hs g hg)
      obtain ⟨f2, w2, e2⟩ := chain_warp d x hs gs g.out b hrest
      refine ⟨fun t => f1 (f2 t), ⟨fun a b h => w1.mono _ _ (w2.mono _ _ h), fun t => ?_, fun t => ?_⟩,
        fun t => ?_⟩
      · have := w1.le_late (f2 t); have := w2.le_late t; simp only [cLo]; omega
      · have := w1.early_le (f2 t); have := w2.early_le t; simp only [cHi]; omega
      · rw [e2, e1]; simp only [cInv]
        generalize (g.init == 1) = u; generalize cInv gs = w
        generalize x (d.wire a) (f1 (f2 t)) = y
        cases u <;> cases w <;> cases y <;> rfl

/-! ## Stage maps and recognition -/

/-- A stage map: per stage its LUT, per pin the chain from the source node's
output wire to the LUT pin wire `pw`, its feedback arc and its reset arc. -/
structure SMap2 {N : Nat} (net : CNet N) where
  lut : Fin N → GSpec
  chain : (j : Fin N) → Fin (net.ar j) → List GSpec
  pw : (j : Fin N) → Fin (net.ar j) → Nat
  fbG : Fin N → GSpec
  rG : Fin N → GSpec
  rst : Nat

/-- **Recognition** (decidable). -/
def Recog2 {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net) : Prop :=
  d.WF ∧ ∀ j : Fin N,
    sm.lut j ∈ d.gates ∧ (sm.lut j).k = 6 ∧ net.ar j ≤ 4 ∧
    InitOK (net.ar j) (net.v j) (net.neg j) (sm.lut j).init ∧
    (sm.lut j).ins = layout (sm.pw j) (sm.fbG j).out (sm.rG j).out ∧
    (∀ p, chainOK d (sm.chain j p) (sm.lut (net.src j p)).out (sm.pw j p) = true ∧
      sm.chain j p ≠ [] ∧ cInv (sm.chain j p) = net.inv j p) ∧
    IsBuf d (sm.fbG j) (sm.lut j).out ∧ IsBuf d (sm.rG j) sm.rst

instance {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net) : Decidable (Recog2 d net sm) := by
  unfold Recog2; exact inferInstance

def SMap2.bands {N : Nat} {net : CNet N} (sm : SMap2 net) : Bands net where
  loF := fun j => (sm.lut j).lo
  hiF := fun j => (sm.lut j).hi
  loG := fun j p => cLo (sm.chain j p)
  hiG := fun j p => cHi (sm.chain j p)
  loQ := fun j => (sm.fbG j).lo
  hiQ := fun j => (sm.fbG j).hi

theorem cLo_pos (d : Design) (hwf : d.WF) : ∀ (gs : List GSpec) (a b : Nat),
    chainOK d gs a b = true → gs ≠ [] → 1 ≤ cLo gs
  | [], _, _, _, h => absurd rfl h
  | g :: gs, a, b, h, _ => by
      simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
      have := (hwf g h.1.1.1.1).2.2.2.1
      simp only [cLo]; omega

theorem lut_transport2 {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net)
    (hr : Recog2 d net sm) (j : Fin N) (x : Fin d.n → Sig) (h0 : ∀ t, x (d.wire 0) t = false)
    (h : ((sm.lut j).toLGate d).rel x) :
    ∃ f, Warp (sm.lut j).lo (sm.lut j).hi f ∧ ∀ t, x (d.wire (sm.lut j).out) t =
      net.lutF j (fun p => x (d.wire (sm.pw j p)) (f t)) (x (d.wire (sm.fbG j).out) (f t))
        (x (d.wire (sm.rG j).out) (f t)) := by
  rw [toLGate_rel] at h
  obtain ⟨_, hk, har, hinit, hins, _⟩ := hr.2 j
  obtain ⟨f, hf, he⟩ := h
  refine ⟨f, hf, fun t => ?_⟩
  rw [he t]
  show (sm.lut j).init.testBit (addr (fun p : Fin (sm.lut j).k =>
    x (d.wire ((sm.lut j).ins.getD p.val 0)) (f t))) = _
  generalize f t = s
  -- the address and its bits
  have hbit : ∀ i, (addr (fun p : Fin (sm.lut j).k => x (d.wire ((sm.lut j).ins.getD p.val 0)) s)).testBit i
      = if i < 6 then x (d.wire ((sm.lut j).ins.getD i 0)) s else false := by
    intro i
    rw [testBit_addr]
    by_cases hi : i < (sm.lut j).k
    · rw [dif_pos hi, if_pos (by omega)]
    · rw [dif_neg hi, if_neg (by omega)]
  generalize ea : addr (fun p : Fin (sm.lut j).k => x (d.wire ((sm.lut j).ins.getD p.val 0)) s) = a at hbit
  have ha : a < 64 := by
    rw [← ea]; have := addr_lt (fun p : Fin (sm.lut j).k => x (d.wire ((sm.lut j).ins.getD p.val 0)) s)
    have h64 : 2 ^ (sm.lut j).k = 64 := by rw [hk]
    rw [h64] at this; exact this
  rw [hins] at hbit
  have hhi : ∀ i, i < 6 → net.ar j + 2 ≤ i → a.testBit i = false := by
    intro i h6 hi; rw [hbit, if_pos h6, layout_hi _ _ _ _ hi, h0]
  rw [hinit a ha hhi]
  unfold spec CNet.lutF
  have hr' : a.testBit (net.ar j + 1) = x (d.wire (sm.rG j).out) s := by
    rw [hbit, if_pos (by omega), layout_r]
  have hq' : a.testBit (net.ar j) = x (d.wire (sm.fbG j).out) s := by
    rw [hbit, if_pos (by omega), layout_q]
  have hp' : ∀ p : Fin (net.ar j), a.testBit p.val = x (d.wire (sm.pw j p)) s := by
    intro p; rw [hbit, if_pos (by omega), layout_pin]
  rw [hr', hq']
  simp only [hp']

/-- **Every behaviour of a recognised design is a `Beh`.** -/
theorem design_beh2 {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net) (hr : Recog2 d net sm)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ bh : Beh net sm.bands, (∀ j t, bh.c j t = x (d.wire (sm.lut j).out) t) ∧
      (∀ j s, T + (sm.rG j).hi ≤ s → bh.r j s = false) := by
  have hs := (sat_build_iff d x).mp hsat
  have hwf := hr.1
  have lo1 : ∀ g ∈ d.gates, 1 ≤ g.lo := fun g hg => (hwf g hg).2.2.2.1
  have tF := fun j => lut_transport2 d net sm hr j x h0 (hs _ (hr.2 j).1)
  have tG : ∀ j p, ∃ f, Warp (cLo (sm.chain j p)) (cHi (sm.chain j p)) f ∧ ∀ t,
      x (d.wire (sm.pw j p)) t = (net.inv j p ^^ x (d.wire (sm.lut (net.src j p)).out) (f t)) := by
    intro j p
    obtain ⟨f, w, e⟩ := chain_warp d x hs _ _ _ ((hr.2 j).2.2.2.2.2.1 p).1
    exact ⟨f, w, fun t => by rw [e t, ((hr.2 j).2.2.2.2.2.1 p).2.2]⟩
  have tQ : ∀ j, ∃ f, Warp (sm.fbG j).lo (sm.fbG j).hi f ∧ ∀ t,
      x (d.wire (sm.fbG j).out) t = x (d.wire (sm.lut j).out) (f t) := fun j =>
    Events.buf_transport d _ _ (hr.2 j).2.2.2.2.2.2.1 x (hs _ (hr.2 j).2.2.2.2.2.2.1.1)
  have tR : ∀ j, ∃ f, Warp (sm.rG j).lo (sm.rG j).hi f ∧ ∀ t,
      x (d.wire (sm.rG j).out) t = x (d.wire sm.rst) (f t) := fun j =>
    Events.buf_transport d _ _ (hr.2 j).2.2.2.2.2.2.2 x (hs _ (hr.2 j).2.2.2.2.2.2.2.1)
  refine ⟨{
    c := fun j => x (d.wire (sm.lut j).out)
    pin := fun j p => x (d.wire (sm.pw j p))
    q := fun j => x (d.wire (sm.fbG j).out)
    r := fun j => x (d.wire (sm.rG j).out)
    F := fun j => Classical.choose (tF j)
    G := fun j p => Classical.choose (tG j p)
    Q := fun j => Classical.choose (tQ j)
    wF := fun j => (Classical.choose_spec (tF j)).1
    wG := fun j p => (Classical.choose_spec (tG j p)).1
    wQ := fun j => (Classical.choose_spec (tQ j)).1
    loF1 := fun j => lo1 _ (hr.2 j).1
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
      have := (Classical.choose_spec (tR j)).1.mono a b hab; omega }, fun j t => rfl, ?_⟩
  intro j s hs
  show x (d.wire (sm.rG j).out) s = false
  rw [(Classical.choose_spec (tR j)).2, hrst]
  have := (Classical.choose_spec (tR j)).1.early_le s
  simp only [decide_eq_false_iff_not]; omega

/-- **Soundness on the parsed design.** -/
theorem design_safe2 {N : Nat} (d : Design) (net : CNet N) (sm : SMap2 net) (hr : Recog2 d net sm)
    {back : (j : Fin N) → Fin (net.ar j) → List (Arc net)} (hB : Back sm.bands back)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ M : Nat → Fin N → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧ (∀ j, M 0 j = 0) ∧
      ∀ t j, x (d.wire (sm.lut j).out) t = ph (net.v j) (M t j) := by
  obtain ⟨bh, hc, _⟩ := design_beh2 d net sm hr x hsat h0 T hT hrst
  exact ⟨bh.M, fun j a b h => bh.M_mono b j a h, bh.M_zero, fun t j => by rw [← hc]; exact bh.safe hB t j⟩

end Formal.Core.XAudit.Events2
