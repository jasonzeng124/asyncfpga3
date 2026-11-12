import Formal.Core.XAudit.Design
import Formal.Core.XAudit.EventsRing

/-!
# Formal.Core.XAudit.EventsDesign — the counter domain on a parsed `xaudit` design

Probe A-events. Connects `Events.safe` to the netlist exactly as `xaudit`
parses it (`Design`, `build`, `Circuit.Sat`): a *stage map* names, for each
C-element stage, its LUT gate and the four routed-arc buffer gates of its pins
I0..I3. `Recog` (decidable, checked by the executable and here by `decide`)
says these are gates of the design with the real `bd_c2n`/`bd_c2n_set` INIT,
wired `[a, b, q, rst, 0, 0]`, with `a`/`b` routed from the LUT outputs of the
stages the `MNet` says, `q` routed from the stage's own output and `rst` from
the reset port. Bands are read off those gates.

* `design_beh`: every `Circuit.Sat` behaviour of `build d` (any delays in the
  parsed bands, as monotone warps; any power-up) whose const-0 wire is 0 and
  whose reset port falls once at step `T ≥ 1` IS a `Beh` of the Muller network
  (node signals = the LUT output wires), with every reset pin low from
  `T + hi` on.
* `design_safe`: hence, with `Pairing` and `Race`, every LUT output wire is
  `ph v (M t j)` at every time.
* `ring3_design_*`: the ring3 design that `xaudit --emit-lean` printed for
  `designs/ring3.json` with `designs/slow_corner.bands.json` (1 step = 10 ps)
  is recognised, `Race` holds (33 ≤ 36 + 9 + 36), and every behaviour of it
  is hazard-free for all time with node period in [6·45, 6·57] steps =
  [2700, 3420] ps. This is the design on which `XSim` reports UNRESOLVED
  from 5.2 ns.
-/

namespace Formal.Core.XAudit.Events

open Formal.Core.XAudit
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig Transport Warp)

/-- INIT of `bd_c2n` (reset value 0) and `bd_c2n_set` (reset value 1),
`cells/rtl/bd_ce.v`. -/
def c2nInit (v : Bool) : Nat := if v then 0xFFB2FFB2FFB2FFB2 else 0x00B200B200B200B2

/-- The real INIT under `[a, b, q, rst, 0, 0]` is `lutF`: reset value under
reset, else `maj(a, ¬b, q)`. -/
theorem c2nInit_eval (v a b q r : Bool) :
    (c2nInit v).testBit (a.toNat + 2 * (b.toNat + 2 * (q.toNat + 2 * (r.toNat + 2 * (0 + 2 * (0 + 2 * 0))))))
      = (if r then v else maj a (!b) q) := by
  cases v <;> cases a <;> cases b <;> cases q <;> cases r <;> decide

/-- A stage map: the gates of each stage. -/
structure SMap (N : Nat) where
  lut : Fin N → GSpec
  pinG : Fin N → Bool → GSpec
  fbG : Fin N → GSpec
  rG : Fin N → GSpec
  rst : Nat

/-- A routed-arc buffer from wire `w`. -/
def IsBuf (d : Design) (g : GSpec) (w : Nat) : Prop :=
  g ∈ d.gates ∧ g.k = 1 ∧ g.init = 2 ∧ g.ins = [w]

instance (d : Design) (g : GSpec) (w : Nat) : Decidable (IsBuf d g w) := by
  unfold IsBuf; exact inferInstance

/-- **Recognition** (decidable). -/
def Recog {N : Nat} (d : Design) (net : MNet N) (sm : SMap N) : Prop :=
  d.WF ∧ ∀ j : Fin N,
    sm.lut j ∈ d.gates ∧ (sm.lut j).k = 6 ∧ (sm.lut j).init = c2nInit (net.v j) ∧
    (sm.lut j).ins = [(sm.pinG j false).out, (sm.pinG j true).out, (sm.fbG j).out, (sm.rG j).out, 0, 0] ∧
    IsBuf d (sm.pinG j false) (sm.lut (net.src j false)).out ∧
    IsBuf d (sm.pinG j true) (sm.lut (net.src j true)).out ∧
    IsBuf d (sm.fbG j) (sm.lut j).out ∧ IsBuf d (sm.rG j) sm.rst

instance {N : Nat} (d : Design) (net : MNet N) (sm : SMap N) : Decidable (Recog d net sm) := by
  unfold Recog; exact inferInstance

/-- Bands read off the recognised gates. -/
def SMap.bands {N : Nat} (sm : SMap N) : Bands N where
  loF := fun j => (sm.lut j).lo
  hiF := fun j => (sm.lut j).hi
  loG := fun j p => (sm.pinG j p).lo
  hiG := fun j p => (sm.pinG j p).hi
  loQ := fun j => (sm.fbG j).lo
  hiQ := fun j => (sm.fbG j).hi

theorem buf_transport (d : Design) (g : GSpec) (w : Nat) (hb : IsBuf d g w) (x : Fin d.n → Sig)
    (h : (g.toLGate d).rel x) : Transport g.lo g.hi (x (d.wire w)) (x (d.wire g.out)) := by
  rw [toLGate_rel] at h
  obtain ⟨_, hk, hi, hins⟩ := hb
  obtain ⟨name, k, init, ins, out, lo, hi'⟩ := g
  simp only at hk hi hins h ⊢
  subst hk; subst hi; subst hins
  have e : (fun t => (2 : Nat).testBit (addr (fun p : Fin 1 => x (d.wire ([w].getD p.val 0)) t)))
      = x (d.wire w) := by
    funext t
    show (2 : Nat).testBit ((x (d.wire w) t).toNat + 2 * 0) = _
    cases x (d.wire w) t <;> decide
  rw [e] at h; exact h

theorem lut_transport {N : Nat} (d : Design) (net : MNet N) (sm : SMap N) (hr : Recog d net sm)
    (j : Fin N) (x : Fin d.n → Sig) (h0 : ∀ t, x (d.wire 0) t = false)
    (h : ((sm.lut j).toLGate d).rel x) :
    Transport (sm.lut j).lo (sm.lut j).hi
      (fun t => net.lutF j (x (d.wire (sm.pinG j false).out) t) (x (d.wire (sm.pinG j true).out) t)
        (x (d.wire (sm.fbG j).out) t) (x (d.wire (sm.rG j).out) t))
      (x (d.wire (sm.lut j).out)) := by
  rw [toLGate_rel] at h
  obtain ⟨_, hk, hi, hins, _⟩ := hr.2 j
  generalize sm.lut j = g at hk hi hins h ⊢
  obtain ⟨name, k, init, ins, out, lo, hi'⟩ := g
  simp only at hk hi hins h ⊢
  subst hk; subst hi; subst hins
  have e : (fun t => (c2nInit (net.v j)).testBit (addr (fun p : Fin 6 =>
        x (d.wire ([(sm.pinG j false).out, (sm.pinG j true).out, (sm.fbG j).out, (sm.rG j).out, 0, 0].getD p.val 0)) t)))
      = (fun t => net.lutF j (x (d.wire (sm.pinG j false).out) t) (x (d.wire (sm.pinG j true).out) t)
        (x (d.wire (sm.fbG j).out) t) (x (d.wire (sm.rG j).out) t)) := by
    funext t
    show (c2nInit (net.v j)).testBit ((x (d.wire (sm.pinG j false).out) t).toNat + 2 *
      ((x (d.wire (sm.pinG j true).out) t).toNat + 2 * ((x (d.wire (sm.fbG j).out) t).toNat + 2 *
      ((x (d.wire (sm.rG j).out) t).toNat + 2 * ((x (d.wire 0) t).toNat + 2 *
      ((x (d.wire 0) t).toNat + 2 * 0)))))) = _
    rw [h0 t]
    exact c2nInit_eval _ _ _ _ _
  rw [e] at h; exact h

/-- **Every behaviour of the parsed design is a behaviour of the Muller
network**, with the reset pins low from `T + hi(rst arc)` on. -/
theorem design_beh {N : Nat} (d : Design) (net : MNet N) (sm : SMap N) (hr : Recog d net sm)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ bh : Beh net sm.bands, (∀ j t, bh.c j t = x (d.wire (sm.lut j).out) t) ∧
      (∀ j s, T + (sm.rG j).hi ≤ s → bh.r j s = false) := by
  have hs := (sat_build_iff d x).mp hsat
  have hwf := hr.1
  have lo1 : ∀ g ∈ d.gates, 1 ≤ g.lo := fun g hg => (hwf g hg).2.2.2.1
  -- warps of every recognised gate
  have tF : ∀ j, ∃ f, Warp (sm.lut j).lo (sm.lut j).hi f ∧ ∀ t,
      x (d.wire (sm.lut j).out) t = net.lutF j (x (d.wire (sm.pinG j false).out) (f t))
        (x (d.wire (sm.pinG j true).out) (f t)) (x (d.wire (sm.fbG j).out) (f t))
        (x (d.wire (sm.rG j).out) (f t)) := fun j =>
    lut_transport d net sm hr j x h0 (hs _ (hr.2 j).1)
  have tG : ∀ jp : Fin N × Bool, ∃ f, Warp (sm.pinG jp.1 jp.2).lo (sm.pinG jp.1 jp.2).hi f ∧ ∀ t,
      x (d.wire (sm.pinG jp.1 jp.2).out) t = x (d.wire (sm.lut (net.src jp.1 jp.2)).out) (f t) := by
    intro ⟨j, p⟩
    have hb : IsBuf d (sm.pinG j p) (sm.lut (net.src j p)).out := by
      cases p
      · exact (hr.2 j).2.2.2.2.1
      · exact (hr.2 j).2.2.2.2.2.1
    exact buf_transport d _ _ hb x (hs _ hb.1)
  have tQ : ∀ j, ∃ f, Warp (sm.fbG j).lo (sm.fbG j).hi f ∧ ∀ t,
      x (d.wire (sm.fbG j).out) t = x (d.wire (sm.lut j).out) (f t) := fun j =>
    buf_transport d _ _ (hr.2 j).2.2.2.2.2.2.1 x (hs _ (hr.2 j).2.2.2.2.2.2.1.1)
  have tR : ∀ j, ∃ f, Warp (sm.rG j).lo (sm.rG j).hi f ∧ ∀ t,
      x (d.wire (sm.rG j).out) t = x (d.wire sm.rst) (f t) := fun j =>
    buf_transport d _ _ (hr.2 j).2.2.2.2.2.2.2 x (hs _ (hr.2 j).2.2.2.2.2.2.2.1)
  obtain ⟨F, hF⟩ := Classical.axiomOfChoice tF
  obtain ⟨G, hG⟩ := Classical.axiomOfChoice tG
  obtain ⟨Q, hQ⟩ := Classical.axiomOfChoice tQ
  obtain ⟨R, hR⟩ := Classical.axiomOfChoice tR
  refine ⟨{
    c := fun j => x (d.wire (sm.lut j).out)
    pin := fun j p => x (d.wire (sm.pinG j p).out)
    q := fun j => x (d.wire (sm.fbG j).out)
    r := fun j => x (d.wire (sm.rG j).out)
    F := F
    G := fun j p => G (j, p)
    Q := Q
    wF := fun j => (hF j).1
    wG := fun j p => (hG (j, p)).1
    wQ := fun j => (hQ j).1
    loF1 := fun j => lo1 _ (hr.2 j).1
    loG1 := fun j p => by
      cases p
      · exact lo1 _ (hr.2 j).2.2.2.2.1.1
      · exact lo1 _ (hr.2 j).2.2.2.2.2.1.1
    loQ1 := fun j => lo1 _ (hr.2 j).2.2.2.2.2.2.1.1
    hc := fun j t => (hF j).2 t
    hpin := fun j p t => (hG (j, p)).2 t
    hq := fun j t => (hQ j).2 t
    r0 := fun j => by
      show x (d.wire (sm.rG j).out) 0 = true
      rw [(hR j).2 0, hrst]
      have := (hR j).1.le_late 0
      simp only [decide_eq_true_eq]; omega
    ranti := fun j a b hab hb => by
      show x (d.wire (sm.rG j).out) a = true
      have hb' : x (d.wire (sm.rG j).out) b = true := hb
      rw [(hR j).2, hrst] at hb' ⊢
      simp only [decide_eq_true_eq] at hb' ⊢
      have := (hR j).1.mono a b hab; omega }, fun j t => rfl, ?_⟩
  intro j s hs
  show x (d.wire (sm.rG j).out) s = false
  rw [(hR j).2, hrst]
  have := (hR j).1.early_le s
  simp only [decide_eq_false_iff_not]; omega

/-- **Soundness on the parsed design.** -/
theorem design_safe {N : Nat} (d : Design) (net : MNet N) (sm : SMap N) (hr : Recog d net sm)
    (hP : net.Pairing) (hR : Race net sm.bands)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ M : Nat → Fin N → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧
      ∀ t j, x (d.wire (sm.lut j).out) t = ph (net.v j) (M t j) := by
  obtain ⟨bh, hc, _⟩ := design_beh d net sm hr x hsat h0 T hT hrst
  exact ⟨bh.M, fun j a b h => bh.M_mono b j a h, fun t j => by rw [← hc]; exact bh.safe hP hR t j⟩

/-! ## ring3 as parsed by `xaudit` -/

namespace Ring3D

/-- What `xaudit --emit-lean` printed for `designs/ring3.json` with
`designs/slow_corner.bands.json` (1 step = 10 ps: LUT [99,121] ps -> [9,13],
route [360,440] -> [36,44], own feedback [270,330] -> [27,33]). Wires: 2 rst,
7 c[0], 5 c[1], 3 c[2]; 0 is const 0. -/
def design : Design := ⟨17, [
    ⟨"st[0].u/I0", 1, 2, [3], 4, 36, 44⟩,
    ⟨"st[0].u/I1", 1, 2, [5], 6, 36, 44⟩,
    ⟨"st[0].u/I2", 1, 2, [7], 8, 27, 33⟩,
    ⟨"st[0].u/I3", 1, 2, [2], 9, 36, 44⟩,
    ⟨"st[0].u/O", 6, 18425070169785302962, [4, 6, 8, 9, 0, 0], 7, 9, 13⟩,
    ⟨"st[1].u/I0", 1, 2, [7], 10, 36, 44⟩,
    ⟨"st[1].u/I1", 1, 2, [3], 11, 36, 44⟩,
    ⟨"st[1].u/I2", 1, 2, [5], 12, 27, 33⟩,
    ⟨"st[1].u/I3", 1, 2, [2], 13, 36, 44⟩,
    ⟨"st[1].u/O", 6, 50103310370341042, [10, 11, 12, 13, 0, 0], 5, 9, 13⟩,
    ⟨"st[2].u/I0", 1, 2, [5], 14, 36, 44⟩,
    ⟨"st[2].u/I1", 1, 2, [7], 15, 36, 44⟩,
    ⟨"st[2].u/I2", 1, 2, [3], 16, 27, 33⟩,
    ⟨"st[2].u/I3", 1, 2, [2], 17, 36, 44⟩,
    ⟨"st[2].u/O", 6, 50103310370341042, [14, 15, 16, 17, 0, 0], 3, 9, 13⟩]⟩

def g (i : Nat) : GSpec := design.gates.getD i default

/-- Stage `j` is gates `5j .. 5j+4` (I0, I1, I2, I3, O). -/
def sm : SMap 3 where
  lut := fun j => g (5 * j.val + 4)
  pinG := fun j p => g (5 * j.val + if p then 1 else 0)
  fbG := fun j => g (5 * j.val + 2)
  rG := fun j => g (5 * j.val + 3)
  rst := 2

theorem recog : Recog design Ring3.net sm := by decide +kernel

theorem race : Race Ring3.net sm.bands := by decide +kernel

theorem bands_lo : ∀ j p, 45 ≤ sm.bands.loF j + sm.bands.loG j p := by decide +kernel

theorem bands_hi : ∀ j p, sm.bands.hiF j + sm.bands.hiG j p ≤ 57 := by decide +kernel

theorem rst_hi : ∀ j : Fin 3, (sm.rG j).hi = 44 := by decide +kernel

/-- **ring3, every behaviour, all time.** For every behaviour of the parsed
ring3 netlist (every LUT, route and feedback delay inside its band as a
monotone warp, any power-up) with reset released at step `T`: there is a hop
count `H` such that
* the three node wires (7 = c0, 5 = c1, 3 = c2) are fixed functions of `H`
  at every step (no X, no glitch, ever);
* `H` grows by at most one per 45 steps (450 ps), and by at least one per 57
  steps (570 ps) from `T + 44` on;
* hence each node toggles at most once per 135 steps and at least once per
  171 steps: period in [270, 342] steps = [2700, 3420] ps. -/
theorem ring3_design (x : Fin design.n → Sig) (hsat : Circuit.Sat (toCircuit (build design)) x)
    (h0 : ∀ t, x (design.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (design.wire 2) t = decide (t < T)) :
    ∃ H : Nat → Nat,
      (∀ t, x (design.wire 5) t = ph false ((H t + 2) / 3) ∧
            x (design.wire 7) t = ph true ((H t + 1) / 3) ∧
            x (design.wire 3) t = ph false (H t / 3)) ∧
      H 0 = 0 ∧
      (∀ t k, H (t + k * 45) ≤ H t + k) ∧
      (∀ t k, T + 44 ≤ t → H t + k ≤ H (t + k * 57)) := by
  obtain ⟨bh, hc, hrel⟩ := design_beh design Ring3.net sm recog x hsat h0 T hT hrst
  refine ⟨Ring3.H bh, fun t => ?_, Ring3.H_zero bh, fun t k => Ring3.hops_upper bh bands_lo t k,
    fun t k ht => Ring3.hops_lower bh bands_hi (R := T + 44)
      (fun j s hs => hrel j s (by rw [rst_hi]; exact hs)) t ht k⟩
  have s := Ring3.ring3_safe bh race t
  rw [hc 1 t, hc 0 t, hc 2 t] at s
  exact s

end Ring3D

end Formal.Core.XAudit.Events
