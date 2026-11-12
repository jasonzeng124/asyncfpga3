import Formal.Net.OpsBusy2

/-!
# Probe C-8x3: bounded structural bundling, the arbiter stage, and the joint time induction

* `forkB_heldT`, `joinB_heldT`, `steerB_heldT`, `linkB_heldT`: C-8x2's `*B_held` at ONE step
  `t`, from the protocol on the steps `≤ t` and the inputs' `Held` on the steps `≤ t` (the steer:
  its select on `≤ t`; the others: their inputs at `t` only).
* **`amergeB_heldT` / `amergeB_held`** (the missing piece (b) of C-8x2): on the relaxed model an
  arbiter stage's output is bundled when its inputs are. Two new facts about 8j's reachable set
  `atbl` (kernel `decide`): in every busy state of the output the input named by the index bit
  `won = g2 ∨ A2` is itself mid-transaction (`amerge_busy`), and `won` does not move across a
  step that starts and ends with the output busy (`amerge_won_stable`).
* `StructK2` (= `StructK` plus `amerge`), **`cellB_heldT`**: per operator, bounded.
* **`net_joint`** (any network): operators meeting `OpProtoT` plus a rule that gives `Held` at
  step `t` from the protocol up to `t` and `Held` before `t` ⇒ every channel obeys the protocol
  AND is bundled. One strong induction on time; neither is assumed.
-/

namespace Formal.Net.OpsBusy2
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.CapstoneBundle (tx_of_jinv tx_of_finv tx_of_sinv)

/-! ## The joint induction (any network) -/

theorem net_joint {C O : Type} (N : Net C O) (ch : C → Chan)
    (hop : ∀ o, OpProtoT ch (N.ins o) (N.outs o))
    (hheld : ∀ t, (∀ c, Init (ch c)) → (∀ c s, s ≤ t → Rules (ch c) s) →
      (∀ c s, s < t → HeldStep (ch c) s) → ∀ c, HeldStep (ch c) t) :
    (∀ c, Protocol (ch c)) ∧ (∀ c, Held (ch c)) := by
  have hinit : ∀ c, Init (ch c) := fun c =>
    ⟨(hop (N.prod c)).initOut c ((N.prod_iff c _).2 rfl),
     (hop (N.cons c)).initIn c ((N.cons_iff c _).2 rfl)⟩
  have key : ∀ t, (∀ c, Rules (ch c) t) ∧ (∀ c, HeldStep (ch c) t) := by
    intro t
    induction t using Nat.strongRecOn with
    | _ t ih =>
      have prem : ∀ o, ∀ s, s < t → (∀ c ∈ N.ins o, Rules (ch c) s) ∧
          (∀ c ∈ N.outs o, Rules (ch c) s) :=
        fun o s hs => ⟨fun c _ => (ih s hs).1 c, fun c _ => (ih s hs).1 c⟩
      have hto : ∀ c, HeldTo (ch c) t := fun c s hs => (ih s hs).2 c
      have R : ∀ c, Rules (ch c) t := fun c =>
        ⟨((hop (N.prod c)).ag t (fun c _ => hinit c) (fun c _ => hinit c) (fun c _ => hto c)
            (prem _)).2 c ((N.prod_iff c _).2 rfl),
         ((hop (N.cons c)).ag t (fun c _ => hinit c) (fun c _ => hinit c) (fun c _ => hto c)
            (prem _)).1 c ((N.cons_iff c _).2 rfl)⟩
      refine ⟨R, hheld t hinit (fun c s hs => ?_) (fun c s hs => (ih s hs).2 c)⟩
      rcases Nat.lt_or_eq_of_le hs with h | h
      · exact (ih s h).1 c
      · rw [h]; exact R c
  exact ⟨fun c => ⟨hinit c, fun t => (key t).1 c⟩, fun c t => (key t).2 c⟩

/-! ## Bounded structural bundling -/

theorem forkB_heldT {a : Chan} {os : List Chan} (B : ForkB a os) (hia : Init a)
    (hio : ∀ o ∈ os, Init o) (t : Nat) (hp : ∀ s, s ≤ t → Rules a s ∧ ∀ o ∈ os, Rules o s)
    (hh : HeldStep a t) : ∀ o ∈ os, HeldStep o t := by
  have F := B.toOld
  have hinv : ∀ u, u ≤ t + 1 → ∀ o ∈ os,
      Fork.FInv (a.req u) (a.ack u) (o.req u) (o.ack u) = true := by
    intro u hu o ho
    exact Fork.fork_inv F hia.1
      (fun o' ho' => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hio c hc).2) u
      (fun s hs => ⟨(hp s (by omega)).1, fun o' ho' => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hp s (by omega)).2 c hc⟩)
      (rel o a.dat) (List.mem_map_of_mem ho)
  intro o ho h0 h1
  rw [B.dat o ho t h0, B.dat o ho (t + 1) h1]
  exact hh (tx_of_finv (hinv t (by omega) o ho) h0) (tx_of_finv (hinv (t + 1) (by omega) o ho) h1)

theorem joinB_heldT {g : List Nat → Nat} {is : List Chan} {o : Chan} (B : JoinB g is o)
    (hio : Init o) (hii : ∀ i ∈ is, Init i) (t : Nat)
    (hp : ∀ s, s ≤ t → Rules o s ∧ ∀ i ∈ is, Rules i s) (hh : ∀ i ∈ is, HeldStep i t) :
    HeldStep o t := by
  have J := B.toOld
  have hinv : ∀ u, u ≤ t + 1 → ∀ i ∈ is, Join.JInv (o.req u) (o.ack u) (i.req u) (i.ack u) = true :=
    fun u hu => Join.join_inv J hio.2 (fun i hi => (hii i hi).1) u
      (fun s hs => ⟨(hp s (by omega)).1, fun i hi => (hp s (by omega)).2 i hi⟩)
  intro h0 h1
  rw [B.dat t h0, B.dat (t + 1) h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hh i hi (tx_of_jinv (hinv t (by omega) i hi) h0) (tx_of_jinv (hinv (t + 1) (by omega) i hi) h1)

theorem steerB_heldT {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (B : SteerB sel f j out) (hij : Init j) (hio : ∀ b, Init (out b)) (t : Nat)
    (hp : ∀ s, s ≤ t → Rules j s ∧ ∀ b, Rules (out b) s) (hh : HeldTo j (t + 1)) :
    ∀ b, HeldStep (out b) t := by
  have S := B.toOld
  have hinv := fun u (hu : u ≤ t + 1) => steer_invT S hij.1 (fun b => (hio b).2) u
    (heldTo_mono hh hu) (fun s hs => ⟨(hp s (by omega)).1, fun b => (hp s (by omega)).2 b⟩)
  intro b h0 h1
  rw [B.dat b t h0, B.dat b (t + 1) h1]
  have tx : ∀ u, u ≤ t + 1 → inTx (out b) u = true → inTx j u = true := by
    intro u hu h
    apply tx_of_sinv (hinv u hu) b
    cases b <;> simpa [inTx, rel] using h
  exact congrArg f (hh t (by omega) (tx t (by omega) h0) (tx (t + 1) (by omega) h1))

section link
open Formal.Net.Ops.Link
variable {i o : Chan} {c : Trace}

theorem link_stepT (L : Link i o c) (hi : i.req 0 = false) (ho : o.ack 0 = false) (t : Nat)
    (hp : ∀ s, s ≤ t → SendStep i s ∧ RecvStep o s) :
    ∃ d q, ltbl.contains (lst i o c t d q) = true ∧
      cnt (riseB o.req) t + 1 = cnt (fallB i.ack) t + d ∧
      cnt (riseB i.ack) t + 1 = cnt (fallB o.ack) t + q ∧
      LConcl (lst i o c t d q) (i.req (t + 1)) (i.ack (t + 1)) (c (t + 1)) (o.req (t + 1))
        (o.ack (t + 1)) := by
  obtain ⟨d, q, hm, h1, h2⟩ := link_inv L hi ho t (fun s hs => hp s (by omega))
  exact ⟨d, q, hm, h1, h2, link_closed _ (lmem hm) _ (hp t (by omega)).1 _ (hp t (by omega)).2
    _ (L.H_CEL_SI t) _ (L.H_ACK_DI t) _ (L.H_REQ_DI t)⟩

theorem linkB_heldT (B : LinkB i o c) (hii : Init i) (hio : Init o) (t : Nat)
    (hp : ∀ s, s ≤ t → Rules i s ∧ Rules o s) (hh : HeldStep i t) : HeldStep o t := by
  have L := B.toOld
  intro h0 h1
  obtain ⟨d, q, _, _, _, K⟩ := link_stepT L hii.1 hio.2 t
    (fun s hs => ⟨(hp s hs).1.1, (hp s hs).2.2⟩)
  have KH := K.2.2.2.2
  simp only [lst, rel_req, rel_ack] at KH
  cases hc : c (t + 1)
  · exact B.H_LATCH_HOLD_B t hc h0 h1
  · obtain ⟨hct, ht0, ht1⟩ := KH (by simpa [inTx] using h0) (by simpa [inTx] using h1) hc
    rw [B.H_LATCH_OPEN_B _ hc h1, B.H_LATCH_OPEN_B _ hct h0]
    exact hh (by simpa [inTx] using ht0) (by simpa [inTx] using ht1)

end link

/-! ## The arbiter stage (piece (b)) -/

section amerge
open Formal.Net.Ops.CM

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
/-- In every reachable state with the output busy, the input named by `won` is busy. -/
theorem amerge_busy : ∀ e ∈ atbl, (e.zr || e.za) = true →
    (if (e.g2 || e.ya) then (e.yr || e.ya) else (e.xr || e.xa)) = true := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
/-- Across a step that starts and ends with the output busy, `won` does not move. -/
theorem amerge_won_stable : ∀ e ∈ atbl,
    ∀ xr : Bool, (xr ≠ e.xr → e.xr = e.xa) →
    ∀ yr : Bool, (yr ≠ e.yr → e.yr = e.ya) →
    ∀ za : Bool, (za ≠ e.za → e.za ≠ e.zr) →
    ∀ g1 : Bool, (g1 ≠ e.g1 → g1 = e.xr ∧ (g1 = true → e.g2 = false ∧ e.za = false)) →
    ∀ g2 : Bool, (g2 ≠ e.g2 → g2 = e.yr ∧ (g2 = true → e.g1 = false ∧ e.za = false)) →
    (g1 && g2) = false →
    ∀ zr : Bool, (zr ≠ e.zr → zr = (e.g1 || e.g2)) →
    (e.zr = false → zr = true → e.xa = false ∧ e.ya = false) →
    ∀ xa : Bool, (xa ≠ e.xa → e.g1 = xa ∧ e.za = xa) →
    ∀ ya : Bool, (ya ≠ e.ya → e.g2 = ya ∧ e.za = ya) →
    (e.zr || e.za) = true → (zr || za) = true → (g2 || ya) = (e.g2 || e.ya) := by
  decide +kernel

theorem amergeB_heldT {x y z : Chan} {g1 g2 : Trace} (B : AMergeB x y z g1 g2)
    (hx : x.req 0 = false) (hy : y.req 0 = false) (hz : z.ack 0 = false) (t : Nat)
    (hp : ∀ s, s ≤ t → SendStep x s ∧ SendStep y s ∧ RecvStep z s)
    (hhx : HeldStep x t) (hhy : HeldStep y t) : HeldStep z t := by
  have M := B.toOld
  obtain ⟨dx, dy, hm, -⟩ := amerge_inv M hx hy hz t (fun s hs => hp s (by omega))
  obtain ⟨dx', dy', hm', -⟩ := amerge_inv M hx hy hz (t + 1) (fun s hs => hp s (by omega))
  obtain ⟨sx, sy, rz⟩ := hp t (by omega)
  intro h0 h1
  have hst := amerge_won_stable _ (amem hm) (x.req (t + 1)) sx (y.req (t + 1)) sy (z.ack (t + 1))
    rz (g1 (t + 1)) (M.H_ARB1 t) (g2 (t + 1)) (M.H_ARB2 t) (M.H_ARB_EXCL (t + 1))
    (z.req (t + 1)) (M.zr t) (M.H_AMERGE_RTZ t) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t)
    h0 h1
  have hb0 := amerge_busy _ (amem hm) h0
  have hb1 := amerge_busy _ (amem hm') h1
  simp only [ast, rel_req, rel_ack] at hst hb0 hb1
  rw [B.dat t h0, B.dat (t + 1) h1, hst]
  simp only [hst] at hb1
  cases hw : (g2 t || y.ack t)
  · simp only [hw, Bool.false_eq_true, ↓reduceIte] at hb0 hb1 ⊢
    rw [hhx hb0 hb1]
  · simp only [hw, ↓reduceIte] at hb0 hb1 ⊢
    rw [hhy hb0 hb1]

/-- **`amergeB_held`**: on the relaxed model an arbiter stage's output is bundled when its two
inputs are (all-time form). -/
theorem amergeB_held {x y z : Chan} {g1 g2 : Trace} (B : AMergeB x y z g1 g2)
    (hpx : Protocol x) (hpy : Protocol y) (hpz : Protocol z) (hhx : Held x) (hhy : Held y) :
    Held z := fun t =>
  amergeB_heldT B hpx.1.1 hpy.1.1 hpz.1.2 t
    (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpz.2 s).2⟩) (hhx t) (hhy t)

end amerge

/-! ## Per operator -/

variable {n : Nat}

/-- Producer kinds whose output bundling follows from the inputs': C-8x2's `StructK` plus the
arbiter stage. -/
def StructK2 : K n → Bool
  | .forkG .. | .forkH .. | .join .. | .bjoin .. | .steerC .. | .steerD .. | .link .. | .src ..
  | .amerge .. => true
  | _ => false

/-- **Bounded structural bundling, per operator.** -/
theorem cellB_heldT (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : CellB ch sv k)
    (hs : StructK2 k = true) (t : Nat) (hi : ∀ c, Init (ch c))
    (hp : ∀ c s, s ≤ t → Rules (ch c) s)
    (hh : ∀ c ∈ k.insC, ∀ s, s ≤ t → HeldStep (ch c) s) :
    ∀ c ∈ k.outsC, HeldStep (ch c) t := by
  cases k with
  | forkG i os =>
    intro c hc'
    exact forkB_heldT hc (hi i) (fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hi c) t
      (fun s hs => ⟨hp i s hs, fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hp c s hs⟩)
      (hh i (by simp [K.insC]) t (by omega)) (ch c) (List.mem_map_of_mem hc')
  | forkH i os l h d hs' =>
    intro c hc'
    exact forkB_heldT hc (hi i) (fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hi c) t
      (fun s hs => ⟨hp i s hs, fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hp c s hs⟩)
      (hh i (by simp [K.insC]) t (by omega)) (ch c) (List.mem_map_of_mem hc')
  | join ins o e js jw =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    exact joinB_heldT hc (hi o) (fun i hi' => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi'; exact hi c) t
      (fun s hs => ⟨hp o s hs, fun i hi' => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi'; exact hp c s hs⟩)
      (fun i hi' => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi'; exact hh c hc t (by omega))
  | bjoin ins o ec ed =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    exact joinB_heldT hc (hi o) (fun i hi' => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi'; exact hi c) t
      (fun s hs => ⟨hp o s hs, fun i hi' => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi'; exact hp c s hs⟩)
      (fun i hi' => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi'; exact hh c hc t (by omega))
  | steerC j tt f =>
    intro c hc'
    have H := steerB_heldT hc (hi j) (fun b => hi _) t (fun s hs => ⟨hp j s hs, fun b => hp _ s hs⟩)
      (fun s hs => hh j (by simp [K.insC]) s (by omega))
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with e | e <;> subst e
    · exact H true
    · exact H false
  | steerD j tt f fd sw =>
    intro c hc'
    have H := steerB_heldT hc (hi j) (fun b => hi _) t (fun s hs => ⟨hp j s hs, fun b => hp _ s hs⟩)
      (fun s hs => hh j (by simp [K.insC]) s (by omega))
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with e | e <;> subst e
    · exact H true
    · exact H false
  | link i o =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    obtain ⟨cc, B⟩ := hc
    exact linkB_heldT B (hi i) (hi o) t (fun s hs => ⟨hp i s hs, hp o s hs⟩)
      (hh i (by simp [K.insC]) t (by omega))
  | src z which d =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    exact srcB_held hc t
  | amerge x y z w =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    obtain ⟨g1, g2, B⟩ := hc
    exact amergeB_heldT B (hi x).1 (hi y).1 (hi z).2 t
      (fun s hs => ⟨(hp x s hs).1, (hp y s hs).1, (hp z s hs).2⟩)
      (hh x (by simp [K.insC]) t (by omega)) (hh y (by simp [K.insC]) t (by omega))
  | mux => simp [StructK2] at hs
  | muxn => simp [StructK2] at hs
  | sink => simp [StructK2] at hs

end Formal.Net.OpsBusy2
