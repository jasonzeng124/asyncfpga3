import Formal.Net.OpsBusyLoc
import Formal.Net.CapstoneCutCells

/-!
# Probe C-8x2: relaxed cells: operator theorems, old-structure views, structural bundling

* `cell_proto_B`, `cell_op_B`: `OpProto` and `OpData` (with the capstone's token equations
  `Eqn`) for every relaxed cell kind.
* `rel`, `*.toOld`: a relaxed cell is an OLD cell once its output channels' buses are replaced
  (handshake wires unchanged) by the zero-delay value; used where only handshake facts are read.
* `amerge_data_upto_B`: C-8r's `amerge_data_upto` for a relaxed arbiter stage.
* `forkB_held`, `joinB_held`, `steerB_held`, `linkB_held`, `srcB_held`: bundled inputs ⇒ bundled
  output, on the relaxed fields.
-/

namespace Formal.Net.OpsBusy
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet
open Formal.Net.CapstoneBundle (tx_of_jinv tx_of_finv tx_of_sinv)

variable {n : Nat}

/-! ## Operator theorems -/

theorem cell_proto_B (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : CellB ch sv k)
    (hd : Dist k) (hj : Disj k) : OpProto ch k.insC k.outsC := by
  obtain ⟨D, hC, -, -⟩ := cellB_loc ch sv (fun _ _ => false) k hc hj
  apply proto_of_mod hj
  cases k with
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hC
    exact (CM.amerge_op _ x y z g1 g2 M).1
  | _ => exact (cell_op _ (fun _ _ => false) sv _ hC trivial hd).1

theorem cell_op_B (ch : Fin n → Chan) (om : Nat → Nat → Bool) (sv : Nat → Nat) (k : K n)
    (hc : CellB ch sv k) (hf : Forced ch om k) (hd : Dist k) (hj : Disj k) :
    OpProto ch k.insC k.outsC ∧ OpData ch k.insC k.outsC (Eqn ch om sv k) := by
  obtain ⟨D, hC, hF, hA⟩ := cellB_loc ch sv om k hc hj
  have h := cell_op (modC ch k.outsC D) om sv k hC (hF hf) hd
  rw [eqn_mod] at h
  exact ⟨proto_of_mod hj h.1, data_of_mod hj (fun hi ho => hA hi (fun c hc => (ho c hc).1)) h.2⟩

/-! ## Old-structure views (handshake wires unchanged) -/

/-- A channel with its bus replaced. -/
def rel (c : Chan) (d : Nat → Nat) : Chan := ⟨c.req, c.ack, d⟩

@[simp] theorem rel_req (c : Chan) (d : Nat → Nat) : (rel c d).req = c.req := rfl
@[simp] theorem rel_ack (c : Chan) (d : Nat → Nat) : (rel c d).ack = c.ack := rfl

theorem ForkB.toOld {a : Chan} {os : List Chan} (B : ForkB a os) :
    Fork.Fork a (os.map (fun o => rel o a.dat)) := by
  refine ⟨?_, ?_, ?_, ?_, B.initA, ?_⟩
  · intro h; apply B.ne; cases os with
    | nil => rfl
    | cons _ _ => simp at h
  · intro o ho t h; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; exact B.wire c hc t h
  · intro t h o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; exact B.cel t h c hc
  · intro o ho t; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; rfl
  · intro o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; exact B.initO c hc

theorem JoinB.toOld {g : List Nat → Nat} {is : List Chan} {o : Chan} (B : JoinB g is o) :
    Join.Join g is (rel o (fun t => g (is.map (fun i => i.dat t)))) :=
  ⟨B.ne, B.cel, B.wire, fun _ => rfl, B.initO, B.initI⟩

theorem SteerB.toOld {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (B : SteerB sel f j out) : Steer.Steer sel f j (fun b => rel (out b) (fun t => f (j.dat t))) :=
  ⟨B.lut, B.orr, fun _ _ => rfl, B.initJ, B.initO⟩

theorem LinkB.toOld {i o : Chan} {c : Trace} (B : LinkB i o c) :
    Link.Link i (rel o (latchD c i.dat o.dat)) c := by
  refine ⟨B.H_CEL_SI, B.H_ACK_DI, B.H_REQ_DI, ?_, ?_, B.ic, B.ii, B.io⟩
  · intro t h
    cases t with
    | zero => simp [rel, latchD, h]
    | succ t => simp [rel, latchD, h]
  · intro t h; simp [rel, latchD, h]

def amD (x y : Chan) (g2 : Trace) : Nat → Nat := fun t =>
  2 * (if (g2 t || y.ack t) then y.dat t else x.dat t) + Mux.b2n (g2 t || y.ack t)

theorem AMergeB.toOld {x y z : Chan} {g1 g2 : Trace} (B : AMergeB x y z g1 g2) :
    CM.AMerge x y (rel z (amD x y g2)) g1 g2 :=
  ⟨B.H_ARB1, B.H_ARB2, B.H_ARB_EXCL, B.zr, B.H_AMERGE_RTZ, B.xa, B.ya, fun _ => rfl, B.i1, B.i2,
    B.iz, B.ix, B.iy⟩

theorem AMergeB.winner_eq {x y z : Chan} {g1 g2 : Trace} (B : AMergeB x y z g1 g2) :
    CM.winner (rel z (amD x y g2)) = CM.winner z := by
  funext k
  exact winner_congr (c := z) (c' := rel z (amD x y g2)) rfl
    (fun r hr => (B.dat (r + 1) (busy_of_rise hr)).symm) k

/-! ## The arbiter's data spec up to a time, relaxed -/

theorem amerge_data_upto_mod (ch : Fin n → Chan) (cx cy cz : Fin n) (g1 g2 : Trace)
    (D : Fin n → Nat → Nat)
    (L : CM.AMerge (modC ch [cz] D cx) (modC ch [cz] D cy) (modC ch [cz] D cz) g1 g2)
    (A : AgrOut ch [cz] D) (hx : cx ≠ cz) (hy : cy ≠ cz) (ω : Nat → Bool)
    (hin : ∀ c ∈ [cx, cy], Protocol (ch c) ∧ Held (ch c))
    (hout : ∀ c ∈ [cz], Protocol (ch c) ∧ Held (ch c))
    {k r : Nat} (hoff : OffAt (ch cz) k r)
    (hF : ∀ j r', r' ≤ r → OffAt (ch cz) j r' → CM.winner (ch cz) j = ω j)
    (σ : Fin n → Nat → Nat) (hag : Agree ch σ r)
    (hE : Capstone.amergeOff (ch cz) ω cx cy cz σ) :
    σ cz k = (ch cz).dat (r + 1) := by
  have hx' : cx ∉ [cz] := by simpa using hx
  have hy' : cy ∉ [cz] := by simpa using hy
  have mz := List.mem_singleton_self cz
  have heldZ : Held (modC ch [cz] D cz) := by
    intro t h0 h1
    rw [modC_in mz, modC_in mz, A cz mz t h0, A cz mz (t + 1) h1]
    exact (hout cz mz).2 t h0 h1
  have h := Capstone.Cut.amerge_data_upto (modC ch [cz] D) cx cy cz g1 g2 L hx hy ω
    (fun c hc => by
      have hcz : c ∉ [cz] := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with e | e <;> rw [e] <;> assumption
      rw [modC_out hcz]; exact hin c hc)
    (fun c hc => by rw [List.mem_singleton.1 hc]; exact ⟨(hout cz mz).1, heldZ⟩)
    hoff
    (fun j r' hr' ho' => by
      rw [winner_congr (c := ch cz) (c' := modC ch [cz] D cz) rfl (fun u hu => by
        rw [modC_in mz]; exact A cz mz (u + 1) (busy_of_rise hu)) j]
      exact hF j r' hr' ho')
    σ
    (fun c' i r' hr' ho' => by
      have e := hag c' i r' hr' ho'
      by_cases hc' : c' ∈ [cz]
      · rw [modC_in hc', A c' hc' (r' + 1) (busy_of_off ho')]; exact e
      · rw [modC_out hc']; exact e)
    hE
  rw [modC_in mz, A cz mz (r + 1) (busy_of_off hoff)] at h
  exact h

theorem amerge_data_upto_B (ch : Fin n → Chan) (cx cy cz : Fin n) (g1 g2 : Trace)
    (M : AMergeB (ch cx) (ch cy) (ch cz) g1 g2) (hx : cx ≠ cz) (hy : cy ≠ cz) (ω : Nat → Bool)
    (hin : ∀ c ∈ [cx, cy], Protocol (ch c) ∧ Held (ch c))
    (hout : ∀ c ∈ [cz], Protocol (ch c) ∧ Held (ch c))
    {k r : Nat} (hoff : OffAt (ch cz) k r)
    (hF : ∀ j r', r' ≤ r → OffAt (ch cz) j r' → CM.winner (ch cz) j = ω j)
    (σ : Fin n → Nat → Nat) (hag : Agree ch σ r)
    (hE : Capstone.amergeOff (ch cz) ω cx cy cz σ) :
    σ cz k = (ch cz).dat (r + 1) := by
  have hx' : cx ∉ [cz] := by simpa using hx
  have hy' : cy ∉ [cz] := by simpa using hy
  obtain ⟨L, A⟩ := loc_amerge ch cx cy cz g1 g2 M hx' hy'
  exact amerge_data_upto_mod ch cx cy cz g1 g2 _ L A hx hy ω hin hout hoff hF σ hag hE

/-! ## Structural bundling on the relaxed model -/

theorem forkB_held {a : Chan} {os : List Chan} (B : ForkB a os) (hpa : Protocol a)
    (hpo : ∀ o ∈ os, Protocol o) (hh : Held a) : ∀ o ∈ os, Held o := by
  have F := B.toOld
  have hinv : ∀ t, ∀ o ∈ os, Fork.FInv (a.req t) (a.ack t) (o.req t) (o.ack t) = true := by
    intro t o ho
    exact Fork.fork_inv F hpa.1.1
      (fun o' ho' => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hpo c hc).1.2) t
      (fun s _ => ⟨hpa.2 s, fun o' ho' => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hpo c hc).2 s⟩)
      (rel o a.dat) (List.mem_map_of_mem ho)
  intro o ho t h0 h1
  rw [B.dat o ho t h0, B.dat o ho (t + 1) h1]
  exact hh t (tx_of_finv (hinv t o ho) h0) (tx_of_finv (hinv (t + 1) o ho) h1)

theorem joinB_held {g : List Nat → Nat} {is : List Chan} {o : Chan} (B : JoinB g is o)
    (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i) (hh : ∀ i ∈ is, Held i) : Held o := by
  have J := B.toOld
  have hinv : ∀ t, ∀ i ∈ is, Join.JInv (o.req t) (o.ack t) (i.req t) (i.ack t) = true :=
    fun t => Join.join_inv J hpo.1.2 (fun i hi => (hpi i hi).1.1) t
      (fun s _ => ⟨hpo.2 s, fun i hi => (hpi i hi).2 s⟩)
  intro t h0 h1
  rw [B.dat t h0, B.dat (t + 1) h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hh i hi t (tx_of_jinv (hinv t i hi) h0) (tx_of_jinv (hinv (t + 1) i hi) h1)

theorem steerB_held {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (B : SteerB sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b)) (hh : Held j) :
    ∀ b, Held (out b) := by
  have S := B.toOld
  have hinv := fun t => Steer.steer_inv S hpj.1.1 (fun b => (hpo b).1.2) hh t
    (fun s _ => ⟨hpj.2 s, fun b => (hpo b).2 s⟩)
  intro b t h0 h1
  rw [B.dat b t h0, B.dat b (t + 1) h1]
  have tx : ∀ u, inTx (out b) u = true → inTx j u = true := by
    intro u hu
    apply tx_of_sinv (hinv u) b
    cases b <;> simpa [inTx, rel] using hu
  exact congrArg f (hh t (tx t h0) (tx (t + 1) h1))

theorem linkB_held {i o : Chan} {c : Trace} (B : LinkB i o c) (hpi : Protocol i)
    (hpo : Protocol o) (hh : Held i) : Held o := by
  have L := B.toOld
  intro t h0 h1
  obtain ⟨d, q, _, _, _, K⟩ := Link.link_step L hpi hpo t
  have KH := K.2.2.2.2
  simp only [Link.lst, rel_req, rel_ack] at KH
  cases hc : c (t + 1)
  · exact B.H_LATCH_HOLD_B t hc h0 h1
  · obtain ⟨hct, ht0, ht1⟩ := KH (by simpa [inTx] using h0) (by simpa [inTx] using h1) hc
    rw [B.H_LATCH_OPEN_B _ hc h1, B.H_LATCH_OPEN_B _ hct h0]
    exact hh t (by simpa [inTx] using ht0) (by simpa [inTx] using ht1)

theorem srcB_held {z : Chan} {v : Nat} (B : SrcB z v) : Held z := by
  intro t h0 h1
  rw [B.dat t h0, B.dat (t + 1) h1]

/-- Producer kinds whose output bundling follows from the inputs' (`*B_held`). -/
def StructK : K n → Bool
  | .forkG .. | .forkH .. | .join .. | .bjoin .. | .steerC .. | .steerD .. | .link .. | .src .. =>
    true
  | _ => false

/-- **Structural bundling, per operator**: a relaxed cell of a structural kind with protocol on
its channels and bundled inputs has bundled outputs. -/
theorem cellB_held (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : CellB ch sv k)
    (hs : StructK k = true) (hp : ∀ c, Protocol (ch c)) (hh : ∀ c ∈ k.insC, Held (ch c)) :
    ∀ c ∈ k.outsC, Held (ch c) := by
  cases k with
  | forkG i os =>
    intro c hc'
    exact forkB_held hc (hp i) (fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hp c)
      (hh i (by simp [K.insC])) (ch c) (List.mem_map_of_mem hc')
  | forkH i os l h d hs' =>
    intro c hc'
    exact forkB_held hc (hp i) (fun o ho => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 ho; exact hp c)
      (hh i (by simp [K.insC])) (ch c) (List.mem_map_of_mem hc')
  | join ins o e js jw =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    exact joinB_held hc (hp o) (fun i hi => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi; exact hp c)
      (fun i hi => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi; exact hh c hc)
  | bjoin ins o ec ed =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    exact joinB_held hc (hp o) (fun i hi => by obtain ⟨c, _, rfl⟩ := List.mem_map.1 hi; exact hp c)
      (fun i hi => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi; exact hh c hc)
  | steerC j t f =>
    intro c hc'
    have H := steerB_held hc (hp j) (fun b => hp _) (hh j (by simp [K.insC]))
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with e | e <;> subst e
    · exact H true
    · exact H false
  | steerD j t f fd sw =>
    intro c hc'
    have H := steerB_held hc (hp j) (fun b => hp _) (hh j (by simp [K.insC]))
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with e | e <;> subst e
    · exact H true
    · exact H false
  | link i o =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    obtain ⟨cc, B⟩ := hc
    exact linkB_held B (hp i) (hp o) (hh i (by simp [K.insC]))
  | src z which d =>
    intro c hc'
    rw [List.mem_singleton.1 hc']
    exact srcB_held hc
  | mux => simp [StructK] at hs
  | muxn => simp [StructK] at hs
  | amerge => simp [StructK] at hs
  | sink => simp [StructK] at hs

end Formal.Net.OpsBusy
