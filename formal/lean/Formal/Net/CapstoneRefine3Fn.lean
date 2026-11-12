import Formal.Net.CapstoneRefine3Cert

/-!
# Probe C-8x3 (c): a relaxed data field from the physical netlist

C-8x2's relaxed field of a cell whose output `o` is sampled says: at every busy instant `t` of
`o`, the observed bus equals the cell function of the input buses at `t`. C-8x2 left it as a
hypothesis (H_CELLS_B) and named its three ingredients. Here they are composed:

1. `sampled_eq_zd` (C-8x, proved from the tcheck row + H_TXWIN): inside transaction `k` the
   observed bus is `zdBus runs data k`, the zero-delay value of the obligation netlist's run `k`;
2. **H_FN** (open, a functional check, not timing): `zdBus runs data k = fn (vin k)`: the netlist's
   zero-delay function, on the launch values `vin k` of run `k`, is the Ops cell function `fn`;
3. **H_LAUNCH** (input agreement at one instant): the launch values of run `k` are the input buses
   right after `o`'s `k`-th offer: `vin k = IN (r + 1)`.

* `field_of_sampled` (generic): 1 + 2 + 3 + stability of `IN` over the transaction ⇒ the field.
* `held_const`: a bundled channel that stays busy keeps its bus.
* `JoinH` / `ForkH`: the handshake halves of `JoinB` / `ForkB` (no data field);
  **`joinB_of_phys`**, **`forkB_of_phys`**: handshake half + protocol + bundled inputs + the
  output's tcheck certificate (DAG or cert row, as a `TxWin` + separation) + H_FN + H_LAUNCH ⇒ the
  full relaxed cell (`JoinB` / `ForkB`): the data field is DERIVED. Stability of the inputs over
  the output's transaction comes from 8w's handshake invariants `JInv` / `FInv` and the inputs'
  `Held`, so the input agreement is needed at the offer only.

Not done: plugging this into `gcd_hw_circuit_safe_phys4` (the derivation needs the protocol and
the inputs' `Held`, which the capstone obtains FROM H_CELLS_B: one more joint induction, with the
data field at step `t` inside it, would be needed), and the analogous steer/link/mux lemmas.
-/

namespace Formal.Net.CapstoneRefine
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.OpsBusy
open Formal.Net.CapstoneBundle (tx_of_jinv tx_of_finv)

/-- **The composing lemma (generic).** -/
theorem field_of_sampled {net : Netlist} (hwf : net.WF) {P : Chan} {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin P sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    (hinit : Init P) (hrecv : ∀ t, RecvStep P t)
    {α : Type} (fn : α → Nat) (vin : Nat → α) (IN : Nat → α)
    (H_FN : ∀ k, zdBus runs data k = fn (vin k))
    (H_LAUNCH : ∀ k r, OffAt P k r → vin k = IN (r + 1))
    (H_STABLE : ∀ r t, riseB P.req r = true → r < t →
      (∀ s, r < s → s ≤ t → inTx P s = true) → IN t = IN (r + 1)) :
    ∀ t, inTx P t = true → P.dat t = fn (IN t) := by
  intro t ht
  obtain ⟨k, r, ho, hr, hs⟩ := busy_cover hinit hrecv t ht
  rw [sampled_eq_zd hwf runs X hsep ho hr hs, H_FN k, H_LAUNCH k r ho,
    H_STABLE r t ho.1 hr hs]

/-- A bundled channel that stays busy on `[a, b]` keeps its bus. -/
theorem held_const {c : Chan} (hh : Held c) {a b : Nat} (hab : a ≤ b)
    (hb : ∀ s, a ≤ s → s ≤ b → inTx c s = true) : c.dat b = c.dat a := by
  have : ∀ d, a + d ≤ b → c.dat (a + d) = c.dat a := by
    intro d
    induction d with
    | zero => intro _; rfl
    | succ d ih =>
      intro hd
      rw [show a + (d + 1) = a + d + 1 by omega,
        hh _ (hb _ (by omega) (by omega)) (hb _ (by omega) (by omega)), ih (by omega)]
  have := this (b - a) (by omega)
  rwa [show a + (b - a) = b by omega] at this

/-! ## Join / compute -/

/-- The handshake half of `JoinB` (no data field). -/
structure JoinH (is : List Chan) (o : Chan) : Prop where
  ne : is ≠ []
  cel : ∀ t, o.req (t + 1) ≠ o.req t → ∀ i ∈ is, i.req t = o.req (t + 1)
  wire : ∀ i ∈ is, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  initO : o.req 0 = false
  initI : ∀ i ∈ is, i.ack 0 = false

theorem JoinH.toOld {is : List Chan} {o : Chan} (J : JoinH is o) (g : List Nat → Nat) :
    Join.Join g is (rel o (fun t => g (is.map (fun i => i.dat t)))) :=
  ⟨J.ne, J.cel, J.wire, fun _ => rfl, J.initO, J.initI⟩

/-- **The join's relaxed field, derived.** `X`/`hsep`: the output's tcheck row and H_TXWIN;
`vin k`: run `k`'s launch values; H_FN, H_LAUNCH as in the module doc. -/
theorem joinB_of_phys {g : List Nat → Nat} {is : List Chan} {o : Chan} (J : JoinH is o)
    (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i) (hh : ∀ i ∈ is, Held i)
    {net : Netlist} (hwf : net.WF) {sig : Nat → Nat → Trace}
    {data : List Nat} {R : Nat → Nat → Prop} (runs : ∀ k, Run net (sig k))
    (X : TxWin o sig data R)
    (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
    (vin : Nat → List Nat)
    (H_FN : ∀ k, zdBus runs data k = g (vin k))
    (H_LAUNCH : ∀ k r, OffAt o k r → vin k = is.map (fun i => i.dat (r + 1))) :
    JoinB g is o := by
  have Jo := J.toOld g
  have hinv : ∀ t, ∀ i ∈ is, Join.JInv (o.req t) (o.ack t) (i.req t) (i.ack t) = true :=
    fun t => Join.join_inv Jo hpo.1.2 (fun i hi => (hpi i hi).1.1) t
      (fun s _ => ⟨hpo.2 s, fun i hi => (hpi i hi).2 s⟩)
  refine ⟨J.ne, J.cel, J.wire, ?_, J.initO, J.initI⟩
  exact field_of_sampled hwf runs X hsep hpo.1 (fun t => (hpo.2 t).2) g vin
    (fun t => is.map (fun i => i.dat t)) H_FN H_LAUNCH (fun r t _ hr hs => by
      apply List.map_congr_left
      intro i hi
      exact held_const (hh i hi) (by omega) (fun s h1 h2 =>
        tx_of_jinv (hinv s i hi) (hs s (by omega) h2)))

/-! ## Fork -/

/-- The handshake half of `ForkB`. -/
structure ForkH (a : Chan) (os : List Chan) : Prop where
  ne : os ≠ []
  wire : ∀ o ∈ os, ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t
  cel : ∀ t, a.ack (t + 1) ≠ a.ack t → ∀ o ∈ os, o.ack t = a.ack (t + 1)
  initA : a.ack 0 = false
  initO : ∀ o ∈ os, o.req 0 = false

theorem ForkH.toOld {a : Chan} {os : List Chan} (F : ForkH a os) :
    Fork.Fork a (os.map (fun o => rel o a.dat)) := by
  refine ⟨?_, ?_, ?_, ?_, F.initA, ?_⟩
  · intro h; apply F.ne; cases os with
    | nil => rfl
    | cons _ _ => simp at h
  · intro o ho t h; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; exact F.wire c hc t h
  · intro t h o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; exact F.cel t h c hc
  · intro o ho t; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; rfl
  · intro o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho; exact F.initO c hc

/-- Per-branch physical data: the branch's tcheck row (H_TXWIN + separation), H_FN (the
branch netlist's zero-delay value is `fn` of the launch value: a wire, `fn = id`, for a fork
branch; the data projection for a steer branch) and H_LAUNCH (the launch value is the input bus
right after the branch's offer). -/
inductive BranchPhys (fn : Nat → Nat) (a o : Chan) : Prop
  | mk (net : Netlist) (hwf : net.WF) (sig : Nat → Nat → Trace) (data : List Nat)
      (R : Nat → Nat → Prop) (runs : ∀ k, Run net (sig k)) (X : TxWin o sig data R)
      (hsep : ∀ k v, R k v → ∀ d ∈ data, ∀ s, changes (sig k d) s → s ≤ v)
      (vin : Nat → Nat) (H_FN : ∀ k, zdBus runs data k = fn (vin k))
      (H_LAUNCH : ∀ k r, OffAt o k r → vin k = a.dat (r + 1)) : BranchPhys fn a o

/-- **The fork's relaxed field, derived** (per branch). -/
theorem forkB_of_phys {a : Chan} {os : List Chan} (F : ForkH a os) (hpa : Protocol a)
    (hpo : ∀ o ∈ os, Protocol o) (hh : Held a) (hph : ∀ o ∈ os, BranchPhys id a o) :
    ForkB a os := by
  have Fo := F.toOld
  have hinv : ∀ t, ∀ o ∈ os, Fork.FInv (a.req t) (a.ack t) (o.req t) (o.ack t) = true := by
    intro t o ho
    exact Fork.fork_inv Fo hpa.1.1
      (fun o' ho' => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hpo c hc).1.2) t
      (fun s _ => ⟨hpa.2 s, fun o' ho' => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho'; exact (hpo c hc).2 s⟩)
      (rel o a.dat) (List.mem_map_of_mem ho)
  refine ⟨F.ne, F.wire, F.cel, fun o ho => ?_, F.initA, F.initO⟩
  obtain ⟨net, hwf, sig, data, R, runs, X, hsep, vin, H_FN, H_LAUNCH⟩ := hph o ho
  exact field_of_sampled hwf runs X hsep (hpo o ho).1 (fun t => ((hpo o ho).2 t).2) id vin
    (fun t => a.dat t) H_FN H_LAUNCH (fun r t _ hr hs =>
      held_const hh (by omega) (fun s h1 h2 => tx_of_finv (hinv s o ho) (hs s (by omega) h2)))

/-! ## Steer -/

/-- The handshake half of `SteerB`. -/
structure SteerH (sel : Nat → Bool) (j : Chan) (out : Bool → Chan) : Prop where
  lut : ∀ b t, (out b).req (t + 1) ≠ (out b).req t →
    (out b).req (t + 1) = (j.req t && (sel (j.dat t) == b))
  orr : ∀ t, j.ack (t + 1) ≠ j.ack t → j.ack (t + 1) = ((out true).ack t || (out false).ack t)
  initJ : j.ack 0 = false
  initO : ∀ b, (out b).req 0 = false

theorem SteerH.toOld {sel : Nat → Bool} {j : Chan} {out : Bool → Chan} (S : SteerH sel j out)
    (f : Nat → Nat) : Steer.Steer sel f j (fun b => rel (out b) (fun t => f (j.dat t))) :=
  ⟨S.lut, S.orr, fun _ _ => rfl, S.initJ, S.initO⟩

/-- **The steer's relaxed field, derived** (per branch; `fn = f`, the data projection). -/
theorem steerB_of_phys {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : SteerH sel j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b)) (hh : Held j)
    (hph : ∀ b, BranchPhys f j (out b)) : SteerB sel f j out := by
  have So := S.toOld f
  have hinv := fun t => Steer.steer_inv So hpj.1.1 (fun b => (hpo b).1.2) hh t
    (fun s _ => ⟨hpj.2 s, fun b => (hpo b).2 s⟩)
  refine ⟨S.lut, S.orr, fun b => ?_, S.initJ, S.initO⟩
  have tx : ∀ u, inTx (out b) u = true → inTx j u = true := by
    intro u hu
    apply CapstoneBundle.tx_of_sinv (hinv u) b
    cases b <;> simpa [inTx, rel] using hu
  obtain ⟨net, hwf, sig, data, R, runs, X, hsep, vin, H_FN, H_LAUNCH⟩ := hph b
  exact field_of_sampled hwf runs X hsep (hpo b).1 (fun t => ((hpo b).2 t).2) f vin
    (fun t => j.dat t) H_FN H_LAUNCH (fun r t _ hr hs =>
      held_const hh (by omega) (fun s h1 h2 => tx s (hs s (by omega) h2)))

end Formal.Net.CapstoneRefine
