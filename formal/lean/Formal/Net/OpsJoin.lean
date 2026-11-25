import Formal.Net.Ops

/-!
# C-8f: `bd_join` and the compute units (Dynamatic `join`, `addi`, `subi`,
`cmpi`, `andi`, `ori`, `shrsi`, `select`, ..., and the join half of `cond_br`)

`cells/rtl/bd_ctl.v`: `req = bd_ctree(req_in)` (a C-element tree),
`ack_out = {N{ack}}` (a wire fan-out). `bdc/compute.py`: every compute unit is
"both operands must have arrived -> bd_join; data through combinational
logic; ack straight back through the join; req_out = delta(req_in)". bdc's
`cond_br` is `bd_join(cond, data)` then `bd_steer`. `select` is a 3-input
compute unit (all three operands consumed).

Gate model `Join g is o` (inputs `is`, output `o`, combinational function `g`
of the input buses, in input order):
* H_CEL_SI + H_CTREE_ATOMIC: the request tree is one C-element: `o.req` moves
  only to a value every input request had one tick earlier. A compute unit's
  matched delay (`uor` + `bd_delay`) after the tree is lumped into the same
  node (unbounded inertial delay; H_DELAY_LUMPED).
* H_WIRE_DI: each input's acknowledge wire is an unbounded inertial delay of
  `o.ack`.
* H_DATA_COMB: `o.dat t = g (input buses at t)`: the logic is modelled with zero
  delay; its real delay is what `Held o` (the bundling obligation on the unit's
  OUTPUT channel) has to cover: H_COMPUTE_DELAY in the notes.

Proved: `join_proto` (causal assume-guarantee, any N ≥ 1), `join_data` (the
k-th output offer comes strictly after the k-th offer of EVERY input, whose
values it combines), `join_op` with token equations
`σ o k = g [σ i₁ k, ..., σ iₙ k]` (join PAIRS, compute APPLIES).
-/

namespace Formal.Net.Ops.Join
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

structure Join (g : List Nat → Nat) (is : List Chan) (o : Chan) : Prop where
  ne : is ≠ []
  cel : ∀ t, o.req (t + 1) ≠ o.req t → ∀ i ∈ is, i.req t = o.req (t + 1)
  wire : ∀ i ∈ is, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  dat : ∀ t, o.dat t = g (is.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ is, i.ack 0 = false

/-- Per-input invariant, by the output's phase. -/
def JInv (or oa r k : Bool) : Bool :=
  match or, oa with
  | false, false => !(r && k)
  | true, false => r && !k
  | true, true => r || k
  | false, true => !r && k

theorem jinv_step : ∀ or oa r k or' oa' r' k' : Bool, JInv or oa r k = true →
    (or' ≠ or → r = or') → (oa' ≠ oa → oa ≠ or) → (k' ≠ k → k' = oa) → (r' ≠ r → r = k) →
    JInv or' oa' r' k' = true := by decide

theorem jinv_send : ∀ or oa r k or' : Bool, JInv or oa r k = true → (or' ≠ or → r = or') →
    or' ≠ or → or = oa := by decide

theorem jinv_recv : ∀ or oa r k k' : Bool, JInv or oa r k = true → (k' ≠ k → k' = oa) →
    k' ≠ k → k ≠ r := by decide

theorem jinv_off : ∀ oa k : Bool, JInv false oa true k = true → oa = false ∧ k = false := by
  decide

theorem jcnt_step : ∀ (X Y : Nat) (or oa r k or' oa' r' : Bool), JInv or oa r k = true →
    X = Y + (if (!or && !oa && r) = true then 1 else 0) →
    (or' ≠ or → r = or') → (oa' ≠ oa → oa ≠ or) → (r' ≠ r → r = k) →
    X + (if (!r && r') = true then 1 else 0) =
      Y + (if (!or && or') = true then 1 else 0) + (if (!or' && !oa' && r') = true then 1 else 0) := by
  intro X Y or oa r k or' oa' r'
  cases or <;> cases oa <;> cases r <;> cases k <;> cases or' <;> cases oa' <;> cases r' <;>
    simp [JInv] <;> omega

variable {g : List Nat → Nat} {is : List Chan} {o : Chan}

theorem join_inv (J : Join g is o) (hro : o.ack 0 = false) (hri : ∀ i ∈ is, i.req 0 = false) :
    ∀ t, (∀ s, s < t → Rules o s ∧ ∀ i ∈ is, Rules i s) →
    ∀ i ∈ is, JInv (o.req t) (o.ack t) (i.req t) (i.ack t) = true := by
  intro t
  induction t with
  | zero =>
    intro _ i hi
    simp [JInv, hro, J.initO, J.initI i hi, hri i hi]
  | succ t ih =>
    intro hp i hi
    have h0 := ih (fun s hs => hp s (by omega)) i hi
    have ⟨⟨_, ho2⟩, hib⟩ := hp t (by omega)
    have ⟨hi1, _⟩ := hib i hi
    exact jinv_step _ _ _ _ _ _ _ _ h0 (fun h => J.cel t h i hi) ho2 (J.wire i hi t) hi1

theorem join_proto (J : Join g is o) (hro : o.ack 0 = false) (hri : ∀ i ∈ is, i.req 0 = false) :
    ∀ t, (∀ s, s < t → Rules o s ∧ ∀ i ∈ is, Rules i s) →
    SendStep o t ∧ ∀ i ∈ is, RecvStep i t := by
  intro t hp
  have hv := join_inv J hro hri t hp
  refine ⟨fun h => ?_, fun i hi h => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, i ∈ is := by
      cases his : is with
      | nil => exact absurd his J.ne
      | cons i _ => exact ⟨i, List.mem_cons_self ..⟩
    exact jinv_send _ _ _ _ _ (hv i hi) (fun h' => J.cel t h' i hi) h
  · exact jinv_recv _ _ _ _ _ (hv i hi) (J.wire i hi t) h

/-- Token level: at the k-th output offer `r'`, every input `i` has its k-th
offer at some `rᵢ < r'`, still open, so its bus at `r'+1` is its offer value. -/
theorem join_data (J : Join g is o) (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i)
    (hh : ∀ i ∈ is, Held i) : ∀ k r', OffAt o k r' →
    ∀ i ∈ is, ∃ r, r < r' ∧ OffAt i k r ∧ i.dat (r' + 1) = i.dat (r + 1) := by
  intro k r' hoff i hi
  have hinv : ∀ t, JInv (o.req t) (o.ack t) (i.req t) (i.ack t) = true :=
    fun t => join_inv J hpo.1.2 (fun i hi => (hpi i hi).1.1) t
      (fun s _ => ⟨hpo.2 s, fun i hi => (hpi i hi).2 s⟩) i hi
  have hcnt : ∀ t, cnt (riseB i.req) t =
      cnt (riseB o.req) t + (if (!o.req t && !o.ack t && i.req t) = true then 1 else 0) := by
    intro t
    induction t with
    | zero => simp [cnt, (hpi i hi).1.1]
    | succ t ih =>
      simp only [cnt, riseB]
      exact jcnt_step _ _ _ _ _ _ _ _ _ (hinv t) ih (fun h => J.cel t h i hi) (hpo.2 t).2
        ((hpi i hi).2 t).1
  have hr0 : o.req r' = false := by have := hoff.1; simp [riseB] at this; exact this.1
  have hr1 : o.req (r' + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
  have hir : i.req r' = true := by
    have := J.cel r' (by rw [hr0, hr1]; decide) i hi; rw [this, hr1]
  have hv := hinv r'; rw [hr0, hir] at hv
  obtain ⟨hoa, hik⟩ := jinv_off _ _ hv
  have hc := hcnt r'
  rw [hr0, hoa, hir, hoff.2] at hc
  obtain ⟨ra, k', hra, hoffa, hcr, hcf, _⟩ := open_offer (hpi i hi) hir
  have hk : k' = k := by simp at hc; omega
  subst hk
  have hcf' : cnt (fallB i.ack) (r' + 1) = k' := by simp [cnt, fallB, hik, hcf]
  exact ⟨ra, hra, hoffa, held_at (hpi i hi) (hh i hi) hoffa (by omega) hcf'⟩

/-! ## Network level -/

variable {C : Type}

/-- The join's token equations: the k-th output token is `g` of the k-th
token of every input. -/
def joinEq (g : List Nat → Nat) (cis : List C) (co : C) (σ : C → Nat → Nat) : Prop :=
  ∀ k, σ co k = g (cis.map (fun c => σ c k))

theorem join_op (ch : C → Chan) (cis : List C) (co : C) (J : Join g (cis.map ch) (ch co)) :
    OpProto ch cis [co] ∧ OpData ch cis [co] (joinEq g cis co) := by
  have mem : ∀ c ∈ cis, ch c ∈ cis.map ch := fun c hc => List.mem_map_of_mem hc
  refine ⟨⟨fun t hi ho _ hp => ?_, ?_, ?_⟩, ?_⟩
  · have h := join_proto J (ho co (List.mem_singleton_self _)).2
      (fun i him => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 him; exact (hi c hc).1) t
      (fun s hs => ⟨(hp s hs).2 co (List.mem_singleton_self _), fun i him => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 him; exact (hp s hs).1 c hc⟩)
    refine ⟨fun c hc => h.2 _ (mem c hc), fun c hc => ?_⟩
    rw [List.mem_singleton.1 hc]; exact h.1
  · intro c hc; exact J.initI _ (mem c hc)
  · intro c hc; rw [List.mem_singleton.1 hc]; exact J.initO
  · intro hin hout c hc k r ho σ hag hE
    rw [List.mem_singleton.1 hc] at ho ⊢
    have hpo := (hout co (List.mem_singleton_self _)).1
    have hd := join_data J hpo
      (fun i him => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 him; exact (hin c hc).1)
      (fun i him => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 him; exact (hin c hc).2) k r ho
    rw [hE k, J.dat, List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    obtain ⟨ra, hra, hoffa, hv⟩ := hd (ch c) (mem c hc)
    simp only [Function.comp]
    rw [hag c k ra hra hoffa, hv]

end Formal.Net.Ops.Join
