import Formal.Net.Ops

/-!
# C-8f: `bd_fork` (Dynamatic `fork`, and `lazy_fork` as bdc maps it)

`cells/rtl/bd_ctl.v`: `req_out = {N{req}}` (a wire fan-out), `ack = bd_ctree(ack_in)`
(a C-element tree), data is a wire fan-out (`emit.py _op_fork`).

Gate model `Fork a os` (SI gates, DI wires, binary, one tick = 1 ps):
* H_WIRE_DI: each branch's request wire is an unbounded inertial delay of
  `a.req`: it moves only to the value `a.req` had one tick earlier. The fork is
  NOT assumed isochronic: every branch has its own delay.
* H_CEL_SI + H_CTREE_ATOMIC: the acknowledge tree is one N-input C-element: its
  output moves only to a value every branch acknowledge had one tick earlier.
  (B's `CTree` is the per-gate argument; lumping the tree into one node is the
  named abstraction.)
* H_DATA_WIRE: every branch bus equals the input bus at every tick (data wire
  skew is pushed into the bundling obligation `Held` of the branch).

Proved: `fork_proto` (causal assume-guarantee, any N ≥ 1), `fork_data`
(the k-th branch offer is preceded by the k-th input offer, whose value it
carries), and `fork_op`: the network-level `OpProto` + `OpData` with token
equations `σ o k = σ a k` (fork DUPLICATES).
-/

namespace Formal.Net.Ops.Fork
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

structure Fork (a : Chan) (os : List Chan) : Prop where
  ne : os ≠ []
  wire : ∀ o ∈ os, ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t
  cel : ∀ t, a.ack (t + 1) ≠ a.ack t → ∀ o ∈ os, o.ack t = a.ack (t + 1)
  dat : ∀ o ∈ os, ∀ t, o.dat t = a.dat t
  initA : a.ack 0 = false
  initO : ∀ o ∈ os, o.req 0 = false

/-- Per-branch invariant: the branch lags the input by at most one phase. -/
def FInv (ar aa r k : Bool) : Bool :=
  if ar == aa then (r == ar && k == ar) else if ar then (!k || r) else (!r || k)

theorem finv_step : ∀ ar aa r k ar' aa' r' k' : Bool, FInv ar aa r k = true →
    (ar' ≠ ar → ar = aa) → (r' ≠ r → r' = ar) → (k' ≠ k → k ≠ r) → (aa' ≠ aa → k = aa') →
    FInv ar' aa' r' k' = true := by decide

theorem finv_recv : ∀ ar aa r k aa' : Bool, FInv ar aa r k = true → (aa' ≠ aa → k = aa') →
    aa' ≠ aa → aa ≠ ar := by decide

theorem finv_send : ∀ ar aa r k r' : Bool, FInv ar aa r k = true → (r' ≠ r → r' = ar) →
    r' ≠ r → r = k := by decide

theorem finv_hi_lo : ∀ aa k : Bool, FInv true aa false k = true → aa = false := by decide

theorem fcnt_step : ∀ (X Y : Nat) (ar aa r k ar' r' : Bool), FInv ar aa r k = true →
    X = Y + (if (ar && !r) = true then 1 else 0) → (ar' ≠ ar → ar = aa) → (r' ≠ r → r' = ar) →
    X + (if (!ar && ar') = true then 1 else 0) =
      Y + (if (!r && r') = true then 1 else 0) + (if (ar' && !r') = true then 1 else 0) := by
  intro X Y ar aa r k ar' r'
  cases ar <;> cases aa <;> cases r <;> cases k <;> cases ar' <;> cases r' <;> simp [FInv] <;> omega

variable {a : Chan} {os : List Chan}

/-- The per-branch invariant holds at every `t` whose past obeyed the protocol. -/
theorem fork_inv (F : Fork a os) (hra : a.req 0 = false) (hka : ∀ o ∈ os, o.ack 0 = false) :
    ∀ t, (∀ s, s < t → Rules a s ∧ ∀ o ∈ os, Rules o s) →
    ∀ o ∈ os, FInv (a.req t) (a.ack t) (o.req t) (o.ack t) = true := by
  intro t
  induction t with
  | zero =>
    intro _ o ho
    simp [FInv, hra, F.initA, F.initO o ho, hka o ho]
  | succ t ih =>
    intro hp o ho
    have h0 := ih (fun s hs => hp s (by omega)) o ho
    have ⟨⟨ha1, _⟩, hob⟩ := hp t (by omega)
    have ⟨_, ho2⟩ := hob o ho
    exact finv_step _ _ _ _ _ _ _ _ h0 ha1 (F.wire o ho t) ho2 (fun h => F.cel t h o ho)

/-- Causal assume-guarantee: the fork acknowledges its input and requests its
branches by the protocol at step `t`, given the protocol before `t`. -/
theorem fork_proto (F : Fork a os) (hra : a.req 0 = false) (hka : ∀ o ∈ os, o.ack 0 = false) :
    ∀ t, (∀ s, s < t → Rules a s ∧ ∀ o ∈ os, Rules o s) →
    RecvStep a t ∧ ∀ o ∈ os, SendStep o t := by
  intro t hp
  have hi := fork_inv F hra hka t hp
  refine ⟨fun h => ?_, fun o ho h => ?_⟩
  · obtain ⟨o, ho⟩ : ∃ o, o ∈ os := by
      cases hos : os with
      | nil => exact absurd hos F.ne
      | cons o _ => exact ⟨o, List.mem_cons_self ..⟩
    exact finv_recv _ _ _ _ _ (hi o ho) (fun h' => F.cel t h' o ho) h
  · exact finv_send _ _ _ _ _ (hi o ho) (F.wire o ho t) h

theorem proto_rules {c : Chan} (h : Protocol c) : ∀ s, Rules c s := fun s => h.2 s

/-- Token level: the k-th offer on a branch comes strictly after the k-th
offer on the input, and carries its value (given `Held` on the input). -/
theorem fork_data (F : Fork a os) (hpa : Protocol a) (hpo : ∀ o ∈ os, Protocol o)
    (hh : Held a) : ∀ o ∈ os, ∀ k r', OffAt o k r' →
    ∃ r, r < r' ∧ OffAt a k r ∧ o.dat (r' + 1) = a.dat (r + 1) := by
  intro o ho k r' hoff
  have prem : ∀ t, ∀ s, s < t → Rules a s ∧ ∀ o ∈ os, Rules o s :=
    fun _ s _ => ⟨hpa.2 s, fun o ho => (hpo o ho).2 s⟩
  have hinv : ∀ t, FInv (a.req t) (a.ack t) (o.req t) (o.ack t) = true :=
    fun t => fork_inv F hpa.1.1 (fun o ho => (hpo o ho).1.2) t (prem t) o ho
  -- count invariant
  have hcnt : ∀ t, cnt (riseB a.req) t =
      cnt (riseB o.req) t + (if (a.req t && !o.req t) = true then 1 else 0) := by
    intro t
    induction t with
    | zero => simp [cnt, hpa.1.1, F.initO o ho]
    | succ t ih =>
      simp only [cnt, riseB]
      exact fcnt_step _ _ _ _ _ _ _ _ (hinv t) ih (hpa.2 t).1 (F.wire o ho t)
  have hr0 : o.req r' = false := by have := hoff.1; simp [riseB] at this; exact this.1
  have hr1 : o.req (r' + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
  have har : a.req r' = true := by
    have := F.wire o ho r' (by rw [hr0, hr1]; decide); rw [← this, hr1]
  have haa : a.ack r' = false := by
    have := hinv r'; rw [har, hr0] at this; exact finv_hi_lo _ _ this
  have hc := hcnt r'
  rw [har, hr0, hoff.2] at hc
  obtain ⟨ra, k', hra, hoffa, hcr, hcf, _⟩ := open_offer hpa har
  have hk : k' = k := by simp at hc; omega
  subst hk
  have hcf' : cnt (fallB a.ack) (r' + 1) = k' := by simp [cnt, fallB, haa, hcf]
  refine ⟨ra, hra, hoffa, ?_⟩
  rw [F.dat o ho, held_at hpa hh hoffa (by omega) hcf']

/-! ## Network level -/

variable {C : Type}

/-- The fork's token equations: every branch carries the input's stream. -/
def forkEq (ca : C) (cos : List C) (σ : C → Nat → Nat) : Prop := ∀ c ∈ cos, ∀ k, σ c k = σ ca k

theorem fork_op (ch : C → Chan) (ca : C) (cos : List C) (F : Fork (ch ca) (cos.map ch)) :
    OpProto ch [ca] cos ∧ OpData ch [ca] cos (forkEq ca cos) := by
  have mem : ∀ c ∈ cos, ch c ∈ cos.map ch := fun c hc => List.mem_map_of_mem hc
  refine ⟨⟨fun t hi ho _ hp => ?_, ?_, ?_⟩, ?_⟩
  · have h := fork_proto F (hi ca (List.mem_singleton_self _)).1
      (fun o hom => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hom; exact (ho c hc).2) t
      (fun s hs => ⟨(hp s hs).1 ca (List.mem_singleton_self _), fun o hom => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hom; exact (hp s hs).2 c hc⟩)
    refine ⟨fun c hc => ?_, fun c hc => h.2 _ (mem c hc)⟩
    rw [List.mem_singleton.1 hc]; exact h.1
  · intro c hc; rw [List.mem_singleton.1 hc]; exact F.initA
  · intro c hc; exact F.initO _ (mem c hc)
  · intro hin hout c hc k r ho σ hag hE
    have ha := hin ca (List.mem_singleton_self _)
    obtain ⟨ra, hra, hoffa, hv⟩ := fork_data F ha.1
      (fun o hom => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hom; exact (hout c hc).1)
      ha.2 (ch c) (mem c hc) k r ho
    rw [hE c hc k, hag ca k ra hra hoffa, hv]

end Formal.Net.Ops.Fork
