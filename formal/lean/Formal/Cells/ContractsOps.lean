import Formal.Cells.Contracts
import Formal.Net.OpsFork
import Formal.Net.OpsJoin
import Formal.Net.OpsSteer
import Formal.Net.OpsMux
import Formal.Net.OpsMuxNOp
import Formal.Net.OpsCM
import Formal.Net.OpsLink
import Formal.Net.CapstoneSrc

/-!
# Probe Cc, part 2: the event data contract of every operator, in C's equations

For each operator C composes (C-8f/8j/8l: `forkEq`, `joinEq`, `linkEq`,
`srcEq`, sink, `steerEq`, `muxEq`, `muxnEq`, `amergeEq`), one structure
`…Ev` states the operator's guarantee in event form, over the ports' request
edges `ρ` and token values `v`:

* **causality**: the output token is offered strictly after the input tokens
  its value is made of (`ρ out (2k) > ρ in (2i)`; every cell path has positive
  delay);
* **value**: the output token value is the token equation applied to those
  input token values.

`…_det` proves that it implies `EarlierDet` for C's equation verbatim, and
`…_spec` (with `opSpec_of_ports`) that, on ports, it gives C's
`OpProto ∧ OpData`, i.e. exactly what C's `net_refines` consumes.

Where an equation reads earlier tokens of an input (the steer's and the
muxes' counters `cnt … k`), the contract also needs that input's request
edges to increase (`Strict`), which every `Port` gives (`Port.strictR`).
-/

namespace Formal.Cells.Contracts
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.Ops.Fork (forkEq) open Formal.Net.Ops.Join (joinEq)
open Formal.Net.Ops.Steer (steerEq) open Formal.Net.Ops.Mux (muxEq b2n)
open Formal.Net.Ops.MuxN (muxnEq) open Formal.Net.Ops.CM (amergeEq cnt_congr_lt)
open Formal.Net.Ops.Link (linkEq) open Formal.Net.Capstone (srcEq)

variable {C : Type} {ρ v : C → Nat → Nat}

/-! ## Fork (`bd_fork`, lazy_fork) -/

/-- Event contract of a fork: every branch's token `k` is offered after the
input's token `k`, with the same value (H_FORK_DATA is the value half). -/
structure ForkEv (ρ v : C → Nat → Nat) (ca : C) (cos : List C) : Prop where
  causal : ∀ c ∈ cos, ∀ k, ρ ca (2 * k) < ρ c (2 * k)
  value : ∀ c ∈ cos, ∀ k, v c k = v ca k

theorem fork_det {ca : C} {cos : List C} (F : ForkEv ρ v ca cos) : EarlierDet ρ v cos (forkEq ca cos) := by
  intro c hc k σ hag hE
  rw [hE c hc k, hag ca k (F.causal c hc k), F.value c hc k]

/-! ## Join and compute units (`bd_join` + logic + `bd_delay`) -/

/-- Event contract of a join / compute unit with output function `g`. -/
structure JoinEv (ρ v : C → Nat → Nat) (g : List Nat → Nat) (cis : List C) (co : C) : Prop where
  causal : ∀ c ∈ cis, ∀ k, ρ c (2 * k) < ρ co (2 * k)
  value : ∀ k, v co k = g (cis.map (fun c => v c k))

theorem join_det {g : List Nat → Nat} {cis : List C} {co : C} (J : JoinEv ρ v g cis co) :
    EarlierDet ρ v [co] (joinEq g cis co) := by
  intro c hc k σ hag hE
  obtain rfl := List.mem_singleton.1 hc
  rw [hE k, J.value k]
  congr 1
  exact List.map_congr_left fun c' hc' => hag c' k (J.causal c' hc' k)

/-! ## Link / pipe without an initial token (`bd_link`, `bd_pipe`) -/

structure LinkEv (ρ v : C → Nat → Nat) (ci co : C) : Prop where
  causal : ∀ k, ρ ci (2 * k) < ρ co (2 * k)
  value : ∀ k, v co k = v ci k

theorem link_det {ci co : C} (L : LinkEv ρ v ci co) : EarlierDet ρ v [co] (linkEq ci co) := by
  intro c hc k σ hag hE
  obtain rfl := List.mem_singleton.1 hc
  rw [hE k, hag ci k (L.causal k), L.value k]

/-! ## Source / constant (`bd_src`) and sink (`bd_snk`) -/

structure SrcEv (v : C → Nat → Nat) (cz : C) (val : Nat) : Prop where
  value : ∀ k, v cz k = val

theorem src_det {cz : C} {val : Nat} (S : SrcEv v cz val) : EarlierDet ρ v [cz] (srcEq cz val) := by
  intro c hc k σ _ hE
  obtain rfl := List.mem_singleton.1 hc
  rw [hE k, S.value k]

theorem sink_det : EarlierDet ρ v ([] : List C) (fun _ => True) := by
  intro c hc; cases hc

/-! ## Steer (`cond_br` = `bd_join` + `bd_steer`) -/

/-- Event contract of a steer: output `b`'s token `m` is the input token `i`
that is the `m`-th one whose condition is `b`; it is offered after that input
token, with value `f (v cj i)`. -/
structure SteerEv (ρ v : C → Nat → Nat) (sel : Nat → Bool) (f : Nat → Nat) (cj : C)
    (cout : Bool → C) : Prop where
  mono : Strict (ρ cj)
  route : ∀ b m, ∃ i, sel (v cj i) = b ∧ cnt (fun i' => sel (v cj i') == b) i = m ∧
    ρ cj (2 * i) < ρ (cout b) (2 * m) ∧ v (cout b) m = f (v cj i)

theorem steer_det {sel : Nat → Bool} {f : Nat → Nat} {cj : C} {cout : Bool → C}
    (S : SteerEv ρ v sel f cj cout) :
    EarlierDet ρ v [cout true, cout false] (steerEq sel f cj cout) := by
  intro c hc m σ hag hE
  obtain ⟨b, rfl⟩ : ∃ b, c = cout b := by
    simp at hc; rcases hc with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨i, hs, hn, hc', hv⟩ := S.route b m
  have hle : ∀ i', i' ≤ i → σ cj i' = v cj i' := fun i' h' =>
    hag cj i' (Nat.lt_of_le_of_lt ((S.mono.le_iff (a := 2 * i') (b := 2 * i)).2 (by omega)) hc')
  have hcnt : cnt (fun i' => sel (σ cj i') == b) i = m := by
    rw [← hn]; exact cnt_congr_lt i fun i' h' => by rw [hle i' (by omega)]
  have := hE i b (by rw [hle i (Nat.le_refl _), hs])
  rw [hcnt, hle i (Nat.le_refl _)] at this
  rw [this, hv]

/-! ## 2-way mux (`bd_mux`) -/

/-- Event contract of a 2-way mux: output token `k` is offered after control
token `k` and after the selected input's `n`-th token (`n` = number of
earlier control tokens with the same select), with that token's value. -/
structure MuxEv (ρ v : C → Nat → Nat) (sel : Nat → Bool) (cc cx cy cz : C) : Prop where
  mono : Strict (ρ cc)
  ctl : ∀ k, ρ cc (2 * k) < ρ cz (2 * k)
  pick : ∀ k, if sel (v cc k) then
      ρ cy (2 * cnt (fun i => sel (v cc i)) k) < ρ cz (2 * k) ∧ v cz k = v cy (cnt (fun i => sel (v cc i)) k)
    else
      ρ cx (2 * cnt (fun i => !sel (v cc i)) k) < ρ cz (2 * k) ∧ v cz k = v cx (cnt (fun i => !sel (v cc i)) k)

theorem mux_det {sel : Nat → Bool} {cc cx cy cz : C} (M : MuxEv ρ v sel cc cx cy cz) :
    EarlierDet ρ v [cz] (muxEq sel cc cx cy cz) := by
  intro c hc k σ hag hE
  obtain rfl := List.mem_singleton.1 hc
  have hle : ∀ i, i ≤ k → σ cc i = v cc i := fun i h' =>
    hag cc i (Nat.lt_of_le_of_lt ((M.mono.le_iff (a := 2 * i) (b := 2 * k)).2 (by omega)) (M.ctl k))
  have c1 : cnt (fun i => sel (σ cc i)) k = cnt (fun i => sel (v cc i)) k :=
    cnt_congr_lt k fun i h' => by rw [hle i (by omega)]
  have c0 : cnt (fun i => !sel (σ cc i)) k = cnt (fun i => !sel (v cc i)) k :=
    cnt_congr_lt k fun i h' => by rw [hle i (by omega)]
  rw [hE k, hle k (Nat.le_refl _), c1, c0]
  have hp := M.pick k
  split
  · rename_i hs; simp only [hs, ite_true] at hp; rw [hag _ _ hp.1, hp.2]
  · rename_i hs; simp only [hs, ite_false, Bool.false_eq_true] at hp; rw [hag _ _ hp.1, hp.2]

/-! ## 3-way mux (`bdc_muxn3`) -/

/-- Event contract of the N-way mux (C's `muxnEq`, N = 3). `range` is
B's H_S_RANGE (`sv k < 3`): without it C's equation leaves the output free
and no contract can determine it. -/
structure MuxNEv (ρ v : C → Nat → Nat) (sel : Nat → Nat) (cc : C) (cxs : Nat → C) (cz : C) : Prop where
  mono : Strict (ρ cc)
  ctl : ∀ k, ρ cc (2 * k) < ρ cz (2 * k)
  range : ∀ k, sel (v cc k) < 3
  pick : ∀ k, ρ (cxs (sel (v cc k))) (2 * cnt (fun i => sel (v cc i) == sel (v cc k)) k) < ρ cz (2 * k) ∧
    v cz k = v (cxs (sel (v cc k))) (cnt (fun i => sel (v cc i) == sel (v cc k)) k)

theorem muxn_det {sel : Nat → Nat} {cc : C} {cxs : Nat → C} {cz : C} (M : MuxNEv ρ v sel cc cxs cz) :
    EarlierDet ρ v [cz] (muxnEq sel cc cxs cz) := by
  intro c hc k σ hag hE
  obtain rfl := List.mem_singleton.1 hc
  have hle : ∀ i, i ≤ k → σ cc i = v cc i := fun i h' =>
    hag cc i (Nat.lt_of_le_of_lt ((M.mono.le_iff (a := 2 * i) (b := 2 * k)).2 (by omega)) (M.ctl k))
  have hk := hle k (Nat.le_refl _)
  have c1 : cnt (fun i => sel (σ cc i) == sel (σ cc k)) k = cnt (fun i => sel (v cc i) == sel (v cc k)) k :=
    cnt_congr_lt k fun i h' => by rw [hle i (by omega), hk]
  rw [hE k (by rw [hk]; exact M.range k), c1, hk, hag _ _ (M.pick k).1, (M.pick k).2]

/-! ## Arbitrated merge / control_merge (`bdc_amerge`) -/

/-- Event contract of the 2-input arbitrated merge, relative to the
arbitration outcome `ω` (C's `amergeEq`; C instantiates `ω` with
`winner (ch cz)`, the index bit the circuit actually emitted). Output token
`k` is the next token of the input that won slot `k`, offered after it,
with value `2 * that value + [won by y]` (index bit packed in bit 0). -/
structure AMergeEv (ρ v : C → Nat → Nat) (ω : Nat → Bool) (cx cy cz : C) : Prop where
  pick : ∀ k, if ω k then
      ρ cy (2 * cnt ω k) < ρ cz (2 * k) ∧ v cz k = 2 * v cy (cnt ω k) + b2n true
    else
      ρ cx (2 * cnt (fun i => !ω i) k) < ρ cz (2 * k) ∧ v cz k = 2 * v cx (cnt (fun i => !ω i) k) + b2n false

theorem amerge_det {ω : Nat → Bool} {cx cy cz : C} (A : AMergeEv ρ v ω cx cy cz) :
    EarlierDet ρ v [cz] (amergeEq ω cx cy cz) := by
  intro c hc k σ hag hE
  obtain rfl := List.mem_singleton.1 hc
  rw [hE k]
  have hp := A.pick k
  cases hw : ω k
  · rw [hw] at hp; simp only [Bool.false_eq_true, ite_false] at hp ⊢
    rw [hag _ _ hp.1, hp.2]
  · rw [hw] at hp; simp only [ite_true] at hp ⊢
    rw [hag _ _ hp.1, hp.2]

/-! ## Uniform statement: each event contract, on ports, is C's `OpSpec` -/

section spec
variable {ch : C → Chan} {α : C → Nat → Nat} (Pall : ∀ c, Port (ch c) (ρ c) (α c) (v c))
include Pall

theorem fork_spec {ca : C} {cos : List C} (F : ForkEv ρ v ca cos) :
    OpSpec ch [ca] cos (forkEq ca cos) := opSpec_of_ports Pall (fork_det F)
theorem join_spec {g : List Nat → Nat} {cis : List C} {co : C} (J : JoinEv ρ v g cis co) :
    OpSpec ch cis [co] (joinEq g cis co) := opSpec_of_ports Pall (join_det J)
theorem link_spec {ci co : C} (L : LinkEv ρ v ci co) :
    OpSpec ch [ci] [co] (linkEq ci co) := opSpec_of_ports Pall (link_det L)
theorem src_spec {cz : C} {val : Nat} (S : SrcEv v cz val) :
    OpSpec ch [] [cz] (srcEq cz val) := opSpec_of_ports Pall (src_det S)
theorem sink_spec {ca : C} : OpSpec ch [ca] [] (fun _ => True) := opSpec_of_ports Pall sink_det
theorem steer_spec {sel : Nat → Bool} {f : Nat → Nat} {cj : C} {cout : Bool → C}
    (S : SteerEv ρ v sel f cj cout) :
    OpSpec ch [cj] [cout true, cout false] (steerEq sel f cj cout) := opSpec_of_ports Pall (steer_det S)
theorem mux_spec {sel : Nat → Bool} {cc cx cy cz : C} (M : MuxEv ρ v sel cc cx cy cz) :
    OpSpec ch [cc, cx, cy] [cz] (muxEq sel cc cx cy cz) := opSpec_of_ports Pall (mux_det M)
theorem muxn_spec {sel : Nat → Nat} {cc : C} {cxs : Nat → C} {cz : C} (M : MuxNEv ρ v sel cc cxs cz) :
    OpSpec ch [cc, cxs 0, cxs 1, cxs 2] [cz] (muxnEq sel cc cxs cz) := opSpec_of_ports Pall (muxn_det M)
theorem amerge_spec {ω : Nat → Bool} {cx cy cz : C} (A : AMergeEv ρ v ω cx cy cz) :
    OpSpec ch [cx, cy] [cz] (amergeEq ω cx cy cz) := opSpec_of_ports Pall (amerge_det A)

end spec

end Formal.Cells.Contracts
