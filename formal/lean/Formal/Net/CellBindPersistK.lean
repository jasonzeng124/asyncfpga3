import Formal.Net.CellBindPersistMux
import Formal.Net.CellBindK

/-!
# Probe C-O4b (persistence 3/3, part 2): H_LEAF_PERSIST and H_REQ_PERSIST discharged

* `GenCellKP`: O4b's `GenCellK` with H_LEAF_PERSIST (fork N = 5, 6 trees; compute joins;
  mux / muxN joins) and H_REQ_PERSIST (bd_link `rdly`, bd_mux `udly`) REMOVED. Everything else
  (H_LUT_SI, H_FB_FIRST, H_PIN_EQ, H_CHAIN_SETTLED, H_WIRE_DI, data / select / arbiter fields,
  H_MUXN_OR, H_R0_ISO, H_PORT_ORDER, reset) is unchanged. `genP_of`: `GenCellK → GenCellKP`.
* `op_proto`: every operator satisfying `GenCellKP` is a causal `OpProto` operator (the joint
  induction of `CellBindPersistOps` / `CellBindPersistMux` enters through `opproto_of`).
* **`cells_of_genP`**: for any kernel, `GenCellKP` on every operator + H_BUNDLE ⟹ H_CELLS
  (`net_protocol` gives the four-phase protocol on every channel; the per-kind cores then give
  every lumped field at every tick).
* **`kernel_circuit_safe_genP`** and its four instances: the generic capstone under
  `GenCellKP`, H_BUNDLE, H_START_ONCE. H_LEAF_PERSIST and H_REQ_PERSIST are no longer
  hypotheses: they are consequences of the protocol, proved jointly with it.
* Non-vacuity: the quiet witnesses of `CellBindK` (gcd_hw, collatz, xorshift) satisfy
  `GenCellKP` (`genP_of`).
-/

namespace Formal.Net.CellBind.PersistK
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.CellBind Formal.Net.CellBind.Ops Formal.Net.CellBind.KOps Formal.Net.CellBind.Persist

variable {n : Nat}

/-- **The generated-netlist hypothesis without H_LEAF_PERSIST / H_REQ_PERSIST.** -/
def GenCellKP (ch : Fin n → Chan) (sv : Nat → Nat) : K n → Prop
  | .forkG i os => GenForkP (ch i) (os.map ch)
  | .forkH i os _ _ _ _ => GenForkP (ch i) ((os.map Prod.fst).map ch)
  | .join ins o e js _ => GenJoinKP (jg e js) (ins.map ch) (ch o)
  | .mux c x y z _ => ∃ j0 j1, GenMuxP sel2 (ch x) (ch y) (ch c) (ch z) j0 j1
  | .muxn c x0 x1 x2 z _ => ∃ j, GenMuxNP selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j
  | .link i o => ∃ c, GenLinkP (ch i) (ch o) c
  | k => GenCellK ch sv k

theorem genP_of (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : GenCellK ch sv k) :
    GenCellKP ch sv k := by
  cases k with
  | forkG i os => exact forkP_of h
  | forkH i os l hh d hs => exact forkP_of h
  | join ins o e js jw => exact joinP_of h
  | mux c x y z mw => obtain ⟨j0, j1, M⟩ := h; exact ⟨j0, j1, muxP_of M⟩
  | muxn c x0 x1 x2 z nw => obtain ⟨j, M⟩ := h; exact ⟨j, muxnP_of M⟩
  | link i o => obtain ⟨c, L⟩ := h; exact ⟨c, linkP_of L⟩
  | _ => exact h

theorem map_fz (S : Nat) (ch : Fin n → Chan) (l : List (Fin n)) :
    (l.map ch).map (fzC S) = l.map (fzK S ch) := by
  simp [List.map_map, Function.comp_def, fzK]

theorem mem_ch {ch : Fin n → Chan} {l : List (Fin n)} {o : Chan} (h : o ∈ l.map ch) :
    ∃ c, c ∈ l ∧ o = ch c := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact ⟨c, hc, rfl⟩

theorem cx3_mem {c x0 x1 x2 : Fin n} {k : Nat} (hk : k < 3) : cx3 x0 x1 x2 k ∈ [c, x0, x1, x2] := by
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> simp [cx3]

/-- Fork, at K level (shared by `forkG` and `forkH`). -/
theorem fork_K (ch : Fin n → Chan) (i : Fin n) (os : List (Fin n)) (h : GenForkP (ch i) (os.map ch))
    (hi : Init (ch i)) (ho : ∀ c ∈ os, Init (ch c)) (T : Nat)
    (hp : ∀ s, s < T → Rules (ch i) s ∧ ∀ c ∈ os, Rules (ch c) s) : ∀ u, u ≤ T → FCel (ch i) (os.map ch) u :=
  fork_core h hi.1 (fun o hom => by obtain ⟨c, hc, rfl⟩ := mem_ch hom; exact (ho c hc).2) T
    (fun s hs => ⟨(hp s hs).1, fun o hom => by obtain ⟨c, hc, rfl⟩ := mem_ch hom; exact (hp s hs).2 c hc⟩)

theorem fork_fzK (ch : Fin n → Chan) (i : Fin n) (os : List (Fin n)) (h : GenForkP (ch i) (os.map ch))
    (S : Nat) (hc : ∀ t, t < S → FCel (ch i) (os.map ch) t) :
    Fork.Fork (fzK S ch i) (os.map (fzK S ch)) := by
  rw [← map_fz]; exact fork_fz h S hc

theorem join_K (ch : Fin n → Chan) (g : List Nat → Nat) (ins : List (Fin n)) (o : Fin n)
    (h : GenJoinKP g (ins.map ch) (ch o)) (hi : ∀ c ∈ ins, Init (ch c)) (ho : Init (ch o)) (T : Nat)
    (hp : ∀ s, s < T → (∀ c ∈ ins, Rules (ch c) s) ∧ Rules (ch o) s) :
    ∀ u, u ≤ T → JCel (ins.map ch) (ch o) u :=
  join_core h ho.2 (fun i him => by obtain ⟨c, hc, rfl⟩ := mem_ch him; exact (hi c hc).1) T
    (fun s hs => ⟨(hp s hs).2, fun i him => by obtain ⟨c, hc, rfl⟩ := mem_ch him; exact (hp s hs).1 c hc⟩)

theorem join_fzK (ch : Fin n → Chan) (g : List Nat → Nat) (ins : List (Fin n)) (o : Fin n)
    (h : GenJoinKP g (ins.map ch) (ch o)) (S : Nat) (hc : ∀ t, t < S → JCel (ins.map ch) (ch o) t) :
    Join.Join g (ins.map (fzK S ch)) (fzK S ch o) := by
  rw [← map_fz]; exact join_fz h S hc

theorem vac {P : Nat → Prop} : ∀ t, t < 0 → P t := fun _ h => absurd h (Nat.not_lt_zero _)

/-- **Every `GenCellKP` operator is a causal `OpProto` operator.** -/
theorem op_proto (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hd : Dist k) (h : GenCellKP ch sv k) :
    OpProto ch k.insC k.outsC := by
  cases k with
  | forkG i os =>
    have h : GenForkP (ch i) (os.map ch) := h
    refine opproto_of ch sv _ hd (fork_fzK ch i os h 0 vac) (fun T hi ho _ hp => ?_)
    exact fork_fzK ch i os h (T + 1) (fun t ht => fork_K ch i os h (hi i (by simp [K.insC, K.outsC])) ho T
      (fun s hs => ⟨(hp s hs).1 i (by simp [K.insC, K.outsC]), (hp s hs).2⟩) t (by omega))
  | forkH i os l hh d hs =>
    have h : GenForkP (ch i) ((os.map Prod.fst).map ch) := h
    refine opproto_of ch sv _ hd (fork_fzK ch i _ h 0 vac) (fun T hi ho _ hp => ?_)
    exact fork_fzK ch i _ h (T + 1) (fun t ht => fork_K ch i _ h (hi i (by simp [K.insC, K.outsC])) ho T
      (fun s hs => ⟨(hp s hs).1 i (by simp [K.insC, K.outsC]), (hp s hs).2⟩) t (by omega))
  | join ins o e js jw =>
    have h : GenJoinKP (jg e js) (ins.map ch) (ch o) := h
    refine opproto_of ch sv _ hd (join_fzK ch _ ins o h 0 vac) (fun T hi ho _ hp => ?_)
    exact join_fzK ch _ ins o h (T + 1) (fun t ht => join_K ch _ ins o h hi (ho o (by simp [K.insC, K.outsC])) T
      (fun s hs => ⟨(hp s hs).1, (hp s hs).2 o (by simp [K.insC, K.outsC])⟩) t (by omega))
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := h
    refine opproto_of ch sv _ hd ⟨fz 0 j0, fz 0 j1, mux_fz M 0 vac⟩ (fun T hi ho hh hp => ?_)
    refine ⟨fz (T + 1) j0, fz (T + 1) j1, mux_fz M (T + 1) (fun t ht => ?_)⟩
    exact mux_core M (hi x (by simp [K.insC, K.outsC])).1 (hi y (by simp [K.insC, K.outsC])).1 (hi c (by simp [K.insC, K.outsC])).1 (ho z (by simp [K.insC, K.outsC])).2
      (hh c (by simp [K.insC, K.outsC])) T (fun s hs => ⟨((hp s hs).1 x (by simp [K.insC, K.outsC])).1, ((hp s hs).1 y (by simp [K.insC, K.outsC])).1,
        ((hp s hs).1 c (by simp [K.insC, K.outsC])).1, ((hp s hs).2 z (by simp [K.insC, K.outsC])).2⟩) t (by omega)
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := h
    refine opproto_of ch sv _ hd ⟨fun k => fz 0 (j k), muxn_fz M 0 vac⟩ (fun T hi ho hh hp => ?_)
    refine ⟨fun k => fz (T + 1) (j k), muxn_fz M (T + 1) (fun t ht => ?_)⟩
    exact muxn_core M (fun k hk => (hi _ (cx3_mem hk)).1) (hi c (by simp [K.insC, K.outsC])).1 (ho z (by simp [K.insC, K.outsC])).2
      (hh c (by simp [K.insC, K.outsC])) T (fun s hs => ⟨fun k hk => ((hp s hs).1 _ (cx3_mem hk)).1,
        ((hp s hs).1 c (by simp [K.insC, K.outsC])).1, ((hp s hs).2 z (by simp [K.insC, K.outsC])).2⟩) t (by omega)
  | link i o =>
    obtain ⟨cc, L⟩ := h
    refine opproto_of ch sv _ hd ⟨fz 0 cc, link_fz L 0 vac⟩ (fun T hi ho _ hp => ?_)
    refine ⟨fz (T + 1) cc, link_fz L (T + 1) (fun t ht => ?_)⟩
    exact link_core L (hi i (by simp [K.insC, K.outsC])).1 (ho o (by simp [K.insC, K.outsC])).2 T
      (fun s hs => ⟨((hp s hs).1 i (by simp [K.insC, K.outsC])).1, ((hp s hs).2 o (by simp [K.insC, K.outsC])).2⟩) t (by omega)
  | bjoin => exact cell_proto' ch sv _ (cell_of_genK ch sv _ h) hd
  | steerC => exact cell_proto' ch sv _ (cell_of_genK ch sv _ h) hd
  | steerD => exact cell_proto' ch sv _ (cell_of_genK ch sv _ h) hd
  | amerge => exact cell_proto' ch sv _ (cell_of_genK ch sv _ h) hd
  | src => exact cell_proto' ch sv _ (cell_of_genK ch sv _ h) hd
  | sink => exact cell_proto' ch sv _ (cell_of_genK ch sv _ h) hd

/-- **With the protocol on every channel, `GenCellKP` gives the Ops gate model.** -/
theorem op_cell (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : GenCellKP ch sv k)
    (hp : ∀ c, Protocol (ch c)) (hh : ∀ c, Held (ch c)) : Cell ch sv k := by
  cases k with
  | forkG i os =>
    have h : GenForkP (ch i) (os.map ch) := h
    exact fork_all h (fun u => fork_K ch i os h (hp i).1 (fun c _ => (hp c).1) u
      (fun s _ => ⟨(hp i).2 s, fun c _ => (hp c).2 s⟩) u (Nat.le_refl u))
  | forkH i os l hh' d hs =>
    have h : GenForkP (ch i) ((os.map Prod.fst).map ch) := h
    exact fork_all h (fun u => fork_K ch i _ h (hp i).1 (fun c _ => (hp c).1) u
      (fun s _ => ⟨(hp i).2 s, fun c _ => (hp c).2 s⟩) u (Nat.le_refl u))
  | join ins o e js jw =>
    have h : GenJoinKP (jg e js) (ins.map ch) (ch o) := h
    exact join_all h (fun u => join_K ch _ ins o h (fun c _ => (hp c).1) (hp o).1 u
      (fun s _ => ⟨fun c _ => (hp c).2 s, (hp o).2 s⟩) u (Nat.le_refl u))
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := h
    exact ⟨j0, j1, mux_all M (fun u => mux_core M (hp x).1.1 (hp y).1.1 (hp c).1.1 (hp z).1.2 (hh c) u
      (fun s _ => ⟨((hp x).2 s).1, ((hp y).2 s).1, ((hp c).2 s).1, ((hp z).2 s).2⟩) u (Nat.le_refl u))⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := h
    exact ⟨j, muxn_all M (fun u => muxn_core M (fun k _ => (hp _).1.1) (hp c).1.1 (hp z).1.2 (hh c) u
      (fun s _ => ⟨fun k _ => ((hp _).2 s).1, ((hp c).2 s).1, ((hp z).2 s).2⟩) u (Nat.le_refl u))⟩
  | link i o =>
    obtain ⟨cc, L⟩ := h
    exact ⟨cc, link_all L (fun u => link_core L (hp i).1.1 (hp o).1.2 u
      (fun s _ => ⟨((hp i).2 s).1, ((hp o).2 s).2⟩) u (Nat.le_refl u))⟩
  | bjoin => exact cell_of_genK ch sv _ h
  | steerC => exact cell_of_genK ch sv _ h
  | steerD => exact cell_of_genK ch sv _ h
  | amerge => exact cell_of_genK ch sv _ h
  | src => exact cell_of_genK ch sv _ h
  | sink => exact cell_of_genK ch sv _ h

section kernel
open Formal.Net.KCap KD KP

/-- **H_CELLS from the generated netlists, with no persistence hypothesis.** -/
theorem cells_of_genP [KD] [KP] (sv : Nat → Nat) (ch : Fin NC → Chan)
    (H_GEN : ∀ o : Fin NO, GenCellKP ch sv (opAt o)) (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ o : Fin NO, Cell ch sv (opAt o) := by
  have hp := net_protocol net ch (fun o => op_proto ch sv (opAt o) (dist_of _ (ops_ok o)) (H_GEN o))
    H_BUNDLE
  exact fun o => op_cell ch sv (opAt o) (H_GEN o) hp H_BUNDLE

/-- **The capstone for any kernel from the generated netlists, H_LEAF_PERSIST and
H_REQ_PERSIST discharged.** -/
theorem kernel_circuit_safe_genP [KD] [KP] (a b : Nat) (hd : dom a b) (ch : Fin NC → Chan)
    (H_GEN : ∀ o : Fin NO, GenCellKP ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (spec a b)) :=
  kernel_circuit_safe a b hd ch (cells_of_genP _ ch H_GEN H_BUNDLE) H_BUNDLE H_START_ONCE

end kernel

/-! ## The four kernels -/

section gcd
open Formal.Net.KCap.GcdInst
attribute [local instance] gcdKD gcdKP

theorem gcd_hw_circuit_safe_genP (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin CapNet.Gcd.NC → Chan)
    (H_GEN : ∀ o : Fin CapNet.Gcd.NO, GenCellKP ch (CapNet.srcV a b) (CapNet.Gcd.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch CapNet.Gcd.start).req) t ≤ 1) :
    (∀ k e, TokAt (ch CapNet.Gcd.out0) k e → (ch CapNet.Gcd.out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch CapNet.Gcd.out0) t =
      List.replicate (Handshake.cnt (fallB (ch CapNet.Gcd.out0).ack) t) (Nat.gcd a b)) :=
  kernel_circuit_safe_genP a b (⟨ha, hb⟩ : a < 2 ^ 31 ∧ b < 2 ^ 31) ch H_GEN H_BUNDLE H_START_ONCE

theorem gcd_genP_witness :
    ∃ ch : Fin CapNet.Gcd.NC → Chan,
      (∀ o : Fin CapNet.Gcd.NO, GenCellKP ch (CapNet.srcV 12 18) (CapNet.Gcd.opAt o)) ∧
      (∀ c, Held (ch c)) ∧ (∀ t, Handshake.cnt (riseB (ch CapNet.Gcd.start).req) t ≤ 1) := by
  obtain ⟨ch, hG, hB, hS⟩ := K.gcd_gen_witness
  exact ⟨ch, fun o => genP_of ch _ _ (hG o), hB, hS⟩

end gcd

section ipow
open Formal.Net.KCap.IpowInst
attribute [local instance] ipowKD ipowKP

theorem ipow_circuit_safe_genP (b e : Nat) (he : e < 2 ^ 32) (ch : Fin IpowCap.NC → Chan)
    (H_GEN : ∀ o : Fin IpowCap.NO, GenCellKP ch (CapNet.srcV b e) (IpowCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch IpowCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch IpowCap.out0) k v → (ch IpowCap.out0).dat v = IpowHw.ipowSpec b e) ∧
    (∀ t, closedVals (ch IpowCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch IpowCap.out0).ack) t) (IpowHw.ipowSpec b e)) :=
  kernel_circuit_safe_genP b e he ch H_GEN H_BUNDLE H_START_ONCE

end ipow

section collatz
open Formal.Net.KCap.CollatzInst
attribute [local instance] collatzKD collatzKP

theorem collatz_circuit_safe_genP (n fuel r : Nat) (hr : CollatzHw.collatzC fuel n = some r)
    (ch : Fin CollatzCap.NC → Chan)
    (H_GEN : ∀ o : Fin CollatzCap.NO, GenCellKP ch (srcC n fuel) (KCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch CollatzCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch CollatzCap.out0) k v → (ch CollatzCap.out0).dat v = r) ∧
    (∀ t, closedVals (ch CollatzCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch CollatzCap.out0).ack) t) r) :=
  collatz_circuit_safe n fuel r hr ch (cells_of_genP _ ch H_GEN H_BUNDLE) H_BUNDLE H_START_ONCE

theorem collatz_genP_witness :
    ∃ ch : Fin CollatzCap.NC → Chan,
      (∀ o : Fin CollatzCap.NO, GenCellKP ch (srcC 7 200) (KCap.opAt o)) ∧
      (∀ c, Held (ch c)) ∧ (∀ t, Handshake.cnt (riseB (ch CollatzCap.start).req) t ≤ 1) := by
  obtain ⟨ch, hG, hB, hS⟩ := K.collatz_gen_witness
  exact ⟨ch, fun o => genP_of ch _ _ (hG o), hB, hS⟩

end collatz

section xorshift
open Formal.Net.KCap.XorshiftInst
attribute [local instance] xorKD xorKP

theorem xorshift_circuit_safe_genP (seed rounds : Nat) (hr : rounds < 2 ^ 32)
    (ch : Fin XorshiftCap.NC → Chan)
    (H_GEN : ∀ o : Fin XorshiftCap.NO, GenCellKP ch (CapNet.srcV seed rounds) (KCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch XorshiftCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch XorshiftCap.out0) k v →
      (ch XorshiftCap.out0).dat v = XorshiftHw.xsSpec seed rounds) ∧
    (∀ t, closedVals (ch XorshiftCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch XorshiftCap.out0).ack) t)
        (XorshiftHw.xsSpec seed rounds)) :=
  kernel_circuit_safe_genP seed rounds hr ch H_GEN H_BUNDLE H_START_ONCE

theorem xorshift_genP_witness :
    ∃ ch : Fin XorshiftCap.NC → Chan,
      (∀ o : Fin XorshiftCap.NO, GenCellKP ch (CapNet.srcV 2463534242 4) (KCap.opAt o)) ∧
      (∀ c, Held (ch c)) ∧ (∀ t, Handshake.cnt (riseB (ch XorshiftCap.start).req) t ≤ 1) := by
  obtain ⟨ch, hG, hB, hS⟩ := K.xorshift_gen_witness
  exact ⟨ch, fun o => genP_of ch _ _ (hG o), hB, hS⟩

end xorshift

end Formal.Net.CellBind.PersistK
