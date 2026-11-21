-- Bsa4 mutant M15 of Formal/Cells/IpowCells.lean: one change, 'def dvL : List Nat := [3, 7,' -> 'def dvL : List Nat := [4, 7,'. Expected: FAIL.
import Formal.Net.IpowCapMain
import Formal.Timing.FbFirstRt
import Formal.Cells.CElemTiming

/-!
# Probe Bipw (shard B): H_CELLS of the ipow network from per-cell contracts

`Formal.Net.IpowCap.ipow_circuit_safe3` (C-8y) proves that every value latched on `out0` of
the 101-channel / 83-operator network of `ipow_ps` is `ipowSpec b e`, under

    H_CELLS : ∀ o : Fin NO, CapNet.Cell ch (srcV b e) (opAt o)

where `CapNet.Cell` is C's SI gate model of each operator kind (`Fork.Fork`, `Join.Join`,
`Steer.Steer`, `Mux.Mux`, `CM.AMerge`, `Link.Link`, `Capstone.Src`, `Ops.Gcd.Sink`). This file
replaces H_CELLS by one CONTRACT per operator, stated on the cells bdc really emits for ipow:

* every handshake LUT is the GENERATED LUT (C-11's yosys import, `Formal/Gen/Cells.lean`,
  through `Ops.Gen.genF`): `bd_c2`/`bd_c3`/`bd_c4` for the fork and join C-elements (by the
  real arity, including the join inputs C's network does not model), `bd_link`'s `ctl.u.u`
  (also every `bd_pipe` stage: `pipe_stage_gate`), `bd_steer`'s `u`/`uack`, `bd_mux`'s
  `uj0`/`uj1`/`uxa`/`uya`/`uor`+delay chain, `bd_arbiter`'s `ugrant`/`ustate`/`ua1`/`ua2`;
* every feedback LUT (C-element, link controller, mux join) carries the timing contract
  `FbCel`: H_LUT_SI (physical, `LutFb`: the output changes only to the LUT function of the pin
  values and the FEEDBACK PIN one tick earlier), H_FB_ROUTE (the feedback route is a
  `BoundedDelay lo hi`), reset agreement, and **H_RT_FB** (`RespAfter hi`: a non-feedback pin
  changes only when the output has been stable for the feedback route's settle bound `hi`).
  H_RT_FB is B's C2 (H_ENV_LATENCY of `CElemTiming.c2_four_phase`) in trace form; C's tcheck
  rule Rc checks its routed inequality. `bounded_of_winDelay` proves that B's own feedback-wire
  model (`CElemTiming.WinDelay`, the `H_FB` field of `CElemTiming.Loop`) gives H_FB_ROUTE.

## Assumed / proved / NOT covered

**Assumed** (`Contract`, per operator; each field named):
H_LUT_SI (generated INITs), H_FB_ROUTE, H_RT_FB (every feedback LUT); H_SEL_PIN (steer and mux
select pins read `sel2` of the bus, at the same tick); H_WIRE_DI (each req/ack fan-out wire is
its own delay-insensitive copy); H_DELAY_LUMPED (the request path `C-element -> uor ->
bd_delay_gated -> z_req` of a fused compute unit, `uor -> bd_delay` of a mux and `ustate.O5 ->
bd_delay_gated` of an amerge is one SI node); H_CTREE_ATOMIC (a join of real arity >= 5 is one
flat C-element: used at exactly ONE operator, op 20 = `bdc_fused_uselect0`'s `bd_join N=5`,
`ctree_atomic_only_select`); H_ARB1/H_ARB2/H_ARB_EXCL/H_AMERGE_RTZ (the two arbiters' grant
behaviour, verbatim C's `CM.AMerge` fields: B proves exclusion only inside race windows,
`ArbBinary`/`ArbHandover`/`OnGcdArb*`); the data fields H_DATA_WIRE / H_DATA_COMB (including
both `muli`s, which yosys maps to DSP48E1) / H_LATCH_OPEN / H_LATCH_HOLD / H_GHOST; reset
(`init*`); the environment (`Capstone.Src` for b, e, start; `Sink` for out0 and p_end).

**Proved:**
* `cell_of_contract`: every operator's contract implies its `CapNet.Cell` gate model.
* `ipow_cells`: the contracts of the 83 operators of `IpowCap.ops` give H_CELLS.
* `ipow_safe_of_contracts`: `ipow_circuit_safe3` with H_CELLS replaced by the contracts.
* `join_extra_weaken` (inside `cell_of_contract`): a real C-element with MORE inputs than the
  network models (the source-chain constants that bdc joins into `uselect0`, `ushrsi0`,
  `ucmpi2`, `extraIn`) meets C's `Join` model on the modelled inputs. C-8m argued this in prose.
* `bounded_of_winDelay`, `fbCel_of_winDelay`: B's window-delay feedback wire gives H_FB_ROUTE.
* Gate equalities by kernel `decide`: `cgate_eq` (generated `bd_c2/c3/c4` = flat C-element),
  `pipe_stage_gate` (both `bd_pipe` stage controllers = `bd_link`'s), `grant_idle`.
* Structure of ipow's network (`decide`): `ipow_kinds` (operator counts), `ipow_no_muxn`,
  `ipow_fork_arity` (fork arities 2..4 only), `ctree_atomic_only_select`.
* Non-vacuity: `ipow_contracts_satisfiable` (one run meets every contract, H_BUNDLE and
  H_START_ONCE at once: the all-quiet run with a data solution checked by `decide`), and
  `fbCel_witness` (a C-element whose output really rises meets `FbCel`, its feedback route
  given as B's `WinDelay`).

**NOT covered:** that any routed ipow_ps build meets these contracts (no route, no GLS here);
the DSP48E1 multiplier as a primitive (H_DATA_COMB treats `muli` as a zero-time function; no
DSP model exists in A, B or C); H_CTREE_ATOMIC for the 5-input join (B's `CTree` results are
in a different model and are not bridged here); H_DELAY_LUMPED (the `bd_delay_gated` timing is
B's `GcdCells`, per-pin FIFO model, not bridged to the tick model); the arbiter grant fields;
liveness (the all-quiet witness latches nothing, exactly as for gcd). The identification of
C's network operators with the emitted Verilog instances (`extraIn`, the arity table in
`formal/notes/B-ipow-cells.md`) is by hand from bdc's output, not checked by Lean.
-/

namespace Formal.Cells.IpowCells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.Ops.Gen Formal.Gen Formal.Gen.Cells
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Timing.FbFirstRt (RespAfter si_of_resp)

/-! ## 1. The feedback-LUT timing contract -/

/-- **FbCel**: a feedback LUT node `o` with pin trace `p` and LUT function `F`
(generated INIT). Fields: H_LUT_SI (`LutFb`, physical: reads the feedback PIN `qp`),
H_FB_ROUTE (`BoundedDelay lo hi o qp`), reset agreement `qp 0 = o 0`, and H_RT_FB
(`RespAfter hi p o`, B's C2 / tcheck Rc in trace form). -/
def FbCel {α : Type} (F : α → Bool → Bool) (p : Nat → α) (o : Trace) : Prop :=
  ∃ (qp : Trace) (lo hi : Nat), LutFb F p qp o ∧ BoundedDelay lo hi o qp ∧ qp 0 = o 0 ∧
    RespAfter hi p o

/-- Under `FbCel` the node is the Ops-style SI gate on its own output (C-10k's
`si_of_resp`). -/
theorem FbCel.si {α : Type} {F : α → Bool → Bool} {p : Nat → α} {o : Trace} (h : FbCel F p o) :
    ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t) (o t) := by
  obtain ⟨qp, lo, hi, hL, hB, h0, hR⟩ := h
  exact si_of_resp hL hB h0 hR

/-- `FbCel` gives C's H_FB_FIRST for the same feedback pin. -/
theorem FbCel.lutFb {α : Type} {F : α → Bool → Bool} {p : Nat → α} {o : Trace} (h : FbCel F p o) :
    ∃ qp, LutFb F p qp o ∧ FbFirst qp o := by
  obtain ⟨qp, lo, hi, hL, hB, h0, hR⟩ := h
  exact ⟨qp, hL, Formal.Timing.FbFirstRt.fbFirst_of_resp hL hB h0 hR⟩

/-- **B's feedback-wire model gives H_FB_ROUTE.** `CElemTiming.Loop.H_FB` is a window delay
`WinDelay dmin dmax o qp`; with the feedback pin quiet until the window is defined
(`t + 1 < dmax`), it is C's `BoundedDelay dmin dmax o qp`. -/
theorem bounded_of_winDelay {dmin dmax : Nat} {o qp : Trace}
    (hW : CElemTiming.WinDelay dmin dmax o qp) (hq : ∀ t, t + 1 < dmax → qp (t + 1) = qp t) :
    BoundedDelay dmin dmax o qp := by
  refine ⟨fun t hc => ?_, fun t ht hs => ?_⟩
  · rcases Nat.lt_or_ge (t + 1) dmax with h | h
    · exact absurd (hq t h).symm hc
    · obtain ⟨s, h1, h2, h3⟩ := hW (t + 1) h
      refine ⟨t + 1 - s, by omega, by omega, by omega, ?_⟩
      rw [h3]; congr 1; omega
  · obtain ⟨s, h1, h2, h3⟩ := hW t ht
    rw [h3, hs s (by omega) (by omega), hs t (by omega) (Nat.le_refl t)]

/-- `FbCel` from B's window-delay feedback wire, with H_RT_FB at the wire's maximum delay. -/
theorem fbCel_of_winDelay {α : Type} {F : α → Bool → Bool} {p : Nat → α} {o qp : Trace}
    {dmin dmax : Nat} (hL : LutFb F p qp o) (hW : CElemTiming.WinDelay dmin dmax o qp)
    (hq : ∀ t, t + 1 < dmax → qp (t + 1) = qp t) (h0 : qp 0 = o 0)
    (hR : RespAfter dmax p o) : FbCel F p o :=
  ⟨qp, dmin, dmax, hL, bounded_of_winDelay hW hq, h0, hR⟩

/-! ## 2. Generated C-element gates by arity -/

/-- The flat C-element of any arity: all inputs 1 → 1, all 0 → 0, else hold. -/
def celL (xs : List Bool) (q : Bool) : Bool :=
  if xs.all id then true else if xs.all (fun x => !x) then false else q

theorem celL_move (xs : List Bool) (q : Bool) (h : celL xs q ≠ q) : ∀ x ∈ xs, x = celL xs q := by
  intro x hx
  unfold celL at h ⊢
  by_cases h1 : xs.all id = true
  · have := List.all_eq_true.mp h1 x hx; simp only [h1, ↓reduceIte]; simpa using this
  · simp only [h1, Bool.false_eq_true, ↓reduceIte] at h ⊢
    by_cases h2 : xs.all (fun x => !x) = true
    · have := List.all_eq_true.mp h2 x hx; simp only [h2, ↓reduceIte]; simpa using this
    · simp only [h2, Bool.false_eq_true, ↓reduceIte] at h; exact absurd rfl h

/-- The generated request/acknowledge C-element of `bd_fork`/`bd_join` by its real arity
(`bd_ctree` in `cells/rtl/bd_ce.v`): N = 1 is a wire (`bd_ctree_N1` has no cell), N = 2, 3, 4
are the single LUTs `bd_c2`, `bd_c3`, `bd_c4` (run mode, `rst = 0`), and N >= 5 is a two-level
tree, taken here as ONE flat C-element (**H_CTREE_ATOMIC**). -/
def cgate : List Bool → Bool → Bool
  | [a], _ => a
  | [a, b], q => genF bd_c2 "u" .O ["a", "b", "q", "rst"] [a, b, q, false]
  | [a, b, c], q => genF bd_c3 "u" .O ["a", "b", "c", "q", "rst"] [a, b, c, q, false]
  | [a, b, c, d], q => genF bd_c4 "u" .O ["a", "b", "c", "d", "q", "rst"] [a, b, c, d, q, false]
  | xs, q => celL xs q

theorem c2_gate_eq : ∀ a b q : Bool,
    genF bd_c2 "u" .O ["a", "b", "q", "rst"] [a, b, q, false] = celL [a, b] q := by decide +kernel
theorem c3_gate_eq : ∀ a b c q : Bool,
    genF bd_c3 "u" .O ["a", "b", "c", "q", "rst"] [a, b, c, q, false] = celL [a, b, c] q := by
  decide +kernel
theorem c4_gate_eq : ∀ a b c d q : Bool,
    genF bd_c4 "u" .O ["a", "b", "c", "d", "q", "rst"] [a, b, c, d, q, false] = celL [a, b, c, d] q := by
  decide +kernel

/-- **The generated C-elements are flat C-elements** (every arity bdc emits for ipow). -/
theorem cgate_eq : ∀ (xs : List Bool) (q : Bool), xs ≠ [] → cgate xs q = celL xs q
  | [a], q, _ => by cases a <;> rfl
  | [a, b], q, _ => c2_gate_eq a b q
  | [a, b, c], q, _ => c3_gate_eq a b c q
  | [a, b, c, d], q, _ => c4_gate_eq a b c d q
  | _ :: _ :: _ :: _ :: _ :: _, _, _ => rfl
  | [], _, h => absurd rfl h

/-- Every `bd_pipe` stage controller has `bd_link`'s controller function (so C's link model,
bound to `bd_link_W2`, also covers the 14 `bd_pipe` instances = 29 of ipow's 36 stages). -/
theorem pipe_stage_gate : ∀ r a q : Bool,
    genF bd_pipe_W1_N2 "many.stage[0].u.ctl.u.u" .O ["req_in", "req_out", "ack_in", "rst"] [r, a, q, false] =
      linkF (r, a) q ∧
    genF bd_pipe_W1_N2 "many.stage[1].u.ctl.u.u" .O ["many.r[1]", "ack_out", "req_out", "rst"] [r, a, q, false] =
      linkF (r, a) q := by decide +kernel

/-! ## 3. Per-cell contracts -/

/-- `bd_fork`: req fan-out wires (H_WIRE_DI), the ack C-element of the real arity (`FbCel`
on the generated LUT), data wires, reset. -/
structure ForkC (a : Chan) (os : List Chan) : Prop where
  ne : os ≠ []
  H_WIRE_DI : ∀ o ∈ os, ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t
  ack : FbCel cgate (fun t => os.map (fun o => o.ack t)) a.ack
  H_DATA_WIRE : ∀ o ∈ os, ∀ t, o.dat t = a.dat t
  initA : a.ack 0 = false
  initO : ∀ o ∈ os, o.req 0 = false

/-- `bd_join` (cond_br joins and fused compute units): the request C-element over the
modelled inputs `is` AND the unmodelled inputs `ex` (source-chain constants), `FbCel` on the
generated LUT of arity `is.length + ex.length` (for a fused unit the node is `z_req`:
H_DELAY_LUMPED); ack fan-out wires; the data function (H_DATA_COMB); reset. -/
structure JoinC (g : List Nat → Nat) (is : List Chan) (ex : List Trace) (o : Chan) : Prop where
  ne : is ≠ []
  req : FbCel cgate (fun t => is.map (fun i => i.req t) ++ ex.map (fun r => r t)) o.req
  H_WIRE_DI : ∀ i ∈ is, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  H_DATA_COMB : ∀ t, o.dat t = g (is.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ is, i.ack 0 = false

/-- `bd_steer`: the generated LUT6_2 `u` (O5/O6) and `uack`, with H_SEL_PIN (the `s` pin
reads `sel` of the joined bus at the tick the request is read); data wires; reset. -/
structure SteerC (sel : Nat → Bool) (f : Nat → Nat) (j : Chan) (out : Bool → Chan) : Prop where
  H_LUT_SI : ∀ b, LutSI (steerF b) (fun t => (j.req t, sel (j.dat t))) (out b).req
  H_ACK_LUT : LutSI (fun p : Bool × Bool => genF bd_steer "uack" .O ["ack0", "ack1"] [p.1, p.2])
    (fun t => ((out false).ack t, (out true).ack t)) j.ack
  H_DATA_WIRE : ∀ b t, (out b).dat t = f (j.dat t)
  initJ : j.ack 0 = false
  initO : ∀ b, (out b).req 0 = false

/-- The generated request path of `bd_mux` (`uor` then the matched delay chain). -/
def muxZF (p : Bool × Bool) : Bool :=
  genF bd_mux_W2 "udly.chain.g[1].u" .O ["udly.chain.s[1]"]
    [genF bd_mux_W2 "udly.chain.g[0].u" .O ["either"] [genF bd_mux_W2 "uor" .O ["j0", "j1"] [p.1, p.2]]]

/-- `bd_mux`: four feedback LUTs with `FbCel` (the select read at `uj0`/`uj1` is H_SEL_PIN),
the request path lumped (H_DELAY_LUMPED), `ctl_ack` = `z_ack` (H_WIRE_DI), the data mux
(H_DATA_COMB), reset. -/
structure MuxC (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) : Prop where
  uj0 : FbCel muxJ0F (fun t => (x.req t, c.req t, sel (c.dat t))) j0
  uj1 : FbCel muxJ1F (fun t => (y.req t, c.req t, sel (c.dat t))) j1
  uxa : FbCel muxXaF (fun t => (j0 t, z.ack t)) x.ack
  uya : FbCel muxYaF (fun t => (j1 t, z.ack t)) y.ack
  H_DELAY_LUMPED : LutSI muxZF (fun t => (j0 t, j1 t)) z.req
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  H_DATA_COMB : ∀ t, z.dat t = if sel (c.dat t) then y.dat t else x.dat t
  i0 : j0 0 = false
  i1 : j1 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false
  ic : c.ack 0 = false

/-- `bdc_amerge2_0`: the arbiter's grant fields (verbatim C's H_ARB*), the grants and `R0`
from the generated `ugrant`/`ustate` with the request path lumped (H_DELAY_LUMPED), the two
acknowledge C-elements `ua1`/`ua2` with `FbCel`, the composite bus (H_GHOST), reset. -/
structure AMergeC (x y z : Chan) (g1 g2 : Trace) : Prop where
  H_ARB1 : ∀ t, g1 (t + 1) ≠ g1 t → g1 (t + 1) = x.req t ∧ (g1 (t + 1) = true → g2 t = false ∧ z.ack t = false)
  H_ARB2 : ∀ t, g2 (t + 1) ≠ g2 t → g2 (t + 1) = y.req t ∧ (g2 (t + 1) = true → g1 t = false ∧ z.ack t = false)
  H_ARB_EXCL : ∀ t, (g1 t && g2 t) = false
  H_GRANT_R0 : ∃ q : Trace,
    (∀ t, g1 t = genF bd_arbiter "ugrant" .O5 ["r1", "r2", "q"] [x.req t, y.req t, q t]) ∧
    (∀ t, g2 t = genF bd_arbiter "ugrant" .O6 ["r1", "r2", "q"] [x.req t, y.req t, q t]) ∧
    (∀ t, z.req (t + 1) ≠ z.req t →
      z.req (t + 1) = genF bd_arbiter "ustate" .O5 ["r1", "r2", "q", "rst", "A0"]
        [x.req t, y.req t, q t, false, z.ack t])
  H_AMERGE_RTZ : ∀ t, z.req t = false → z.req (t + 1) = true → x.ack t = false ∧ y.ack t = false
  ua1 : FbCel arbA1F (fun t => (g1 t, z.ack t)) x.ack
  ua2 : FbCel arbA2F (fun t => (g2 t, z.ack t)) y.ack
  H_GHOST : ∀ t, z.dat t = 2 * (if (g2 t || y.ack t) then y.dat t else x.dat t) + Mux.b2n (g2 t || y.ack t)
  i1 : g1 0 = false
  i2 : g2 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false

/-- `bd_link` (and each `bd_pipe` stage): the controller with `FbCel` on the generated LUT;
`ack_in`/`req_out` wires (H_WIRE_DI); the latch (H_LATCH_OPEN/HOLD); reset. -/
structure LinkC (i o : Chan) (c : Trace) : Prop where
  ctl : FbCel linkF (fun t => (i.req t, o.ack t)) c
  H_ACK_DI : ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = c t
  H_REQ_DI : ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = c t
  H_LATCH_OPEN : ∀ t, c t = true → o.dat t = i.dat t
  H_LATCH_HOLD : ∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t
  ic : c 0 = false
  ii : i.ack 0 = false
  io : o.req 0 = false

variable {n : Nat}

/-- **The per-operator contract.** `nx` is the number of real join inputs the network does
not model (used only by `join`/`bjoin`). `src` is the environment (H_SRC: `ipow_ps` drives
b, e, start from the PS, not from a `bd_src`), `sink` is a wire (`snk_wire`; H_ENV_OUT for
out0 and p_end), `muxn` (bdc_muxn3, not in ipow: `ipow_no_muxn`) keeps C's model. -/
def Contract (ch : Fin n → Chan) (sv : Nat → Nat) (nx : Nat) : K n → Prop
  | .forkG i os => ForkC (ch i) (os.map ch)
  | .forkH i os _ _ _ _ => ForkC (ch i) ((os.map Prod.fst).map ch)
  | .join ins o e js _ => ∃ ex : List Trace, ex.length = nx ∧ JoinC (jg e js) (ins.map ch) ex (ch o)
  | .bjoin ins o ec ed => ∃ ex : List Trace, ex.length = nx ∧ JoinC (bg ec ed) (ins.map ch) ex (ch o)
  | .steerC j t f => SteerC sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then t else f))
  | .steerD j t f fd _ =>
      SteerC sel2 (fun v => fd.eval [v / 2]) (ch j) (fun b => ch (bif b then t else f))
  | .mux c x y z _ => ∃ j0 j1, MuxC sel2 (ch x) (ch y) (ch c) (ch z) j0 j1
  | .muxn c x0 x1 x2 z _ =>
      ∃ j, MuxN.MuxN selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j
  | .amerge x y z _ => ∃ g1 g2, AMergeC (ch x) (ch y) (ch z) g1 g2
  | .link i o => ∃ c, LinkC (ch i) (ch o) c
  | .src z which _ => Capstone.Src (ch z) (sv which)
  | .sink i => Ops.Gcd.Sink (ch i)

/-! ## 4. Contract ⇒ C's gate model, per kind -/

theorem fork_of_contract {a : Chan} {os : List Chan} (h : ForkC a os) : Fork.Fork a os := by
  refine ⟨h.ne, h.H_WIRE_DI, fun t ht o ho => ?_, h.H_DATA_WIRE, h.initA, h.initO⟩
  have e := h.ack.si t ht
  have hne : os.map (fun o => o.ack t) ≠ [] := by simpa using h.ne
  rw [cgate_eq _ _ hne] at e
  rw [e] at ht ⊢
  exact celL_move _ _ ht _ (List.mem_map.mpr ⟨o, ho, rfl⟩)

/-- **A join with unmodelled inputs meets C's `Join` on the modelled ones** (`cel` only
weakens). -/
theorem join_of_contract {g : List Nat → Nat} {is : List Chan} {ex : List Trace} {o : Chan}
    (h : JoinC g is ex o) : Join.Join g is o := by
  refine ⟨h.ne, fun t ht i hi => ?_, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
  have e := h.req.si t ht
  have hne : is.map (fun i => i.req t) ++ ex.map (fun r => r t) ≠ [] := by
    intro hn; apply h.ne; simpa using (List.append_eq_nil_iff.mp hn).1
  rw [cgate_eq _ _ hne] at e
  rw [e] at ht ⊢
  exact celL_move _ _ ht _ (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨i, hi, rfl⟩)))

theorem steer_of_contract {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (h : SteerC sel f j out) : Steer.Steer sel f j out := by
  obtain ⟨hl, ho⟩ := steer_bound h.H_LUT_SI h.H_ACK_LUT
  exact ⟨hl, ho, h.H_DATA_WIRE, h.initJ, h.initO⟩

theorem mux_of_contract {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}
    (h : MuxC sel x y c z j0 j1) : Mux.Mux sel x y c z j0 j1 := by
  obtain ⟨q0, h0, f0⟩ := h.uj0.lutFb
  obtain ⟨q1, h1, f1⟩ := h.uj1.lutFb
  obtain ⟨q2, h2, f2⟩ := h.uxa.lutFb
  obtain ⟨q3, h3, f3⟩ := h.uya.lutFb
  obtain ⟨c0, c1, xa, ya⟩ := mux_bound h0 f0 h1 f1 h2 f2 h3 f3
  refine ⟨c0, c1, fun t ht => ?_, xa, ya, h.H_WIRE_DI, h.H_DATA_COMB, h.i0, h.i1, h.iz, h.ix, h.iy, h.ic⟩
  rw [h.H_DELAY_LUMPED t ht]; exact mux_zr_chain _ _

theorem amerge_of_contract {x y z : Chan} {g1 g2 : Trace} (h : AMergeC x y z g1 g2) :
    CM.AMerge x y z g1 g2 := by
  obtain ⟨q1, h1, f1⟩ := h.ua1.lutFb
  obtain ⟨q2, h2, f2⟩ := h.ua2.lutFb
  obtain ⟨xa, ya⟩ := amerge_ack_bound h1 f1 h2 f2
  obtain ⟨q, hg1, hg2, hz⟩ := h.H_GRANT_R0
  refine ⟨h.H_ARB1, h.H_ARB2, h.H_ARB_EXCL, fun t ht => ?_, h.H_AMERGE_RTZ, xa, ya, h.H_GHOST,
    h.i1, h.i2, h.iz, h.ix, h.iy⟩
  rw [hz t ht, arb_r0_or, ← hg1, ← hg2]

theorem link_of_contract {i o : Chan} {c : Trace} (h : LinkC i o c) : Link.Link i o c := by
  obtain ⟨qp, hL, hF⟩ := h.ctl.lutFb
  exact link_of_gen hL hF h.H_ACK_DI h.H_REQ_DI h.H_LATCH_OPEN h.H_LATCH_HOLD h.ic h.ii h.io

/-- **Every operator's contract gives C's gate model** (`CapNet.Cell`). -/
theorem cell_of_contract (ch : Fin n → Chan) (sv : Nat → Nat) (nx : Nat) (k : K n)
    (h : Contract ch sv nx k) : Cell ch sv k := by
  cases k with
  | forkG i os => exact fork_of_contract h
  | forkH i os l hh d hs => exact fork_of_contract h
  | join ins o e js jw => obtain ⟨ex, _, J⟩ := h; exact join_of_contract J
  | bjoin ins o ec ed => obtain ⟨ex, _, J⟩ := h; exact join_of_contract J
  | steerC j t f => exact steer_of_contract h
  | steerD j t f fd sw => exact steer_of_contract h
  | mux c x y z mw => obtain ⟨j0, j1, M⟩ := h; exact ⟨j0, j1, mux_of_contract M⟩
  | muxn c x0 x1 x2 z nw => exact h
  | amerge x y z w => obtain ⟨g1, g2, A⟩ := h; exact ⟨g1, g2, amerge_of_contract A⟩
  | link i o => obtain ⟨c, L⟩ := h; exact ⟨c, link_of_contract L⟩
  | src z which d => exact h
  | sink i => exact h

/-! ## 5. The ipow network -/

open Formal.Net.IpowCap (NC NO ops opAt start out0)

/-- Unmodelled join inputs per operator (read from bdc's emitted `bdc_ipow`, by hand):
op 20 = `bdc_fused_uselect0` (`bd_join N=5`; C models 3 inputs, the constants `n14` = 1 and
`n25` = 0 are source-chain channels); op 22 = `bdc_fused_ushrsi0` (shift amount `n20` = 1);
op 24 = `bdc_fused_ucmpi2` (comparand `n23` = 0). -/
def extraIn (o : Fin NO) : Nat :=
  if o.val = 20 then 2 else if o.val = 22 then 1 else if o.val = 24 then 1 else 0

/-- Real C-element arity of an operator (fork acks; join requests incl. unmodelled inputs). -/
def arity (k : K NC) (nx : Nat) : Nat :=
  match k with
  | .forkG _ os => os.length
  | .forkH _ os _ _ _ _ => os.length
  | .join ins _ _ _ _ => ins.length + nx
  | .bjoin ins _ _ _ => ins.length + nx
  | _ => 0

def kindId : K NC → Nat
  | .forkG .. => 0 | .forkH .. => 1 | .join .. => 2 | .bjoin .. => 3 | .steerC .. => 4
  | .steerD .. => 5 | .mux .. => 6 | .muxn .. => 7 | .amerge .. => 8 | .link .. => 9
  | .src .. => 10 | .sink .. => 11

/-- Operator counts of ipow's network: forkG 4, forkH 6, join 5, bjoin 8, steerC 2,
steerD 6, mux 4, muxn 0, amerge 2, link 36, src 3, sink 7. -/
theorem ipow_kinds : (List.range 12).map (fun k => (ops.filter (fun o => kindId o == k)).length) =
    [4, 6, 5, 8, 2, 6, 4, 0, 2, 36, 3, 7] := by decide +kernel

theorem ipow_no_muxn : ∀ o : Fin NO, kindId (opAt o) ≠ 7 := by decide +kernel

/-- Fork arities are 2, 3 or 4: every fork ack C-element is one generated LUT. -/
theorem ipow_fork_arity : ∀ o : Fin NO, kindId (opAt o) ≤ 1 →
    2 ≤ arity (opAt o) (extraIn o) ∧ arity (opAt o) (extraIn o) ≤ 4 := by decide +kernel

/-- **H_CTREE_ATOMIC is used at exactly one operator**: every join has real arity 1..4
except op 20 (`uselect0`, arity 5); the three `extraIn` operators are the joins C models with
3, 1 and 1 inputs. -/
theorem ctree_atomic_only_select :
    (∀ o : Fin NO, (kindId (opAt o) = 2 ∨ kindId (opAt o) = 3) → o.val ≠ 20 →
      1 ≤ arity (opAt o) (extraIn o) ∧ arity (opAt o) (extraIn o) ≤ 4) ∧
    kindId (opAt 20) = 2 ∧ arity (opAt 20) (extraIn 20) = 5 ∧
    (opAt 20).insC.length = 3 ∧ (opAt 22).insC.length = 1 ∧ (opAt 24).insC.length = 1 ∧
    kindId (opAt 22) = 2 ∧ kindId (opAt 24) = 2 ∧
    (∀ o : Fin NO, extraIn o ≠ 0 → kindId (opAt o) = 2) := by decide +kernel

/-- **IpowCells: H_CELLS of the ipow network from the per-cell contracts.** -/
theorem ipow_cells (b e : Nat) (ch : Fin NC → Chan)
    (H_CONTRACTS : ∀ o : Fin NO, Contract ch (srcV b e) (extraIn o) (opAt o)) :
    ∀ o : Fin NO, Cell ch (srcV b e) (opAt o) :=
  fun o => cell_of_contract ch (srcV b e) (extraIn o) (opAt o) (H_CONTRACTS o)

/-- **ipow's circuit safety from the cell contracts** (C-8y's `ipow_circuit_safe3` with
H_CELLS discharged by `ipow_cells`). -/
theorem ipow_safe_of_contracts (b e : Nat) (he : e < 2 ^ 32) (ch : Fin NC → Chan)
    (H_CONTRACTS : ∀ o : Fin NO, Contract ch (srcV b e) (extraIn o) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k v, TokAt (ch out0) k v → (ch out0).dat v = IpowHw.ipowSpec b e) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (cnt (fallB (ch out0).ack) t) (IpowHw.ipowSpec b e)) :=
  Formal.Net.IpowCap.ipow_circuit_safe3 b e he ch (ipow_cells b e ch H_CONTRACTS) H_BUNDLE H_START_ONCE

/-! ## 6. Non-vacuity -/

/-- One step of the data equations of the all-quiet run: the value an operator puts on its
output, given the values `dv` of its inputs (link outputs and control outputs are 0). -/
def qstep (sv : Nat → Nat) (dv : Nat → Nat) : K NC → Nat
  | .forkG i _ => dv i.val
  | .forkH i _ _ _ _ _ => dv i.val
  | .join ins _ e js _ => jg e js (ins.map (fun i => dv i.val))
  | .bjoin ins _ ec ed => bg ec ed (ins.map (fun i => dv i.val))
  | .steerD j _ _ fd _ => fd.eval [dv j.val / 2]
  | .mux c x y _ _ => if sel2 (dv c.val) then dv y.val else dv x.val
  | .amerge x _ _ _ => 2 * dv x.val
  | .src _ which _ => sv which
  | _ => 0

/-- The data equations an all-quiet run must solve, per operator (decidable). -/
def DataOK (sv : Nat → Nat) (dv : Fin n → Nat) : K n → Prop
  | .forkG i os => os ≠ [] ∧ ∀ o ∈ os, dv o = dv i
  | .forkH i os _ _ _ _ => os ≠ [] ∧ ∀ p ∈ os, dv p.1 = dv i
  | .join ins o e js _ => ins ≠ [] ∧ dv o = jg e js (ins.map dv)
  | .bjoin ins o ec ed => ins ≠ [] ∧ dv o = bg ec ed (ins.map dv)
  | .steerC _ t f => dv t = 0 ∧ dv f = 0
  | .steerD j t f fd _ => dv t = fd.eval [dv j / 2] ∧ dv f = fd.eval [dv j / 2]
  | .mux c x y z _ => dv z = if sel2 (dv c) then dv y else dv x
  | .muxn .. => False
  | .amerge x _ z _ => dv z = 2 * dv x
  | .link .. => True
  | .src z which _ => dv z = sv which
  | .sink _ => True

instance (sv : Nat → Nat) (dv : Fin n → Nat) (k : K n) : Decidable (DataOK sv dv k) := by
  cases k <;> unfold DataOK <;> infer_instance

/-- The all-quiet run with bus values `dv`: no wire ever moves. -/
def chQ (dv : Fin n → Nat) (c : Fin n) : Chan := ⟨fun _ => false, fun _ => false, fun _ => dv c⟩

/-- A feedback LUT whose pins never move and whose output stays low meets `FbCel`. -/
theorem fbCel_quiet {α : Type} (F : α → Bool → Bool) (p : Nat → α) (hp : ∀ t, p (t + 1) = p t) :
    FbCel F p (fun _ => false) :=
  ⟨fun _ => false, 0, 0, fun _ h => absurd rfl h, ⟨fun _ h => absurd rfl h, fun _ _ _ => rfl⟩, rfl,
    fun u h => absurd (hp u) h⟩

/-- The idle arbiter grants nothing (generated `ugrant`). -/
theorem grant_idle :
    genF bd_arbiter "ugrant" .O5 ["r1", "r2", "q"] [false, false, false] = false ∧
    genF bd_arbiter "ugrant" .O6 ["r1", "r2", "q"] [false, false, false] = false := by decide +kernel

theorem mem_chQ {dv : Fin n → Nat} {l : List (Fin n)} {o : Chan} (h : o ∈ l.map (chQ dv)) :
    ∃ c ∈ l, o = chQ dv c := by
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact ⟨c, hc, rfl⟩

/-- **The all-quiet run meets every contract** whose data equations it solves. -/
theorem quiet_contract (sv : Nat → Nat) (dv : Fin n → Nat) (nx : Nat) (k : K n)
    (hd : DataOK sv dv k) : Contract (chQ dv) sv nx k := by
  cases k with
  | forkG i os =>
    refine ⟨by simpa using hd.1, fun o ho t h => ?_, fbCel_quiet _ _ (fun t => ?_), fun o ho t => ?_, rfl,
      fun o ho => ?_⟩
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; exact absurd rfl h
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, hc, rfl⟩ := mem_chQ ho; exact hd.2 c hc
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; rfl
  | forkH i os l hh d hs =>
    refine ⟨by simpa using hd.1, fun o ho t h => ?_, fbCel_quiet _ _ (fun t => ?_), fun o ho t => ?_, rfl,
      fun o ho => ?_⟩
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; exact absurd rfl h
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, hc, rfl⟩ := mem_chQ ho
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact hd.2 p hp
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; rfl
  | join ins o e js jw =>
    refine ⟨List.replicate nx (fun _ => false), List.length_replicate .., by simpa using hd.1,
      fbCel_quiet _ _ (fun t => ?_), fun i hi t h => ?_, fun t => ?_, rfl, fun i hi => ?_⟩
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; exact absurd rfl h
    · simp only [List.map_map, Function.comp_def, chQ]; exact hd.2
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; rfl
  | bjoin ins o ec ed =>
    refine ⟨List.replicate nx (fun _ => false), List.length_replicate .., by simpa using hd.1,
      fbCel_quiet _ _ (fun t => ?_), fun i hi t h => ?_, fun t => ?_, rfl, fun i hi => ?_⟩
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; exact absurd rfl h
    · simp only [List.map_map, Function.comp_def, chQ]; exact hd.2
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; rfl
  | steerC j t f =>
    refine ⟨fun b u h => absurd rfl h, fun u h => absurd rfl h, fun b u => ?_, rfl, fun b => rfl⟩
    cases b
    · exact hd.2
    · exact hd.1
  | steerD j t f fd sw =>
    refine ⟨fun b u h => absurd rfl h, fun u h => absurd rfl h, fun b u => ?_, rfl, fun b => rfl⟩
    cases b
    · exact hd.2
    · exact hd.1
  | mux c x y z mw =>
    exact ⟨fun _ => false, fun _ => false, fbCel_quiet _ _ (fun _ => rfl), fbCel_quiet _ _ (fun _ => rfl),
      fbCel_quiet _ _ (fun _ => rfl), fbCel_quiet _ _ (fun _ => rfl), fun _ h => absurd rfl h,
      fun _ h => absurd rfl h, fun _ => hd, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | muxn c x0 x1 x2 z nw => exact hd.elim
  | amerge x y z w =>
    refine ⟨fun _ => false, fun _ => false, fun _ h => absurd rfl h, fun _ h => absurd rfl h,
      fun _ => rfl, ⟨fun _ => false, fun _ => grant_idle.1.symm, fun _ => grant_idle.2.symm,
        fun _ h => absurd rfl h⟩, fun _ _ h => by simp [chQ] at h, fbCel_quiet _ _ (fun _ => rfl),
      fbCel_quiet _ _ (fun _ => rfl), fun _ => ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [chQ, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Mux.b2n]
    exact hd
  | link i o =>
    exact ⟨fun _ => false, fbCel_quiet _ _ (fun _ => rfl), fun _ h => absurd rfl h, fun _ h => absurd rfl h,
      fun _ h => by simp at h, fun _ _ => rfl, rfl, rfl, rfl⟩
  | src z which d => exact ⟨fun _ h => absurd rfl h, fun _ => hd, rfl⟩
  | sink i => exact ⟨fun _ h => absurd rfl h, rfl⟩

/-- Bus values of the witness run (b = 3, e = 7, the C file's own `main` vector): a solution
of the all-quiet data equations, computed by iterating `qstep` and checked below by the
kernel (`dataOK_all`), not trusted. -/
def dvL : List Nat := [4, 7, 0, 0, 0, 0, 7, 7, 0, 0, 0, 0, 0, 0, 3, 0, 0, 3, 7, 0, 0, 7, 1, 0, 0, 1,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
  0, 6, 14, 2, 0, 0, 0, 0, 0, 0, 0]

def dvW (c : Fin NC) : Nat := dvL.getD c.val 0

theorem dataOK_all : ∀ o : Fin NO, DataOK (srcV 3 7) dvW (opAt o) := by decide +kernel

theorem cnt_quiet (t : Nat) : cnt (riseB (fun _ => false)) t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [cnt, ih, riseB]

/-- **Non-vacuity of `ipow_safe_of_contracts`**: one run (b = 3, e = 7) meets every
operator contract, H_BUNDLE and H_START_ONCE at once. It is the all-quiet run (as for gcd's
H_CELLS, no network-level run that delivers `out0` is known: liveness is open). -/
theorem ipow_contracts_satisfiable :
    ∃ (b e : Nat) (ch : Fin NC → Chan), e < 2 ^ 32 ∧
      (∀ o : Fin NO, Contract ch (srcV b e) (extraIn o) (opAt o)) ∧ (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) :=
  ⟨3, 7, chQ dvW, by decide, fun o => quiet_contract _ _ _ _ (dataOK_all o),
    fun _ _ _ _ => rfl, fun t => by rw [show (chQ dvW start).req = fun _ => false from rfl, cnt_quiet]; decide⟩

/-- The two-input generated C-element is C-10k's majority-with-feedback `maj`. -/
theorem cgate2_maj : ∀ a b q : Bool, cgate [a, b] q = Formal.Timing.FbFirstRt.maj (a, b) q := by
  decide +kernel

/-- **`FbCel` is met by a C-element that really switches**, with its feedback route given in
B's own channel model: C-10k's run (both inputs rise at 5, output at 6, feedback pin at 7),
feedback wire = `CElemTiming.WinDelay 1 1` (a transport delay of 1, `transport_winDelay`),
H_RT_FB at the wire's maximum delay 1. -/
theorem fbCel_witness :
    let p : Nat → List Bool := fun t => [(Formal.Timing.FbFirstRt.wp t).1, (Formal.Timing.FbFirstRt.wp t).2]
    FbCel cgate p Formal.Timing.FbFirstRt.wo ∧
      CElemTiming.WinDelay 1 1 Formal.Timing.FbFirstRt.wo Formal.Timing.FbFirstRt.wq ∧
      Formal.Timing.FbFirstRt.wo 6 ≠ Formal.Timing.FbFirstRt.wo 5 := by
  intro p
  obtain ⟨hL, _, _, hR, _, hc⟩ := Formal.Timing.FbFirstRt.fbFirst_witness
  have hW : CElemTiming.WinDelay 1 1 Formal.Timing.FbFirstRt.wo Formal.Timing.FbFirstRt.wq :=
    CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun t => by
      simp only [Formal.Timing.FbFirstRt.wq, Formal.Timing.FbFirstRt.wo]
      by_cases h : 6 ≤ t <;> simp [h] <;> omega)
  refine ⟨fbCel_of_winDelay (fun t h => ?_) hW (fun t h => by omega) rfl (fun u h => hR u ?_), hW, hc⟩
  · rw [hL t h]; exact (cgate2_maj _ _ _).symm
  · intro he; apply h; simp only [p, he]

end Formal.Cells.IpowCells
