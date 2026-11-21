import Formal.Gen.Cells
import Formal.Net.OpsFork
import Formal.Net.OpsJoin
import Formal.Net.OpsSteer
import Formal.Net.OpsMux
import Formal.Net.OpsCM
import Formal.Net.OpsLink
import Formal.Net.OpsMuxNOp
import Formal.Net.CapstoneSrc
import Formal.Net.OpsGcd
import Formal.Net.Bridge

/-!
# Probe C-8n (O4): the Ops gate models are the generated cells

C-8f/8j/8l model each operator (fork, join, steer, mux, muxN, amerge, link,
src, sink) by hand-written SI gate relations ("node `o` moves only to the value
`F` of its inputs one tick earlier"). C-11d generated, from yosys, the netlist
of every library cell (`Formal/Gen/Cells.lean`). This file closes the gap
between the two (C-8l open item O4).

## The physical gate, and the one extra timing condition

A LUT with feedback (C-element, mux join `uj0`, link controller) does not read
its own output: pin `I2`/`I3` reads the routed copy `qp` of the output `o`. The
physical SI relation is therefore

* `LutFb F p qp o` (H_LUT_SI, physical form): `o` changes only to
  `F (p t) (qp t)`, the generated LUT's function of the pin values one tick
  earlier, with the FEEDBACK PIN's value `qp t`, not `o t`.

The Ops models read `o t` in place of `qp t`. The condition under which they
agree is

* `FbFirst qp o` (H_FB_FIRST, the step form of shard B's C2,
  "feedback-first"/`H_ENV_LATENCY`/`H_FB_FAST`): whenever `o` changes, the
  feedback pin already shows `o`.

`fbFirst_of_gap`: if the feedback route is any channel with a settle bound
`hi` (B's `WinDelay`, Bridge's `Inertial`/`NoOvertake`, `Prelim.BoundedDelay`
all have this `settle` field), then H_FB_FIRST follows from
`Gap hi o`: consecutive output changes are at least `hi` ticks apart (and the
first is at least `hi` after reset). That is B's C1/C2 in time: B's
`c2_four_phase` derives exactly this separation (`c (k+1) ≥ c k + Dmax`) from
`H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E`. `fb_stale_breaks`: without it,
the generated C-element LUT legally drops a held 1 while its inputs disagree,
violating the Ops fork/join field (negative control).

## What is proved, per cell

For each cell: (1) the generated gate (`Netlist.gateN boolSem`, i.e. shard A's
`Lut.eval` on the yosys INIT and pin map) equals the Ops model's function,
by `decide +kernel` over all inputs; (2) a node that obeys the generated gate
physically (`LutFb`/`LutSI` with `genF …`, the generated function itself in the
hypothesis) and H_FB_FIRST satisfies the Ops field verbatim.

| Ops field | generated cell | extra hypothesis |
|---|---|---|
| `Fork.cel` (N=2) | `bd_fork_N2` `u.genblk1.g2.u.u` (bd_c2) | H_FB_FIRST |
| `Join.cel` (N=2, 3) | `bd_join_N2`, `bd_join_N3` | H_FB_FIRST |
| `Steer.lut`, `Steer.orr` | `bd_steer` `u` (O5/O6), `uack` | H_SEL_PIN (`s` pin = `sel (j.dat)`) |
| `Mux.cj0/cj1/xa/ya` | `bd_mux_W2` `uj0`,`uj1`,`uxa.u`,`uya.u` | H_FB_FIRST, H_SEL_PIN |
| `Mux.zr` | `uor` → `udly.chain.g[0..1].u` composes to `j0 ∨ j1` | H_DELAY_LUMPED (named, not derived) |
| `Mux.ca` | `ctl_ack` is the `z_ack` net | H_WIRE_DI (generalisation) |
| `MuxN.cj/xa` | `bd_c2` (bdc_muxn instantiates `bd_c2` per input) | H_FB_FIRST, H_SEL_PIN (decode) |
| `AMerge.xa/ya` | `bd_arbiter` `ua1.u`, `ua2.u` | H_FB_FIRST |
| `AMerge.zr` (function) | `ustate` O5 (`R0`) = `ugrant` O5 ∨ O6 on every input | H_DELAY_LUMPED; `H_ARB*` remain B's |
| `Link.H_CEL_SI` | `bd_link_W2` `ctl.u.u` (= B's `ctlB`) | H_FB_FIRST |
| `Src.H_LUT_SI` | `bd_src_W2` `u` (LUT1 `¬ack`) | none |
| `Sink.wire` | `bd_snk_W2` has no cell: `ack` IS the `req` net | H_WIRE_DI (generalisation) |

Not bound here: the fork/join C-TREE for N ≥ 4 (two LUT levels; the Ops model
lumps the tree, H_CTREE_ATOMIC, which is B's `CTree` result), the data paths
(H_DATA_COMB; only the bit-level datamux function is checked), and the
arbiter's grant behaviour (`H_ARB1/2`, B's `ArbBinary`/`ArbHandover`).
-/

namespace Formal.Net.Ops.Gen
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Gen Formal.Gen.Cells

/-! ## 1. The physical gate and H_FB_FIRST -/

/-- H_LUT_SI, physical form, for a LUT reading its own output through the
feedback pin trace `qp`: `o` changes only to `F` of the pin values (`p t`)
and the feedback pin (`qp t`) one tick earlier. -/
def LutFb {α : Type} (F : α → Bool → Bool) (p : Nat → α) (qp o : Trace) : Prop :=
  ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t) (qp t)

/-- H_LUT_SI for a LUT without feedback. -/
def LutSI {α : Type} (F : α → Bool) (p : Nat → α) (o : Trace) : Prop :=
  ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t)

/-- H_FB_FIRST (step form of B's C2): whenever the output changes, the feedback
pin already reads the output. -/
def FbFirst (qp o : Trace) : Prop := ∀ t, o (t + 1) ≠ o t → qp t = o t

/-- Output changes are spaced: each is at least `hi` ticks after the previous
one and after reset (B's C1/C2 separation, `c (k+1) ≥ c k + Dmax`). -/
def Gap (hi : Nat) (o : Trace) : Prop := ∀ t, o (t + 1) ≠ o t → hi ≤ t ∧ stableOn o (t - hi) t

/-- The settle half of any bounded channel from `o` to `qp`. -/
def SettleFrom (hi : Nat) (o qp : Trace) : Prop := ∀ t, hi ≤ t → stableOn o (t - hi) t → qp t = o t

theorem fbFirst_of_gap {hi : Nat} {o qp : Trace} (hs : SettleFrom hi o qp) (hg : Gap hi o) :
    FbFirst qp o := fun t h => hs t (hg t h).1 (hg t h).2

/-- Every channel the project uses has this settle half. -/
theorem settle_of_bounded {lo hi : Nat} {o qp : Trace} (h : BoundedDelay lo hi o qp) :
    SettleFrom hi o qp := h.settle
theorem settle_of_inertial {lo hi : Nat} {o qp : Trace} (h : Bridge.Inertial lo hi o qp) :
    SettleFrom hi o qp := h.settle
theorem settle_of_noOvertake {hi : Nat} {o qp : Trace} (h : Bridge.NoOvertake hi o qp) :
    SettleFrom hi o qp := h.settle

/-- Under H_FB_FIRST the physical gate is the Ops-style SI gate on `o` itself. -/
theorem lutFb_si {α : Type} {F : α → Bool → Bool} {p : Nat → α} {qp o : Trace}
    (hL : LutFb F p qp o) (hF : FbFirst qp o) : ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t) (o t) := by
  intro t h; rw [hL t h, hF t h]

/-! ## 2. The generated gate functions

`genF nl cell pin names vs`: the output pin `pin` of cell `cell` of the generated
netlist `nl`, with the nets `names` (in that order) carrying `vs`; `false` if
the netlist does not compute it (it always does below: every `_gate` lemma
says `some`). -/

def genF (nl : Netlist) (cell : String) (pin : Pin) (names : List String) (vs : List Bool) : Bool :=
  (nl.gateN boolSem cell pin (names.zip vs)).getD false

/-- The 2-input C-element (`Fork.cel`, `Join.cel`, mux `uxa`). -/
def cel2 (a b q : Bool) : Bool := if a = b then a else q
/-- The 3-input C-element. -/
def cel3 (a b c q : Bool) : Bool := if a = b ∧ b = c then a else q

theorem cel2_move : ∀ a b q : Bool, cel2 a b q ≠ q → a = cel2 a b q ∧ b = cel2 a b q := by decide
theorem cel3_move : ∀ a b c q : Bool, cel3 a b c q ≠ q →
    a = cel3 a b c q ∧ b = cel3 a b c q ∧ c = cel3 a b c q := by decide

/-! ### fork / join -/

def forkCell := "u.genblk1.g2.u.u"

/-- `bd_fork` N = 2: the acknowledge LUT is the C-element of the two branch
acks with feedback `ack`, in run mode (`rst = 0`); both `req_out` ports are
the `req` net itself (the fan-out is wire). -/
theorem fork2_gate : ∀ a0 a1 q : Bool,
    genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"] [a0, a1, q, false] =
      cel2 a0 a1 q := by decide +kernel

theorem fork2_wires : bd_fork_N2.outputs = [("ack", .net 4), ("req_out[0]", .net 3), ("req_out[1]", .net 3)] ∧
    bd_fork_N2.netName 3 = "req" ∧ bd_fork_N2.netName 4 = "ack" := by decide

theorem join2_gate : ∀ r0 r1 q : Bool,
    genF bd_join_N2 forkCell .O ["req_in[0]", "req_in[1]", "req", "rst"] [r0, r1, q, false] =
      cel2 r0 r1 q := by decide +kernel

theorem join2_wires : bd_join_N2.outputs = [("ack_out[0]", .net 5), ("ack_out[1]", .net 5), ("req", .net 6)] ∧
    bd_join_N2.netName 5 = "ack" := by decide

theorem join3_gate : ∀ r0 r1 r2 q : Bool,
    genF bd_join_N3 "u.genblk1.genblk1.g3.u.u" .O ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"]
      [r0, r1, r2, q, false] = cel3 r0 r1 r2 q := by decide +kernel

/-- **Fork, bound.** The fork's acknowledge node obeys the generated LUT with its
feedback pin `qp`, and H_FB_FIRST holds: then `Fork.cel` holds. -/
theorem fork2_cel {a o0 o1 : Chan} {qp : Trace}
    (hL : LutFb (fun p q => genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"]
      [p.1, p.2, q, false]) (fun t => (o0.ack t, o1.ack t)) qp a.ack)
    (hF : FbFirst qp a.ack) :
    ∀ t, a.ack (t + 1) ≠ a.ack t → ∀ o ∈ [o0, o1], o.ack t = a.ack (t + 1) := by
  intro t h o ho
  have e := lutFb_si hL hF t h
  simp only [fork2_gate] at e
  have m := cel2_move (o0.ack t) (o1.ack t) (a.ack t) (by rw [← e]; exact h)
  rw [← e] at m
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · exact m.1
  · exact m.2

theorem join2_cel {i0 i1 o : Chan} {qp : Trace}
    (hL : LutFb (fun p q => genF bd_join_N2 forkCell .O ["req_in[0]", "req_in[1]", "req", "rst"]
      [p.1, p.2, q, false]) (fun t => (i0.req t, i1.req t)) qp o.req)
    (hF : FbFirst qp o.req) :
    ∀ t, o.req (t + 1) ≠ o.req t → ∀ i ∈ [i0, i1], i.req t = o.req (t + 1) := by
  intro t h i hi
  have e := lutFb_si hL hF t h
  simp only [join2_gate] at e
  have m := cel2_move (i0.req t) (i1.req t) (o.req t) (by rw [← e]; exact h)
  rw [← e] at m
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact m.1
  · exact m.2

theorem join3_cel {i0 i1 i2 o : Chan} {qp : Trace}
    (hL : LutFb (fun (p : Bool × Bool × Bool) q => genF bd_join_N3 "u.genblk1.genblk1.g3.u.u" .O
      ["req_in[0]", "req_in[1]", "req_in[2]", "req", "rst"] [p.1, p.2.1, p.2.2, q, false])
      (fun t => (i0.req t, i1.req t, i2.req t)) qp o.req)
    (hF : FbFirst qp o.req) :
    ∀ t, o.req (t + 1) ≠ o.req t → ∀ i ∈ [i0, i1, i2], i.req t = o.req (t + 1) := by
  intro t h i hi
  have e := lutFb_si hL hF t h
  simp only [join3_gate] at e
  have m := cel3_move (i0.req t) (i1.req t) (i2.req t) (o.req t) (by rw [← e]; exact h)
  rw [← e] at m
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact m.1
  · exact m.2.1
  · exact m.2.2

/-- **Negative control: H_FB_FIRST is needed.** The generated fork LUT, read
with a stale feedback pin (`qp = 0` while `ack = 1`), lets `ack` fall while
the branches disagree; `Fork.cel` then fails. -/
theorem fb_stale_breaks :
    genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"] [true, false, false, false] = false := by
  decide +kernel

/-- The stale-feedback run, as traces: branch acks `1, 0`, the node `ack` falls
from 1 to 0 at `t = 0` reading `qp = 0`. It obeys `LutFb` with the generated
LUT, and violates `Fork.cel`. -/
theorem fb_stale_run :
    let o0 : Chan := ⟨fun _ => false, fun _ => true, fun _ => 0⟩
    let o1 : Chan := ⟨fun _ => false, fun _ => false, fun _ => 0⟩
    let a : Chan := ⟨fun _ => false, fun t => decide (t = 0), fun _ => 0⟩
    LutFb (fun p q => genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"]
      [p.1, p.2, q, false]) (fun t => (o0.ack t, o1.ack t)) (fun _ => false) a.ack ∧
    ¬ (∀ t, a.ack (t + 1) ≠ a.ack t → ∀ o ∈ [o0, o1], o.ack t = a.ack (t + 1)) := by
  intro o0 o1 a
  refine ⟨fun t h => ?_, fun H => ?_⟩
  · have ht : t = 0 := by
      apply Classical.byContradiction; intro hne
      apply h; simp [a]; omega
    subst ht
    show decide (1 = 0) = genF bd_fork_N2 forkCell .O _ [true, false, false, false]
    decide +kernel
  · have := H 0 (by simp [a]) o0 (by simp)
    simp [o0, a] at this

/-! ### steer -/

/-- `bd_steer`: `req0 = req ∧ ¬s` (O5), `req1 = req ∧ s` (O6), `ack = ack0 ∨ ack1`. -/
theorem steer_gate : ∀ r s a0 a1 : Bool,
    genF bd_steer "u" .O5 ["req", "s"] [r, s] = (r && (s == false)) ∧
    genF bd_steer "u" .O6 ["req", "s"] [r, s] = (r && (s == true)) ∧
    genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1] = (a1 || a0) := by decide +kernel

/-- The generated steer's branch LUT as a function of the branch index. -/
def steerF (b : Bool) (p : Bool × Bool) : Bool :=
  genF bd_steer "u" (if b then .O6 else .O5) ["req", "s"] [p.1, p.2]

/-- **Steer, bound.** Branch `b`'s request obeys the generated LUT on the pins
`req = j.req`, `s = sel (j.dat)` (H_SEL_PIN: the select pin reads the decoded
condition, zero-delay data; its real delay is H_STEER_SEL), and the
acknowledge obeys `uack`: then `Steer.lut` and `Steer.orr` hold. -/
theorem steer_bound {sel : Nat → Bool} {j : Chan} {out : Bool → Chan}
    (hL : ∀ b, LutSI (steerF b) (fun t => (j.req t, sel (j.dat t))) (out b).req)
    (hA : LutSI (fun p : Bool × Bool => genF bd_steer "uack" .O ["ack0", "ack1"] [p.1, p.2])
      (fun t => ((out false).ack t, (out true).ack t)) j.ack) :
    (∀ b t, (out b).req (t + 1) ≠ (out b).req t →
      (out b).req (t + 1) = (j.req t && (sel (j.dat t) == b))) ∧
    (∀ t, j.ack (t + 1) ≠ j.ack t → j.ack (t + 1) = ((out true).ack t || (out false).ack t)) := by
  refine ⟨fun b t h => ?_, fun t h => ?_⟩
  · rw [hL b t h]
    cases b <;> simp only [steerF]
    · exact (steer_gate _ _ false false).1
    · exact (steer_gate _ _ false false).2.1
  · rw [hA t h]; exact (steer_gate false false _ _).2.2

/-! ### mux (`bd_mux` W = 2) -/

/-- `uj0 = C(x_req, ctl_req ∧ ¬s)`, `uj1 = C(y_req, ctl_req ∧ s)` with feedback,
`uxa = C(j0, z_ack)`, `uya = C(j1, z_ack)`, in run mode. -/
theorem mux_gate : ∀ x y c s q z : Bool,
    genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"] [x, c, s, q, false] =
      cel2 x (c && !s) q ∧
    genF bd_mux_W2 "uj1" .O ["y_req", "ctl_req", "s", "j1", "rst"] [y, c, s, q, false] =
      cel2 y (c && s) q ∧
    genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"] [x, z, q, false] = cel2 x z q ∧
    genF bd_mux_W2 "uya.u" .O ["j1", "z_ack", "y_ack", "rst"] [y, z, q, false] = cel2 y z q := by
  decide +kernel

/-- The request path `uor → udly.chain.g[0] → udly.chain.g[1]` computes `j0 ∨ j1`
(the Ops model lumps it into one inertial node: H_DELAY_LUMPED). -/
theorem mux_zr_chain : ∀ j0 j1 : Bool,
    genF bd_mux_W2 "udly.chain.g[1].u" .O ["udly.chain.s[1]"]
      [genF bd_mux_W2 "udly.chain.g[0].u" .O ["either"]
        [genF bd_mux_W2 "uor" .O ["j0", "j1"] [j0, j1]]] = (j0 || j1) := by decide +kernel

/-- `ctl_ack` is the `z_ack` net; the data mux bit is `s ? y : x`. -/
theorem mux_wires : bd_mux_W2.outputs.lookup "ctl_ack" = some (.net 12) ∧ bd_mux_W2.netName 12 = "z_ack" ∧
    ∀ s x y x1 y1 : Bool, genF bd_mux_W2 "udat.pair[0].u" .O5
      ["s", "x_data[0]", "y_data[0]", "x_data[1]", "y_data[1]"] [s, x, y, x1, y1] =
      (if s then y else x) := by decide +kernel

def muxJ0F (p : Bool × Bool × Bool) (q : Bool) : Bool :=
  genF bd_mux_W2 "uj0" .O ["x_req", "ctl_req", "s", "j0", "rst"] [p.1, p.2.1, p.2.2, q, false]
def muxJ1F (p : Bool × Bool × Bool) (q : Bool) : Bool :=
  genF bd_mux_W2 "uj1" .O ["y_req", "ctl_req", "s", "j1", "rst"] [p.1, p.2.1, p.2.2, q, false]
def muxXaF (p : Bool × Bool) (q : Bool) : Bool :=
  genF bd_mux_W2 "uxa.u" .O ["j0", "z_ack", "x_ack", "rst"] [p.1, p.2, q, false]
def muxYaF (p : Bool × Bool) (q : Bool) : Bool :=
  genF bd_mux_W2 "uya.u" .O ["j1", "z_ack", "y_ack", "rst"] [p.1, p.2, q, false]

/-- **Mux, bound.** The four C-element nodes obey the generated LUTs (feedback
pins `q0 … q3`) with H_FB_FIRST, and the select pin reads `sel (c.dat)`
(H_SEL_PIN): then `Mux.cj0`, `cj1`, `xa`, `ya` hold. -/
theorem mux_bound {sel : Nat → Bool} {x y c z : Chan} {j0 j1 q0 q1 q2 q3 : Trace}
    (h0 : LutFb muxJ0F (fun t => (x.req t, c.req t, sel (c.dat t))) q0 j0) (f0 : FbFirst q0 j0)
    (h1 : LutFb muxJ1F (fun t => (y.req t, c.req t, sel (c.dat t))) q1 j1) (f1 : FbFirst q1 j1)
    (h2 : LutFb muxXaF (fun t => (j0 t, z.ack t)) q2 x.ack) (f2 : FbFirst q2 x.ack)
    (h3 : LutFb muxYaF (fun t => (j1 t, z.ack t)) q3 y.ack) (f3 : FbFirst q3 y.ack) :
    (∀ t, j0 (t + 1) ≠ j0 t → x.req t = j0 (t + 1) ∧ (c.req t && !sel (c.dat t)) = j0 (t + 1)) ∧
    (∀ t, j1 (t + 1) ≠ j1 t → y.req t = j1 (t + 1) ∧ (c.req t && sel (c.dat t)) = j1 (t + 1)) ∧
    (∀ t, x.ack (t + 1) ≠ x.ack t → j0 t = x.ack (t + 1) ∧ z.ack t = x.ack (t + 1)) ∧
    (∀ t, y.ack (t + 1) ≠ y.ack t → j1 t = y.ack (t + 1) ∧ z.ack t = y.ack (t + 1)) := by
  refine ⟨fun t h => ?_, fun t h => ?_, fun t h => ?_, fun t h => ?_⟩
  · have e := lutFb_si h0 f0 t h
    simp only [muxJ0F, (mux_gate _ false _ _ _ false).1] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m
  · have e := lutFb_si h1 f1 t h
    simp only [muxJ1F, (mux_gate false _ _ _ _ false).2.1] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m
  · have e := lutFb_si h2 f2 t h
    simp only [muxXaF, (mux_gate _ false false false _ _).2.2.1] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m
  · have e := lutFb_si h3 f3 t h
    simp only [muxYaF, (mux_gate false _ false false _ _).2.2.2] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m

/-! ### muxN (bdc_muxn: one `bd_c2` per input join and per input ack) -/

def c2F (p : Bool × Bool) (q : Bool) : Bool := genF bd_c2 "u" .O ["a", "b", "q", "rst"] [p.1, p.2, q, false]

theorem c2_gate : ∀ a b q : Bool, c2F (a, b) q = cel2 a b q := by
  intro a b q; revert a b q; decide +kernel

/-- **MuxN, bound.** bdc's `emit_muxn` instantiates `bd_c2 uj_k (in_k_req,
ctl_req ∧ (s == k))` and `bd_c2 ua_k (j_k, z_ack)`. With the generated `bd_c2`
LUT, H_FB_FIRST, and the decode `ctl_req ∧ (s == k)` read at the `b` pin
(H_SEL_PIN; bdc's header argues the decode cannot glitch), `MuxN.cj` and
`MuxN.xa` hold. -/
theorem muxn_bound {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j qj qa : Nat → Trace}
    (hj : ∀ k, k < 3 → LutFb c2F (fun t => ((xs k).req t, c.req t && (sel (c.dat t) == k))) (qj k) (j k))
    (fj : ∀ k, k < 3 → FbFirst (qj k) (j k))
    (ha : ∀ k, k < 3 → LutFb c2F (fun t => (j k t, z.ack t)) (qa k) (xs k).ack)
    (fa : ∀ k, k < 3 → FbFirst (qa k) (xs k).ack) :
    (∀ k, k < 3 → ∀ t, j k (t + 1) ≠ j k t →
      (xs k).req t = j k (t + 1) ∧ (c.req t && (sel (c.dat t) == k)) = j k (t + 1)) ∧
    (∀ k, k < 3 → ∀ t, (xs k).ack (t + 1) ≠ (xs k).ack t →
      j k t = (xs k).ack (t + 1) ∧ z.ack t = (xs k).ack (t + 1)) := by
  refine ⟨fun k hk t h => ?_, fun k hk t h => ?_⟩
  · have e := lutFb_si (hj k hk) (fj k hk) t h
    rw [c2_gate] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m
  · have e := lutFb_si (ha k hk) (fa k hk) t h
    rw [c2_gate] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m

/-! ### amerge (`bd_arbiter` acknowledge C-elements and `R0`) -/

theorem arb_gate : ∀ g a q : Bool,
    genF bd_arbiter "ua1.u" .O ["g1", "A0", "A1", "rst"] [g, a, q, false] = cel2 g a q ∧
    genF bd_arbiter "ua2.u" .O ["g2", "A0", "A2", "rst"] [g, a, q, false] = cel2 g a q := by
  decide +kernel

/-- `R0` (the request bdc's amerge delays into `z_req`) is, on every input
combination, the OR of the two grants: the lumped `AMerge.zr` function. -/
theorem arb_r0_or : ∀ r1 r2 q a : Bool,
    genF bd_arbiter "ustate" .O5 ["r1", "r2", "q", "rst", "A0"] [r1, r2, q, false, a] =
      (genF bd_arbiter "ugrant" .O5 ["r1", "r2", "q"] [r1, r2, q] ||
       genF bd_arbiter "ugrant" .O6 ["r1", "r2", "q"] [r1, r2, q]) := by decide +kernel

def arbA1F (p : Bool × Bool) (q : Bool) : Bool := genF bd_arbiter "ua1.u" .O ["g1", "A0", "A1", "rst"] [p.1, p.2, q, false]
def arbA2F (p : Bool × Bool) (q : Bool) : Bool := genF bd_arbiter "ua2.u" .O ["g2", "A0", "A2", "rst"] [p.1, p.2, q, false]

/-- **AMerge acknowledges, bound** (n = 2: `A0 = z_ack`, `A1 = x_ack`, `A2 = y_ack`). -/
theorem amerge_ack_bound {x y z : Chan} {g1 g2 q1 q2 : Trace}
    (h1 : LutFb arbA1F (fun t => (g1 t, z.ack t)) q1 x.ack) (f1 : FbFirst q1 x.ack)
    (h2 : LutFb arbA2F (fun t => (g2 t, z.ack t)) q2 y.ack) (f2 : FbFirst q2 y.ack) :
    (∀ t, x.ack (t + 1) ≠ x.ack t → g1 t = x.ack (t + 1) ∧ z.ack t = x.ack (t + 1)) ∧
    (∀ t, y.ack (t + 1) ≠ y.ack t → g2 t = y.ack (t + 1) ∧ z.ack t = y.ack (t + 1)) := by
  refine ⟨fun t h => ?_, fun t h => ?_⟩
  · have e := lutFb_si h1 f1 t h
    simp only [arbA1F, (arb_gate _ _ _).1] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m
  · have e := lutFb_si h2 f2 t h
    simp only [arbA2F, (arb_gate _ _ _).2] at e
    have m := cel2_move _ _ _ (by rw [← e]; exact h); rw [← e] at m; exact m

/-! ### link, src, sink -/

def linkF (p : Bool × Bool) (q : Bool) : Bool :=
  genF bd_link_W2 "ctl.u.u" .O ["req_in", "ack_out", "ack_in", "rst"] [p.1, p.2, q, false]

theorem link_gate : ∀ r a q : Bool, linkF (r, a) q = Formal.Cells.LinkHandshake.ctlB r a q false := by
  intro r a q; revert r a q; decide +kernel

/-- In the generated `bd_link`, `ack_in` and `req_out` are the controller node
itself (the Ops model's two DI wires generalise this). -/
theorem link_wires : bd_link_W2.outputs.take 2 = [("ack_in", .net 4), ("req_out", .net 4)] := by decide

/-- **Link, bound.** -/
theorem link_bound {i o : Chan} {c qp : Trace}
    (hL : LutFb linkF (fun t => (i.req t, o.ack t)) qp c) (hF : FbFirst qp c) :
    ∀ t, c (t + 1) ≠ c t → c (t + 1) = Formal.Cells.LinkHandshake.ctlB (i.req t) (o.ack t) (c t) false := by
  intro t h; rw [lutFb_si hL hF t h, link_gate]

theorem src_gate : ∀ a : Bool, genF bd_src_W2 "u" .O ["ack"] [a] = !a := by decide +kernel

/-- **Src, bound.** -/
theorem src_bound {z : Chan}
    (hL : LutSI (fun a => genF bd_src_W2 "u" .O ["ack"] [a]) z.ack z.req) :
    ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = !z.ack t := by
  intro t h; rw [hL t h]; exact src_gate _

/-- `bd_snk` has no cell: its `ack` port is the `req` net. -/
theorem snk_wire : bd_snk_W2.cells = [] ∧ bd_snk_W2.outputs = [("ack", .net 2)] ∧
    bd_snk_W2.netName 2 = "req" := by decide

/-! ## 3. Assembled: the Ops structures from generated cells

The two C-element-only operators are assembled in full (every field). -/

/-- **`Fork` from the generated cell.** -/
theorem fork_of_gen {a o0 o1 : Chan} {qp : Trace}
    (hL : LutFb (fun p q => genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"]
      [p.1, p.2, q, false]) (fun t => (o0.ack t, o1.ack t)) qp a.ack)
    (hF : FbFirst qp a.ack)
    (H_WIRE_DI : ∀ o ∈ [o0, o1], ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t)
    (H_DATA_WIRE : ∀ o ∈ [o0, o1], ∀ t, o.dat t = a.dat t)
    (ia : a.ack 0 = false) (io : ∀ o ∈ [o0, o1], o.req 0 = false) :
    Fork.Fork a [o0, o1] :=
  ⟨by simp, H_WIRE_DI, fork2_cel hL hF, H_DATA_WIRE, ia, io⟩

/-- **`Join` from the generated cell.** -/
theorem join_of_gen {g : List Nat → Nat} {i0 i1 o : Chan} {qp : Trace}
    (hL : LutFb (fun p q => genF bd_join_N2 forkCell .O ["req_in[0]", "req_in[1]", "req", "rst"]
      [p.1, p.2, q, false]) (fun t => (i0.req t, i1.req t)) qp o.req)
    (hF : FbFirst qp o.req)
    (H_WIRE_DI : ∀ i ∈ [i0, i1], ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t)
    (H_DATA_COMB : ∀ t, o.dat t = g ([i0, i1].map (fun i => i.dat t)))
    (io : o.req 0 = false) (ii : ∀ i ∈ [i0, i1], i.ack 0 = false) :
    Join.Join g [i0, i1] o :=
  ⟨by simp, join2_cel hL hF, H_WIRE_DI, H_DATA_COMB, io, ii⟩

/-- **`Link` from the generated cell.** -/
theorem link_of_gen {i o : Chan} {c qp : Trace}
    (hL : LutFb linkF (fun t => (i.req t, o.ack t)) qp c) (hF : FbFirst qp c)
    (H_ACK_DI : ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = c t)
    (H_REQ_DI : ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = c t)
    (H_LATCH_OPEN : ∀ t, c t = true → o.dat t = i.dat t)
    (H_LATCH_HOLD : ∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t)
    (ic : c 0 = false) (ii : i.ack 0 = false) (io : o.req 0 = false) :
    Link.Link i o c :=
  ⟨link_bound hL hF, H_ACK_DI, H_REQ_DI, H_LATCH_OPEN, H_LATCH_HOLD, ic, ii, io⟩

/-- **`Src` from the generated cell.** -/
theorem src_of_gen {z : Chan} {v : Nat}
    (hL : LutSI (fun a => genF bd_src_W2 "u" .O ["ack"] [a]) z.ack z.req)
    (hd : ∀ t, z.dat t = v) (iz : z.req 0 = false) : Capstone.Src z v :=
  ⟨src_bound hL, hd, iz⟩

end Formal.Net.Ops.Gen
