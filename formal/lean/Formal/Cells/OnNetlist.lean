import Formal.Core.LutList
import Formal.Cells.MuxTree
import Formal.Cells.CElemFn
import Formal.Cells.Latch
import Formal.Cells.ArbBinary
import Formal.Cells.ArbKleene
import Formal.Net.Fasm.Basic
import Formal.Net.FasmLink.S1
import Formal.Net.FasmLink.S2
import Formal.Net.FasmLink.S3
import Formal.Net.FasmLink.S4
open Formal.Core.LutList

/-!
# Probe Bn: shard B's cell theorems on the netlist read back from the bits

Shard B's cell theorems are stated about the RTL's INIT constants on the
RTL's pin order (`lutB`/`lutK`/`o5K`/`o6K` of `Formal.Cells.Prelim`), i.e.
about a hand transcription of `cells/rtl`. Shard C (track 11c,
`Formal.Net.FasmLink`) read the physical LUT netlist of `link_arb` (one
`bd_link #(.W(3))` + one `bd_arbiter`) back from four routed `.bit` files
(seeds 1..4, nextpnr sha256 9c732bc6303458df, `toolchain.sh` ok): physical
INIT on physical pins A1..A6, every pin's source as the active pips route it
(`Formal.Net.FasmLink.S<n>.net`, generated, used unchanged here).

This file states shard B's functions DIRECTLY about those physical LUTs: no
yosys netlist and no RTL transcription in between.

## Model (gate level, the same granularity as `ArbKleene.Net`)

* Every physical LUT output is a node with its own value `w i o : K3`; every
  input port has a value `pv j : K3` (`j` = index in the common port list).
* A pin reads its routed source: a tie is the constant (11b's H_TIE), a port
  or LUT output its current value. All pins fed from one source read the same
  value here: per-pin skew (11b's `Behaves.H_ROUTE`) is NOT modelled; it is
  covered by B's scenarios only where they put `x` on the whole window.
* `excK N pv w i o` = the Kleene LUT function (`o6K`/`o5K`, hypothesis
  H_KLEENE_LUT of Prelim) of the PHYSICAL INIT on the PHYSICAL pin vector.
  The binary counterpart is 11b's own `PNet.exc` (`o6B`/`o5B`), unchanged.

## Node map

`Seed.m` names the physical source of every logical node. Ports are fixed by
the (common, checked) port order; state nodes come from C's renaming `rho`;
the combinational nodes g1, g2, R0 from the output ports the bits drive.
None of it is trusted: every claim below is a statement about the physical
LUT at `m n` and the physical sources at `m n'`, and `map_consistent_s*`
checks that the output ports A1, A2, ack_in, req_out, data_out[*] are driven
by the mapped LUT outputs.

## Proof method

`Seed.check n args F` resolves each physical pin of the LUT at `m n` to a
logical node or a tie, then enumerates all K3 values (3^|support|, support
<= 5 here) of the nodes it can read on either side. `check_sound` proves this
covers every `pv`, `w` (the physical side reads only its resolved pins, the
spec only `args`). Plain `decide` per seed.
-/

namespace Formal.Cells.OnNetlist
open Formal.Cells
open Formal.Net.Fasm (Src LOut PLut PNet)

/-! ## Logical nodes of `link_arb` -/

inductive Node
  | r1 | r2 | a0 | rst | reqIn | ackOut | d0 | d1 | d2
  | c | q0 | q1 | q2 | a1 | a2 | q | g1 | g2 | r0
  deriving DecidableEq, Repr

def allNodes : List Node :=
  [.r1, .r2, .a0, .rst, .reqIn, .ackOut, .d0, .d1, .d2,
   .c, .q0, .q1, .q2, .a1, .a2, .q, .g1, .g2, .r0]

/-- The port order of all four seeds (`Src.port j` reads `ports[j]`). -/
def ports : List String :=
  ["A0", "ack_out", "data_in[0]", "data_in[1]", "data_in[2]", "r1", "r2", "req_in", "rst"]

theorem ports_s1 : Formal.Net.FasmLink.S1.ports = ports := rfl
theorem ports_s2 : Formal.Net.FasmLink.S2.ports = ports := rfl
theorem ports_s3 : Formal.Net.FasmLink.S3.ports = ports := rfl
theorem ports_s4 : Formal.Net.FasmLink.S4.ports = ports := rfl

def outSrc (N : PNet) (p : String) : Src :=
  match N.outs.find? (·.1 == p) with
  | some (_, s) => s
  | none => .const false

def stSrc (rho : List (List Src)) (k j : Nat) : Src := (rho.getD k []).getD j (.const false)

/-- One routed seed: the physical net from the bits and C's state renaming. -/
structure Seed where
  net : PNet
  rho : List (List Src)

/-- Physical source of each logical node. -/
def Seed.m (S : Seed) : Node → Src
  | .a0 => .port 0 | .ackOut => .port 1 | .d0 => .port 2 | .d1 => .port 3 | .d2 => .port 4
  | .r1 => .port 5 | .r2 => .port 6 | .reqIn => .port 7 | .rst => .port 8
  | .c => stSrc S.rho 0 0
  | .q0 => stSrc S.rho 1 0 | .q1 => stSrc S.rho 1 1 | .q2 => stSrc S.rho 1 2
  | .a1 => stSrc S.rho 2 0 | .a2 => stSrc S.rho 2 1 | .q => stSrc S.rho 2 2
  | .g1 => outSrc S.net "g1" | .g2 => outSrc S.net "g2" | .r0 => outSrc S.net "R0"

def seed1 : Seed := ⟨Formal.Net.FasmLink.S1.net, Formal.Net.FasmLink.S1.rho⟩
def seed2 : Seed := ⟨Formal.Net.FasmLink.S2.net, Formal.Net.FasmLink.S2.rho⟩
def seed3 : Seed := ⟨Formal.Net.FasmLink.S3.net, Formal.Net.FasmLink.S3.rho⟩
def seed4 : Seed := ⟨Formal.Net.FasmLink.S4.net, Formal.Net.FasmLink.S4.rho⟩

/-- The map agrees with the output ports the bits drive (A1, A2, ack_in,
req_out, data_out[*]), so the internal names are pinned to visible ports. -/
def Seed.consistent (S : Seed) : Bool :=
  outSrc S.net "A1" == S.m .a1 && outSrc S.net "A2" == S.m .a2 &&
  outSrc S.net "ack_in" == S.m .c && outSrc S.net "req_out" == S.m .c &&
  outSrc S.net "data_out[0]" == S.m .q0 && outSrc S.net "data_out[1]" == S.m .q1 &&
  outSrc S.net "data_out[2]" == S.m .q2 &&
  -- injective on the 19 nodes
  (allNodes.map S.m).Nodup

theorem map_consistent_s1 : seed1.consistent = true := by decide
theorem map_consistent_s2 : seed2.consistent = true := by decide
theorem map_consistent_s3 : seed3.consistent = true := by decide
theorem map_consistent_s4 : seed4.consistent = true := by decide

/-! ## Kleene physical semantics -/

/-- H_KLEENE_LUT on the physical INIT and the physical pin vector A1..A6. -/
def fnK (L : PLut) : LOut → List K3 → K3
  | .o6, v => o6K L.init v
  | .o5, v => o5K L.init v

def srcK (pv : Nat → K3) (w : Nat → LOut → K3) : Src → K3
  | .const b => K3.ofBool b
  | .port i => pv i
  | .lut i o => w i o

/-- Excitation of every physical LUT output (zero-delay next value). -/
def excK (N : PNet) (pv : Nat → K3) (w : Nat → LOut → K3) : Nat → LOut → K3 := fun i o =>
  match N.luts[i]? with
  | some L => fnK L o (L.pins.map (srcK pv w))
  | none => .f

def Seed.val (S : Seed) (pv : Nat → K3) (w : Nat → LOut → K3) (n : Node) : K3 :=
  srcK pv w (S.m n)

/-- Next value of node `n`: the physical LUT at `m n` on its routed pins. -/
def Seed.next (S : Seed) (pv : Nat → K3) (w : Nat → LOut → K3) (n : Node) : K3 :=
  S.val pv (excK S.net pv w) n

/-! ## The finite check -/

inductive Pin
  | const (b : Bool)
  | node (n : Node)
  deriving DecidableEq, Repr

def Pin.eval (e : Node → K3) : Pin → K3
  | .const b => K3.ofBool b
  | .node n => e n

def Pin.nodes : Pin → List Node
  | .const _ => []
  | .node n => [n]

/-- Logical reading of a physical source: a tie, or the node it is the source of. -/
def Seed.resolve (S : Seed) : Src → Option Pin
  | .const b => some (.const b)
  | s => (allNodes.find? (fun n => decide (S.m n = s))).map Pin.node

def Seed.resolveAll (S : Seed) : List Src → Option (List Pin)
  | [] => some []
  | s :: ss =>
    match S.resolve s, S.resolveAll ss with
    | some p, some ps => some (p :: ps)
    | _, _ => none

def dedupN : List Node → List Node
  | [] => []
  | a :: l => if a ∈ dedupN l then dedupN l else a :: dedupN l

theorem mem_dedupN : ∀ (l : List Node) x, x ∈ l → x ∈ dedupN l := by
  intro l
  induction l with
  | nil => intro x h; cases h
  | cons a l ih =>
    intro x h
    simp only [dedupN]
    rcases List.mem_cons.1 h with rfl | h
    · split
      · assumption
      · simp
    · split
      · exact ih x h
      · exact List.mem_cons_of_mem _ (ih x h)

def forallK3 : Nat → (List K3 → Bool) → Bool
  | 0, f => f []
  | n + 1, f => forallK3 n (fun l => f (.f :: l)) && forallK3 n (fun l => f (.t :: l)) &&
      forallK3 n (fun l => f (.x :: l))

theorem forallK3_sound : ∀ n f, forallK3 n f = true → ∀ l : List K3, l.length = n → f l = true := by
  intro n
  induction n with
  | zero => intro f h l hl; cases l with
    | nil => exact h
    | cons _ _ => simp at hl
  | succ n ih =>
    intro f h l hl
    cases l with
    | nil => simp at hl
    | cons b l =>
      simp only [forallK3, Bool.and_eq_true] at h
      simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
      cases b
      · exact ih _ h.1.1 l hl
      · exact ih _ h.1.2 l hl
      · exact ih _ h.2 l hl

def assocK : List Node → List K3 → Node → K3
  | a :: as, b :: bs, x => if x = a then b else assocK as bs x
  | _, _, _ => .x

theorem assocK_map (v : Node → K3) : ∀ (V : List Node) x, x ∈ V → assocK V (V.map v) x = v x := by
  intro V
  induction V with
  | nil => intro x h; cases h
  | cons a V ih =>
    intro x h
    simp only [List.map_cons, assocK]
    by_cases hx : x = a
    · subst hx; simp
    · simp only [hx, ite_false]
      exact ih x (by simpa [hx] using h)

/-- The claim "the physical LUT at `m n` computes `F` of the nodes `args`",
decided over every K3 value of the nodes either side can read. -/
def Seed.check (S : Seed) (n : Node) (args : List Node) (F : List K3 → K3) : Bool :=
  match S.m n with
  | .lut i o =>
    match S.net.luts[i]? with
    | some L =>
      match S.resolveAll L.pins with
      | some pl =>
        forallK3 (dedupN (pl.flatMap Pin.nodes ++ args)).length (fun l =>
          decide (fnK L o (pl.map (Pin.eval (assocK (dedupN (pl.flatMap Pin.nodes ++ args)) l))) =
            F (args.map (assocK (dedupN (pl.flatMap Pin.nodes ++ args)) l))))
      | none => false
    | none => false
  | _ => false

theorem Seed.resolve_spec (S : Seed) (pv w) : ∀ (s : Src) (p : Pin), S.resolve s = some p →
    p.eval (S.val pv w) = srcK pv w s := by
  intro s p h
  cases s with
  | const b => simp only [resolve, Option.some.injEq] at h; subst h; rfl
  | port i =>
    simp only [resolve, Option.map_eq_some_iff] at h
    obtain ⟨n, hn, rfl⟩ := h
    have := List.find?_some hn
    simp only [decide_eq_true_eq] at this
    simp only [Pin.eval, Seed.val, this]
  | lut i o =>
    simp only [resolve, Option.map_eq_some_iff] at h
    obtain ⟨n, hn, rfl⟩ := h
    have := List.find?_some hn
    simp only [decide_eq_true_eq] at this
    simp only [Pin.eval, Seed.val, this]

theorem Seed.resolveAll_spec (S : Seed) (pv w) : ∀ (ss : List Src) (pl : List Pin),
    S.resolveAll ss = some pl → pl.map (Pin.eval (S.val pv w)) = ss.map (srcK pv w) := by
  intro ss
  induction ss with
  | nil => intro pl h; simp only [resolveAll, Option.some.injEq] at h; subst h; rfl
  | cons s ss ih =>
    intro pl h
    simp only [resolveAll] at h
    cases hs : S.resolve s with
    | none => simp [hs] at h
    | some p =>
      cases hr : S.resolveAll ss with
      | none => simp [hs, hr] at h
      | some ps =>
        simp only [hs, hr, Option.some.injEq] at h
        subst h
        simp only [List.map_cons, S.resolve_spec pv w s p hs, ih ps hr]

theorem Pin.eval_congr (e e' : Node → K3) (p : Pin) (h : ∀ x ∈ p.nodes, e x = e' x) :
    p.eval e = p.eval e' := by
  cases p with
  | const b => rfl
  | node n => exact h n (by simp [Pin.nodes])

/-- **Soundness of the check**: for every port valuation and every value of
every physical LUT output, the physical next value of node `n` is `F` of the
physical values of the nodes `args`. -/
theorem Seed.check_sound (S : Seed) (n : Node) (args : List Node) (F : List K3 → K3)
    (h : S.check n args F = true) (pv : Nat → K3) (w : Nat → LOut → K3) :
    S.next pv w n = F (args.map (S.val pv w)) := by
  unfold Seed.check at h
  split at h
  next i o hm =>
    split at h
    next L hL =>
      split at h
      next pl hpl =>
        have h1 := forallK3_sound _ _ h ((dedupN (pl.flatMap Pin.nodes ++ args)).map (S.val pv w))
          (by simp)
        have h2 := of_decide_eq_true h1
        have hV := assocK_map (S.val pv w) (dedupN (pl.flatMap Pin.nodes ++ args))
        have hpins : pl.map (Pin.eval (assocK (dedupN (pl.flatMap Pin.nodes ++ args))
            ((dedupN (pl.flatMap Pin.nodes ++ args)).map (S.val pv w)))) =
            pl.map (Pin.eval (S.val pv w)) := by
          apply List.map_congr_left
          intro p hp
          apply Pin.eval_congr
          intro x hx
          apply hV
          apply mem_dedupN
          exact List.mem_append_left _ (List.mem_flatMap.2 ⟨p, hp, hx⟩)
        have hargs : args.map (assocK (dedupN (pl.flatMap Pin.nodes ++ args))
            ((dedupN (pl.flatMap Pin.nodes ++ args)).map (S.val pv w))) = args.map (S.val pv w) := by
          apply List.map_congr_left
          intro x hx
          exact hV x (mem_dedupN _ x (List.mem_append_right _ hx))
        rw [hpins, hargs, S.resolveAll_spec pv w L.pins pl hpl] at h2
        simp only [Seed.next, Seed.val, hm, srcK, excK, hL]
        exact h2
      next => cases h
    next => cases h
  next => cases h

theorem Seed.check_lut (S : Seed) (n : Node) (args : List Node) (F : List K3 → K3)
    (h : S.check n args F = true) : ∃ i o, S.m n = .lut i o := by
  unfold Seed.check at h
  split at h
  next i o hm => exact ⟨i, o, hm⟩
  next => cases h

/-! ## The claims: shard B's functions, with B's INIT on B's pin order -/

def get (l : List K3) (i : Nat) : K3 := l.getD i .x

/-- `bd_link`'s controller C-element `bd_c2n` (a = req_in, b = ack_out). -/
def Fc : List K3 → K3 := fun l => CElemFn.c2nK (get l 0) (get l 1) (get l 2) (get l 3)
def Ac : List Node := [.reqIn, .ackOut, .c, .rst]
/-- `bd_latch` pair, O5 (bit 0) and O6 (bit 1); `en` = the node c. -/
def Fq0 : List K3 → K3 := fun l =>
  o5K Latch.PAIR [get l 0, get l 1, get l 2, get l 3, get l 4, .t]
def Fq1 : List K3 → K3 := fun l =>
  o6K Latch.PAIR [get l 0, get l 1, get l 2, get l 3, get l 4, .t]
def Aq01 : List Node := [.d0, .c, .q0, .d1, .q1]
/-- `bd_latch` odd bit (bit 2). -/
def Fq2 : List K3 → K3 := fun l => lutK Latch.ODD [get l 0, get l 1, get l 2, .f, .f, .f]
def Aq2 : List Node := [.d2, .c, .q2]
/-- `bd_arbiter.ustate` O6 (q) and O5 (R0). -/
def Fq : List K3 → K3 := fun l => ArbKleene.qArbK (get l 0) (get l 1) (get l 2) (get l 3) (get l 4)
def Fr0 : List K3 → K3 := fun l => ArbKleene.r0K (get l 0) (get l 1) (get l 2) (get l 3) (get l 4)
def Ast : List Node := [.r1, .r2, .q, .rst, .a0]
/-- `bd_arbiter.ugrant` O5 (g1) and O6 (g2). -/
def Fg1 : List K3 → K3 := fun l => ArbKleene.g1K (get l 0) (get l 1) (get l 2)
def Fg2 : List K3 → K3 := fun l => ArbKleene.g2K (get l 0) (get l 1) (get l 2)
def Agr : List Node := [.r1, .r2, .q]
/-- `bd_arbiter.ua1`, `ua2` (`bd_c2`, a = g1/g2, b = A0). -/
def Fa : List K3 → K3 := fun l => ArbKleene.cK (get l 0) (get l 1) (get l 2) (get l 3)
def Aa1 : List Node := [.g1, .a0, .a1, .rst]
def Aa2 : List Node := [.g2, .a0, .a2, .rst]

/-- All ten LUT-output claims of `link_arb`. -/
def Seed.checkAll (S : Seed) : Bool :=
  S.check .c Ac Fc && S.check .q0 Aq01 Fq0 && S.check .q1 Aq01 Fq1 && S.check .q2 Aq2 Fq2 &&
  S.check .q Ast Fq && S.check .r0 Ast Fr0 && S.check .g1 Agr Fg1 && S.check .g2 Agr Fg2 &&
  S.check .a1 Aa1 Fa && S.check .a2 Aa2 Fa

/-- **The bitstreams' LUTs compute shard B's cell functions** (all ten LUT
outputs of `link_arb`, every seed, Kleene, hence also binary). -/
theorem checkAll_s1 : seed1.checkAll = true := by decide
theorem checkAll_s2 : seed2.checkAll = true := by decide
theorem checkAll_s3 : seed3.checkAll = true := by decide
theorem checkAll_s4 : seed4.checkAll = true := by decide

/-! ## The claims in readable form (any seed passing `checkAll`) -/

section Claims
variable (S : Seed) (h : S.checkAll = true) (pv : Nat → K3) (w : Nat → LOut → K3)
include h

private theorem parts : S.check .c Ac Fc = true ∧ S.check .q0 Aq01 Fq0 = true ∧
    S.check .q1 Aq01 Fq1 = true ∧ S.check .q2 Aq2 Fq2 = true ∧ S.check .q Ast Fq = true ∧
    S.check .r0 Ast Fr0 = true ∧ S.check .g1 Agr Fg1 = true ∧ S.check .g2 Agr Fg2 = true ∧
    S.check .a1 Aa1 Fa = true ∧ S.check .a2 Aa2 Fa = true := by
  simp only [Seed.checkAll, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem next_c : S.next pv w .c =
    CElemFn.c2nK (S.val pv w .reqIn) (S.val pv w .ackOut) (S.val pv w .c) (S.val pv w .rst) :=
  S.check_sound _ _ _ (parts S h).1 pv w
theorem next_q0 : S.next pv w .q0 =
    o5K Latch.PAIR [S.val pv w .d0, S.val pv w .c, S.val pv w .q0, S.val pv w .d1, S.val pv w .q1, .t] :=
  S.check_sound _ _ _ (parts S h).2.1 pv w
theorem next_q1 : S.next pv w .q1 =
    o6K Latch.PAIR [S.val pv w .d0, S.val pv w .c, S.val pv w .q0, S.val pv w .d1, S.val pv w .q1, .t] :=
  S.check_sound _ _ _ (parts S h).2.2.1 pv w
theorem next_q2 : S.next pv w .q2 =
    lutK Latch.ODD [S.val pv w .d2, S.val pv w .c, S.val pv w .q2, .f, .f, .f] :=
  S.check_sound _ _ _ (parts S h).2.2.2.1 pv w
theorem next_q : S.next pv w .q =
    ArbKleene.qArbK (S.val pv w .r1) (S.val pv w .r2) (S.val pv w .q) (S.val pv w .rst) (S.val pv w .a0) :=
  S.check_sound _ _ _ (parts S h).2.2.2.2.1 pv w
theorem next_r0 : S.next pv w .r0 =
    ArbKleene.r0K (S.val pv w .r1) (S.val pv w .r2) (S.val pv w .q) (S.val pv w .rst) (S.val pv w .a0) :=
  S.check_sound _ _ _ (parts S h).2.2.2.2.2.1 pv w
theorem next_g1 : S.next pv w .g1 = ArbKleene.g1K (S.val pv w .r1) (S.val pv w .r2) (S.val pv w .q) :=
  S.check_sound _ _ _ (parts S h).2.2.2.2.2.2.1 pv w
theorem next_g2 : S.next pv w .g2 = ArbKleene.g2K (S.val pv w .r1) (S.val pv w .r2) (S.val pv w .q) :=
  S.check_sound _ _ _ (parts S h).2.2.2.2.2.2.2.1 pv w
theorem next_a1 : S.next pv w .a1 =
    ArbKleene.cK (S.val pv w .g1) (S.val pv w .a0) (S.val pv w .a1) (S.val pv w .rst) :=
  S.check_sound _ _ _ (parts S h).2.2.2.2.2.2.2.2.1 pv w
theorem next_a2 : S.next pv w .a2 =
    ArbKleene.cK (S.val pv w .g2) (S.val pv w .a0) (S.val pv w .a2) (S.val pv w .rst) :=
  S.check_sound _ _ _ (parts S h).2.2.2.2.2.2.2.2.2 pv w

/-! ### Headline Kleene results, restated on the bits -/

/-- `ArbKleene.kleene_exclusion` on the bitstream: whatever K3 values the
physical nets carry, the physical ugrant LUT never drives both grants to a
definite 1. -/
theorem kleene_exclusion_bits : ¬ (S.next pv w .g1 = .t ∧ S.next pv w .g2 = .t) := by
  rw [next_g1 S h, next_g2 S h]
  exact ArbKleene.kleene_exclusion _ _ _

/-- `Latch.pair_o5_kleene` / `pair_o6_kleene` / `odd_kleene` on the bits:
each physical latch LUT is the Kleene mux `en ? d : q` of its own bit, with
`en` the physical C node; X on the other bit of a pair never reaches it. -/
theorem latch_bits :
    S.next pv w .q0 = K3.mux (S.val pv w .c) (S.val pv w .q0) (S.val pv w .d0) ∧
    S.next pv w .q1 = K3.mux (S.val pv w .c) (S.val pv w .q1) (S.val pv w .d1) ∧
    S.next pv w .q2 = K3.mux (S.val pv w .c) (S.val pv w .q2) (S.val pv w .d2) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [next_q0 S h]; exact Latch.pair_o5_kleene _ _ _ _ _
  · rw [next_q1 S h]; exact Latch.pair_o6_kleene _ _ _ _ _
  · rw [next_q2 S h]; exact Latch.odd_kleene _ _ _

end Claims

/-! ## `ArbKleene`'s six-node step is simulated by the physical step -/

/-- The six arbiter nodes of a physical state (ports are irrelevant to them:
they are LUT outputs, `val_lut`). -/
def Seed.arb (S : Seed) (w : Nat → LOut → K3) : ArbKleene.Net :=
  ⟨S.val (fun _ => .x) w .q, S.val (fun _ => .x) w .g1, S.val (fun _ => .x) w .g2,
   S.val (fun _ => .x) w .r0, S.val (fun _ => .x) w .a1, S.val (fun _ => .x) w .a2⟩

/-- Arbiter inputs from the port values (A0 is one port: both fork branches
read the same value, see the notes). -/
def arbIn (pv : Nat → K3) : ArbKleene.Inp := ArbKleene.I (pv 5) (pv 6) (pv 0) (pv 8)

theorem Seed.val_lut (S : Seed) (n : Node) (i : Nat) (o : LOut) (hm : S.m n = .lut i o)
    (pv pv' : Nat → K3) (w : Nat → LOut → K3) : S.val pv w n = S.val pv' w n := by
  simp only [Seed.val, hm, srcK]

/-- **Commuting square**: one physical Kleene step of the routed bits, read
on the six arbiter nodes, is exactly one `ArbKleene.step`. -/
theorem arb_step (S : Seed) (h : S.checkAll = true) (pv : Nat → K3) (w : Nat → LOut → K3) :
    S.arb (excK S.net pv w) = ArbKleene.step (arbIn pv) (S.arb w) := by
  have P := parts S h
  have e : ∀ (n : Node) args F, S.check n args F = true →
      S.val (fun _ => .x) (excK S.net pv w) n = S.next pv w n := fun n args F hc => by
    obtain ⟨i, o, hm⟩ := S.check_lut n args F hc
    exact S.val_lut n i o hm _ _ _
  have e' : ∀ (n : Node) args F, S.check n args F = true →
      S.val pv w n = S.val (fun _ => .x) w n := fun n args F hc => by
    obtain ⟨i, o, hm⟩ := S.check_lut n args F hc
    exact S.val_lut n i o hm _ _ _
  simp only [Seed.arb, ArbKleene.step, arbIn, ArbKleene.I]
  rw [e _ _ _ P.2.2.2.2.1, e _ _ _ P.2.2.2.2.2.1, e _ _ _ P.2.2.2.2.2.2.1,
    e _ _ _ P.2.2.2.2.2.2.2.1, e _ _ _ P.2.2.2.2.2.2.2.2.1, e _ _ _ P.2.2.2.2.2.2.2.2.2,
    next_q S h, next_r0 S h, next_g1 S h, next_g2 S h, next_a1 S h, next_a2 S h,
    e' _ _ _ P.2.2.2.2.1, e' _ _ _ P.2.2.2.2.2.2.1, e' _ _ _ P.2.2.2.2.2.2.2.1,
    e' _ _ _ P.2.2.2.2.2.2.2.2.1, e' _ _ _ P.2.2.2.2.2.2.2.2.2]
  rfl

/-- Physical settle / run (every LUT output updated per step, as in B). -/
def Seed.settle (S : Seed) : Nat → (Nat → K3) → (Nat → LOut → K3) → (Nat → LOut → K3)
  | 0, _, w => w
  | k + 1, pv, w => S.settle k pv (excK S.net pv w)

def Seed.run (S : Seed) (k : Nat) : List (Nat → K3) → (Nat → LOut → K3) → (Nat → LOut → K3)
  | [], w => w
  | pv :: pvs, w => S.run k pvs (S.settle k pv w)

theorem arb_settle (S : Seed) (h : S.checkAll = true) :
    ∀ k pv w, S.arb (S.settle k pv w) = ArbKleene.settle k (arbIn pv) (S.arb w) := by
  intro k
  induction k with
  | zero => intro pv w; rfl
  | succ k ih =>
    intro pv w
    simp only [Seed.settle, ArbKleene.settle]
    rw [ih, arb_step S h]

theorem arb_run (S : Seed) (h : S.checkAll = true) (k : Nat) :
    ∀ pvs w, S.arb (S.run k pvs w) = ArbKleene.run k (pvs.map arbIn) (S.arb w) := by
  intro pvs
  induction pvs with
  | nil => intro w; rfl
  | cons pv pvs ih =>
    intro w
    simp only [Seed.run, List.map_cons, ArbKleene.run]
    rw [ih, arb_settle S h]

/-- `ArbKleene.sc_reset` on the bits: from ANY physical state whose arbiter
nodes are all `x`, holding rst = 1 with r1 = r2 = A0 = 0 for 4 steps gives
the definite idle state (q = 1, all else 0), a fixed point. -/
theorem sc_reset_bits (S : Seed) (h : S.checkAll = true) (pv : Nat → K3) (w : Nat → LOut → K3)
    (hin : arbIn pv = ArbKleene.I .f .f .f .t) (hx : S.arb w = ⟨.x, .x, .x, .x, .x, .x⟩) :
    S.arb (S.settle 4 pv w) = ArbKleene.idle1 ∧
    S.arb (excK S.net pv (S.settle 4 pv w)) = ArbKleene.idle1 := by
  have h1 : S.arb (S.settle 4 pv w) = ArbKleene.idle1 := by
    rw [arb_settle S h, hin, hx]; exact ArbKleene.sc_reset.1
  refine ⟨h1, ?_⟩
  rw [arb_step S h, hin, h1]; exact ArbKleene.sc_reset.2

/-- `ArbKleene.sc_tie_acked` on the bits: the near-tie from idle that the
server acks ends with BOTH physical ack LUTs (A1, A2) at `x`, a fixed point. -/
theorem sc_tie_acked_bits (S : Seed) (h : S.checkAll = true) (pvs : List (Nat → K3))
    (w : Nat → LOut → K3) (pvL : Nat → K3)
    (hin : pvs.map arbIn = [ArbKleene.I .x .x .f .f, ArbKleene.I .t .t .f .f,
      ArbKleene.I .t .t .x .f, ArbKleene.I .t .t .t .f])
    (hL : arbIn pvL = ArbKleene.I .t .t .t .f)
    (h0 : S.arb w = ArbKleene.idle1) :
    S.arb (S.run 3 pvs w) = ⟨.x, .x, .x, .t, .x, .x⟩ ∧
    S.arb (excK S.net pvL (S.run 3 pvs w)) = ⟨.x, .x, .x, .t, .x, .x⟩ := by
  have h1 : S.arb (S.run 3 pvs w) = ⟨.x, .x, .x, .t, .x, .x⟩ := by
    rw [arb_run S h, hin, h0]; exact ArbKleene.sc_tie_acked.1
  refine ⟨h1, ?_⟩
  rw [arb_step S h, hL, h1]; exact ArbKleene.sc_tie_acked.2

/-! ## Binary: 11b's own `PNet.exc`, unchanged -/

theorem completions_ofBool : ∀ v : List Bool, completions (v.map K3.ofBool) = [v] := by
  intro v
  induction v with
  | nil => rfl
  | cons b v ih =>
    cases b <;> simp [completions, K3.ofBool, K3.admits, ih]

theorem lutK_ofBool (init : Nat) (v : List Bool) :
    lutK init (v.map K3.ofBool) = K3.ofBool (lutB init v) := by
  simp only [MuxTree.lutK_eq_closure, completions_ofBool]
  cases hb : lutB init v <;> simp [hb, K3.ofBool]

theorem fnK_ofBool (L : PLut) (o : LOut) (v : List Bool) :
    fnK L o (v.map K3.ofBool) = K3.ofBool (L.fn o v) := by
  cases o
  · exact lutK_ofBool _ _
  · simp only [fnK, o5K, PLut.fn, o5B, ← List.map_take]
    exact lutK_ofBool _ _

/-- Binary next value of node `n` under 11b's `PNet.exc`. -/
def Seed.valB (S : Seed) (ins : List Bool) (st : Nat → LOut → Bool) (n : Node) : Bool :=
  (S.m n).val ins st
def Seed.nextB (S : Seed) (ins : List Bool) (st : Nat → LOut → Bool) (n : Node) : Bool :=
  S.valB ins (fun i o => S.net.exc i o ins st) n

def kpv (ins : List Bool) : Nat → K3 := fun i => K3.ofBool (ins.getD i false)
def kw (st : Nat → LOut → Bool) : Nat → LOut → K3 := fun i o => K3.ofBool (st i o)

theorem srcK_ofBool (ins : List Bool) (st : Nat → LOut → Bool) (s : Src) :
    srcK (kpv ins) (kw st) s = K3.ofBool (s.val ins st) := by
  cases s <;> rfl

theorem Seed.val_ofBool (S : Seed) (ins st n) : S.val (kpv ins) (kw st) n = K3.ofBool (S.valB ins st n) :=
  srcK_ofBool ins st (S.m n)

theorem Seed.next_ofBool (S : Seed) (ins st n) :
    S.next (kpv ins) (kw st) n = K3.ofBool (S.nextB ins st n) := by
  have hw : excK S.net (kpv ins) (kw st) = kw (fun i o => S.net.exc i o ins st) := by
    funext i o
    simp only [excK, kw, PNet.exc]
    cases S.net.luts[i]? with
    | none => rfl
    | some L =>
      simp only
      rw [show L.pins.map (srcK (kpv ins) (kw st)) = (L.pins.map (Src.val ins st)).map K3.ofBool by
        rw [List.map_map]; exact List.map_congr_left (fun s _ => srcK_ofBool ins st s)]
      exact fnK_ofBool L o _
  simp only [Seed.next, hw]
  exact S.val_ofBool ins _ n

theorem ofBool_inj {a b : Bool} (h : K3.ofBool a = K3.ofBool b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

theorem g1K_ofBool (a b c : Bool) :
    ArbKleene.g1K (K3.ofBool a) (K3.ofBool b) (K3.ofBool c) = K3.ofBool (ArbBinary.gr1 a b c) := by
  cases a <;> cases b <;> cases c <;> decide
theorem g2K_ofBool (a b c : Bool) :
    ArbKleene.g2K (K3.ofBool a) (K3.ofBool b) (K3.ofBool c) = K3.ofBool (ArbBinary.gr2 a b c) := by
  cases a <;> cases b <;> cases c <;> decide
theorem cK_ofBool (a b c d : Bool) :
    ArbKleene.cK (K3.ofBool a) (K3.ofBool b) (K3.ofBool c) (K3.ofBool d) =
      K3.ofBool (CElemFn.c2B a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem c2nK_ofBool (a b c d : Bool) :
    CElemFn.c2nK (K3.ofBool a) (K3.ofBool b) (K3.ofBool c) (K3.ofBool d) =
      K3.ofBool (CElemFn.c2nB a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide
theorem qArbK_ofBool (a b c d e : Bool) :
    ArbKleene.qArbK (K3.ofBool a) (K3.ofBool b) (K3.ofBool c) (K3.ofBool d) (K3.ofBool e) =
      K3.ofBool (o6B ArbBinary.ARB_ST [a, b, c, d, e, true]) := by
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

section Binary
variable (S : Seed) (h : S.checkAll = true) (ins : List Bool) (st : Nat → LOut → Bool)
include h

theorem nextB_g1 : S.nextB ins st .g1 =
    ArbBinary.gr1 (S.valB ins st .r1) (S.valB ins st .r2) (S.valB ins st .q) := by
  apply ofBool_inj
  rw [← S.next_ofBool, next_g1 S h, S.val_ofBool, S.val_ofBool, S.val_ofBool, g1K_ofBool]
theorem nextB_g2 : S.nextB ins st .g2 =
    ArbBinary.gr2 (S.valB ins st .r1) (S.valB ins st .r2) (S.valB ins st .q) := by
  apply ofBool_inj
  rw [← S.next_ofBool, next_g2 S h, S.val_ofBool, S.val_ofBool, S.val_ofBool, g2K_ofBool]
theorem nextB_a1 : S.nextB ins st .a1 =
    CElemFn.c2B (S.valB ins st .g1) (S.valB ins st .a0) (S.valB ins st .a1) (S.valB ins st .rst) := by
  apply ofBool_inj
  rw [← S.next_ofBool, next_a1 S h, S.val_ofBool, S.val_ofBool, S.val_ofBool, S.val_ofBool, cK_ofBool]
theorem nextB_a2 : S.nextB ins st .a2 =
    CElemFn.c2B (S.valB ins st .g2) (S.valB ins st .a0) (S.valB ins st .a2) (S.valB ins st .rst) := by
  apply ofBool_inj
  rw [← S.next_ofBool, next_a2 S h, S.val_ofBool, S.val_ofBool, S.val_ofBool, S.val_ofBool, cK_ofBool]
theorem nextB_c : S.nextB ins st .c =
    CElemFn.c2nB (S.valB ins st .reqIn) (S.valB ins st .ackOut) (S.valB ins st .c) (S.valB ins st .rst) := by
  apply ofBool_inj
  rw [← S.next_ofBool, next_c S h, S.val_ofBool, S.val_ofBool, S.val_ofBool, S.val_ofBool, c2nK_ofBool]
theorem nextB_q : S.nextB ins st .q =
    o6B ArbBinary.ARB_ST [S.valB ins st .r1, S.valB ins st .r2, S.valB ins st .q,
      S.valB ins st .rst, S.valB ins st .a0, true] := by
  apply ofBool_inj
  rw [← S.next_ofBool, next_q S h, S.val_ofBool, S.val_ofBool, S.val_ofBool, S.val_ofBool,
    S.val_ofBool, qArbK_ofBool]

/-- `ArbBinary.settled_exclusion` on the bitstream (11b's binary semantics):
the physical g1 and g2 never are both 1, for every port vector and every
value of every physical LUT output. -/
theorem settled_exclusion_bits : (S.nextB ins st .g1 && S.nextB ins st .g2) = false := by
  rw [nextB_g1 S h, nextB_g2 S h]
  exact ArbBinary.settled_exclusion _ _ _

/-- `CElemFn.c2_spec` on the bits: each physical ack LUT is `~rst . C(g, A0)`
of the PHYSICAL grant output it is routed from. -/
theorem c2_spec_bits :
    S.nextB ins st .a1 = CElemFn.clr (S.valB ins st .rst)
      (CElemFn.cSpec [S.valB ins st .g1, S.valB ins st .a0] (S.valB ins st .a1)) ∧
    S.nextB ins st .a2 = CElemFn.clr (S.valB ins st .rst)
      (CElemFn.cSpec [S.valB ins st .g2, S.valB ins st .a0] (S.valB ins st .a2)) := by
  rw [nextB_a1 S h, nextB_a2 S h]
  exact ⟨CElemFn.c2_spec _ _ _ _, CElemFn.c2_spec _ _ _ _⟩

/-- `CElemFn.c2n_spec` on the bits: the link's C node is `~rst . C(req_in, ~ack_out)`. -/
theorem c2n_spec_bits :
    S.nextB ins st .c = CElemFn.clr (S.valB ins st .rst)
      (CElemFn.cSpec [S.valB ins st .reqIn, !S.valB ins st .ackOut] (S.valB ins st .c)) := by
  rw [nextB_c S h]; exact CElemFn.c2n_spec _ _ _ _

/-- `ArbBinary.stA_moves_only_if_alone` on the bits (rst = 0): the physical
state LUT changes q only when exactly one request is up. -/
theorem q_moves_only_if_alone_bits (hr : S.valB ins st .rst = false)
    (hmv : S.nextB ins st .q ≠ S.valB ins st .q) : S.valB ins st .r1 ≠ S.valB ins st .r2 := by
  rw [nextB_q S h, hr] at hmv
  exact (ArbBinary.stA_moves_only_if_alone _ _ _ _ hmv).1

end Binary

/-! ## Per-seed instances -/

theorem settled_exclusion_s1 (ins st) : (seed1.nextB ins st .g1 && seed1.nextB ins st .g2) = false :=
  settled_exclusion_bits seed1 checkAll_s1 ins st
theorem settled_exclusion_s2 (ins st) : (seed2.nextB ins st .g1 && seed2.nextB ins st .g2) = false :=
  settled_exclusion_bits seed2 checkAll_s2 ins st
theorem settled_exclusion_s3 (ins st) : (seed3.nextB ins st .g1 && seed3.nextB ins st .g2) = false :=
  settled_exclusion_bits seed3 checkAll_s3 ins st
theorem settled_exclusion_s4 (ins st) : (seed4.nextB ins st .g1 && seed4.nextB ins st .g2) = false :=
  settled_exclusion_bits seed4 checkAll_s4 ins st

theorem kleene_exclusion_s1 (pv w) : ¬ (seed1.next pv w .g1 = .t ∧ seed1.next pv w .g2 = .t) :=
  kleene_exclusion_bits seed1 checkAll_s1 pv w
theorem kleene_exclusion_s2 (pv w) : ¬ (seed2.next pv w .g1 = .t ∧ seed2.next pv w .g2 = .t) :=
  kleene_exclusion_bits seed2 checkAll_s2 pv w
theorem kleene_exclusion_s3 (pv w) : ¬ (seed3.next pv w .g1 = .t ∧ seed3.next pv w .g2 = .t) :=
  kleene_exclusion_bits seed3 checkAll_s3 pv w
theorem kleene_exclusion_s4 (pv w) : ¬ (seed4.next pv w .g1 = .t ∧ seed4.next pv w .g2 = .t) :=
  kleene_exclusion_bits seed4 checkAll_s4 pv w

theorem arb_step_s1 (pv w) : seed1.arb (excK seed1.net pv w) = ArbKleene.step (arbIn pv) (seed1.arb w) :=
  arb_step seed1 checkAll_s1 pv w
theorem arb_step_s2 (pv w) : seed2.arb (excK seed2.net pv w) = ArbKleene.step (arbIn pv) (seed2.arb w) :=
  arb_step seed2 checkAll_s2 pv w
theorem arb_step_s3 (pv w) : seed3.arb (excK seed3.net pv w) = ArbKleene.step (arbIn pv) (seed3.arb w) :=
  arb_step seed3 checkAll_s3 pv w
theorem arb_step_s4 (pv w) : seed4.arb (excK seed4.net pv w) = ArbKleene.step (arbIn pv) (seed4.arb w) :=
  arb_step seed4 checkAll_s4 pv w

/-! ## Structural facts the B statements silently rely on, checked on the bits -/

/-- g1 and g2 are O5 and O6 of ONE physical LUT6_2 site, so in any per-pin
trace model both read the SAME routed q pin (the premise of
`ArbBinary.settled_exclusion`: "both grant outputs reading the same value of
q"); likewise the latch pair's O5/O6 share one en pin, and R0/q share ustate. -/
def Seed.sameSite (S : Seed) (a b : Node) : Bool :=
  match S.m a, S.m b with
  | .lut i .o5, .lut j .o6 => i == j
  | _, _ => false

theorem shared_sites_s1 : seed1.sameSite .g1 .g2 ∧ seed1.sameSite .q0 .q1 ∧ seed1.sameSite .r0 .q := by decide
theorem shared_sites_s2 : seed2.sameSite .g1 .g2 ∧ seed2.sameSite .q0 .q1 ∧ seed2.sameSite .r0 .q := by decide
theorem shared_sites_s3 : seed3.sameSite .g1 .g2 ∧ seed3.sameSite .q0 .q1 ∧ seed3.sameSite .r0 .q := by decide
theorem shared_sites_s4 : seed4.sameSite .g1 .g2 ∧ seed4.sameSite .q0 .q1 ∧ seed4.sameSite .r0 .q := by decide

/-- Read-once: on every physical LUT of every seed, no node reaches two pins
(so `MuxTree.evalK_eq_lutK` applies to the physical pin order, whatever the
silicon mux order), and every fractured LUT6_2 has A6 tied to 1. -/
def Seed.readOnce (S : Seed) : Bool :=
  S.net.luts.all fun L =>
    match S.resolveAll L.pins with
    | some pl => (pl.flatMap Pin.nodes).Nodup
    | none => false

def Seed.fracturedA6 (S : Seed) : Bool :=
  [Node.q0, Node.r0, Node.g1].all fun n =>
    match S.m n with
    | .lut i .o5 => match S.net.luts[i]? with
      | some L => L.pins.getD 5 (.const false) == .const true
      | none => false
    | _ => false

theorem read_once_s1 : seed1.readOnce ∧ seed1.fracturedA6 := by decide
theorem read_once_s2 : seed2.readOnce ∧ seed2.fracturedA6 := by decide
theorem read_once_s3 : seed3.readOnce ∧ seed3.fracturedA6 := by decide
theorem read_once_s4 : seed4.readOnce ∧ seed4.fracturedA6 := by decide

/-! ## Negative control: a check that can fail

Seed 1 with the arbiter's ugrant INIT bit 36 flipped (C's `MutInit`, the
lowest address consistent with its ties and A6 = 1, so it changes O6 = g2):
the g2 claim is refuted. And swapping the latch's q0/q1 in the renaming makes
the q0 claim fail. -/

def mutNet : PNet :=
  match Formal.Net.FasmLink.S1.net with
  | ⟨luts, outs⟩ => ⟨luts.modify 5 (fun L => ⟨L.site, L.init ^^^ (1 <<< 36), L.pins⟩), outs⟩

def mutSeed : Seed := ⟨mutNet, Formal.Net.FasmLink.S1.rho⟩

/-- The mutated bits violate the g2 claim (counterexample r1 = r2 = q = 0,
the address of the flipped bit), and the check sees it. -/
theorem mut_init_caught :
    (¬ ∀ pv w, mutSeed.next pv w .g2 =
      ArbKleene.g2K (mutSeed.val pv w .r1) (mutSeed.val pv w .r2) (mutSeed.val pv w .q)) ∧
    mutSeed.check .g2 Agr Fg2 = false :=
  ⟨fun hall => absurd (hall (fun _ => .f) (fun _ _ => .f)) (by decide), by decide⟩

def swapRho : List (List Src) :=
  match Formal.Net.FasmLink.S1.rho with
  | [a, [x, y, z], b] => [a, [y, x, z], b]
  | r => r

def swapSeed : Seed := ⟨Formal.Net.FasmLink.S1.net, swapRho⟩

/-- With q0/q1 swapped in the renaming, the "q0" LUT output follows d1, not
d0 (counterexample en = 1, d0 = 0, d1 = 1), and the check sees it. -/
theorem swap_rho_caught :
    (¬ ∀ pv w, swapSeed.next pv w .q0 =
      o5K Latch.PAIR [swapSeed.val pv w .d0, swapSeed.val pv w .c, swapSeed.val pv w .q0,
        swapSeed.val pv w .d1, swapSeed.val pv w .q1, .t]) ∧
    swapSeed.check .q0 Aq01 Fq0 = false :=
  ⟨fun hall => absurd (hall (fun i => if i = 3 then .t else .f) (fun _ _ => .t)) (by decide),
   by decide⟩

end Formal.Cells.OnNetlist
