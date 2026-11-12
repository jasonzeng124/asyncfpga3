import Formal.Cells.AssumeGuaranteeLinks

/-!
# Probe Bnet (shard B): the closed assume-guarantee circle on C's gcd_hw `CapstoneNet`

## Assumed / proved / NOT covered

**Proved (kernel `decide`, over C's `opAt`/`prodOf`/`consOf`):**
* `heads_count`, `tails_count`, `chains_cover`: the 175 links form exactly 100 maximal
  link chains (75 link-to-link channels inside them), covering all 175 links, so there is
  no all-link cycle; `chain_lengths`: 37 single links, 51 pairs, 12 triples;
* `head_classes`: the producers at the 100 chain heads are steerD 39, forkG3 15,
  forkH2 12, mux 9, forkH4 9, join2 4, steerC 4, forkG2 4, forkG4 4;
  `tail_classes`: the consumers at the 100 chain tails are mux 63, join2 17, join1 11,
  amerge 5, muxn 4.
* `physLink_of_inChain`, `gcd_hw_safe_chains`: C's `gcd_hw_circuit_safe` with `H_CELLS` of
  every link replaced by `InChain` (the link is a cell of a `Chain` of B's physical links,
  whose pins are C's channel traces). Each link's `Env1` is DERIVED (`chain_env1`), not
  assumed. Non-vacuity of `InChain`: `inChain_witness`.

**Assumed:** inside `InChain`, `Chain`'s gate/wire/time/timing fields and the chain's two
END contracts (the classes above), H_WIRE_SPREAD and the latch data fields (as Bfb2's
`PhysLink`); outside, C's `H_CELLS` for the 192 non-link operators, H_BUNDLE, H_CM_FORCED.

**NOT covered:** no END contract is proved for any gcd_hw class: steer, mux, muxn,
amerge, joins, and forks N ≥ 3 have no segment lemma; a 2-input C-element has one
(`celc_segK`), but a fork's request side is its upstream's node through a wire, so a fork
end needs its upstream's class too. `InChain` is one existential per link, not one chain
datum per chain (it is discharged by the real chain, but the theorem does not enforce
that the 175 data agree). Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeCap
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink PhysLink link_of_phys gcd_hw_safe_phys_links)
open Formal.Cells.AssumeGuaranteeLinks (ChainData Chain ChainT chain_env1)
open Formal.Cells.WinFifoCausal (Env1)

/-! ## 1. The link chains of gcd_hw (kernel-checked census) -/

def kname {n : Nat} : K n → String
  | .forkG _ os => s!"forkG{os.length}"
  | .forkH _ os _ _ _ _ => s!"forkH{os.length}"
  | .join ins _ _ _ _ => s!"join{ins.length}"
  | .bjoin ins _ _ _ => s!"bjoin{ins.length}"
  | .steerC _ _ _ => "steerC"
  | .steerD _ _ _ _ _ => "steerD"
  | .mux _ _ _ _ _ => "mux"
  | .muxn _ _ _ _ _ _ => "muxn"
  | .amerge _ _ _ _ => "amerge"
  | .link _ _ => "link"
  | .src _ _ _ => "src"
  | .sink _ => "sink"

def linkIn : K NC → Option (Fin NC)
  | .link i _ => some i
  | _ => none
def linkOut : K NC → Option (Fin NC)
  | .link _ o => some o
  | _ => none

def links : List (Fin NO) := (List.finRange NO).filter (fun o => isLink (opAt o))
def heads : List (Fin NO) := links.filter (fun o =>
  match linkIn (opAt o) with | some i => !isLink (opAt (prodOf i)) | none => false)
def tails : List (Fin NO) := links.filter (fun o =>
  match linkOut (opAt o) with | some c => !isLink (opAt (consOf c)) | none => false)

def chainFrom : Nat → Fin NO → List (Fin NO)
  | 0, _ => []
  | f + 1, o => match linkOut (opAt o) with
    | some c => if isLink (opAt (consOf c)) then o :: chainFrom f (consOf c) else [o]
    | none => [o]

def census (l : List String) : List (String × Nat) :=
  (l.eraseDups).map (fun s => (s, l.count s))


/-- **gcd_hw's 175 links form exactly 100 maximal link chains, with no all-link cycle**:
100 chain heads (links whose input comes from a non-link), 100 tails, and the chains
grown from the heads cover 175 links (a link on an all-link cycle would be missed). -/
theorem heads_count : heads.length = 100 := by decide +kernel
theorem tails_count : tails.length = 100 := by decide +kernel
theorem chains_cover : (heads.map (fun h => (chainFrom 176 h).length)).sum = 175 := by
  decide +kernel

/-- Chain lengths: 37 single links, 51 chains of 2, 12 chains of 3 (none longer). -/
theorem chain_lengths :
    census (heads.map (fun h => toString (chainFrom 176 h).length)) =
      [("1", 37), ("2", 51), ("3", 12)] := by decide +kernel

/-- **The classes at the chain heads** (the producer of a head's input channel). -/
theorem head_classes :
    census (heads.map (fun o => match linkIn (opAt o) with
      | some i => kname (opAt (prodOf i)) | none => "?")) =
      [("forkH2", 12), ("steerD", 39), ("join2", 4), ("forkG3", 15), ("mux", 9),
       ("steerC", 4), ("forkH4", 9), ("forkG2", 4), ("forkG4", 4)] := by decide +kernel

/-- **The classes at the chain tails** (the consumer of a tail's output channel). -/
theorem tail_classes :
    census (tails.map (fun o => match linkOut (opAt o) with
      | some c => kname (opAt (consOf c)) | none => "?")) =
      [("join1", 11), ("muxn", 4), ("join2", 17), ("mux", 63), ("amerge", 5)] := by
  decide +kernel

/-! ## 2. The capstone with every link's `Env1` DERIVED from its chain -/

/-- **B's physical model of a link INSIDE A CHAIN** (`AssumeGuaranteeLinks.Chain`, no `Env1`
on any link) matched to C's channels `i` (input) and `o` (output): the link is cell `m+1`
of a chain `D` whose pins at this link ARE C's channel traces; plus Bfb2's H_WIRE_SPREAD
for its two outgoing wires and the latch data fields (as `PhysLink`). What the chain still
assumes is listed in `Chain`: gates, wires, edge-time definitions, timing, and the two END
contracts (`SRC_*`, `SNK_*`) of the chain's head producer and tail consumer. -/
def InChain (ch : Fin NC → Chan) (i o : Fin NC) : Prop :=
  ∃ (D : ChainData) (m : Nat), m < D.N ∧ Chain D ∧ ChainT D ∧
    D.req (m + 1) = (ch i).req ∧ D.ack (m + 1) = (ch o).ack ∧
    D.ack m = (ch i).ack ∧ D.req (m + 2) = (ch o).req ∧
    D.vh m + D.hi (m + 1) ≤ 2 * D.lo (m + 1) + min (D.Es m) (D.Ea m) ∧
    D.wh (m + 1) + D.hi (m + 1) ≤ 2 * D.lo (m + 1) + min (D.Es m) (D.Ea m) ∧
    (∀ t, D.O (m + 1) t = true → (ch o).dat t = (ch i).dat t) ∧
    (∀ t, D.O (m + 1) (t + 1) = false → (ch o).dat (t + 1) = (ch o).dat t)

/-- **`PhysLink` (with its `Env1`) from the chain** (`chain_env1`). -/
theorem physLink_of_inChain {ch : Fin NC → Chan} {i o : Fin NC} (h : InChain ch i o) :
    PhysLink (ch i) (ch o) := by
  obtain ⟨D, m, hm, C, T, e1, e2, e3, e4, s1, s2, d1, d2⟩ := h
  obtain ⟨E, Tm⟩ := chain_env1 C T m hm
  have St := C.H_STAGE m hm
  have Wa := C.H_WB m (by omega)
  have Wr := C.H_WF (m + 1) (by omega)
  rw [e1, e2] at St E
  rw [e3] at Wa
  rw [e4] at Wr
  exact ⟨D.rst, D.O (m + 1), D.qp (m + 1), D.lo (m + 1), D.hi (m + 1), D.fl (m + 1),
    D.fh (m + 1), D.R, D.Es m, D.Ea m, D.vl m, D.vh m, D.wl (m + 1), D.wh (m + 1), D.ρL m,
    D.αL m, St, E, Tm, C.H_LUT_POS (m + 1) (by omega), C.H_PWR m hm, Wa, Wr,
    (T.H_WIRE_R m (by omega)).2, (T.H_WIRE_R (m + 1) (by omega)).1, s1, s2, d1, d2⟩

/-- **End to end, with no link environment assumed.** C's gcd_hw circuit safety theorem
(`gcd_hw_circuit_safe`, via Bfb2's `gcd_hw_safe_phys_links`), with `H_CELLS` for all 175
link operators replaced by `InChain`: each link sits in a chain of B's physical links whose
`Env1` is DERIVED by the assume-guarantee induction (`chain_env1`). Still assumed: `H_CELLS`
for the other 192 operators, H_BUNDLE, H_CM_FORCED (C's), and, inside `InChain`, each
chain's two end contracts (the classes of `head_classes` / `tail_classes`).
CAVEAT (audit P12b, 2026-10-31): the chain hypothesis is a per-link existential. Nothing
ties one link's chain to another's or to gcd_hw's real producer/consumer cells, and a
chain-end contract holds whenever its end node is clean (`SelfAuditB9.seg_of_clean`). So
"Env1 derived" is derived from per-link end contracts whose content equals Env1's; it is
not a derivation from the netlist. The census chains of `head_classes`/`tail_classes`
are not used by the proof. -/
theorem gcd_hw_safe_chains (a b : Nat) (ch : Fin NC → Chan)
    (H_LINKS : ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → InChain ch i o')
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_phys_links a b ch (fun o i o' h => physLink_of_inChain (H_LINKS o i o' h))
    H_OTHER H_BUNDLE H_CM_FORCED

/-- **Non-vacuity of `InChain`**: the live chain `wD 1` of `AssumeGuaranteeLinks` (one
real `bd_c2n` link between a square-wave source and sink, LUT band `[1, 3]`, wires 1),
with C's two channels set to its pin traces, satisfies every field (H_WIRE_SPREAD with
slack 1). -/
theorem inChain_witness :
    InChain (fun c => if c = (0 : Fin NC) then
        ⟨Formal.Cells.PipeTimed.Wit.sq 4, Formal.Cells.PipeTimed.Wit.sq 6, fun _ => 0⟩
      else ⟨Formal.Cells.PipeTimed.Wit.sq 6, Formal.Cells.PipeTimed.Wit.sq 8, fun _ => 0⟩)
      0 1 := by
  refine ⟨AssumeGuaranteeLinks.wD 1, 0, by decide, AssumeGuaranteeLinks.w_chain 1,
    AssumeGuaranteeLinks.w_chainT 1, rfl, rfl, rfl, rfl, by decide, by decide,
    fun _ _ => rfl, fun _ _ => rfl⟩

end Formal.Cells.AssumeGuaranteeCap
