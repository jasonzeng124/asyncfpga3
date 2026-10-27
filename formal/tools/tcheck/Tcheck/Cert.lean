import Formal.Timing.Unroll
import Tcheck.Sound

/-!
# Late sides on the cyclic routed graph, by checked potential (probe C-10h)

10g emitted the late (request) side of rules F, R and H as ONE path chosen by a
Python Dijkstra (H_EXTRACT_MIN). Here the late side is the whole routed graph
(one `GArc` list per corner variant, emitted once per file), seen through a
small per-obligation **phase rule** (`Late`), and its earliest change is bounded
by a potential that tcheck **checks** (`Formal.Timing.potOK_sound`). Python
still proposes the potential (its Dijkstra distances), but any proposal that
passes the check is sound, so the extractor's choice is no longer trusted.

The phase rule is the modelling content (it says which arcs can carry the
response); it is stated here, in Lean, instead of inside the Python search:

* node `(p, ph)` = routed pin `p` in phase `ph ∈ {0, 1}`; `(s, 0)` is the launch
  (node 0 of the netlist), every other `(p, ph)` is `2 (p + 1) + ph`;
* `noFr0`: phase 0 drops FASTRISE-side arcs (a falling wave does not travel
  through a rise-only tap, tighten's polarity rule);
* `stop0`: phase 0 does not leave a storage node other than the launch (tighten's
  segment walk);
* `swStor`: leaving a storage node other than the launch enters phase 1
  (rule H: past the first state node any polarity);
* `sw`: pins with a `[0,0]` switch `(p,0) → (p,1)` (rule F: the line's tail);
* `blocked`: pins whose arcs are dropped in both phases (rule H: ctl's own,
  closed, latch bits);
* `two = false`: no phase 1 at all (rule R: the raw graph).
-/

namespace Tcheck
open Formal.Timing Formal.Net

/-- One routed arc of one corner variant, with its FASTRISE-side flag. -/
structure GArc where
  src : Nat
  dst : Nat
  lo : Nat
  hi : Nat
  fr : Bool

/-- The per-obligation phase rule (see the module doc). -/
structure Late where
  s : Nat
  two : Bool := false
  noFr0 : Bool := false
  stop0 : Bool := false
  swStor : Bool := false
  sw : List Nat := []
  blocked : List Nat := []
  targets : List (Nat × Nat) := []

def enc (L : Late) (p ph : Nat) : Nat := if p = L.s ∧ ph = 0 then 0 else 2 * (p + 1) + ph

/-- The product arcs one routed arc contributes. -/
def expand (L : Late) (stor : Nat → Bool) (g : GArc) : List Arc :=
  if L.blocked.contains g.src then [] else
  let st := stor g.src && g.src != L.s
  let a0 : List Arc :=
    if (L.noFr0 && g.fr) || (L.stop0 && st) then []
    else [⟨enc L g.src 0, enc L g.dst (if L.swStor && st then 1 else 0), g.lo, g.hi⟩]
  let a1 : List Arc := if L.two then [⟨enc L g.src 1, enc L g.dst 1, g.lo, g.hi⟩] else []
  a0 ++ a1

def switches (L : Late) : List Arc := L.sw.map fun p => ⟨enc L p 0, enc L p 1, 0, 0⟩

/-- The late-side netlist (cyclic in general): the hypothesis of a cert verdict is
that the circuit's response to the launch is a 10a `Run` of this netlist. -/
def lateNet (L : Late) (stor : Nat → Bool) (G : List GArc) : Netlist :=
  ⟨switches L ++ G.flatMap (expand L stor)⟩

/-- The same check as `potOK (lateNet ..).arcs`, without building the list. -/
def lateOK (L : Late) (stor : Nat → Bool) (G : List GArc) (pot : Nat → Nat) : Bool :=
  (switches L).all (potArcOK pot) && G.all fun g => (expand L stor g).all (potArcOK pot)

theorem lateOK_eq (L : Late) (stor : Nat → Bool) (G : List GArc) (pot : Nat → Nat) :
    lateOK L stor G pot = potOK (lateNet L stor G).arcs pot := by
  simp [lateOK, potOK, lateNet, List.all_append, List.all_flatMap]

/-- One cert obligation: a data DAG (10a/10d, must be early) and a late side on the
cyclic graph (must be late), both launched by the same event at time 0. -/
structure CInst where
  dag : Netlist
  data : List Nat
  setup : Nat
  late : Late
  pot : Array Nat
  cap : Nat

def CInst.potf (i : CInst) (x : Nat) : Nat := i.pot.getD x i.cap

/-- What tcheck prints as PASS for a cert obligation. -/
def cverdict (stor : Nat → Bool) (G : List GArc) (i : CInst) : Bool :=
  decide i.dag.WF && lateOK i.late stor G i.potf &&
  i.late.targets.all (fun q => enc i.late q.1 q.2 != 0) &&
  i.data.all fun d => match winArr i.dag d with
    | none => true
    | some (_, l) => i.late.targets.all fun q => decide (l + i.setup ≤ i.potf (enc i.late q.1 q.2))

/-- The late bound tcheck prints: the least potential over the targets. -/
def cbound (i : CInst) : Option Nat :=
  i.late.targets.foldl (fun acc q => let b := i.potf (enc i.late q.1 q.2)
    match acc with | none => some b | some a => some (min a b)) none

/-- **Soundness of a cert PASS.** If the data side is a `Run` of the emitted DAG and
the response is a `Run` of the late-side netlist (same launch at time 0), every
data change precedes every change of every target by at least `setup`. -/
theorem cverdict_sound {stor : Nat → Bool} {G : List GArc} {i : CInst}
    (h : cverdict stor G i = true) {sigD sigL : Nat → Trace}
    (rD : Run i.dag sigD) (rL : Run (lateNet i.late stor G) sigL) :
    ∀ d ∈ i.data, ∀ q ∈ i.late.targets, ∀ s t, changes (sigD d) s →
      changes (sigL (enc i.late q.1 q.2)) t → s + i.setup ≤ t := by
  intro d hd q hq s t hs ht
  simp only [cverdict, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hwf, hlate⟩, hnz⟩, hdata⟩ := h
  rw [lateOK_eq] at hlate
  have hq0 : enc i.late q.1 q.2 ≠ 0 := by
    have := hnz q hq; simpa using this
  have hb := potOK_sound hlate rL t _ hq0 ht
  obtain ⟨e, l, hw, _, hsl⟩ := changes_in_winArr hwf rD d s hs
  have := hdata d hd
  rw [hw] at this
  simp only [List.all_eq_true, decide_eq_true_eq] at this
  have := this q hq
  omega

end Tcheck
