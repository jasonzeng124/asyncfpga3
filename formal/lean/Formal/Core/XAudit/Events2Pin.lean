import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Events2Strict
import Formal.Core.XAudit.Events2Design
import Formal.Core.XAudit.Events2PinDesign

/-!
# `xevents2pin` — the per-pin own-feedback race checker (executable main)

    xevents2pin NETLIST.json --bands BANDS.json [--top T] [--env LO:HI] [--cap N]

Shard A, probe events2pin. Notes: `formal/notes/A-events2pin.md`. The open item 1
of `Wip/Contradictions.lean` (X2): `xevents2` (strict or not) reads one band per
LUT, so its verdict is about H_ATOMIC_LUT behaviours (all pins of a LUT sampled at
one instant). This executable decides `Events2Strict.BackPin` on PER-PIN arcs and
prints CLEAN only as an instance of `sound_pin`, whose conclusion holds for every
behaviour in which every LUT reads each input pin through its own warp in its own
band (`Events2Pin.SatPin`): no H_ATOMIC_LUT.

## Bands

`BANDS.json` is a `Parse.Bands` file (unit, cells, arcs, ...) plus

    "pins":     {"<cell>/I<i>": [lo, hi], ...}   per-pin LUT arc (ps): site-pin delay
                                                  of the physical pin + its pin-to-O arc
    "sitepins": {"<cell>/I<i>": [lo, hi], ...}   (report only) the site-pin part alone

`formal/tools-A/xaudit/pinbands.py` writes them from a routed design: the LUT in
LOGICAL pin order (the bd_ce.v layout `xevents2` recognises), each logical pin
carrying the band of the PHYSICAL pin the placer put it on (the permutation read
from the routed JSON's `X_ORIG_PORT_A<k>`, which fasm_audit checks against the
FASM). `arcs` are then the route alone (prjxray IC row minus the site-pin
intrinsic of that corner), so the site pin is counted once, in the pin band.
A pin with no `pins` entry, and every 1-input gate, keeps its gate's band.

## What is PROVED here

`sound_pin`: if `Recog2 (close d env) net sm`, `BackPin sm.bands (pinsOf sm pl)
back`, `OneOK (close d env) pl`, `PinOK sm pl` and every environment gate is
`EnvOK`, then for EVERY per-pin behaviour of the parsed netlist (`SatPin d pl x`:
every gate reads each input index through its own monotone warp in `pl g i`; any
power-up; reset released once at `T`) whose input ports answer as their
environment gates say, every C-element output is `ph v (M t j)` at every time,
with `M` monotone and the per-window bound of every closed walk: no X, no
glitch, for all time. The executable checks exactly
these hypotheses with the compiled `Decidable` instances, on exactly the objects
`sound_pin` takes, and also `BandsOK` (no empty pin band, so `SatPin` is not
vacuous for want of a warp).

## What is TRUSTED

The parser (`Parse`), the `pins` table reader below, the recogniser and walk
search (copied from `Events2MainStrict`), and the report numbers (the atomic
comparison margins are printed, not proved). The Lean compiler is trusted to
run the `Decidable` instances as the kernel would.

Also proved and printed: the per-window upper bound (`cycle_le_pin`: at most
`wTok w` events of `j` in every window of `wLoP w`, around any closed walk `w`).
Not here: the long-run rate certificates of `Events2Time` (`UpCert`/`LoCert`),
proved for `Events2.Beh` only.
-/

namespace Formal.Core.XAudit.Events2PinMain

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Parse
open Formal.Core.XAudit.Events2
open Formal.Core.XAudit.Events2Strict
open Formal.Core.XAudit.Events2Pin
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig Transport)
open Formal.Core.XAudit.Events (ph)

/-! ## The verdict theorem (PROVED) -/

/-- **What `xevents2pin` prints is this theorem.** Hypotheses checked by the
executable with compiled `decide`: `hr`, `hB`, `h1`, `hp`, `he`. Modelling
hypotheses: `hsat` (per-pin semantics of every gate of the parsed netlist),
`henv` (each environment port answers its stage in a sub-band of its gate's
band), `h0`, `hrst`. -/
theorem sound_pin {N : Nat} (d : Design) (env : List GSpec) (net : CNet N) (sm : SMap2 net)
    (pl : PinTab) (back : (j : Fin N) → Fin (net.ar j) → List (Arc net))
    (hr : Recog2 (close d env) net sm) (hB : BackPin sm.bands (pinsOf sm pl) back)
    (h1 : OneOK (close d env) pl) (hp : PinOK sm pl) (he : ∀ g ∈ env, EnvOK g)
    (x : Fin d.n → Sig) (hsat : SatPin d pl x)
    (henv : ∀ g ∈ env, ∃ lo hi, g.lo ≤ lo ∧ hi ≤ g.hi ∧
      Transport lo hi (fun t => (g.init == 1) ^^ x (d.wire (g.ins.getD 0 0)) t) (x (d.wire g.out)))
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ M : Nat → Fin N → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧
      (∀ t j, x (d.wire (sm.lut j).out) t = ph (net.v j) (M t j)) ∧
      (∀ (w : List (Arc net)) (j : Fin N), walkOK net j j w = true →
        ∀ t, M (t + wLoP sm.bands (pinsOf sm pl) w) j ≤ M t j + wTok net w) := by
  have hs := sat_pin_close d env pl x hsat (fun g hg => by
    obtain ⟨lo, hi, h1', h2', h3'⟩ := henv g hg
    have hk := (he g hg).1
    exact env_pin (close d env) pl g (he g hg)
      (h1 g (by simp only [close, List.mem_append]; exact Or.inr hg) hk) x lo hi h1' h2' h3')
  exact design_safe_pin (close d env) net sm pl hr h1 hp hB x hs h0 T hT hrst

/-- The atomic `xevents2` behaviours are covered too: an atomic behaviour of a
netlist whose pin bands contain the gate bands is a per-pin one
(`sat_pin_of_sat`), so `sound_pin` applies to it. -/
theorem sound_pin_atomic {N : Nat} (d : Design) (env : List GSpec) (net : CNet N) (sm : SMap2 net)
    (pl : PinTab) (back : (j : Fin N) → Fin (net.ar j) → List (Arc net))
    (hr : Recog2 (close d env) net sm) (hB : BackPin sm.bands (pinsOf sm pl) back)
    (h1 : OneOK (close d env) pl) (hp : PinOK sm pl) (he : ∀ g ∈ env, EnvOK g)
    (hb : ∀ g ∈ d.gates, ∀ i, i < g.k → (pl g i).1 ≤ g.lo ∧ g.hi ≤ (pl g i).2)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (henv : ∀ g ∈ env, ∃ lo hi, g.lo ≤ lo ∧ hi ≤ g.hi ∧
      Transport lo hi (fun t => (g.init == 1) ^^ x (d.wire (g.ins.getD 0 0)) t) (x (d.wire g.out)))
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ M : Nat → Fin N → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧
      (∀ t j, x (d.wire (sm.lut j).out) t = ph (net.v j) (M t j)) ∧
      (∀ (w : List (Arc net)) (j : Fin N), walkOK net j j w = true →
        ∀ t, M (t + wLoP sm.bands (pinsOf sm pl) w) j ≤ M t j + wTok net w) :=
  sound_pin d env net sm pl back hr hB h1 hp he x (sat_pin_of_sat d pl x hb hsat) henv h0 T hT hrst

/-! ## Recognition (TRUSTED; copied from `Events2MainStrict`, re-checked by `Recog2`) -/

structure PinR where
  src : Nat
  chain : List GSpec
  pw : Nat
  inv : Bool
  neg : Bool
  port : Option String := none
  deriving Inhabited

structure StageR where
  lut : GSpec
  n : Nat
  v : Bool
  negMask : Nat
  pins : Array PinR
  fbG : GSpec
  rG : GSpec
  rstW : Nat
  deriving Inhabited

def isBufFrom (g : GSpec) (w : Nat) : Bool := g.k == 1 && g.init == 2 && g.ins == [w]

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

def asCel (gs : List GSpec) (g : GSpec) : Except String (Nat × Bool × Nat × GSpec × GSpec) := do
  let drv (w : Nat) := gs.find? (·.out == w)
  let fbIdx := (List.range 6).find? (fun i =>
    match drv (g.ins.getD i 0) with
    | some b => isBufFrom b g.out
    | none => false)
  let some n := fbIdx | throw "no own-feedback pin"
  if n == 0 || n > 4 then throw s!"own feedback on I{n}: not the bd_ce.v layout"
  if !((List.range 6).all (fun i => i < n + 2 || g.ins.getD i 0 == 0)) then
    throw s!"pins above I{n+1} are not tied to 0: not the bd_ce.v layout (latch or other storage?)"
  let some fbG := drv (g.ins.getD n 0) | throw "no feedback gate"
  let some rG := drv (g.ins.getD (n + 1) 0) | throw s!"I{n+1} has no driving arc (constant?): not a C-element reset pin"
  if !(rG.k == 1 && rG.init == 2 && rG.ins.length == 1) then throw s!"I{n+1} (reset) is not a routed arc"
  for m in List.range (2 ^ n) do
    for v in [false, true] do
      if decide (InitOK n v (fun p : Fin n => m.testBit p.val) g.init) then
        return (n, v, m, fbG, rG)
  throw s!"INIT {hex g.init} is not a {n}-input C-element (InitOK fails for every reset value and bubble pattern)"

def tracePin (gs : List GSpec) (stageOf : Nat → Option Nat) (portOf : Nat → Option String)
    (pw : Nat) : Except String (List GSpec × Sum Nat (String × Nat)) := do
  let mut cur := pw
  let mut ch : List GSpec := []
  for _ in List.range 256 do
    let some g := gs.find? (·.out == cur) | throw s!"wire {cur} has no driver"
    if !(g.k == 1 && (g.init == 1 || g.init == 2) && g.ins.length == 1) then
      throw s!"{g.name} is not a 1-input buffer/inverter and not a C-element stage (choice, datapath or unsupported logic: E5/E6)"
    ch := g :: ch
    cur := g.ins.getD 0 0
    if let some k := stageOf cur then return (ch, .inl k)
    if let some p := portOf cur then return (ch, .inr (p, cur))
    if cur ≤ 1 then throw s!"{g.name} reads a constant"
  throw "chain longer than 256 gates"

partial def walksGo (ar : Array Nat) (src : Array (Array Nat)) (b cap : Nat) (cur : Nat)
    (seen : List Nat) (acc : List (Nat × Nat)) (out : List (List (Nat × Nat))) :
    List (List (Nat × Nat)) :=
  (List.range (ar[cur]!)).foldl (fun out p =>
    if out.length ≥ cap then out else
    let nx := src[cur]![p]!
    let acc' := acc ++ [(cur, p)]
    if nx == b then acc' :: out
    else if seen.contains nx then out
    else walksGo ar src b cap nx (nx :: seen) acc' out) out

def walks (ar : Array Nat) (src : Array (Array Nat)) (a b cap : Nat) : List (List (Nat × Nat)) :=
  if a == b then [[]] else walksGo ar src b cap a [a] [] []

/-! ## Per-pin band table (TRUSTED reader) -/

/-- `"<cell>/I<i>"` → `(cell, i)`. -/
def splitPinKey (k : String) : Option (String × Nat) :=
  match k.splitOn "/I" with
  | [] | [_] => none
  | parts =>
      let i := parts.getLast!
      let cell := "/I".intercalate (parts.dropLast)
      i.toNat?.map (cell, ·)

def readTable (j : Json) (key : String) (u : Nat) : List (String × Nat × (Nat × Nat)) :=
  ((jget j key).map jobj).getD [] |>.filterMap (fun (k, v) => do
    let (c, i) ← splitPinKey k
    let b ← pairOf v
    let (lo, hi, _) := toSteps u b
    pure (c, i, (lo, hi)))

/-- The cell a LUT gate came from (`Parse` names LUT gates `<cell>/O`, `<cell>/O6`, `<cell>/O5`). -/
def cellOfGate (name : String) : String :=
  match name.splitOn "/" with
  | [] => name
  | parts => "/".intercalate parts.dropLast

def lookPin (tab : List (String × Nat × (Nat × Nat))) (cell : String) (i : Nat) : Option (Nat × Nat) :=
  (tab.find? (fun e => e.1 == cell && e.2.1 == i)).map (·.2.2)

/-! ## Main -/

def usage : String :=
  "usage: xevents2pin NETLIST.json --bands BANDS.json [--top T] [--env LO:HI (ps, default 0:500)] [--cap N]"

def parseLoHi (s : String) : Option (Nat × Nat) :=
  match s.splitOn ":" with
  | [a, b] => do pure (← a.toNat?, ← b.toNat?)
  | _ => none

def run (args : List String) : IO UInt32 := do
  let some netf := args.head? | IO.eprintln usage; return 2
  let j ← readJson netf
  let some bandsF := getArg args "--bands" | IO.eprintln usage; return 2
  let bj ← readJson bandsF
  let B := parseBands bj
  let (tname, top) ← IO.ofExcept (pickTop j (getArg args "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let d := bt.d
  let u := bt.unit
  let cap := ((getArg args "--cap").bind String.toNat?).getD 4096
  let some envPs := parseLoHi ((getArg args "--env").getD "0:500")
    | IO.eprintln usage; return 2
  let (elo, ehi, eraised) := toSteps u envPs
  if !d.wfB then IO.eprintln "xevents2pin: design not well formed (Design.WF failed)"; return 1
  let gs := d.gates
  let pinTab := readTable bj "pins" u
  let siteTab := readTable bj "sitepins" u
  -- the per-pin band table `sound_pin` takes
  let pl : PinTab := fun g i =>
    if g.k == 1 then (g.lo, g.hi) else (lookPin pinTab (cellOfGate g.name) i).getD (g.lo, g.hi)
  let site (g : GSpec) (i : Nat) : Nat × Nat := (lookPin siteTab (cellOfGate g.name) i).getD (0, 0)
  IO.println s!"xevents2pin: {netf} top {tname}: {d.n} wires, {gs.length} gates; {pinTab.length} per-pin LUT arcs, {siteTab.length} site-pin entries"
  IO.println s!"bands: 1 step = {u} ps; environment answer band [{elo}, {ehi}] steps = [{elo * u}, {ehi * u}] ps{if eraised then " (lo raised to 1 step)" else ""}"
  -- 1. C-element stages
  let cands := gs.filter (fun g => g.k == 6 && (List.range 6).any (fun i =>
    match gs.find? (·.out == g.ins.getD i 0) with
    | some b => isBufFrom b g.out
    | none => false))
  let mut stages : Array (GSpec × Nat × Bool × Nat × GSpec × GSpec) := #[]
  let mut others : List String := []
  for g in cands do
    match asCel gs g with
    | .ok (n, v, m, fb, rg) => stages := stages.push (g, n, v, m, fb, rg)
    | .error e => others := s!"{g.name}: {e}" :: others
  for o in others.reverse do
    IO.println s!"  storage LUT outside the control domain: {o}"
  let N := stages.size
  IO.println s!"{N} C-element stages recognised (InitOK on the bd_ce.v layout, logical pin order)"
  if hN : N = 0 then IO.println "no C-element stage: nothing to check"; return 0
  else
  have hN' : 0 < N := Nat.pos_of_ne_zero hN
  let stageOf (w : Nat) : Option Nat := stages.findIdx? (fun s => s.1.out == w)
  let portOf (w : Nat) : Option String := (bt.inputs.find? (·.2 == w)).map (·.1)
  -- 2. pins
  let mut errs : List String := []
  let mut srs : Array StageR := #[]
  let mut envGs : List GSpec := []
  let mut usedPorts : List String := []
  let rstW := (stages[0]!).2.2.2.2.2.ins.getD 0 0
  for jj in List.range N do
    let (g, n, v, m, fb, rg) := stages[jj]!
    if rg.ins.getD 0 0 != rstW then errs := s!"{g.name}: reset arc reads a different wire" :: errs
    let mut pins : Array PinR := #[]
    for p in List.range n do
      let pw := g.ins.getD p 0
      let neg := m.testBit p
      match tracePin gs stageOf portOf pw with
      | .error e => errs := s!"{g.name} pin I{p}: {e}" :: errs
      | .ok (ch, .inl k) =>
          pins := pins.push { src := k, chain := ch, pw, inv := cInv ch, neg }
      | .ok (ch, .inr (pn, pwire)) =>
          if pwire == rstW then errs := s!"{g.name} pin I{p}: reads the reset port" :: errs
          if usedPorts.contains pn then errs := s!"{g.name} pin I{p}: port {pn} is read by two control pins: no single handshake partner" :: errs
          usedPorts := pn :: usedPorts
          let envInv := !neg ^^ cInv ch
          let eg : GSpec := { name := s!"env:{pn}", k := 1, init := if envInv then 1 else 2,
                              ins := [g.out], out := pwire, lo := elo, hi := ehi }
          envGs := envGs ++ [eg]
          pins := pins.push { src := jj, chain := eg :: ch, pw, inv := !neg, neg, port := some pn }
    srs := srs.push { lut := g, n, v, negMask := m, pins, fbG := fb, rG := rg, rstW }
  if !errs.isEmpty then
    for e in errs.reverse do IO.println s!"  NOT RECOGNISED {e}"
    IO.println "VERDICT: NOT RECOGNISED: the control is not a network of C-elements joined by buffer/inverter chains and handshake ports; the Events2 domain does not apply"
    return 3
  if srs.any (fun s => s.pins.size != s.n) then IO.println "internal: pin count"; return 3
  -- 3. the objects `sound_pin` takes
  let fin (i : Nat) : Fin N := ⟨i % N, Nat.mod_lt _ hN'⟩
  let net : CNet N := {
    v := fun j => (srs[j.val]!).v
    ar := fun j => max 1 (srs[j.val]!).n
    ar_pos := fun _ => Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)
    src := fun j p => fin ((srs[j.val]!).pins[p.val]!).src
    inv := fun j p => ((srs[j.val]!).pins[p.val]!).inv
    neg := fun j p => ((srs[j.val]!).pins[p.val]!).neg }
  let sm : SMap2 net := {
    lut := fun j => (srs[j.val]!).lut
    chain := fun j p => ((srs[j.val]!).pins[p.val]!).chain
    pw := fun j p => ((srs[j.val]!).pins[p.val]!).pw
    fbG := fun j => (srs[j.val]!).fbG
    rG := fun j => (srs[j.val]!).rG
    rst := rstW }
  let D := close d envGs
  let bd := sm.bands
  let pb := pinsOf sm pl
  let arA : Array Nat := srs.map (fun s => s.n)
  let srcA : Array (Array Nat) := srs.map (fun s => s.pins.map (·.src))
  let toArcs (w : List (Nat × Nat)) : List (Arc net) := w.map (fun (k, p) =>
    ⟨fin k, ⟨p % net.ar (fin k), Nat.mod_lt _ (net.ar_pos _)⟩⟩)
  -- 4. back walks: the per-pin fastest traversal, largest among walks with few enough tokens
  let mut backA : Array (Array (List (Nat × Nat))) := #[]
  for jj in List.range N do
    let j := fin jj
    let mut row := #[]
    for pp in List.range arA[jj]! do
      let p : Fin (net.ar j) := ⟨pp % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
      let ws := (walks arA srcA (srcA[jj]!)[pp]! jj cap).filter (fun w =>
        wTok net (toArcs w) + net.off j p ≤ 1)
      let best := ws.foldl (fun (acc : Option (List (Nat × Nat))) w =>
        match acc with
        | none => some w
        | some a => if wLoP bd pb (toArcs w) > wLoP bd pb (toArcs a) then some w else some a) none
      row := row.push (best.getD [])
    backA := backA.push row
  let back : (j : Fin N) → Fin (net.ar j) → List (Arc net) := fun j p => toArcs ((backA[j.val]!)[p.val]!)
  -- 5. per-stage report
  let siteLo : List (Arc net) → Nat := fun w => w.foldl (fun a ar => a + (site (sm.lut ar.1) ar.2.val).1) 0
  let mut nNeg := 0
  let mut minPin : Option Int := none
  let mut minAt : Option Int := none
  for jj in List.range N do
    let j := fin jj
    let s := srs[jj]!
    let bub := (List.range s.n).filter (fun p => s.negMask.testBit p)
    let fbI := s.n
    IO.println s!"  stage {jj} {s.lut.name}: {s.n}-input C-element, reset {if s.v then 1 else 0}, bubbles {bub.map (s!"I{·}")}; LUT (atomic) [{bd.loF j * u},{bd.hiF j * u}] ps; feedback route [{bd.loQ j * u},{bd.hiQ j * u}] ps + feedback pin I{fbI} [{pb.loPq j * u},{pb.hiPq j * u}] ps (site pin [{(site s.lut fbI).1 * u},{(site s.lut fbI).2 * u}])"
    for pp in List.range s.n do
      let p : Fin (net.ar j) := ⟨pp % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
      let pin := s.pins[pp]!
      let w := back j p
      let tok := wTok net w + net.off j p
      let okW := walkOK net (net.src j p) j w
      let mPin : Int := (Int.ofNat (pb.loP j p + bd.loG j p + wLoP bd pb w) - Int.ofNat (bd.hiQ j + pb.hiPq j)) * u
      -- atomic comparison (report only): H_ATOMIC_LUT with the site pin counted in the route,
      -- as routed2x/xray_delay bands do: Back's margin on the same physical data
      let sp := site s.lut pp
      let sq := site s.lut fbI
      let mAt : Int := (Int.ofNat (bd.loG j p + sp.1 + wLo bd w + siteLo w) - Int.ofNat (bd.hiQ j + sq.2)) * u
      nNeg := if mPin ≤ 0 then nNeg + 1 else nNeg
      minPin := some (match minPin with | none => mPin | some m => min m mPin)
      minAt := some (match minAt with | none => mAt | some m => min m mAt)
      let what := match pin.port with
        | some pn => s!"port {pn} (environment, [{elo * u},{ehi * u}] ps)"
        | none => s!"stage {pin.src} through {pin.chain.length} gate(s){if pin.inv then ", inverted" else ""}"
      let wtxt := if w.isEmpty then "empty walk" else
        " -> ".intercalate (w.map (fun a => s!"{a.1.val}.I{a.2.val}"))
      IO.println s!"    I{pp} <- {what}; route [{bd.loG j p * u},{bd.hiG j p * u}] ps, pin arc [{pb.loP j p * u},{pb.hiP j p * u}] ps (site pin [{sp.1 * u},{sp.2 * u}]), token {net.off j p}"
      IO.println s!"      BackPin: walk {wtxt}, tokens {tok}{if okW then "" else " (walk invalid)"}; fastest return to O {(pb.loP j p + bd.loG j p + wLoP bd pb w) * u} ps vs slowest feedback to O {(bd.hiQ j + pb.hiPq j) * u} ps: margin {mPin} ps{if mPin ≤ 0 then "  <= 0" else ""} | atomic Back margin {mAt} ps (per-pin skew eats {mAt - mPin} ps)"
  -- per-window upper bounds (cycle_le_pin via `sound_pin`): the tightest simple cycle through each stage
  IO.println "per-window upper bounds (Events2PinDesign.cycle_le_pin, via `sound_pin`; walk re-checked with walkOK):"
  for jj in List.range N do
    let j := fin jj
    let cyc := (List.range arA[jj]!).flatMap (fun p =>
        (walks arA srcA (srcA[jj]!)[p]! jj cap).map ((jj, p) :: ·))
    let live := cyc.filter (fun c => wTok net (toArcs c) > 0)
    let best := live.foldl (fun (acc : Option (List (Nat × Nat))) c =>
      let w := toArcs c
      match acc with
      | none => some c
      | some a => let wa := toArcs a
          if wLoP bd pb w * wTok net wa > wLoP bd pb wa * wTok net w then some c else some a) none
    match best with
    | none => IO.println s!"  stage {jj}: on no live cycle: no per-window bound"
    | some c =>
        let w := toArcs c
        IO.println s!"  stage {jj}: at most {wTok net w} event(s) in every window of {wLoP bd pb w * u} ps (walk {" -> ".intercalate (c.map (fun a => s!"{a.1}.I{a.2}"))}, checked {walkOK net j j w})"
  -- 6. the checks `sound_pin` needs
  let recog := decide (Recog2 D net sm)
  let backOK := decide (BackPin bd pb back)
  let envOK := envGs.all (fun g => decide (EnvOK g))
  let oneOK := decide (OneOK D pl)
  let pinOK := decide (PinOK sm pl)
  let bandsOK := decide (BandsOK D pl)
  IO.println s!"Recog2 on the netlist closed by {envGs.length} environment gate(s) (proved-decidable): {recog}"
  IO.println s!"BackPin (every pin, per-pin arcs, margin >= 0 at 1 step = {u} ps, proved-decidable): {backOK}"
  IO.println s!"OneOK (1-input gates keep their band): {oneOK}; PinOK (pin arcs >= 1 step): {pinOK}; BandsOK (no empty pin band): {bandsOK}; EnvOK: {envOK}"
  IO.println s!"summary: {nNeg} pin(s) with BackPin margin <= 0; min BackPin margin {minPin.getD 0} ps; min atomic Back margin {minAt.getD 0} ps"
  if recog && backOK && envOK && oneOK && pinOK && bandsOK then
    IO.println s!"VERDICT: CLEAN FOREVER (Events2PinMain.sound_pin, per-pin LUT arcs, no H_ATOMIC_LUT): every per-pin behaviour of the parsed netlist (each LUT pin read through its own warp in its own band, every route in its band, any power-up, reset released once), with every handshake port answered by its stage within [{elo * u}, {ehi * u}] ps (HYPOTHESIS: environment = {envGs.map (·.name)}), has every C-element output = reset value flipped M t j times at every time."
    return 0
  else
    IO.println "VERDICT: NOT PROVED (a hypothesis of Events2PinMain.sound_pin fails; see the margins above). This is not a hazard report."
    return 1

end Formal.Core.XAudit.Events2PinMain

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Events2PinMain.run args
