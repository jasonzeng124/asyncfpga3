import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.EventsDesign

/-!
# `xevents` — counter-domain (event) check of closed Muller networks (executable main)

    xevents NETLIST.json [--top T] [--bands BANDS.json]

Probe A-events. TRUSTED (not proved): the parser (`Formal.Core.XAudit.Parse`,
shared with `xaudit`), the recogniser `recognise`, and the
report. What is NOT trusted: the recogniser's output is re-checked by the
proved-decidable `Recog` (compiled `decide`), and `Pairing` and `Race` are
evaluated by their `Decidable` instances. When all three hold, the printed
verdict is `Events.design_safe`: every behaviour of the parsed netlist (all
delays in the parsed bands, any power-up, reset released once) has every
C-element node equal to its reset value flipped `M t j` times, at every time:
no X, no glitch, ever.

The event-spacing bounds printed per node are the max cycle ratio of the
counter graph (sum of LUT+route delays / tokens on each simple cycle). That
number is COMPUTED, not proved, except for ring3 where `EventsRing` proves
`[3d, 3D]` and `EventsDesign.Ring3D.ring3_design` proves it on the parsed
netlist.
-/

namespace Formal.Core.XAudit.EventsMain

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Parse


/-! ## Muller recognition and report (events) -/

def c2n : Nat := 0x00B200B200B200B2
def c2nSet : Nat := 0xFFB2FFB2FFB2FFB2

def bufOf (gs : List GSpec) (w : Nat) : Option GSpec :=
  gs.find? (fun g => g.out == w && g.k == 1 && g.init == 2 && g.ins.length == 1)

/-- Simple cycles of the counter graph (edge `src j p → j`), by DFS from each
smallest node; returns, per cycle, (Σ lo, Σ hi, Σ tokens). -/
partial def cycles (N : Nat) (edges : List (Nat × Nat × Nat × Nat × Nat)) : List (Nat × Nat × Nat) :=
  -- edges: (from, to, lo, hi, tok)
  let rec go (s cur : Nat) (seen : List Nat) (lo hi tok : Nat) : List (Nat × Nat × Nat) :=
    edges.foldl (fun acc (a, b, l, h, k) =>
      if a != cur then acc
      else if b == s then (lo + l, hi + h, tok + k) :: acc
      else if b < s || seen.contains b then acc
      else acc ++ go s b (b :: seen) (lo + l) (hi + h) (tok + k)) []
  (List.range N).flatMap (fun s => go s s [s] 0 0 0)

def fmtRatio (num den : Nat) : String :=
  if den == 0 then "inf" else s!"{num / den}.{(num * 10 / den) % 10}"

def runEvents (args : List String) : IO UInt32 := do
  let some netf := args.head? | IO.eprintln "usage: xevents NETLIST.json [--top T] [--bands B.json]"; return 2
  let j ← readJson netf
  let B ← match getArg args "--bands" with
    | some p => pure (parseBands (← readJson p))
    | none => pure ({} : Bands)
  let (tname, top) ← IO.ofExcept (pickTop j (getArg args "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let d := bt.d
  let u := bt.unit
  if !d.wfB then IO.eprintln "xevents: design not well formed"; return 1
  let gs := d.gates
  let luts := gs.filter (fun g => g.k == 6 && (g.init == c2n || g.init == c2nSet) &&
    g.ins.length == 6 && g.ins.getD 4 99 == 0 && g.ins.getD 5 99 == 0)
  let N := luts.length
  IO.println s!"xevents: {netf} top {tname}: {d.n} wires, {gs.length} gates; {N} C-element stages (bd_c2n / bd_c2n_set INIT on [a, b, q, rst, 0, 0])"
  IO.println s!"bands: 1 step = {u} ps"
  if hN : N = 0 then IO.println "no C-element stage: nothing to check"; return 0
  else
  have hN' : 0 < N := Nat.pos_of_ne_zero hN
  let idxOf (w : Nat) : Option Nat := luts.findIdx? (fun g => g.out == w)
  let fin (i : Nat) : Fin N := ⟨i % N, Nat.mod_lt _ hN'⟩
  -- recognise every stage's four pin buffers
  let mut srcs : Array (Nat × Nat) := #[]
  let mut pinGs : Array (GSpec × GSpec × GSpec × GSpec) := #[]
  let mut rstW : Option Nat := none
  let mut errs : List String := []
  for g in luts do
    let w := fun i => g.ins.getD i 0
    match bufOf gs (w 0), bufOf gs (w 1), bufOf gs (w 2), bufOf gs (w 3) with
    | some ga, some gb, some gq, some gr =>
        let ia := ga.ins.getD 0 0
        let ib := gb.ins.getD 0 0
        match idxOf ia, idxOf ib with
        | some ka, some kb =>
            if gq.ins.getD 0 0 != g.out then errs := s!"{g.name}: I2 is not routed from its own output" :: errs
            let r := gr.ins.getD 0 0
            if rstW.isSome && rstW != some r then errs := s!"{g.name}: I3 reads a different reset wire" :: errs
            rstW := some r
            srcs := srcs.push (ka, kb)
            pinGs := pinGs.push (ga, gb, gq, gr)
        | _, _ => errs := s!"{g.name}: I0/I1 reads wire {bt.wname[ia]?.getD "?"} / {bt.wname[ib]?.getD "?"}, not a C-element node (environment port?): not a closed Muller network" :: errs
    | _, _, _, _ => errs := s!"{g.name}: a pin is not a routed arc" :: errs
  if !errs.isEmpty then
    for e in errs.reverse do IO.println s!"  NOT RECOGNISED {e}"
    IO.println "VERDICT: not a closed Muller network of bd_c2n stages; the counter domain (Events.design_safe) does not apply as is (an open pipe needs an environment model: see formal/notes/A-events.md)"
    return 3
  let some rw := rstW | return 3
  let lutsA := luts.toArray
  let net : Events.MNet N := { v := fun j => (lutsA[j.val]!).init == c2nSet,
                               src := fun j p => fin (if p then (srcs[j.val]!).2 else (srcs[j.val]!).1) }
  let sm : Events.SMap N := {
    lut := fun j => lutsA[j.val]!
    pinG := fun j p => if p then (pinGs[j.val]!).2.1 else (pinGs[j.val]!).1
    fbG := fun j => (pinGs[j.val]!).2.2.1
    rG := fun j => (pinGs[j.val]!).2.2.2
    rst := rw }
  let recog := decide (Events.Recog d net sm)
  let pair := decide net.Pairing
  let race := decide (Events.Race net sm.bands)
  let bd := sm.bands
  for jj in List.range N do
    let j := fin jj
    let g := lutsA[jj]!
    IO.println s!"  stage {jj} {g.name} (wire {g.out} '{bt.wname[g.out]?.getD "?"}', reset {if net.v j then 1 else 0}): a <- stage {(net.src j false).val}, b <- stage {(net.src j true).val}; LUT [{bd.loF j * u},{bd.hiF j * u}] ps, own feedback [{bd.loQ j * u},{bd.hiQ j * u}] ps"
    for p in [false, true] do
      let k := net.src j p
      for p' in [false, true] do
        if net.src k p' == j then
          let rt := bd.loG j p + bd.loF k + bd.loG k p'
          IO.println s!"    race via {if p then "b" else "a"} -> stage {k.val} -> back: fastest round trip {rt * u} ps vs own feedback max {bd.hiQ j * u} ps: margin {(Int.ofNat rt - Int.ofNat (bd.hiQ j)) * u} ps"
  IO.println s!"Recog (proved-decidable, re-checks the recogniser): {recog}"
  IO.println s!"Pairing (handshake structure): {pair}"
  IO.println s!"Race (feedback <= fastest neighbour round trip, every pin): {race}"
  -- counter graph cycles (untrusted arithmetic, report only)
  let edges := (List.range N).flatMap (fun jj => [false, true].map (fun p =>
    let j := fin jj
    ((net.src j p).val, jj, bd.loF j + bd.loG j p, bd.hiF j + bd.hiG j p, net.off j p)))
  let cs := cycles N edges
  let zero := cs.filter (fun c => c.2.2 == 0)
  let best := cs.foldl (fun (acc : Nat × Nat × Nat × Nat) (lo, hi, tok) =>
    if tok == 0 then acc else
    let (alo, atok, ahi, ahtok) := acc
    let acc1 := if lo * atok > alo * tok then (lo, tok) else (alo, atok)
    let acc2 := if hi * ahtok > ahi * tok then (hi, tok) else (ahi, ahtok)
    (acc1.1, acc1.2, acc2.1, acc2.2)) (0, 1, 0, 1)
  IO.println s!"counter graph: {cs.length} simple cycles, {zero.length} with no token"
  if !zero.isEmpty then IO.println "  a token-free cycle: that loop can never fire (dead)"
  IO.println s!"event spacing per node (max cycle ratio, COMPUTED not proved except ring3): [{fmtRatio (best.1 * u) best.2.1}, {fmtRatio (best.2.2.1 * u) best.2.2.2}] ps; period (two events) twice that"
  if recog && pair && race then
    IO.println "VERDICT: CLEAN FOREVER. Events.design_safe: every behaviour (every delay in the bands, any power-up, reset released once) has every C-element node = reset value flipped M t j times at every time, M the counter recursion: no X, no glitch, no stored X, for all time."
    return 0
  else
    IO.println "VERDICT: NOT PROVED (a hypothesis of Events.design_safe fails; see above). This is not a hazard report: run xaudit for the X-window audit."
    return 1

end Formal.Core.XAudit.EventsMain

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.EventsMain.runEvents args
