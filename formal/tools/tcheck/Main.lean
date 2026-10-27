import Tcheck.Sound
import Tcheck.Cert

/-!
`tcheck` (probe C-10e): read obligation instances, run the PROVED checker on each,
print verdict and margin.

    lake exe tcheck FILE.tc        (or `-` for stdin)

Input, one token group per line (written by `extract.py`):

    inst LABEL...            start an instance; LABEL is echoed back verbatim
    setup N                  setup margin (ps, Nat)
    req V                    the request node
    data V1 V2 ...           the data nodes (may repeat)
    arc SRC DST LO HI        one 10a arc (ps); nodes are Nats, launch = 0
    end                      finish the instance

Output, one line per instance, tab separated:

    LABEL  PASS|FAIL|ILLFORMED  margin  req=[e,l]  data_late=L  arcs=N

C-10k additions inside a cert instance (after its `late` line): `cut A B ...` (routed
arcs dropped from the late side, `Tcheck.Late.cut`) and `pair D X PH` (per-pair
targets: the verdict is then `Tcheck.pverdict`, proved in `Tcheck.pverdict_sound`,
and the margin is the least pair margin).

The verdict is `Tcheck.verdict` (= decide WF && 10d's checkArr), proved sound in
`Tcheck.verdict_sound`; margin is `Tcheck.margin` (= 10a's `slack`).
-/

open Formal.Timing Tcheck

structure Pending where
  label : String := ""
  setup : Nat := 0
  req : Nat := 0
  data : Array Nat := #[]
  arcs : Array Arc := #[]
  -- C-10h cert obligations (late side on the cyclic graph)
  late : Option (Nat × Late) := none
  cap : Nat := 0
  pots : Array (Nat × Nat × Nat) := #[]
  -- C-10k: per-pair targets (data node, target pin, phase); empty = cross product
  pairs : Array (Nat × Nat × Nat) := #[]

/-- The global routed graph (C-10h): one arc list per corner variant, storage flags. -/
structure Graph where
  nodes : Nat := 0
  arcs : Array (List GArc) := Array.replicate 6 []
  stor : Array Bool := #[]

def parseNat! (s : String) : Except String Nat :=
  match s.toNat? with
  | some n => .ok n
  | none => .error s!"not a natural number: '{s}'"

def showWin : Option Win → String
  | none => "never"
  | some (e, l) => s!"[{e},{l}]"

def report (p : Pending) : String :=
  let i : Inst := { net := ⟨p.arcs.toList⟩, req := p.req, data := p.data.toList, setup := p.setup }
  let wf := decide i.net.WF
  let v := verdict i
  let tag := if !wf then "ILLFORMED" else if v then "PASS" else "FAIL"
  let m := match margin i with | some x => toString x | none => "none"
  -- latest data arrival (for the report only; the verdict does not use it)
  let T := winTable i.net
  let late := i.data.foldl (fun acc d => match getW T d with
    | some (_, l) => max acc l | none => acc) 0
  s!"{p.label}\t{tag}\t{m}\treq={showWin (winArr i.net i.req)}\tdata_late={late}\tarcs={p.arcs.size}"

/-- C-10h: a cert obligation; the verdict is `Tcheck.cverdict` (`cverdict_sound`). -/
def reportCert (g : Graph) (p : Pending) (vi : Nat) (L : Late) : String :=
  let size := 2 * (g.nodes + 1) + 2
  let pot := p.pots.foldl (fun (A : Array Nat) (x, ph, v) => A.setIfInBounds (enc L x ph) v)
    (Array.replicate size p.cap)
  let i : CInst := { dag := ⟨p.arcs.toList⟩, data := p.data.toList, setup := p.setup,
                     late := L, pot := pot, cap := p.cap }
  let G := g.arcs.getD vi []
  let stor := fun x => g.stor.getD x false
  let wf := decide i.dag.WF
  let T := winTable i.dag
  if p.pairs.size > 0 then
    -- C-10k: per-pair verdict `Tcheck.pverdict` (`pverdict_sound`); margin = least
    -- (target potential - data latest - setup) over the pairs
    let v := pverdict stor G i p.pairs.toList
    let tag := if !wf then "ILLFORMED" else if v then "PASS"
      else if !lateOK L stor G i.potf then "CERTBAD" else "FAIL"
    let ms := p.pairs.toList.filterMap fun (d, x, ph) => match getW T d with
      | some (_, l) => some ((i.potf (enc L x ph) : Int) - l - p.setup)
      | none => none
    let m := match ms with
      | [] => "none"
      | a :: r => toString (r.foldl min a)
    s!"{p.label}\t{tag}\t{m}\treq=[pairs={p.pairs.size},cert]\tdata_late=-\tarcs={p.arcs.size}"
  else
  let v := cverdict stor G i
  let tag := if !wf then "ILLFORMED" else if v then "PASS"
    else if !lateOK L stor G i.potf then "CERTBAD" else "FAIL"
  let late := i.data.foldl (fun acc d => match getW T d with
    | some (_, l) => max acc l | none => acc) 0
  let b := cbound i
  let m := match b with | some x => toString ((x : Int) - late - p.setup) | none => "none"
  let bs := match b with | some x => toString x | none => "none"
  s!"{p.label}\t{tag}\t{m}\treq=[{bs},cert]\tdata_late={late}\tarcs={p.arcs.size}"

def flag (s : String) : Bool := s == "1"

partial def loop (h : IO.FS.Stream) (g : Graph) (cur : Option Pending) (n : Nat) (out : IO.FS.Stream) :
    IO (Except String Nat) := do
  let line ← h.getLine
  if line.isEmpty then
    return (if cur.isSome then .error "unterminated instance at end of input" else .ok n)
  let ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
  match ws, cur with
  | [], _ => loop h g cur n out
  | "#" :: _, _ => loop h g cur n out
  | ["graph", k], none =>
    match parseNat! k with
    | .ok k => loop h { nodes := k, stor := Array.replicate (k + 1) false } none n out
    | .error e => return .error e
  | "g" :: a :: b :: fr :: ivs, none =>
    match parseNat! a, parseNat! b, ivs.mapM parseNat! with
    | .ok a, .ok b, .ok xs =>
      if xs.length != 12 then return .error s!"bad g line: {line}" else
      let arr := (List.range 6).foldl (fun (A : Array (List GArc)) k =>
        A.modify k (fun l => ⟨a, b, xs.getD (2 * k) 0, xs.getD (2 * k + 1) 0, flag fr⟩ :: l)) g.arcs
      loop h { g with arcs := arr } none n out
    | _, _, _ => return .error s!"bad g line: {line}"
  | "stor" :: xs, none =>
    match xs.mapM parseNat! with
    | .ok ks => loop h { g with stor := ks.foldl (fun A k => A.setIfInBounds k true) g.stor } none n out
    | .error e => return .error e
  | "inst" :: rest, none => loop h g (some { label := " ".intercalate rest }) n out
  | ["setup", s], some p =>
    match parseNat! s with
    | .ok k => loop h g (some { p with setup := k }) n out
    | .error e => return .error e
  | ["req", s], some p =>
    match parseNat! s with
    | .ok k => loop h g (some { p with req := k }) n out
    | .error e => return .error e
  | "data" :: ds, some p =>
    match ds.mapM parseNat! with
    | .ok ks => loop h g (some { p with data := p.data ++ ks.toArray }) n out
    | .error e => return .error e
  | ["arc", a, b, c, d], some p =>
    match parseNat! a, parseNat! b, parseNat! c, parseNat! d with
    | .ok a, .ok b, .ok c, .ok d => loop h g (some { p with arcs := p.arcs.push ⟨a, b, c, d⟩ }) n out
    | _, _, _, _ => return .error s!"bad arc line: {line}"
  | ["late", vi, s, two, nf, st, sws], some p =>
    match parseNat! vi, parseNat! s with
    | .ok vi, .ok s =>
      let L : Late := { s := s, two := flag two, noFr0 := flag nf, stop0 := flag st, swStor := flag sws }
      loop h g (some { p with late := some (vi, L) }) n out
    | _, _ => return .error s!"bad late line: {line}"
  | "sw" :: xs, some p =>
    match xs.mapM parseNat!, p.late with
    | .ok ks, some (vi, L) => loop h g (some { p with late := some (vi, { L with sw := L.sw ++ ks }) }) n out
    | _, _ => return .error s!"bad sw line: {line}"
  | "blocked" :: xs, some p =>
    match xs.mapM parseNat!, p.late with
    | .ok ks, some (vi, L) =>
      loop h g (some { p with late := some (vi, { L with blocked := L.blocked ++ ks }) }) n out
    | _, _ => return .error s!"bad blocked line: {line}"
  | ["target", x, ph], some p =>
    match parseNat! x, parseNat! ph, p.late with
    | .ok x, .ok ph, some (vi, L) =>
      loop h g (some { p with late := some (vi, { L with targets := L.targets ++ [(x, ph)] }) }) n out
    | _, _, _ => return .error s!"bad target line: {line}"
  | "cut" :: xs, some p =>
    match xs.mapM parseNat!, p.late with
    | .ok ks, some (vi, L) =>
      let rec prs : List Nat → List (Nat × Nat) → Option (List (Nat × Nat))
        | [], acc => some acc.reverse
        | a :: b :: r, acc => prs r ((a, b) :: acc)
        | _, _ => none
      match prs ks [] with
      | some cs => loop h g (some { p with late := some (vi, { L with cut := L.cut ++ cs }) }) n out
      | none => return .error s!"bad cut line (not pairs): {line}"
    | _, _ => return .error s!"bad cut line: {line}"
  | ["pair", d, x, ph], some p =>
    match parseNat! d, parseNat! x, parseNat! ph with
    | .ok d, .ok x, .ok ph => loop h g (some { p with pairs := p.pairs.push (d, x, ph) }) n out
    | _, _, _ => return .error s!"bad pair line: {line}"
  | ["cap", c], some p =>
    match parseNat! c with
    | .ok c => loop h g (some { p with cap := c }) n out
    | .error e => return .error e
  | "pot" :: xs, some p =>
    match xs.mapM parseNat! with
    | .ok ks =>
      let rec trip : List Nat → Array (Nat × Nat × Nat) → Option (Array (Nat × Nat × Nat))
        | [], acc => some acc
        | a :: b :: c :: r, acc => trip r (acc.push (a, b, c))
        | _, _ => none
      match trip ks p.pots with
      | some ps => loop h g (some { p with pots := ps }) n out
      | none => return .error s!"bad pot line (not triples): {line}"
    | .error e => return .error e
  | ["end"], some p =>
    match p.late with
    | none => out.putStrLn (report p)
    | some (vi, L) => out.putStrLn (reportCert g p vi L)
    out.flush
    loop h g none (n + 1) out
  | _, _ => return .error s!"unexpected line: {line.trimAscii}"

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let h ← match args with
    | ["-"] | [] => IO.getStdin
    | [f] => do
      let fh ← IO.FS.Handle.mk f .read
      pure (IO.FS.Stream.ofHandle fh)
    | _ => do IO.eprintln "usage: tcheck FILE.tc"; return 2
  match ← loop h {} none 0 out with
  | .ok n => IO.eprintln s!"tcheck: {n} instance(s) checked"; return 0
  | .error e => IO.eprintln s!"tcheck: input error: {e}"; return 2
