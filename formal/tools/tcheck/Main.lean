import Tcheck.Sound

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

partial def loop (h : IO.FS.Stream) (cur : Option Pending) (n : Nat) (out : IO.FS.Stream) :
    IO (Except String Nat) := do
  let line ← h.getLine
  if line.isEmpty then
    return (if cur.isSome then .error "unterminated instance at end of input" else .ok n)
  let ws := (line.trimAscii.toString.splitOn " ").filter (· ≠ "")
  match ws, cur with
  | [], _ => loop h cur n out
  | "#" :: _, _ => loop h cur n out
  | "inst" :: rest, none => loop h (some { label := " ".intercalate rest }) n out
  | ["setup", s], some p =>
    match parseNat! s with
    | .ok k => loop h (some { p with setup := k }) n out
    | .error e => return .error e
  | ["req", s], some p =>
    match parseNat! s with
    | .ok k => loop h (some { p with req := k }) n out
    | .error e => return .error e
  | "data" :: ds, some p =>
    match ds.mapM parseNat! with
    | .ok ks => loop h (some { p with data := p.data ++ ks.toArray }) n out
    | .error e => return .error e
  | ["arc", a, b, c, d], some p =>
    match parseNat! a, parseNat! b, parseNat! c, parseNat! d with
    | .ok a, .ok b, .ok c, .ok d => loop h (some { p with arcs := p.arcs.push ⟨a, b, c, d⟩ }) n out
    | _, _, _, _ => return .error s!"bad arc line: {line}"
  | ["end"], some p =>
    out.putStrLn (report p)
    out.flush
    loop h none (n + 1) out
  | _, _ => return .error s!"unexpected line: {line.trimAscii}"

def main (args : List String) : IO UInt32 := do
  let out ← IO.getStdout
  let h ← match args with
    | ["-"] | [] => IO.getStdin
    | [f] => do
      let fh ← IO.FS.Handle.mk f .read
      pure (IO.FS.Stream.ofHandle fh)
    | _ => do IO.eprintln "usage: tcheck FILE.tc"; return 2
  match ← loop h none 0 out with
  | .ok n => IO.eprintln s!"tcheck: {n} instance(s) checked"; return 0
  | .error e => IO.eprintln s!"tcheck: input error: {e}"; return 2
