import Formal.Target.AssemblyPS
import Formal.Target.PlanPS
import Formal.Target.PlanRPS
import Formal.Target.CertN1
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ok := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut n : Nat := 0
  let mut bad : Nat := 0
  let mut nT : Nat := 0
  let mut allAx : Std.HashSet Name := {}
  for (c, _) in env.constants.toList do
    let some idx := env.getModuleIdxFor? c | continue
    let mn := env.header.moduleNames[idx.toNat]!
    unless (`Formal).isPrefixOf mn do continue
    n := n + 1
    if (`Formal.Target).isPrefixOf mn then nT := nT + 1
    let axs ← liftCoreM (Lean.collectAxioms c)
    for a in axs do
      allAx := allAx.insert a
      unless ok.contains a do
        bad := bad + 1
        logInfo s!"BAD {c} ({mn}) uses {a}"
  logInfo s!"AUDIT formalConstants={n} formalTargetConstants={nT} bad={bad} axiomsSeen={allAx.toList}"
  -- per-module counts for the four target modules
  for m in [`Formal.Target.AssemblyPS, `Formal.Target.PlanPS, `Formal.Target.PlanRPS, `Formal.Target.CertN1] do
    let some mi := env.getModuleIdx? m | logInfo s!"missing {m}"; continue
    let cs := env.header.moduleData[mi.toNat]!.constNames
    logInfo s!"MODULE {m} constants={cs.size}"
