import Krylov
import Lean.Util.CollectAxioms

/-! Audit every public/private kernel-safe project declaration, including all
project theorem constants, definitions, instances and generated logical constants.
Lean's compiler also emits unsafe runtime specializations. These are explicitly
listed separately: they cannot be logical proof dependencies and are not accepted
as additional axioms. No project theorem is omitted from the logical audit. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let projectModule := fun name : Name =>
    match env.getModuleIdxFor? name with
    | some idx => (`Krylov).isPrefixOf env.header.moduleNames[idx.toNat]!
    | none => false
  let entries := env.constants.toList.filter fun (name,_) => projectModule name
  for (name,info) in entries do
    if info.isTheorem && info.isUnsafe then
      throwError "Unexpected unsafe theorem: {name}"
    if !info.isUnsafe then
      let dependencies := info.type.getUsedConstants ++
        (match info.value? with | some v => v.getUsedConstants | none => #[])
      for dependency in dependencies do
        if let some dependencyInfo := env.find? dependency then
          if dependencyInfo.isUnsafe then
            throwError "Unsafe logical dependency: {name} -> {dependency}"
  let safeEntries := entries.filter fun (_,info) => !info.isUnsafe
  let runtimeEntries := entries.filter fun (_,info) => info.isUnsafe
  let names := safeEntries.map Prod.fst
  let theoremCount := (entries.filter fun (_,info) => info.isTheorem).length
  let (_, state) := ((names.forM Lean.CollectAxioms.collect).run env).run {}
  for ax in state.axioms do
    unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
      throwError "Unapproved reachable logical axiom: {ax}"
  for name in names do
    logInfo m!"AUDITED {name}"
  for (name,_) in runtimeEntries do
    logInfo m!"COMPILER_RUNTIME_ONLY_UNSAFE {name}"
  logInfo m!"AXIOM UNION: {state.axioms}"
  logInfo "MODULE COVERAGE: every declaration originating in a Krylov project module, regardless of namespace"
  logInfo m!"RUNTIME CLASSIFICATION: {runtimeEntries.length} unsafe compiler declarations listed separately; no theorem omitted"
  logInfo m!"AUDIT PASSED: {names.length} kernel-safe project declarations, including all {theoremCount} public/private theorem constants; only propext, Classical.choice, Quot.sound permitted"
