import Krylov
import Lean

/-! Release gate: traverse VALUES ONLY, never declaration types. Requirements
are per final source-facing root, and missing roots, bridges or paths are fatal.
JSON-lines evidence accompanies concrete shortest dependency paths. -/
set_option maxHeartbeats 0
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let requirements : List (Name × List Name) := [
    (`Krylov.CanonicalFamilySource.main_continued_cv_lower,[`Krylov.FamilySourceAPI.mainSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.main_continued_finite_witness,[`Krylov.FamilySourceAPI.mainSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.main_continued_cv_unbounded,[`Krylov.FamilySourceAPI.mainSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.main_continued_source_properties,[`Krylov.FamilySourceAPI.mainSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.reciprocal_continued_cv_lower,[`Krylov.FamilySourceAPI.reciprocalSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.reciprocal_continued_finite_witness,[`Krylov.FamilySourceAPI.reciprocalSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.reciprocal_continued_cv_unbounded,[`Krylov.FamilySourceAPI.reciprocalSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.reciprocal_continued_source_properties,[`Krylov.FamilySourceAPI.reciprocalSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.reciprocal_scaled_continued_finite_witness,[`Krylov.FamilySourceAPI.reciprocalSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.reciprocal_scaled_continued_cv_value,[`Krylov.FamilySourceAPI.reciprocalSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.reciprocal_scaled_continued_cv_unbounded,[`Krylov.FamilySourceAPI.reciprocalSpread_canonical,`Krylov.CertifiedFamilyGS.five_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.fixed_uniform_bounds,[`Krylov.FamilySourceAPI.fixedSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.fixed_periodMean_bounds,[`Krylov.FamilySourceAPI.fixedSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.fixed_periodMean_unbounded,[`Krylov.FamilySourceAPI.fixedSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.fixed_uniformly_diverges,[`Krylov.FamilySourceAPI.fixedSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.qutrit_all_time_strict,[`Krylov.FamilySourceAPI.qutritSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.qutrit_no_positive_multiplier,[`Krylov.FamilySourceAPI.qutritSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.qutrit_peak_ratio,[`Krylov.FamilySourceAPI.qutritSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.CanonicalFamilySource.qutrit_asymptotic,[`Krylov.FamilySourceAPI.qutritSpread_canonical,`Krylov.CertifiedFamilyGS.three_atom,`Krylov.CertifiedGS.gramSchmidt_eq_inv_smul,`Krylov.MatrixGSBridge.spread_eq_normalized]),
    (`Krylov.PerturbedSourceAPI.robust_qutrit_witness,[`Krylov.PerturbedSourceAPI.mixed_canonical,`Krylov.PerturbedSourceAPI.purified_canonical,`Krylov.PureShortTime.operatorComplexity_physical,`Krylov.PerturbedDynamics.actualComplexity_eq_expectation]),
    (`Krylov.PerturbedSourceAPI.finite_certificate,[`Krylov.PerturbedSourceAPI.mixed_canonical,`Krylov.PerturbedSourceAPI.purified_canonical,`Krylov.PureShortTime.operatorComplexity_physical,`Krylov.PerturbedDynamics.actualComplexity_eq_expectation]),
    (`Krylov.PerturbedSourceAPI.cubic_certificate,[`Krylov.PerturbedSourceAPI.mixed_canonical,`Krylov.PerturbedSourceAPI.purified_canonical,`Krylov.PureShortTime.operatorComplexity_physical,`Krylov.PerturbedDynamics.actualComplexity_eq_expectation]) ]
  let mut checked := 0
  for (root,bridges) in requirements do
    let some rootInfo := env.find? root | throwError "Missing final release root: {root}"
    unless rootInfo.isTheorem do throwError "Release root is not a theorem: {root}"
    unless rootInfo.value?.isSome do throwError "Release root has no proof body: {root}"
    for bridge in bridges do
      unless env.contains bridge do throwError "Missing required bridge: {bridge}"
      let mut queue : Array (Name × List Name) := #[(root,[root])]
      let mut seen : NameSet := ({} : NameSet).insert root
      let mut cursor := 0
      let mut found : Option (List Name) := none
      while cursor < queue.size && found.isNone do
        let (name,path) := queue[cursor]!
        cursor := cursor + 1
        if name == bridge then
          found := some path.reverse
        else
          if let some info := env.find? name then
            -- Deliberately do not read info.type: a type-only reference is not evidence.
            let deps := match info.value? with
              | some value => value.getUsedConstants
              | none => #[]
            for dep in deps do
              if !seen.contains dep then
                seen := seen.insert dep
                queue := queue.push (dep,dep::path)
      match found with
      | none => throwError "VALUE_ONLY_REQUIRED_BRIDGE_MISSING root={root} bridge={bridge}"
      | some path =>
        let row := Json.mkObj [
          ("root",toJson root.toString),
          ("required_bridge",toJson bridge.toString),
          ("traversal",toJson "value-only"),
          ("reachable",toJson true),
          ("path",toJson (path.map Name.toString))]
        logInfo m!"REQUIRED_BRIDGE_JSON {row.compress}"
        logInfo m!"VALUE_ONLY_PATH {String.intercalate " -> " (path.map Name.toString)}"
        checked := checked + 1
  logInfo m!"VALUE-ONLY RELEASE GATE PASSED: {requirements.length} final source roots, {checked} required root/bridge pairs"
