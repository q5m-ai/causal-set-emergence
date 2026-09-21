import BoundaryDraft
import Lean.Util.CollectAxioms

-- Fail rather than merely printing a warning. Audit every public declaration
-- in the library namespace, so new theorems cannot escape a hand-kept list.
-- Private helper dependencies are included transitively by collectAxioms.
-- Exclude compiler-generated implementation artifacts, not their dependencies
-- when they actually occur in a public proof or definition.
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let env ← Lean.getEnv
  let declarations := (env.constants.toList.filter fun (name, _) =>
    name.getRoot == `BoundaryDraft && !name.isInternalDetail).mergeSort
      fun a b => a.1.toString ≤ b.1.toString
  let mut theoremCount := 0
  for (declaration, info) in declarations do
    let dependencies ← Lean.collectAxioms declaration
    for dependency in dependencies do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {declaration}"
    if info.isTheorem then
      theoremCount := theoremCount + 1
      Lean.logInfo m!"{declaration} depends on axioms: {dependencies}"
  if theoremCount == 0 then
    throwError "No BoundaryDraft theorems were audited"
  Lean.logInfo m!"Audited {theoremCount} public theorems and all public definitions in BoundaryDraft"

-- These are propositions, not proofs of those propositions.
#check BoundaryDraft.NullCapLimitGoal
#check BoundaryDraft.EllipsoidLimitGoal
#check BoundaryDraft.GraphReductionGoal
#check BoundaryDraft.KernelMassGoal
#check BoundaryDraft.KernelTailGoal

-- The concrete kernel targets, exact ellipsoid reduction, and unchanged
-- four-dimensional EllipsoidLimitGoal now have proofs. NullCapLimitGoal does not.
#check BoundaryDraft.kernelMassGoal
#check BoundaryDraft.kernelTailGoal
#check BoundaryDraft.planeKernel_rescaling_limit
#check BoundaryDraft.ellipsoid_complete_future
#check BoundaryDraft.planeAuxiliaryThird_eq_coneIntegral
#check BoundaryDraft.ellipsoid_graphReduction
#check BoundaryDraft.volume_ellipsoid_superlevel
#check BoundaryDraft.integral_ellipsoid_profile
#check BoundaryDraft.integrableOn_ellipsoid_profile
#check BoundaryDraft.integrableOn_ellipsoid_weight_mul
#check BoundaryDraft.integrableOn_ellipsoid_rescaled
#check BoundaryDraft.ellipsoid_continuumMean_eq_rescaled
#check BoundaryDraft.ellipsoidLimitGoal
