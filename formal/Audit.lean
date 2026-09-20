import BoundaryDraft
import Lean.Util.CollectAxioms

-- Fail the audit, rather than just printing a warning, if any checked theorem
-- depends on something beyond the standard Lean foundations.
run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let declarations := [
    ``BoundaryDraft.coefficient_factorization,
    ``BoundaryDraft.interval_moment_cancellation,
    ``BoundaryDraft.plane_coefficient_recurrence,
    ``BoundaryDraft.null_joint_area_decomposition,
    ``BoundaryDraft.uncut_joint_area,
    ``BoundaryDraft.angle_weight_squared,
    ``BoundaryDraft.signed_rescaling_limit,
    ``BoundaryDraft.signed_rescaling_limit_unit_mass]
  for declaration in declarations do
    for dependency in (← Lean.collectAxioms declaration) do
      unless allowed.contains dependency do
        throwError "Unexpected axiom {dependency} in {declaration}"

-- Human-readable audit trail for the same eight checked theorems.
#print axioms BoundaryDraft.coefficient_factorization
#print axioms BoundaryDraft.interval_moment_cancellation
#print axioms BoundaryDraft.plane_coefficient_recurrence
#print axioms BoundaryDraft.null_joint_area_decomposition
#print axioms BoundaryDraft.uncut_joint_area
#print axioms BoundaryDraft.angle_weight_squared
#print axioms BoundaryDraft.signed_rescaling_limit
#print axioms BoundaryDraft.signed_rescaling_limit_unit_mass

-- These are propositions, not proofs of those propositions.
#check BoundaryDraft.NullCapLimitGoal
#check BoundaryDraft.EllipsoidLimitGoal
#check BoundaryDraft.GraphReductionGoal
#check BoundaryDraft.KernelMassGoal
#check BoundaryDraft.KernelTailGoal
