import Condorcet
import Lean.Util.CollectAxioms

/-!
# Proof dependencies

After `lake build`, run `lake env lean Audit.lean`. Each listed theorem is
checked against its allowed axioms. Lean reports an error for any additional
dependency, including an unfinished proof.
-/

open Lean

private def checkAxioms (declarations allowed : List Name) : Elab.Command.CommandElabM Unit := do
  for decl in declarations do
    let dependencies ← collectAxioms decl
    for ax in dependencies do
      unless allowed.contains ax do
        throwError "{decl} depends on an unexpected axiom: {ax}"

run_cmd
  let standard := [``propext, ``Classical.choice, ``Quot.sound]
  let ordinaryProofs := [
    ``ElectionLift.A_eq_sup_min_max, ``ElectionLift.coverage_guarantee_iff,
    ``ElectionLift.repeated_challenges, ``ElectionLift.rational_grade_realization,
    ``ElectionLift.Grades.pairValue_le, ``ElectionLift.Grades.weak_pair_certificate,
    ``ElectionLift.Grades.strict_pair_certificate, ``ElectionLift.SmallTables.hand_pair,
    ``ElectionLift.SmallTables.easy_triple, ``ElectionLift.SmallTables.sharp_triple,
    ``ElectionLift.SmallTables.four_seats, ``ElectionLift.general_transfer,
    ``ElectionLift.strict_thresholds, ``ElectionLift.dimension_at_least_four,
    ``ElectionLift.five_suffice, ``ElectionLift.four_or_five,
    ``ElectionLift.Historical.elkind_lang_saffidine, ``ElectionLift.Historical.cycle_limit,
    ``ElectionLift.Historical.speyer_eleven_of_twenty_one, ``ElectionLift.Historical.geist_dimension]
  let nativeChecks := [
    `PairBound.all_rows_pass._native.native_decide.ax_1_1,
    `Physical.every_literal_state._native.native_decide.ax_1_1,
    `Physical.total_weight._native.native_decide.ax_1_1]
  let certificateProofs := [
    ``Physical.appendix_certificate, ``Physical.pair_opposition_exact, ``ElectionLift.coverage_bound,
    ``ElectionLift.rounded_percentages, ``ElectionLift.asymptotic, ``ElectionLift.finite_at_epsilon,
    ``ElectionLift.refutes_cyclic_threshold, ``ElectionLift.every_triple_blocked]
  checkAxioms ordinaryProofs standard
  checkAxioms certificateProofs (standard ++ nativeChecks)
  logInfo m!"Verified axiom dependencies of {ordinaryProofs.length} ordinary theorems and \
    {certificateProofs.length} theorems using the numeric certificate."
