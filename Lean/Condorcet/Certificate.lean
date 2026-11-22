import LiteralWords
import Condorcet.Pair

/-! Proposition 9 in its grade-table form. Integer weights are implemented by
repeating each voter position, so the table can also be used directly with
the general lemmas about grades. -/

noncomputable section
namespace Physical
open ElectionLift Finset

instance : NeZero PairBound.width := ⟨by decide⟩

/-- The appendix table, with each rational position weight cleared to an integer. -/
abbrev appendixMenus := model.expand weight total_weight
abbrev appendixGrades := appendixMenus.totalGrades

theorem appendix_row_count : boards.size = 113 := by native_decide

/-- Simultaneous realization of the nonzero-denominator and ratio conditions
for every rival assignment, including two equal assignments. -/
theorem appendix_certificate (a b : model.Cand) :
    ∃ h : model.Cand,
      appendixGrades.tally a b h 2 < PairBound.width ∧
      PairBound.numerator * (PairBound.width - appendixGrades.tally a b h 2) ≤
        PairBound.denominator * appendixGrades.tally a b h 1 := by
  classical
  obtain ⟨h, hh⟩ := perturbed_response a b
  obtain ⟨c, hc⟩ := appendixMenus.assemble PairBound.den PairBound.num a b h.1
  refine ⟨c, ?_⟩
  apply (score_test (P := PairBound.numerator) (Q := PairBound.denominator)
    (M := PairBound.width) (W := appendixGrades.tally a b c 1)
    (T := appendixGrades.tally a b c 2) (by decide) (tag_count_bound _)).mp
  change PairBound.num * PairBound.width <
      PairBound.den * appendixGrades.tally a b c 1 +
      PairBound.num * appendixGrades.tally a b c 2
  rw [Nat.mul_comm PairBound.num, show PairBound.den * appendixGrades.tally a b c 1 +
    PairBound.num * appendixGrades.tally a b c 2 = _ from hc]
  apply hh.trans_le
  apply Finset.sum_le_sum
  intro r _
  change model.score weight PairBound.den PairBound.num a b h.1 r (h.2 r) ≤ _
  rw [← model.expansion_score weight total_weight]
  exact Finset.le_sup (f := appendixMenus.rowScore PairBound.den PairBound.num a b h.1 r)
    (Finset.mem_univ (h.2 r))

end Physical
end
