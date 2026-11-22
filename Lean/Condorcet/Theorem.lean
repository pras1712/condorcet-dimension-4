import Condorcet.Blocks
import Condorcet.SmallTablesResults
import Condorcet.Certificate
import Condorcet.Dimension
import Condorcet.Asymptotic

/-!
# Elections with Condorcet Dimension 4

The general transfer bounds the worst-case opposition `A k` in terms of `A 2`.
The appendix gives a lower bound `z` on `A 2`. Combining the two gives
`coverage_bound`, the main theorem for the universal coverage guarantee `C k`.
-/

namespace ElectionLift
noncomputable section
open Filter

/-- The rational lower bound on pair opposition certified in the appendix. -/
def z : ℝ := 351449648252133 / 512000000000000

theorem z_le_pair : z ≤ A 2 := by
  rw [A_two_eq]
  exact Physical.pair_opposition_exact

/-- Proposition 8. The two-seat opposition bound transfers to every larger committee size. -/
theorem general_transfer (k : ℕ) (hk : 2 ≤ k) : 3 * A 2 / (k + 1) ≤ A k := by
  rw [A_two_eq]
  exact transfer_from_bases SmallTables.sharp_triple SmallTables.four_seats k hk

/-- Theorem 1. Both upper bounds apply to the largest universal coverage guarantee. -/
theorem coverage_bound (k : ℕ) (hk : 2 ≤ k) :
    C k ≤ 1 - 3 * A 2 / (k + 1) ∧ 1 - 3 * A 2 / (k + 1) ≤ 1 - 3 * z / (k + 1) := by
  refine ⟨sub_le_sub_left (general_transfer k hk) _, sub_le_sub_left ?_ _⟩
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left z_le_pair (by norm_num)) (by positivity)

theorem numerical_bound (k : ℕ) (hk : 2 ≤ k) : C k ≤ 1 - 3 * z / (k + 1) :=
  (coverage_bound k hk).1.trans (coverage_bound k hk).2

/-! ## Small committee sizes and the asymptotic bound -/

/-- The elementary constructions already give both strict thresholds. -/
theorem strict_thresholds : C 2 < 1 / 3 ∧ C 3 < 1 / 2 := by
  have pair := SmallTables.hand_pair
  have triple := SmallTables.easy_triple
  unfold C
  rw [A_two_eq]
  constructor <;> linarith

theorem table_small_k :
    C 2 ≤ 1 - z ∧ C 3 ≤ 1 - 3 * z / 4 ∧ C 4 ≤ 1 - 3 * z / 5 ∧ C 5 ≤ 1 - z / 2 := by
  have h₂ := numerical_bound 2 (by decide)
  have h₃ := numerical_bound 3 (by decide)
  have h₄ := numerical_bound 4 (by decide)
  have h₅ := numerical_bound 5 (by decide)
  norm_num [z] at *
  exact ⟨h₂, h₃, h₄, h₅⟩

/-- Coverage fractions corresponding to 31.36%, 48.52%, 58.82%, and 65.68%. -/
theorem rounded_percentages :
    C 2 ≤ 3136 / 10000 ∧ C 3 ≤ 4852 / 10000 ∧
      C 4 ≤ 5882 / 10000 ∧ C 5 ≤ 6568 / 10000 := by
  obtain ⟨h₂, h₃, h₄, h₅⟩ := table_small_k
  norm_num [z] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem asymptotic :
    (3 * z : ℝ) > 2059275 / 1000000 ∧
      ((3 * z : ℝ) : EReal) ≤ liminf (fun k : ℕ => ((k * (1 - C k) : ℝ) : EReal)) atTop :=
  ⟨by norm_num [z], liminf_of_coverage_bound (3 * z) numerical_bound⟩

/-! ## Finite elections and the quantifiers in the lower bound -/

/-- One finite election witnesses the threshold against every committee of size `k`. -/
theorem finite_at_epsilon (k : ℕ) (hk : 2 ≤ k) {ε : ℝ} (hε : 0 < ε) :
    3 * z / (k + 1) - ε ∈ realizableK k := by
  apply finite_witness_below
  have bound := numerical_bound k hk
  unfold C at bound
  linarith

/-- The outsider may depend on the committee in the chosen election. -/
theorem finite_strictly_above (k : ℕ) (hk : 2 ≤ k) {b : ℝ} (hb : b < 3 * z / (k + 1)) :
    ∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧ k < Fintype.card e.C ∧
      ∀ S : Finset e.C, S.card = k → ∃ h ∉ S, b < jointSupport e h S.toList := by
  obtain ⟨c, hc, hc'⟩ := exists_between hb
  obtain ⟨e, strict, size, blocks⟩ := finite_at_epsilon k hk (sub_pos.mpr hc')
  refine ⟨e, strict, size, fun S hS => ?_⟩
  obtain ⟨h, nh, good⟩ := blocks S hS
  exact ⟨h, nh, by linarith⟩

theorem refutes_cyclic_threshold (k : ℕ) (hk : 2 ≤ k) :
    ∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧ k < Fintype.card e.C ∧
      ∀ S : Finset e.C, S.card = k → ∃ h ∉ S, 2 / (k + 1) < jointSupport e h S.toList :=
  finite_strictly_above k hk (div_lt_div_of_pos_right (by norm_num [z]) (by positivity))

theorem every_triple_blocked :
    ∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧ 3 < Fintype.card e.C ∧
      ∀ S : Finset e.C, S.card = 3 → ∃ h ∉ S, 5148 / 10000 < jointSupport e h S.toList :=
  finite_strictly_above 3 (by decide) (by norm_num [z])

/-! ## Condorcet dimension -/

/-- The hand-checkable triple obstruction gives an election of dimension at least four. -/
theorem dimension_at_least_four :
    ∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧ 4 ≤ dimension e := by
  have half : (1 : ℝ) / 2 < A 3 := by
    linarith [SmallTables.hand_pair, SmallTables.easy_triple]
  obtain ⟨b, hb, near⟩ := exists_between half
  obtain ⟨e, strict, size, blocks⟩ := finite_witness_below near
  refine ⟨e, strict, dimension_gt_of_blocked size (fun S hS => ?_)⟩
  obtain ⟨h, hn, hs⟩ := blocks S hS
  exact ⟨h, hn, hb.le.trans hs⟩

/-- `Condorcet.Majority` supplies the five-seat theorem to obtain the unconditional result. -/
theorem four_or_five_of_five_suffice
    (five : ∀ e : Election, (∀ v, Function.Injective (e.rank v)) → dimension e ≤ 5) :
    ∃ d ∈ ({4, 5} : Finset ℕ),
      (∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧ dimension e = d) ∧
      ∀ e : Election, (∀ v, Function.Injective (e.rank v)) → dimension e ≤ d := by
  classical
  by_cases four : ∀ e : Election, (∀ v, Function.Injective (e.rank v)) → dimension e ≤ 4
  · obtain ⟨e, strict, lower⟩ := dimension_at_least_four
    exact ⟨4, by simp, ⟨e, strict, le_antisymm (four e strict) lower⟩, four⟩
  · push Not at four
    obtain ⟨e, strict, lower⟩ := four
    have upper := five e strict
    exact ⟨5, by simp, ⟨e, strict, by omega⟩, five⟩

end
end ElectionLift
