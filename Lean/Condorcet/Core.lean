import Elections

namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

/-- Fraction of ballots on which one candidate is strictly above every entry. -/
def jointSupport (e : Election) (h : e.C) (r : List e.C) : ℝ := by
  classical
  exact mean fun v => ind (∀ x ∈ r, e.rank v h < e.rank v x)

def blocksList (e : Election) (k : ℕ) (q : ℝ) : Prop :=
  ∀ r : List e.C, r.length = k → ∃ h, q ≤ jointSupport e h r

/-- Ideal credit when exactly `i` rivals share the challenger's best grade. -/
def tiesCredit (a : ℝ) (i : ℕ) : ℝ :=
  if i ≤ 1 then 1 else max 0 (1-((i-1:ℕ):ℝ)*(1-a))

/-- One position's credit; a strictly better rival cancels all credit. -/
def rowCredit (a : ℝ) (g : ℕ) (grades : List ℕ) : ℝ :=
  if grades.any (· < g) then 0 else tiesCredit a (grades.filter (· == g)).length

end
end ElectionLift
