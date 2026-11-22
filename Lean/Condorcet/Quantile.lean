import Condorcet.Core

namespace ElectionLift
open Finset

/-- Cut a ballot at the first rank whose cumulative probability reaches one third.
The atom at the cut is counted on neither side. -/
theorem ballot_quantile (e : Election) (_strict : ∀ v, Function.Injective (e.rank v))
    (v : e.V) (p : e.C → ℝ) (_hp : ∀ c, 0 ≤ p c) (hs : ∑ c,p c = 1) :
    ∃ c, (∑ x : e.C, if e.rank v x < e.rank v c then p x else 0) ≤ 1/3 ∧
         (∑ x : e.C, if e.rank v c < e.rank v x then p x else 0) ≤ 2/3 := by
  classical
  let mass (j : ℕ) := ∑ x : e.C, if e.rank v x < j then p x else 0
  have top : mass e.height = 1 := by simpa [mass,e.bounded] using hs
  have ex : ∃ j, (1:ℝ)/3 ≤ mass j := ⟨e.height,by rw [top]; norm_num⟩
  obtain ⟨j,hj⟩ : ∃ j, Nat.find ex = j+1 := by
    cases eq : Nat.find ex with
    | zero =>
      have h := Nat.find_spec ex
      rw [eq] at h
      norm_num [mass] at h
    | succ j => exact ⟨j, rfl⟩
  have hi := Nat.find_spec ex
  rw [hj] at hi
  have lo : mass j < 1/3 := lt_of_not_ge (Nat.find_min ex (m:=j) (by omega))
  have atCut : ∃ x, e.rank v x = j := by
    by_contra! absent
    have eq : mass (j+1) = mass j := by
      apply Finset.sum_congr rfl
      intro x _
      have h := absent x
      have same : e.rank v x < j+1 ↔ e.rank v x < j := by omega
      simp [same]
    linarith
  obtain ⟨c,hc⟩ := atCut
  refine ⟨c, hc ▸ lo.le,?_⟩
  rw [hc]
  have part : mass (j+1) + (∑ x : e.C, if j < e.rank v x then p x else 0) = 1 := by
    unfold mass
    rw [← Finset.sum_add_distrib, ← hs]
    apply Finset.sum_congr rfl
    intro x _
    by_cases h : e.rank v x < j+1
    · simp [h, show ¬j < e.rank v x by omega]
    · simp [h, show j < e.rank v x by omega]
  linarith

end ElectionLift
