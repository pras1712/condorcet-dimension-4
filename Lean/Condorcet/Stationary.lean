import Condorcet.External.FixedPointTheorems.brouwer
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

/-- If a reply is chosen for each list of five independent draws, there is
a distribution on candidates for which the reply has the same law as a draw. -/
theorem stationary_reply {α : Type} [Fintype α] [Nonempty α] [DecidableEq α]
    (f : (Fin 5 → α) → α) :
    ∃ p : α → ℝ, (∀ c, 0 ≤ p c) ∧ (∑ c, p c) = 1 ∧
      ∀ c, (∑ s : Fin 5 → α, (if f s = c then ∏ i, p (s i) else 0)) = p c := by
  classical
  let K := stdSimplex ℝ α
  let next (p : K) (c : α) :=
    ∑ s : Fin 5 → α, if f s = c then ∏ i, p.val (s i) else (0:ℝ)
  have maps (p : K) : next p ∈ K := by
    constructor
    · intro c
      apply Finset.sum_nonneg
      intro s _
      split
      · exact Finset.prod_nonneg fun i _ => p.property.1 (s i)
      · exact le_rfl
    · change ∑ c, (∑ s : Fin 5 → α, if f s = c then ∏ i, p.val (s i) else (0:ℝ)) = 1
      rw [Finset.sum_comm]
      simp only [Finset.sum_ite_eq,mem_univ,if_true]
      rw [← Fintype.sum_pow, p.property.2, one_pow]
  have hc : Continuous next := by
    apply continuous_pi
    intro c
    apply continuous_finsetSum
    intro s _
    by_cases h : f s = c
    · simp only [if_pos h]
      exact continuous_finsetProd _ fun i _ => (continuous_apply (s i)).comp continuous_subtype_val
    · simpa only [if_neg h] using (continuous_const (X := K) (y := (0:ℝ)))
  let F : C(K,K) := ⟨fun p => ⟨next p, maps p⟩,hc.subtype_mk maps⟩
  let c : α := Classical.choice ‹Nonempty α›
  have hne : K.Nonempty := ⟨Pi.single c 1,single_mem_stdSimplex ℝ c⟩
  obtain ⟨p, hp⟩ := brouwer_fixed_point K (convex_stdSimplex ℝ α)
    (isCompact_stdSimplex ℝ α) hne F
  exact ⟨p.val, p.property.1, p.property.2, fun c => congrArg (fun q : K => q.val c) hp⟩

end
end ElectionLift
