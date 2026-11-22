import Condorcet.Opposition
import Condorcet.Refinement

namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

/-- Remove the cyclic tie-breaking loss; each individual approximant is a
single finite strict election. -/
theorem le_A_of_clone_limit {k : ℕ} {M : ℝ}
    (realize : ∀ L : ℕ, [NeZero L] → k < 3*L →
      ∃ out : Election, (∀ v, Function.Injective (out.rank v)) ∧
        k < Fintype.card out.C ∧ blocksList out k (M-1/(L:ℝ))) :
    M ≤ A k := by
  by_contra! bad
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt (sub_pos.mpr bad)
  let L := n + k + 1
  have : NeZero L := ⟨by dsimp [L]; omega⟩
  obtain ⟨e,s,size,H⟩ := realize L (by dsimp [L]; omega)
  have hA := le_A_of_mem (mem_realizableK_of_list _ s size H)
  have hpos : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hden : (n:ℝ)+1 ≤ (L:ℝ) := by dsimp [L]; push_cast; linarith
  have hcut : 1/(L:ℝ) < M-A k := (one_div_le_one_div_of_le hpos hden).trans_lt hn
  linarith

theorem graded_realization_le_A {G : Type} [Fintype G] [Nonempty G]
    {n : ℕ} [NeZero n] (tab : Grades G n) (k : ℕ)
    (e : Election) (ce : 3 ≤ Fintype.card e.C) {a M : ℝ} (hp : blocks e a)
    (cert : ∀ rs : List G, rs.length = k → ∃ g : G, M ≤
      mean (fun i => rowCredit a (tab.grade i g) (rs.map (tab.grade i)))) : M ≤ A k :=
  le_A_of_clone_limit fun L _ hk => graded_realization tab k L hk e ce hp cert

theorem weighted_realization_le_A {R G : Type} [Fintype R] [Fintype G] [Nonempty G]
    (w : R → ℕ) (wpos : 0 < ∑ i, w i) (grade : R → G → ℕ) (k : ℕ)
    (e : Election) (ce : 3 ≤ Fintype.card e.C) {a M : ℝ} (hp : blocks e a)
    (cert : ∀ rs : List G, rs.length = k → ∃ g : G, M ≤
      (∑ i, (w i:ℝ)*rowCredit a (grade i g) (rs.map (grade i))) / (∑ i, w i : ℕ)) :
    M ≤ A k :=
  le_A_of_clone_limit fun L _ hk => weighted_realization w wpos grade k L hk e ce hp cert

/-- An inner election can be chosen at any level strictly below the pair supremum. -/
theorem pair_source_below {a : ℝ} (ha : a < A₂) :
    ∃ e : Election, (∀ v, Function.Injective (e.rank v)) ∧
      3 ≤ Fintype.card e.C ∧ blocks e a := by
  rw [← A_two_eq] at ha
  obtain ⟨e,s,hc,H⟩ := finite_witness_below ha
  exact ⟨e,s,hc,(blocksList_two e a).mp ((list_iff_committees e 2 a hc).mpr H)⟩

end
end ElectionLift
