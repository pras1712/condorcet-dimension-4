import Condorcet.RealizationBound
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FieldSimp

namespace ElectionLift
noncomputable section
open Finset
open scoped BigOperators

/-- Put a finite distribution of rational row weights over a common denominator,
including the rows of weight zero. -/
theorem integer_row_weights {R : Type} [Fintype R] (w : R → ℚ)
    (hn : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) :
    ∃ m : R → ℕ, 0 < ∑ i, m i ∧ ∀ i, (m i : ℝ) = (∑ j, m j : ℕ) * (w i : ℝ) := by
  classical
  let D : ℕ := ∏ i, (w i).den
  have hd : 0 < D := Finset.prod_pos (fun i _ => (w i).den_pos)
  have divides (i : R) : (w i).den ∣ D := Finset.dvd_prod_of_mem _ (mem_univ i)
  choose u hu using divides
  let m i := u i * (w i).num.toNat
  have eqn (i : R) : (m i : ℝ) = D * (w i : ℝ) := by
    have nnum : (0:ℤ) ≤ (w i).num := Rat.num_nonneg.mpr (hn i)
    have pos : ((w i).den : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (w i).den_ne_zero
    have natcast : ((w i).num.toNat : ℝ) = ((w i).num : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg nnum
    change (((u i * (w i).num.toNat : ℕ) : ℝ)) = _
    rw [Rat.cast_def, hu i]
    simp only [Nat.cast_mul,natcast]
    field_simp
  have sr : (∑ i, (w i:ℝ)) = 1 := by exact_mod_cast hs
  have sd : (∑ i, m i : ℕ) = D := by
    have hm : ((∑ i, m i : ℕ) : ℝ) = (D:ℝ) := by
      push_cast
      simp_rw [eqn]
      rw [←Finset.mul_sum,sr,mul_one]
    exact_mod_cast hm
  exact ⟨m,sd ▸ hd,fun i => sd ▸ eqn i⟩

def rationalTableScore {R G : Type} [Fintype R] (w : R → ℚ) (grade : R → G → ℕ)
    (a : ℝ) (r : List G) (g : G) : ℝ :=
  ∑ i, (w i:ℝ) * rowCredit a (grade i g) (r.map (grade i))

/-- The minimum over rival tuples of the maximum over all challenger assignments. -/
def rationalTableValue {R G : Type} [Fintype R] [Fintype G] [Nonempty G]
    (w : R → ℚ) (grade : R → G → ℕ) (a : ℝ) (k : ℕ) : ℝ :=
  (univ : Finset (Fin k → G)).inf' univ_nonempty fun r =>
    (univ : Finset G).sup' univ_nonempty (rationalTableScore w grade a (List.ofFn r))

theorem rational_table_response {R G : Type} [Fintype R] [Fintype G] [Nonempty G]
    (w : R → ℚ) (grade : R → G → ℕ) (a : ℝ) (k : ℕ) (rs : List G) (hlen : rs.length=k) :
    ∃ g, rationalTableValue w grade a k ≤ rationalTableScore w grade a rs g := by
  classical
  subst k
  obtain ⟨g,_,hg⟩ := Finset.exists_mem_eq_sup' (s := (univ : Finset G))
    univ_nonempty (rationalTableScore w grade a rs)
  refine ⟨g,le_trans ?_ hg.le⟩
  unfold rationalTableValue
  have h := Finset.inf'_le (fun r : Fin rs.length → G =>
    (univ : Finset G).sup' univ_nonempty (rationalTableScore w grade a (List.ofFn r)))
    (mem_univ rs.get)
  simpa only [List.ofFn_get] using h

/-- Lemma 2 in its exact finite form, with arbitrary rational position
weights and the actual min-max score of the grade table. -/
theorem rational_grade_realization {R G : Type} [Fintype R] [Fintype G] [Nonempty G]
    (w : R → ℚ) (hn : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (grade : R → G → ℕ)
    (k L : ℕ) [NeZero L] (hk : k < 3*L)
    (e : Election) (ce : 3 ≤ Fintype.card e.C) {a : ℝ} (hp : blocks e a) :
    ∃ out : Election, (∀ v, Function.Injective (out.rank v)) ∧
      k < Fintype.card out.C ∧
      blocksList out k (rationalTableValue w grade a k - 1/(L:ℝ)) := by
  obtain ⟨m,hm,hmw⟩ := integer_row_weights w hn hs
  apply weighted_realization m hm grade k L hk e ce hp
  intro rs hlen
  obtain ⟨g,hg⟩ := rational_table_response w grade a k rs hlen
  refine ⟨g, hg.trans ?_⟩
  apply le_of_eq
  unfold rationalTableScore
  apply (eq_div_iff (Nat.cast_ne_zero.mpr hm.ne')).mpr
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [hmw i]
  ring

theorem rational_grade_value_le {R G : Type} [Fintype R] [Fintype G] [Nonempty G]
    (w : R → ℚ) (hn : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (grade : R → G → ℕ)
    (k : ℕ) (e : Election) (ce : 3 ≤ Fintype.card e.C) {a : ℝ} (hp : blocks e a) :
    rationalTableValue w grade a k ≤ A k :=
  le_A_of_clone_limit fun L _ hk => rational_grade_realization w hn hs grade k L hk e ce hp

end
end ElectionLift
