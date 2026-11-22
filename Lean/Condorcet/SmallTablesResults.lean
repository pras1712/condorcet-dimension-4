import Condorcet.SmallTables
import Condorcet.SmallTablesPair
import Condorcet.RealizationBound

namespace ElectionLift.SmallTables
open Finset
open scoped BigOperators
noncomputable section

/-- When an inner bound is below the pair supremum, a weighted grade certificate
bounds the opposition supremum among genuine strict finite elections. -/
theorem weighted_bound {R G : Type} [Fintype R] [Fintype G] [Nonempty G]
    (w : R → ℕ) (wpos : 0 < ∑ i, w i) (g : R → G → ℕ)
    (k : ℕ) {a M : ℝ} (ha : a < A₂)
    (cert : ∀ rs : List G, rs.length = k → ∃ h, M ≤ score w g rs h a / (∑ i, w i : ℕ)) :
    M ≤ A k := by
  obtain ⟨e,_,hc,hp⟩ := pair_source_below ha
  exact weighted_realization_le_A w wpos g k e hc hp cert

/-- Proposition 4, obtained from the three short words alone. -/
theorem hand_pair : (2:ℝ)/3 < A₂ := by
  by_contra! bad
  let a := A₂-1/1458
  have hlt : a < A₂ := by dsimp [a]; linarith
  have hh := weighted_bound pairWeight (by rw [pairWeight_sum]; decide) pairGrade 2 hlt
    (pair_gain (hlt.le.trans bad))
  rw [A_two_eq] at hh
  dsimp [a] at hh
  linarith

/-- Pass a positive affine bound through the pair supremum using rational inner
bounds strictly less than it. Consequently all row weights in every witness are rational. -/
private theorem from_rational (k : ℕ) {b c d : ℝ} (hp : 0 < b) (hd : 0 < d)
    (H : ∀ q : ℚ, 2/3 < (q:ℝ) → (q:ℝ) < A₂ → (b*(q:ℝ)+c)/d ≤ A k) :
    (b*A₂+c)/d ≤ A k := by
  by_contra! bad
  have lt : (A k*d-c)/b < A₂ := (div_lt_iff₀ hp).mpr (by linarith [(lt_div_iff₀ hd).mp bad])
  obtain ⟨q,h₁,h₂⟩ := exists_rat_btwn (max_lt hand_pair lt)
  have h := H q ((le_max_left ..).trans_lt h₁) h₂
  have t := (div_lt_iff₀ hp).mp ((le_max_right ..).trans_lt h₁)
  linarith [(div_le_iff₀ hd).mp h]

private theorem pair_le_one : A₂ ≤ 1 := by simpa only [A_two_eq] using A_le_one 2

/-- Proposition 5, the six-row hand triple bound. -/
theorem easy_triple : (1+3*A₂)/6 ≤ A 3 := by
  rw [add_comm]
  apply from_rational 3 (by norm_num) (by norm_num)
  intro q hq qa
  apply weighted_bound (fun _ : Fin 6 => 1) (by decide) easyGrade 3 qa
  intro rs hs
  obtain ⟨h,v⟩ := easy_triple_table hq.le (qa.le.trans pair_le_one) rs hs
  refine ⟨h,?_⟩
  simpa [add_comm] using div_le_div_of_nonneg_right v (by norm_num : (0:ℝ) ≤ 6)

/-- The four weighted binary rows of Proposition 7. -/
theorem four_seats : 3*A₂/5 ≤ A 4 := by
  rw [←add_zero (3*A₂)]
  apply from_rational 4 (by norm_num) (by norm_num)
  intro q hq qa
  apply weighted_bound quartetWeight (by decide) quartetGrade 4 qa
  intro rs hs
  obtain ⟨h,v⟩ := quartet_table hq.le (qa.le.trans pair_le_one) rs hs
  have total : ∑ j, quartetWeight j = 5 := by decide
  refine ⟨h,?_⟩
  simpa [total] using div_le_div_of_nonneg_right v (by norm_num : (0:ℝ) ≤ 5)

/-- The family indexed by a rational pair bound uses p copies of each row of
its first half and (n-p) copies of each row of its second half, for a=p/n. -/
private theorem integer_shares (q : ℚ) (hq : 0 ≤ (q:ℝ)) (hb : (q:ℝ) ≤ 1) :
    ∃ p n : ℕ, 0<n ∧ p≤n ∧ (p:ℝ) = q*n := by
  have hq' : 0 ≤ q := by exact_mod_cast hq
  have num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr hq')
  have conv : (q.num.natAbs:ℝ) = (q.num:ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z:ℤ => (z:ℝ)) num
  have id : (q.num.natAbs:ℝ) = (q:ℝ)*q.den := by
    rw [Rat.cast_def, div_mul_cancel₀ _ (by exact_mod_cast q.den_ne_zero)]
    exact conv
  have le : (q.num.natAbs:ℝ) ≤ q.den := by
    rw [id]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hb (Nat.cast_nonneg (α:=ℝ) q.den)
  exact ⟨q.num.natAbs, q.den, q.den_pos, by exact_mod_cast le, id⟩

/-- Proposition 6, using both four-row families at rational weights. -/
theorem sharp_triple : 3*A₂/4 ≤ A 3 := by
  rw [←add_zero (3*A₂)]
  apply from_rational 3 (by norm_num) (by norm_num)
  intro q hq qa
  have qb := qa.le.trans pair_le_one
  obtain ⟨p,n,hn,hpn,peq⟩ := integer_shares q (by linarith) qb
  let w : Fin 4 ⊕ Fin 4 → ℕ := Sum.elim (fun _ => p) (fun _ => n-p)
  let g : Fin 4 ⊕ Fin 4 → Fin 8 → ℕ := Sum.elim (sharpGrade false) (sharpGrade true)
  have total : ∑ j, w j = 4*n := by
    simp only [w,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,Finset.sum_const,
      Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    omega
  apply weighted_bound w (by rw [total]; omega) g 3 qa
  intro rs hs
  obtain ⟨h,v⟩ := sharp_triple_table hq.le qb rs hs
  refine ⟨h,?_⟩
  have sumScore : score w g rs h q = (p:ℝ)*score (fun _ => 1) (sharpGrade false) rs h q +
      ((n-p:ℕ):ℝ)*score (fun _ => 1) (sharpGrade true) rs h q := by
    simp [score,w,g,Fintype.sum_sum_type,Finset.mul_sum]
  rw [sumScore,total]
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  push_cast
  have den : (0:ℝ)<4*n := by positivity
  apply (le_div_iff₀ den).mpr
  rw [Nat.cast_sub hpn,peq]
  nlinarith [mul_le_mul_of_nonneg_right v hn'.le]

end
end ElectionLift.SmallTables
